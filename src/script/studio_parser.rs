//! Asset-id extraction for `StudioParser`.
//!
//! Drop-in replacement for the `impl StudioParser` block that holds
//! `all_animations_in_scripts` / `get_script_refs`.
//!
//! # What changed vs. the old two-branch regex
//!
//! The old pattern only recognised `rbxassetid://N` and `roblox.com/asset/?id=N`,
//! plus an all-or-nothing "any 6+ digit number" fallback. This version recognises
//! eight *tiers* of evidence in a single pass, and lets you pick how far down the
//! ladder you want to go via [`SearchMode`].
//!
//! | Tier       | Named group | Example                                        | Strict | Contextual | Everything |
//! |------------|-------------|------------------------------------------------|:------:|:----------:|:----------:|
//! | 1 uri      | `uri`       | `rbxassetid://14382749013`                     |   ✅   |     ✅     |     ✅     |
//! | 1 thumb    | `thumb`     | `rbxthumb://type=Animation&id=383728&w=150`    |   ✅   |     ✅     |     ✅     |
//! | 2 url      | `url`       | `roblox.com/library/1234567890/Song`           |   ✅   |     ✅     |     ✅     |
//! | 3 key      | `key`       | `SoundId = 138620809`, `["MeshId"]=102076772`  |        |     ✅     |     ✅     |
//! | 4 call     | `call`      | `loadanimation(383728)`, `module.load(8378239)`|        |     ✅     |     ✅     |
//! | 5 quoted   | `quoted`    | `{"666777888"}`                                |        |     ✅     |     ✅     |
//! | 6 list     | `list`      | `{38378282, 83728272}`, `{[903338113] = true}` |        |     ✅     |     ✅     |
//! | 7 bare     | `bare`      | `return 333322221111`                          |        |            |     ✅     |
//!
//! A tier-0 "swallow" branch runs first and *consumes* constructs that never hold
//! an asset id (hex/float/exponent literals, `for i = 1, 1000000 do`,
//! `Vector3.new(...)`, `Random.new(seed)`, `task.wait(...)`, `UserId = ...`), so
//! their digits never reach a lower tier.

use std::borrow::Cow;
use std::collections::HashSet;
use std::sync::LazyLock;

use fancy_regex::Regex;
use rbx_dom_weak::types::{Ref, Variant};
use roboat::assetdelivery::AssetBatchResponse;
use tracing::{debug, info, trace, warn};
use ustr::Ustr;

use crate::StudioParser;

// ═══════════════════════════════════════════════════════════════════════════
//  Public knobs
// ═══════════════════════════════════════════════════════════════════════════

/// How aggressively to treat a number as an asset id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SearchMode {
    /// Only `rbxassetid://`, `rbxthumb://…id=` and roblox.com URLs.
    /// Effectively zero false positives, but misses bare numeric ids.
    Strict,

    /// **Recommended.** Everything in [`Strict`](SearchMode::Strict) plus ids that
    /// have syntactic evidence behind them: an `…Id = N` assignment, an
    /// `load/require/play/insert…(N)` call, an all-digit string literal, or an
    /// element of a table / argument list.
    #[default]
    Contextual,

    /// Everything in [`Contextual`](SearchMode::Contextual) plus *any* bare run of
    /// 6+ digits. Equivalent to the old `unformatted_search = true`.
    Everything,
}

impl From<bool> for SearchMode {
    /// Back-compat shim so existing `all_animations_in_scripts(true)` /
    /// `all_animations_in_scripts(false)` call sites keep compiling.
    /// `true` -> [`Everything`](SearchMode::Everything),
    /// `false` -> [`Contextual`](SearchMode::Contextual).
    fn from(unformatted_search: bool) -> Self {
        if unformatted_search {
            SearchMode::Everything
        } else {
            SearchMode::Contextual
        }
    }
}

/// Which syntactic shape produced a candidate id. Ordered most -> least confident.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Tier {
    /// `rbxassetid://123`
    Uri,
    /// `rbxthumb://…&id=123`
    Thumb,
    /// `roblox.com/library/123/…`
    Url,
    /// `AnimationId = 123`
    Key,
    /// `loadanimation(123)`
    Call,
    /// `"123456"`
    Quoted,
    /// `{ 123456, 789012 }` / `f(123456)`
    List,
    /// any other bare `123456`
    Bare,
}

/// `(capture-group name, tier)` in the order they appear in the pattern.
const TIERS: [(&str, Tier); 8] = [
    ("uri", Tier::Uri),
    ("thumb", Tier::Thumb),
    ("url", Tier::Url),
    ("key", Tier::Key),
    ("call", Tier::Call),
    ("quoted", Tier::Quoted),
    ("list", Tier::List),
    ("bare", Tier::Bare),
];

impl Tier {
    #[inline]
    pub fn enabled_by(self, mode: SearchMode) -> bool {
        match mode {
            SearchMode::Strict => matches!(self, Tier::Uri | Tier::Thumb | Tier::Url),
            SearchMode::Contextual => !matches!(self, Tier::Bare),
            SearchMode::Everything => true,
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════
//  The pattern
// ═══════════════════════════════════════════════════════════════════════════
//
// Compiled ONCE, at first use. The previous code called `Regex::new(..).unwrap()`
// on every invocation of `all_animations_in_scripts`, which re-runs the regex
// compiler each time.
//
// Two deliberate choices worth knowing about:
//
//  * `[0-9]` rather than `\d`. In Rust's `regex` crate `\d` is Unicode `\p{Nd}`,
//    so it also matches Arabic-Indic / Devanagari digits. Those then fail
//    `parse::<u64>()` and get silently dropped. `[0-9]` is ASCII-exact.
//
//  * No global `(?i)`. Case-insensitivity is scoped with `(?i:…)` only where it
//    belongs (URI schemes, url paths, call/keyword names). Keeping the `id`
//    suffix case-*sensitive* is what lets us tell `AssetId` apart from `valid`,
//    `guid`, `width` and `identity`.
static ASSET_ID_RE: LazyLock<Regex> = LazyLock::new(|| {
    let pattern = concat!(
        // ── Tier 0: swallow constructs that never hold an asset id ──────────
        r#"(?:0[xXbB][0-9a-fA-F]+"#,                       // 0xFF00AA
        r#"|[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?"#,          // 1730457600.5
        r#"|[0-9]+[eE][+-]?[0-9]+"#,                       // 1e300
        r#"|for\b[^()\n]*\bdo\b"#,                         // for i = 1, 1000000 do
        r#"|(?<![\w.])(?:task\s*\.\s*)?(?:wait|delay|spawn)\s*\([^()]*\)"#,
        r#"|(?<![\w.])(?:print|warn|error|assert|typeof|type|tostring|tonumber)\s*\([^()]*\)"#,
        r#"|(?:Vector3|Vector2|CFrame|UDim2?|Rect|Color3|ColorSequence|NumberRange"#,
        r#"|NumberSequence|PhysicalProperties|BrickColor|Random|DateTime|Axes|Faces"#,
        r#"|Region3|Ray|PathWaypoint|string|table|math|os|bit32|tick|coroutine)"#,
        r#"\s*(?:\.\s*\w+\s*)?\([^()]*\)"#,
        r#"|(?<![\w.])(?i:[\w.]*(?:user|player|account|group|place|job|session|device|team)id)"#,
        r#"[\w.]*\s*[=:]\s*["'`\]]*[0-9]+)"#,
        //
        // ── Tier 1: rbxassetid:// and rbxthumb:// ───────────────────────────
        // No length floor here: the prefix is already proof.
        r#"|(?i:rbxasset(?:id)?://)(?P<uri>[0-9]{1,19})(?![\w.])"#,
        r#"|(?i:rbxthumb://)[^\s"'`)\]}]*?(?i:[?&]id=)(?P<thumb>[0-9]{1,19})(?![\w.])"#,
        //
        // ── Tier 2: roblox web urls ─────────────────────────────────────────
        r#"|(?i:(?:roblox\.com|roblox\.cn)/(?:asset/?\?id=|library/|catalog/"#,
        r#"|items/|bundles/|marketplace/asset/))(?P<url>[0-9]{1,19})(?![\w.])"#,
        //
        // ── Tier 3: `AnimationId = 123`, `id: 123`, `["MeshId"]=123` ────────
        // The identifier must end in an `id` *component* (camelCase, SCREAMING,
        // snake_case, `.`/`:` member, or the whole token) — that is what stops
        // `valid`, `guid`, `width`, `identity` and `solid` from matching.
        // An optional Luau type annotation (`: number`, `: number?`, `: {number}`)
        // is allowed between the name and the `=`.
        r#"|(?<![\w.])(?:(?:"#,
        r#"[\w.]*[a-z0-9]I[Dd]"#,      // AssetId, soundId
        r#"|[\w.]*[A-Z]I[D]"#,         // ASSETID
        r#"|[\w.]*_[iI][dD]"#,         // asset_id, ASSET_ID
        r#"|[\w.]*[.:][iI][dD]"#,      // props.id, self:Id
        r#"|[iI][dD]"#,                // id, Id, ID
        r#")[?]?"#,
        r#"|[\w.]*(?i:asset|animation|anim|sound|image|decal|texture|mesh|emote"#,
        r#"|bundle|package|thumbnail|song|music|audio|video|track)[\w.]*)"#,
        r#"["'`\]]*\s*(?::\s*[\w.|?<>\[\](){}]+\s*)?[=:]\s*["'`\]]*"#,
        r#"(?P<key>[0-9]{4,19})(?![\w.])"#,
        //
        // ── Tier 4: call whose name hints at loading an asset ───────────────
        r#"|(?<![\w.])(?i:[\w.]*(?:load|require|insert|play|get|fetch|create|new|from"#,
        r#"|add|use|equip|apply|resolve|import|clone|build|purchase|own|find)[\w.]*)"#,
        r#"\s*[(\[]\s*["'`\]]*(?P<call>[0-9]{4,19})(?![\w.])"#,
        //
        // ── Tier 5: a string literal that is nothing but digits ─────────────
        r#"|["'`](?P<quoted>[0-9]{6,19})["'`]"#,
        //
        // ── Tier 6: element of a table constructor / argument list ──────────
        r#"|[{,(\[]\s*(?P<list>[0-9]{6,19})(?![\w.])"#,
        //
        // ── Tier 7: any other bare run of 6+ digits ─────────────────────────
        r#"|(?:^|[^\w.])(?P<bare>[0-9]{6,19})(?![\w.])"#,
    );

    Regex::new(pattern).expect("ASSET_ID_RE failed to compile")
});

// ═══════════════════════════════════════════════════════════════════════════
//  Extraction
// ═══════════════════════════════════════════════════════════════════════════

/// Neutralises control characters **without deleting them**.
///
/// The old code did `.filter(|c| !c.is_control())`, which *removed* newlines and
/// tabs. That glues adjacent lines together, so
///
/// ```lua
/// local x = 1
/// 23456789
/// ```
///
/// became `local x = 123456789` and produced a phantom id. Mapping control
/// characters to a space keeps token boundaries intact, and keeping `\n` as `\n`
/// preserves the line anchor used by the `for … do` swallow rule.
fn sanitize(source: &str) -> Cow<'_, str> {
    if !source.chars().any(|c| c.is_control() && c != '\n') {
        return Cow::Borrowed(source);
    }
    Cow::Owned(
        source
            .chars()
            .map(|c| if c == '\n' { '\n' } else if c.is_control() { ' ' } else { c })
            .collect(),
    )
}

/// Pulls candidate asset ids out of one Luau source string.
///
/// Returns `(tier, id)` pairs, de-duplicated by id and ordered by first
/// appearance. Because the regex alternatives are ordered most-confident first,
/// the tier recorded for an id is the strongest evidence found for it.
///
/// This is a free function on purpose: it needs no `WeakDom`, so it is trivially
/// unit-testable.
pub fn extract_asset_ids(source: &str, mode: SearchMode) -> Vec<(Tier, u64)> {
    let text = sanitize(source);

    let mut seen: HashSet<u64> = HashSet::new();
    let mut out: Vec<(Tier, u64)> = Vec::new();

    // `fancy_regex` yields `Result<Captures, Error>` because the backtracking VM
    // can fail part-way through an iteration.
    for caps in ASSET_ID_RE.captures_iter(&text) {
        let Ok(caps) = caps else { continue };

        for (group, tier) in TIERS {
            let Some(m) = caps.name(group) else { continue };
            if !tier.enabled_by(mode) {
                break; // this match was won by a disabled tier -> drop it
            }
            if let Ok(id) = m.as_str().parse::<u64>() {
                if seen.insert(id) {
                    out.push((tier, id));
                }
            }
            break; // only one named group can win per match
        }
    }

    out
}

impl StudioParser {
    /// Returns every animation (from the asset batch API) referenced anywhere in
    /// the place's scripts.
    ///
    /// # Notes
    ///
    /// Scans all `Script` / `LocalScript` / `ModuleScript` sources in one regex
    /// pass, de-duplicates the ids, then posts them to the asset batch API in
    /// chunks of 250 and keeps only animations.
    ///
    /// * Requires a cookie.
    /// * The batch API hangs sometimes; that is handled by retries + a 3s timeout
    ///   in `fetch_animation_assets`.
    ///
    /// `mode` accepts a [`SearchMode`] **or** the old `bool`
    /// (`true` -> `Everything`, `false` -> `Contextual`), so existing call sites
    /// do not need to change.
    pub async fn all_animations_in_scripts<M: Into<SearchMode>>(
        &mut self,
        mode: M,
    ) -> anyhow::Result<Vec<AssetBatchResponse>> {
        let mode = mode.into();
        let script_refs = self.get_script_refs();

        // Hoisted out of the loop: `Ustr::from` interns, so doing it per-script
        // was a pointless hash + lookup every iteration.
        let source_key = Ustr::from("Source");

        let mut all_ids: HashSet<u64> = HashSet::new();
        let mut tier_counts: [usize; 8] = [0; 8];

        for script_ref in &script_refs {
            let Some(instance) = self.dom.get_by_ref(*script_ref) else {
                continue;
            };
            let Some(Variant::String(source)) = instance.properties.get(&source_key) else {
                continue;
            };

            for (tier, id) in extract_asset_ids(source, mode) {
                tier_counts[tier as usize] += 1;
                all_ids.insert(id);
            }
        }

        let mut id_list: Vec<u64> = all_ids.into_iter().collect();
        id_list.sort_unstable();

        // Was `info!("{:?}", id_list)` — that dumps potentially thousands of ids
        // into your logs on every run. Kept at trace, with a summary at info.
        debug!(mode = ?mode, scripts = script_refs.len(), "tier hits: {:?}", tier_breakdown(&tier_counts));
        trace!(ids = ?id_list);
        info!("Got {} unique asset ids from {} scripts", id_list.len(), script_refs.len());

        if id_list.is_empty() {
            warn!("No asset ids found in any script — check that sources were actually loaded");
        }

        self.fetch_animation_assets(id_list).await
    }

    /// References to every script-like instance in the DOM.
    pub fn get_script_refs(&self) -> Vec<Ref> {
        self.dom
            .descendants()
            .filter(|instance| {
                matches!(
                    instance.class.as_str(),
                    "Script" | "LocalScript" | "ModuleScript"
                )
            })
            .map(|instance| instance.referent())
            .collect()
    }
}

fn tier_breakdown(counts: &[usize; 8]) -> Vec<(&'static str, usize)> {
    TIERS
        .iter()
        .map(|(_, t)| (tier_name(*t), counts[*t as usize]))
        .filter(|(_, n)| *n > 0)
        .collect()
}

fn tier_name(tier: Tier) -> &'static str {
    match tier {
        Tier::Uri => "uri",
        Tier::Thumb => "thumb",
        Tier::Url => "url",
        Tier::Key => "key",
        Tier::Call => "call",
        Tier::Quoted => "quoted",
        Tier::List => "list",
        Tier::Bare => "bare",
    }
}

// ═══════════════════════════════════════════════════════════════════════════
//  Tests — `cargo test extract`
// ═══════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    fn ids(src: &str, mode: SearchMode) -> HashSet<u64> {
        extract_asset_ids(src, mode).into_iter().map(|(_, id)| id).collect()
    }

    const SRC: &str = r#"
local Anim = Instance.new("Animation")
Anim.AnimationId = "rbxassetid://14382749013"
local old = "rbxassetid://1816865187"
local url = "https://www.roblox.com/asset/?id=1816865187"
local thumb = "rbxthumb://type=Animation&id=383728&w=150&h=150"
local lib   = "https://www.roblox.com/library/1234567890/Cool-Song"
local a = loadanimation(383728)
local b = module.load(8378239)
local d = InsertService:LoadAsset(181590540)
local e = require(4987234987)
local ids = {38378282, 83728272}
local multi = {
    111222333,
    444555666,
}
local keyed = {[903338113] = true, [903338114] = true}
local strings = {"666777888"}
local SoundId = 138620809
local props = { AssetId = 181590540, TextureId = "rbxassetid://7021445199", ["MeshId"]=102076772 }
local Animation = 5596115440
local AnimationId: number = 1234567891
local DecalId2: number? = 8888991
local ASSET_ID = 8888992
local id = 8888995
local Z = pcall(loadanimation, 444433332222)
local Y = 333322221111
"#;

    const NOISE: &str = r#"
local stamp = 1730457600.5
local ratio = 3.141592653589
local hex = 0xFF00AA
local small = 12345
local mathy = 999999 * 1000000
local seed = Random.new(1234567)
task.wait(1000000)
local v = Vector3.new(1000000, 0, 0)
local rep = string.rep("a", 1000000)
for i = 1, 1000000 do print(i) end
local UserId = 2837465
local PlaceId = 4455667
print(7788990)
warn(7788990)
local identity = 1000000
local valid = 1000000
local guid = 1000000
local width = 1000000
local bc = BrickColor.new(1000000)
local AssetId = 123456.7
local SoundId = 7654321.5
local MeshId: number = 1111222.25
loadanimation(3333444.5)
local img = "rbxassetid://4444555.5"
"#;

    #[test]
    fn contextual_finds_every_requested_shape() {
        let got = ids(SRC, SearchMode::Contextual);
        for want in [
            14382749013u64, // AnimationId = "rbxassetid://N"
            1816865187,     // rbxassetid:// + url + quoted
            383728,         // rbxthumb id= / loadanimation(N)
            1234567890,     // /library/N/Name
            8378239,        // module.load(N)
            181590540,      // LoadAsset(N) / AssetId = N
            4987234987,     // require(N)
            38378282,       // {a, b}
            83728272,       // {a, b}
            111222333,      // multi-line table
            444555666,      // multi-line table
            903338113,      // {[N] = true}
            903338114,      // {[N] = true}
            138620809,      // SoundId = N
            7021445199,     // TextureId = "rbxassetid://N"
            102076772,      // ["MeshId"] = N
            5596115440,     // Animation = N
            1234567891,     // AnimationId: number = N
            8888991,        // DecalId2: number? = N
            8888992,        // ASSET_ID = N
            8888995,        // id = N
            666777888,      // "666777888"
            444433332222,   // pcall(loadanimation, N)
        ] {
            assert!(got.contains(&want), "missed {want}");
        }
    }

    #[test]
    fn contextual_rejects_noise() {
        let got = ids(NOISE, SearchMode::Contextual);
        for nope in [
            1730457600u64, // float
            16711850,      // 0xFF00AA
            12345,         // too short
            999999,        // math operand
            1234567,       // Random.new(seed)
            1000000,       // wait / Vector3 / for / rep / BrickColor / valid / guid / width
            123456, 7654321, 1111222, 3333444, // float heads must not be truncated into ids
            4444555,
            2837465,       // UserId
            4455667,       // PlaceId
            7788990,       // print() / warn()
        ] {
            assert!(!got.contains(&nope), "false positive {nope}");
        }
    }

    #[test]
    fn bare_runs_only_in_everything_mode() {
        assert!(!ids(SRC, SearchMode::Contextual).contains(&333322221111));
        assert!(ids(SRC, SearchMode::Everything).contains(&333322221111));
    }

    #[test]
    fn strict_only_accepts_prefixed_forms() {
        let got = ids(SRC, SearchMode::Strict);
        assert_eq!(
            got,
            [14382749013u64, 1816865187, 383728, 1234567890, 7021445199]
                .into_iter()
                .collect()
        );
    }

    #[test]
    /// Regression: stripping control chars used to glue lines together and
    /// invent ids. They must be replaced with a space, not deleted.
    fn control_chars_do_not_invent_ids() {
        let src = "local x = 1\n23456789\nlocal y = 2\r\n34567890";
        let got = ids(src, SearchMode::Everything);
        assert!(!got.contains(&123456789), "phantom id from line-gluing");
        assert!(got.contains(&23456789) && got.contains(&34567890));
    }

    #[test]
    fn bool_still_converts() {
        assert_eq!(SearchMode::from(true), SearchMode::Everything);
        assert_eq!(SearchMode::from(false), SearchMode::Contextual);
    }

    #[test]
    fn unicode_digits_are_ignored() {
        // `\d` in Rust is Unicode \p{Nd}; we deliberately use [0-9].
        assert!(ids("local x = ١٢٣٤٥٦٧٨٩ and y = {١٢٣٤٥٦٧٨٩}", SearchMode::Everything).is_empty());
    }
}
