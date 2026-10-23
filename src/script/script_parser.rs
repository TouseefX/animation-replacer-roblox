use crate::StudioParser;
use rbx_dom_weak::types::Variant;
use fancy_regex::Regex;
use roboat::assetdelivery::AssetBatchResponse;
use std::collections::HashSet;
use tracing::info;
use ustr::Ustr;

impl StudioParser {
    /// Returns a vector of AssetBatchResponse (Animation Details from batch API) found in the script
    /// # Notes:
    /// Takes in a script, scans all the IDs into it then has batch_sizes of 250.
    /// It posts 250 Ids at a time to the asset batch API then filters out everything but
    /// animations.
    /// * Requires a cookie
    /// * Batch API does hang sometimes, fixed that with retries and 3 second timeout.
    pub async fn all_animations_in_scripts(
        &mut self,
        unformatted_search: bool,
    ) -> anyhow::Result<Vec<AssetBatchResponse>> {
        let script_refs = self.get_script_refs();

        // High-performance context pattern
        // Flags used: (?x) allows spaces/comments, (?i) makes it case-insensitive
        let pattern = if unformatted_search {
            Regex::new(r"(?xi)
                (?:
                    # Context 1: Function calls like playeranimation(char, 1234567) or LoadAnimation(1234567)
                    \b[a-z0-9_]+\s*\([^)]*\b
                    |
                    # Context 2: Table Arrays/Dictionaries like {1234567, 891011} or id = 1234567
                    [{,=\[]\s*
                    |
                    # Context 3: Standard Asset Property strings
                    rbxassetid://|id=
                )
                # Capture target: matches 6 to 12 digits
                (\d{6,12})
                # Lookahead boundary context check
                (?=\b|[\s,}\)]|$)
            ").unwrap()
        } else {
            Regex::new(r"(?:rbxassetid:\/\/|roblox\.com\/asset\/\?id=)(\d{6,12})").unwrap()
        };

        // Collect and deduplicate all IDs from all scripts
        let mut all_ids: HashSet<u64> = HashSet::new();
        for script_ref in &script_refs {
            if let Some(instance) = self.dom.get_by_ref(*script_ref)
                && let Some(Variant::String(source)) =
                    instance.properties.get(&Ustr::from("Source"))
            {
                // FIX: Running directly on `source` instead of character filtering loop copies.
                // .flatten() handles fancy-regex's wrapper format flawlessly.
                for cap in pattern.captures_iter(source).flatten() {
                    if let Some(id_match) = cap.get(1)
                        && let Ok(id) = id_match.as_str().parse::<u64>()
                    {
                        all_ids.insert(id);
                    }
                }
            }
        }
        
        // Convert to Vec and fetch assets
        let mut id_list: Vec<u64> = all_ids.into_iter().collect();
        id_list.sort();
        info!("{:?}", id_list);
        info!("Got asset ids from scripts: {}", id_list.len());
        self.fetch_animation_assets(id_list).await
    }

    /// Gets references to all script instances in the DOM.
    pub fn get_script_refs(&self) -> Vec<rbx_dom_weak::types::Ref> {
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
