use crate::terminal::StyleId;

pub(crate) const ASCII_ART: &str = r#"
       ───────────────────────────────
       ███████████████████████████████
       ▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇
     █▀▀█   ██▀▀█████▀▀▀█████▀▀█   ██▀▀█
     █                                 █
     █▄▄█   ██▄▄█████▄▄▄█████▄▄█   ██▄▄█
       ██████ rusty razor  1.0 ███████
       ▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇▇
       ───────────────────────────────
"#;
pub(crate) const STYLE_LOGO: StyleId = 0;
pub(crate) const STYLE_INFO: StyleId = 1;
pub(crate) const STYLE_THEORY: StyleId = 2;
pub(crate) const STYLE_MODEL_DOMAIN: StyleId = 3;
pub(crate) const STYLE_MODEL_FACTS: StyleId = 4;
