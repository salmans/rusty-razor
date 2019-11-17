use term::{color::{BRIGHT_RED, GREEN, BRIGHT_YELLOW, BRIGHT_BLUE}};

pub const INFO_COLOR: term::color::Color = 27;
pub const LOGO_TOP_COLOR: term::color::Color = 136;
pub const ERROR_COLOR: term::color::Color = BRIGHT_RED;
pub const MODEL_DOMAIN_COLOR: term::color::Color = GREEN;
pub const MODEL_ELEMENTS_COLOR: term::color::Color = BRIGHT_YELLOW;
pub const MODEL_FACTS_COLOR: term::color::Color = BRIGHT_BLUE;
pub const INFO_ATTRIBUTE: term::Attr = term::Attr::Bold;

pub struct Terminal {
    term: Box<term::StdoutTerminal>,
    color: Option<term::color::Color>,
    attribute: Option<term::Attr>,
    formatted: bool,
}

impl Terminal {
    pub fn new(formatted: bool) -> Terminal {
        Self {
            term: term::stdout().unwrap(),
            color: None,
            attribute: None,
            formatted,
        }
    }

    pub fn foreground(&mut self, color: term::color::Color) -> &mut Self {
        if self.formatted {
            self.color = Some(color);
        }
        self
    }

    pub fn attribute(&mut self, attribute: term::Attr) -> &mut Self {
        if self.formatted {
            self.attribute = Some(attribute);
        }
        self
    }

    pub fn apply(&mut self, closure: impl Fn()) -> &mut Self {
        if let Some(color) = self.color {
            self.term.fg(color).unwrap();
        }
        if let Some(attribute) = self.attribute {
            self.term.attr(attribute).unwrap();
        }
        closure();
        self
    }

    pub fn reset(&mut self) {
        if self.color.is_some() || self.attribute.is_some() {
            self.term.reset().unwrap();
        }
    }
}