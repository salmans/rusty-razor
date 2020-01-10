use term::{color::{BRIGHT_RED, GREEN, BRIGHT_YELLOW, BRIGHT_BLUE}};

pub const INFO_COLOR: term::color::Color = 27;
pub const LOGO_TOP_COLOR: term::color::Color = 136;
pub const ERROR_COLOR: term::color::Color = BRIGHT_RED;
pub const MODEL_DOMAIN_COLOR: term::color::Color = GREEN;
pub const MODEL_ELEMENTS_COLOR: term::color::Color = BRIGHT_YELLOW;
pub const MODEL_FACTS_COLOR: term::color::Color = BRIGHT_BLUE;
pub const INFO_ATTRIBUTE: term::Attr = term::Attr::Bold;

pub struct Terminal {
    term: Option<Box<term::StdoutTerminal>>,
    color: Option<term::color::Color>,
    attribute: Option<term::Attr>,
    formatted: bool,
}

impl Terminal {
    pub fn new(formatted: bool) -> Terminal {
        let term = term::stdout();
        // disable formatting if can't open the terminal
        let formatted = if term.is_some() { formatted } else { false };

        Self {
            term,
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
            let _ = self.term.as_mut().unwrap().fg(color);
        }
        if let Some(attribute) = self.attribute {
            let _ = self.term.as_mut().unwrap().attr(attribute);
        }
        closure();
        self
    }

    pub fn reset(&mut self) {
        if self.color.is_some() || self.attribute.is_some() {
            let _ = self.term.as_mut().unwrap().reset();
        }
    }
}