use std::collections::HashMap;

pub type StyleId = u8;

#[derive(Clone)]
pub struct Stylus {
    styles: HashMap<StyleId, Style>,
}

impl Stylus {
    pub fn new() -> Self {
        Self {
            styles: HashMap::new(),
        }
    }

    pub fn insert_style(&mut self, id: StyleId, style: Style) {
        self.styles.insert(id, style);
    }

    #[allow(dead_code)]
    pub fn delete_style(&mut self, id: StyleId) {
        self.styles.remove(&id);
    }

    pub fn set(&self, id: StyleId) {
        self.styles.get(&id).map(|s| self.set_style(s));
    }

    pub fn set_style(&self, style: &Style) {
        self.clear();
        Self::apply(style);
    }

    pub fn clear(&self) {
        term::stdout().as_mut().unwrap().reset().unwrap();
    }

    fn apply(style: &Style) {
        let mut term = term::stdout();
        style.color.map(|c| term.as_mut().unwrap().fg(c).unwrap());
        style.attr.map(|a| term.as_mut().unwrap().attr(a).unwrap());
    }
}

impl Drop for Stylus {
    fn drop(&mut self) {
        self.clear();
    }
}

#[derive(Clone)]
pub struct Style {
    color: Option<term::color::Color>,
    attr: Option<term::Attr>,
}

impl Style {
    pub fn new() -> Self {
        Self {
            color: None,
            attr: None,
        }
    }

    pub fn foreground(self, color: term::color::Color) -> Self {
        Self {
            color: Some(color),
            ..self
        }
    }

    pub fn attribute(self, attr: term::Attr) -> Self {
        Self {
            attr: Some(attr),
            ..self
        }
    }
}
