use super::{constants::*, Error};
use itertools::Itertools;
use razor_fol::syntax;
use std::convert::TryFrom;
use std::ops::Deref;
use std::str::FromStr;
use Variant::*;

/// Is the variants of attributes.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Variant {
    /// Universal attribute from a range restricted universally quantified variable.
    Universal,

    /// Existential attribute from an existential variable.
    Existential,

    /// Equational attribute, introduced by expanding equations.
    Equational(Box<Attribute>),
}

/// In the context of a relational expression, a variable is refered to as an `Attribute`.
///
/// **Note**:
/// More accurately, an attribute is identified as a position on a relational formula.
/// However, because we work with formulae where every position is occupied by a unique
/// variable, attributes can be identified by variables.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct Attribute {
    /// Is the attribute's name.
    name: String,

    /// Is the variation of the attribute.
    variant: Variant,
}

impl Attribute {
    /// Returns `true` if the attribute is universal.
    #[inline(always)]
    pub fn is_universal(&self) -> bool {
        matches!(self.variant, Universal)
    }

    /// Returns true if the attribute is existential.
    #[inline(always)]
    pub fn is_existential(&self) -> bool {
        matches!(self.variant, Existential)
    }

    /// Consumes the receiver attribute and returns its canonical form.
    /// For `Universal` and `Existential` variants, the canonical form is the attribute
    /// itself. For equality attributes, the canonical form is a `Universal` or
    /// `Existential` attribute to which the attribute refers.
    #[inline]
    pub fn into_canonical(self) -> Attribute {
        match self.variant {
            Universal | Existential => self,
            Equational(attr) => attr.into_canonical(),
        }
    }
}

impl TryFrom<&syntax::V> for Attribute {
    type Error = Error;

    fn try_from(value: &syntax::V) -> Result<Self, Error> {
        value.0.parse()
    }
}

impl From<&Attribute> for syntax::V {
    fn from(attr: &Attribute) -> Self {
        let name = &attr.name;
        syntax::V(name.into())
    }
}

impl FromStr for Attribute {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.starts_with(EXISTENTIAL_PREFIX) {
            Ok(Self {
                name: s.into(),
                variant: Existential,
            })
        } else if s.starts_with(EQUATIONAL_PREFIX) {
            if let Some(end) = s.find(SEPERATOR) {
                let name = s.into();
                Ok(Self {
                    name,
                    variant: Equational(Box::new(s[1..end].parse()?)),
                })
            } else {
                Err(Error::BadAttributeName {
                    name: s.to_string(),
                })
            }
        } else {
            Ok(Self {
                name: s.into(),
                variant: Universal,
            })
        }
    }
}

/// Represents the list of attributes of a relational expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct AttributeList(Vec<Attribute>);

impl AttributeList {
    /// Returns the set union of the attributes in the receiver and those in `other`.
    pub fn union(&self, other: &[Attribute]) -> AttributeList {
        self.iter()
            .chain(other.iter().filter(|v| !self.contains(v)))
            .cloned()
            .collect_vec()
            .into()
    }

    /// Returns the attributes that are present in both the receiver and `other`.
    pub fn intersect(&self, other: &[Attribute]) -> AttributeList {
        self.iter()
            .filter(|v| other.contains(v))
            .cloned()
            .collect_vec()
            .into()
    }

    /// Creates a new `AttributeList` from `formula`.
    pub fn try_from_formula(formula: &syntax::Formula) -> Result<Self, Error> {
        let attributes = formula
            .free_vars()
            .into_iter()
            .map(Attribute::try_from)
            .collect::<Result<Vec<_>, Error>>();

        attributes.map(Self)
    }

    /// Creates a new `AttributeList` from `formula`.
    pub fn universals(&self) -> AttributeList {
        self.attributes()
            .iter()
            .filter(|a| a.is_universal())
            .cloned()
            .into()
    }

    /// Returns the list of attributes.
    pub fn attributes(&self) -> &[Attribute] {
        &self.0
    }
}

impl Deref for AttributeList {
    type Target = [Attribute];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<I: IntoIterator<Item = Attribute>> From<I> for AttributeList {
    fn from(attributes: I) -> Self {
        Self(attributes.into_iter().map(Into::into).collect())
    }
}

impl From<&AttributeList> for Vec<syntax::V> {
    fn from(attrs: &AttributeList) -> Self {
        attrs.iter().map(syntax::V::from).collect()
    }
}
