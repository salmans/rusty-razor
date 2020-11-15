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
    Equational,
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
        let variant = if s.starts_with(EXISTENTIAL_PREFIX) {
            Some(Existential)
        } else if s.starts_with(EQUATIONAL_PREFIX) {
            if s.find(SEPERATOR).is_some() {
                Some(Equational)
            } else {
                None
            }
        } else {
            Some(Universal)
        };

        let name = s.into();
        if let Some(variant) = variant {
            Ok(Self { name, variant })
        } else {
            Err(Error::BadAttributeName { name })
        }
    }
}

/// Represents the list of attributes of a relational expression.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct AttributeList(Vec<Attribute>);

impl AttributeList {
    pub fn new<I: IntoIterator<Item = Attribute>>(attributes: I) -> Self {
        Self(attributes.into_iter().map(Into::into).collect())
    }

    /// Returns the set union of the attributes in the receiver and those in `other`.
    pub fn union(&self, other: &[Attribute]) -> AttributeList {
        Self::new(
            self.iter()
                .chain(other.iter().filter(|v| !self.contains(v)))
                .cloned()
                .collect_vec(),
        )
    }

    /// Returns the attributes that are present in both the receiver and `other`.
    pub fn intersect(&self, other: &[Attribute]) -> AttributeList {
        Self::new(
            self.iter()
                .filter(|v| other.contains(v))
                .cloned()
                .collect_vec(),
        )
    }

    /// Returns a new `AttributeList` containing the universal attributes in the receiver.
    pub fn universals(&self) -> AttributeList {
        Self::new(
            self.attributes()
                .iter()
                .filter(|a| a.is_universal())
                .cloned(),
        )
    }

    /// Returns the list of attributes wrapped inside the receiver.
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

impl TryFrom<&syntax::Formula> for AttributeList {
    type Error = Error;

    fn try_from(value: &syntax::Formula) -> Result<Self, Self::Error> {
        let attributes = value
            .free_vars()
            .into_iter()
            .map(Attribute::try_from)
            .collect::<Result<Vec<_>, Error>>();

        attributes.map(Self)
    }
}

impl From<&AttributeList> for Vec<syntax::V> {
    fn from(attrs: &AttributeList) -> Self {
        attrs.iter().map(syntax::V::from).collect()
    }
}
