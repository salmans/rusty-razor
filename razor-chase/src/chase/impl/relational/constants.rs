use razor_fol::syntax;

/// The naming prefix of existential attributes and variables in relational formulae.
pub(super) const EXISTENTIAL_PREFIX: &str = "?";

/// The naming prefix of equational attributes and variables in relational formulae.
pub(super) const EQUATIONAL_PREFIX: &str = "~";

/// The naming prefix of constant predicates created by relationalization
pub(super) const CONSTANT_PREDICATE_PREFIX: &str = "@";

/// The naming prefix of functional predicates created by relationalization
pub(super) const FUNCTIONAL_PREDICATE_PREFIX: &str = "$";

/// Seperates the different parts of attribute and variable names.
pub(super) const SEPERATOR: &str = ":";

/// Is the name of the database instance that stores the domain of elements.
pub(super) const DOMAIN: &str = "$$domain";

/// Is the name of the database instance for the equality relation.
pub(super) const EQUALITY: &str = razor_fol::syntax::EQ_SYM;

// Creates the database instance name for the given constant.
#[inline]
pub(super) fn constant_instance_name(c: &syntax::C) -> String {
    format!("@{}", c.0)
}

// Creates the database instance name for the given function symbol.
#[inline]
pub(super) fn function_instance_name(f: &syntax::F) -> String {
    format!("${}", f.0)
}

// Creates the database instance name for the given predicate.
#[inline]
pub(super) fn predicate_instance_name(p: &syntax::Pred) -> String {
    p.to_string()
}
