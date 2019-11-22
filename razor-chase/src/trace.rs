pub mod subscriber;

pub const DEFAULT_JSON_LOG_FILE: &str = "log.json";

// model log record fields:
pub const EVENT_FILED: &str = "event";
pub const MODEL_ID_FIELD: &str = "model_id";
pub const PARENT_FIELD: &str = "parent";
pub const MODEL_FIELD: &str = "model";

// chase step evaluation log fields:
pub const SEQUENT_FIELD: &str = "sequent";
pub const MAPPING_FIELD: &str = "mapping";

// log span types:
/// Inside a chase step
pub const CHASE_STEP: &str = "@chase_step";

// log event types:
/// New model found.
pub const MODEL: &str = "@model";

/// The model is expanded by the chase step.
pub const EXTEND: &str = "@extend";

/// The chase step failed. The model will be discarded.
pub const FAIL: &str = "@fail";

/// A model bound is reached. The model will be discarded.
pub const BOUND: &str = "@bound";

/// A sequent was successfully evaluated by the chase step.
pub const EVALUATE: &str = "@evaluate";