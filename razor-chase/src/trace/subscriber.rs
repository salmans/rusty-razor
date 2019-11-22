use tracing::*;
use serde_derive::{Serialize, Deserialize};
use std::{fmt, fs::File, io::Write, sync::Mutex};

/// Thread safe json logger that rights records of `ChaseStepRecord` into a given log file.
pub struct JsonLogger {
    log_file: Mutex<File>,
    chase_step_record: Mutex<ChaseStepRecord>,
}

impl JsonLogger {
    pub fn new(log_file: File) -> Self {
        Self {
            log_file: Mutex::new(log_file),
            chase_step_record: Mutex::new(ChaseStepRecord::new()),
        }
    }
}

impl subscriber::Subscriber for JsonLogger {
    fn enabled(&self, _: &Metadata) -> bool {
        true // for now
    }

    fn new_span(&self, span: &span::Attributes) -> Id {
        let mut record = Recorder::new();
        span.record(&mut record);
        Id::from_u64(record.model_id.unwrap_or(1))
    }

    fn record(&self, _span: &Id, _values: &span::Record) {}

    fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

    fn event(&self, event: &Event) {
        let mut event_record = Recorder::new();
        event.record(&mut event_record);

        if let Some(event_type) = &event_record.event {
            match event_type.as_ref() {
                super::EXTEND | super::MODEL | super::FAIL | super::BOUND => {
                    let _ = self.chase_step_record
                        .lock()
                        .map(|mut rec| {
                            rec.set_model(ModelRecord::try_from(event_record).ok());
                            rec
                        });
                }
                super::EVALUATE => {
                    let mut evaluate_record = Recorder::new();
                    event.record(&mut evaluate_record);
                    let _ = self.chase_step_record
                        .lock()
                        .map(|mut rec| {
                            rec.set_evaluate(EvaluateRecord::try_from(event_record).ok());
                            rec
                        });
                }
                _ => (),
            }
        }
    }

    fn enter(&self, _span: &Id) {}

    fn exit(&self, _span: &Id) {
        let record = self.chase_step_record.lock().unwrap();
        self.log_file
            .lock()
            .unwrap()
            .write_all(serde_json::to_string_pretty(&*record)
                .unwrap()
                .to_string()
                .as_bytes())
            .expect("unable to write data");
    }
}

/// Log information associated to a chase step, including the extended model after the step and
/// the sequent and its triggering mapping.
#[derive(Serialize)]
struct ChaseStepRecord {
    #[serde(rename = "evaluate")]
    evaluate_record: Option<EvaluateRecord>,
    #[serde(rename = "model")]
    model_record: Option<ModelRecord>,
}

impl ChaseStepRecord {
    fn new() -> Self {
        Self {
            evaluate_record: None,
            model_record: None,
        }
    }

    /// Set the `EvaluateRecord` of the step, triggered by an EVALUATE event.
    fn set_evaluate(&mut self, evaluate_record: Option<EvaluateRecord>) {
        self.evaluate_record = evaluate_record;
    }

    /// Set the `ModelRecord` of the step, triggered by EXTEND, FAIL, MODEL and BOUND events.
    fn set_model(&mut self, model_record: Option<ModelRecord>) {
        self.model_record = model_record;
    }
}

/// A record, containing information about a model as it is being extended by the chase or when it
/// is done, a bound is reached or it fails.
#[derive(Serialize, Deserialize)]
struct ModelRecord {
    event: String,
    model_id: u64,
    parent: Option<u64>,
    model: String,
}

impl ModelRecord {
    fn try_from(value: Recorder) -> Result<Self, ()> {
        if value.event.is_none() | value.model_id.is_none() | value.model.is_none() {
            Err(())
        } else {
            Ok(ModelRecord {
                event: value.event.unwrap(),
                model_id: value.model_id.unwrap(),
                parent: value.parent,
                model: value.model.unwrap(),
            })
        }
    }
}

/// A record, containing information about the sequent that is processed by a chase step and the
/// mapping that triggers it.
#[derive(Serialize, Deserialize)]
struct EvaluateRecord {
    sequent: String,
    mapping: String,
}

impl EvaluateRecord {
    fn try_from(value: Recorder) -> Result<Self, ()> {
        if value.sequent.is_none() | value.mapping.is_none() {
            Err(())
        } else {
            Ok(EvaluateRecord {
                sequent: value.sequent.unwrap(),
                mapping: value.mapping.unwrap(),
            })
        }
    }
}

/// Generic trace visitor to collect as many fields as it can. Based on the triggering vent,
/// `Recorder` will be converted to its corresponding log record.
struct Recorder {
    event: Option<String>,
    model_id: Option<u64>,
    parent: Option<u64>,
    model: Option<String>,
    sequent: Option<String>,
    mapping: Option<String>,
}

impl Recorder {
    fn new() -> Recorder {
        Recorder {
            event: None,
            model_id: None,
            parent: None,
            model: None,
            sequent: None,
            mapping: None,
        }
    }
}

impl field::Visit for Recorder {
    fn record_u64(&mut self, field: &field::Field, value: u64) {
        match field.name().as_ref() {
            super::MODEL_ID_FIELD => self.model_id = Some(value),
            super::PARENT_FIELD => self.parent = Some(value),
            _ => (),
        }
    }

    fn record_str(&mut self, field: &field::Field, value: &str) {
        match field.name().as_ref() {
            super::EVENT_FILED => self.event = Some(value.to_owned()),
            _ => (),
        }
    }

    fn record_debug(&mut self, field: &field::Field, value: &dyn fmt::Debug) {
        match field.name().as_ref() {
            super::MODEL_FIELD => self.model = Some(format!("{:?}", value)),
            super::SEQUENT_FIELD => self.sequent = Some(format!("{:?}", value)),
            super::MAPPING_FIELD => self.mapping = Some(format!("{:?}", value)),
            _ => (),
        }
    }
}