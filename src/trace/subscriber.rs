use tracing::*;
use serde_derive::{Serialize, Deserialize};
use std::{fmt, fs::File, io::Write, sync::Mutex};

pub struct JsonLogger {
    log_file: Mutex<File>,
}

impl JsonLogger {
    pub fn new(log_file: File) -> JsonLogger {
        JsonLogger {
            log_file: Mutex::new(log_file),
        }
    }
}

#[derive(Serialize, Deserialize)]
pub struct ModelRecord {
    event: Option<String>,
    model_id: Option<u64>,
    parent: Option<u64>,
    model: Option<String>,
}

impl ModelRecord {
    fn new() -> ModelRecord {
        ModelRecord {
            event: None,
            model_id: None,
            parent: None,
            model: None,
        }
    }
}

impl field::Visit for ModelRecord {
    fn record_u64(&mut self, field: &field::Field, value: u64) {
        let field_name = field.name();
        if field_name == super::MODEL_ID_FIELD {
            self.model_id = Some(value);
        } else if field_name == super::PARENT_FIELD {
            self.parent = Some(value);
        }
    }

    fn record_str(&mut self, field: &field::Field, value: &str) {
        let field_name = field.name();
        if field_name == super::EVENT_FILED {
            self.event = Some(value.to_owned());
        }
    }

    fn record_debug(&mut self, field: &field::Field, value: &fmt::Debug) {
        let field_name = field.name();
        if field_name == super::MODEL_FIELD {
            self.model = Some(format!("{:?}", value));
        }
    }
}

impl subscriber::Subscriber for JsonLogger {
    fn enabled(&self, metadata: &Metadata) -> bool {
        metadata.fields().field(super::EVENT_FILED).is_some()
    }

    fn new_span(&self, span: &span::Attributes) -> Id {
        let mut record = ModelRecord::new();
        span.record(&mut record);
        Id::from_u64(record.model_id.unwrap_or(1))
    }

    fn record(&self, _span: &Id, _values: &span::Record) {}

    fn record_follows_from(&self, _span: &Id, _follows: &Id) {}

    fn event(&self, event: &Event) {
        let mut record = ModelRecord::new();
        event.record(&mut record);
        if let Some(event_type) = &record.event {
            if event_type == super::NEW_MODEL_EVENT {
                self.log_file.lock().unwrap()
                    .write_all(serde_json::to_string(&record).unwrap()
                        .to_string().as_bytes())
                    .expect("Unable to write data");
            }
        }
    }

    fn enter(&self, _span: &Id) {}

    fn exit(&self, _span: &Id) {}
}