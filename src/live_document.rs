// A live document is in the process of being edited.
// It has a version number that is incremented each time the document is edited.
// We also track the version number it had the last time it was saved.
pub struct LiveDocument {
    text: String,

    // The most recent version we have.
    live_version: i32,

    // The version number the document had the last time it was saved.
    saved_version: i32,
}

impl LiveDocument {
    // Called when a file is opened, so we don't have any history before this version.
    pub fn new(text: String, version: i32) -> LiveDocument {
        LiveDocument {
            text,
            live_version: version,
            saved_version: version,
        }
    }

    pub fn handle_change(&mut self, new_live_version: i32) {
        self.live_version = new_live_version;
    }

    pub fn handle_save(&mut self, text: String) {
        self.text = text;
        self.saved_version = self.live_version;
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn saved_version(&self) -> i32 {
        self.saved_version
    }
}