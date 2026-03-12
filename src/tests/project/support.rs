use tokio_util::sync::CancellationToken;

use crate::builder::{BuildEvent, BuildStatus, Builder};
use crate::project::Project;

pub(super) fn expect_build_ok(project: &mut Project) -> i32 {
    let mut events: Vec<BuildEvent> = vec![];
    let (status, searches_success, build_cache) = {
        let mut builder = Builder::new(&project, CancellationToken::new(), |event| {
            events.push(event)
        });
        builder.build();
        let cache = builder.build_cache.take();
        (builder.status, builder.metrics.searches_success, cache)
    };
    assert_eq!(status, BuildStatus::Good);
    assert!(!events.is_empty());
    let (done, total) = events.last().unwrap().progress.unwrap();
    assert_eq!(done, total, "expected number of build events didn't match");

    if project.config.write_cache || project.config.read_cache {
        if let Some(cache) = build_cache {
            project.update_build_cache(cache, false);
        }
    }

    searches_success
}

pub(super) const FOO_AC: &str = r#"
// Imported by other tests
type Foo: axiom
type AlsoFoo: Foo
type NotFoo: axiom
let foo: Foo = axiom
define fooify(x: Foo) -> Foo { foo }
"#;
