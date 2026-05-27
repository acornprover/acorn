use std::collections::HashSet;

use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::environment::Environment;
use crate::elaborator::fact::Fact;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::source::SourceType;

#[test]
fn test_structural_typeclass_facts_survive_import_filter() {
    let mut env = Environment::test();
    env.add(
        r#"
            typeclass F: Foo {
                foo_true {
                    true
                }
            }
            typeclass B: Bar extends Foo {
                bar_true {
                    true
                }
            }

            inductive Unit {
                unit
            }
            let kept: Unit = axiom

            instance Unit: Foo
            instance Unit: Bar

            axiom excluded {
                true
            }
            "#,
    );

    let facts = env.importable_facts(Some(&HashSet::new()));

    assert!(
        facts.iter().any(|fact| {
            matches!(fact, Fact::Definition(_, _, source)
                if matches!(&source.source_type, SourceType::ConstantDefinition(_, name)
                    if name == "kept"))
        }),
        "normalization-relevant constant definitions should survive empty import filters"
    );
    assert!(
        !facts.iter().any(|fact| {
            matches!(fact, Fact::Proposition(prop)
                if matches!(&prop.source.source_type, SourceType::Axiom(Some(name))
                    if name == "excluded"))
        }),
        "empty import filters should exclude ordinary named facts"
    );
    assert!(
        facts.iter().any(|fact| {
            matches!(fact, Fact::Extends(typeclass, bases, _, _)
                if typeclass.name == "Bar" && bases.iter().any(|base| base.name == "Foo"))
        }),
        "expected the Bar extends Foo fact to survive filtering"
    );
    assert!(
        facts.iter().any(|fact| {
            matches!(fact, Fact::Instance(instance, _)
                if instance.datatype.name == "Unit" && instance.typeclass.name == "Bar")
        }),
        "expected the Unit: Bar instance fact to survive filtering"
    );
}

#[test]
fn test_parameterized_instance_schema_uses_proposition_bridge() {
    let mut env = Environment::test();
    env.add(
        r#"
            structure Box[T] {
                value: T
            }

            typeclass A: Identity {
                id: A -> A
            }

            instance Box[T]: Identity {
                define id(self) -> Box[T] {
                    self
                }
            }
            "#,
    );

    let facts = env.importable_facts(None);

    assert!(
        facts.iter().any(|fact| {
            matches!(fact, Fact::Instance(instance, source)
                if instance.datatype.name == "Box"
                    && instance.typeclass.name == "Identity"
                    && !instance.is_concrete()
                    && matches!(&source.source_type, SourceType::Instance(instance_name, typeclass_name)
                        if instance_name == "Box" && typeclass_name == "Identity"))
        }),
        "expected a parameterized Box: Identity instance fact"
    );

    assert!(
        facts.iter().any(|fact| {
            matches!(fact, Fact::Proposition(prop)
                if matches!(&prop.source.source_type, SourceType::Instance(instance_name, typeclass_name)
                    if instance_name == "Box" && typeclass_name == "Identity"))
        }),
        "expected parameterized instance bridge to be a proposition fact"
    );

    let has_concrete_style_definition_bridge = facts.iter().any(|fact| {
        matches!(
            fact,
            Fact::Definition(
                PotentialValue::Resolved(AcornValue::Constant(public_ci)),
                AcornValue::Constant(instance_ci),
                source,
            ) if matches!(&source.source_type, SourceType::Instance(instance_name, typeclass_name)
                    if instance_name == "Box" && typeclass_name == "Identity")
                && matches!(public_ci.name, ConstantName::TypeclassAttribute(..))
                && matches!(instance_ci.name, ConstantName::InstanceAttribute(..))
        )
    });
    assert!(
        !has_concrete_style_definition_bridge,
        "parameterized instance bridges should not use the concrete definition-alias schema"
    );
}

#[test]
fn test_instance_family_parameters_are_binders_not_patterns() {
    let mut env = Environment::test();
    env.add(
        r#"
            type Nat: axiom

            structure Matrix[S, m: Nat, n: Nat] {
                entry: S
            }

            typeclass R: Ring {
                ring_true {
                    true
                }
            }
            "#,
    );

    let message = env.bad("instance Matrix[S, n: Nat, n: Nat]: Ring");
    assert!(
        message.contains("duplicate parameter"),
        "expected duplicate binder error, got: {message}"
    );
}
