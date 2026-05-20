use crate::elaborator::acorn_type::{AcornType, Datatype, DependentTypeArg};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::environment::Environment;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::names::DefinedName;
use crate::elaborator::potential_value::PotentialValue;
use crate::kernel::atom::AtomId;
use crate::project::ProjectLookup;

fn conjoin(values: Vec<AcornValue>) -> AcornValue {
    let mut iter = values.into_iter();
    let Some(first) = iter.next() else {
        return AcornValue::Bool(true);
    };
    iter.fold(first, AcornValue::and)
}

fn datatype_args_for_type(acorn_type: &AcornType) -> Option<(Datatype, Vec<DependentTypeArg>)> {
    match acorn_type {
        AcornType::Data(datatype, type_args) => Some((
            datatype.clone(),
            type_args
                .iter()
                .cloned()
                .map(DependentTypeArg::Type)
                .collect(),
        )),
        AcornType::Family(datatype, args) => Some((datatype.clone(), args.clone())),
        _ => None,
    }
}

fn split_datatype_args(args: &[DependentTypeArg]) -> (Vec<AcornType>, Vec<AcornValue>) {
    let mut type_args = vec![];
    let mut value_args = vec![];
    for arg in args {
        match arg {
            DependentTypeArg::Type(acorn_type) => type_args.push(acorn_type.clone()),
            DependentTypeArg::Value(value) => value_args.push(value.clone()),
        }
    }
    (type_args, value_args)
}

pub(crate) struct TransportBuilder<'a> {
    bindings: &'a BindingMap,
    project: &'a dyn ProjectLookup,
}

impl<'a> TransportBuilder<'a> {
    pub(super) fn new(
        env: &'a Environment,
        project: &'a dyn ProjectLookup,
    ) -> TransportBuilder<'a> {
        TransportBuilder {
            bindings: &env.bindings,
            project,
        }
    }

    pub(crate) fn from_bindings(
        bindings: &'a BindingMap,
        project: &'a dyn ProjectLookup,
    ) -> TransportBuilder<'a> {
        TransportBuilder { bindings, project }
    }

    pub(crate) fn relation(
        &self,
        source_type: &AcornType,
        target_type: &AcornType,
        source_value: AcornValue,
        target_value: AcornValue,
        source: &dyn ErrorContext,
        stack_size: AtomId,
    ) -> error::Result<AcornValue> {
        self.build_relation(
            source_type,
            target_type,
            source_value,
            target_value,
            source,
            stack_size,
            0,
        )
    }

    pub(crate) fn witness(
        &self,
        source_type: &AcornType,
        target_type: &AcornType,
        source_value: AcornValue,
        source: &dyn ErrorContext,
        stack_size: AtomId,
    ) -> error::Result<Option<AcornValue>> {
        self.build_witness(
            source_type,
            target_type,
            source_value,
            source,
            stack_size,
            0,
        )
    }

    fn apply_datatype_attr(
        &self,
        receiver_type: &AcornType,
        receiver: AcornValue,
        attr_name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        let Some((_, datatype_args)) = datatype_args_for_type(receiver_type) else {
            return Err(source.error("transport attribute receiver is not a datatype"));
        };
        let (module_id, const_name) = self
            .bindings
            .resolve_datatype_attr_for_type(receiver_type, attr_name)
            .map_err(|e| source.error(&e))?;
        let attr_bindings = self.bindings.get_bindings(module_id, self.project);
        let potential = attr_bindings
            .get_constant_value(&DefinedName::Constant(const_name))
            .map_err(|e| source.error(&e))?;
        let (type_args, value_args) = split_datatype_args(&datatype_args);
        let attr =
            potential.resolve_constant_with_datatype_args(&type_args, &value_args, source)?;
        self.bindings
            .apply_potential(PotentialValue::Resolved(attr), vec![receiver], None, source)
    }

    fn datatype_arg_conditions(
        &self,
        source_args: &[DependentTypeArg],
        target_args: &[DependentTypeArg],
        source: &dyn ErrorContext,
    ) -> error::Result<Vec<AcornValue>> {
        if source_args.len() != target_args.len() {
            return Err(source.error("transport source and target types have different arity"));
        }

        let mut conditions = vec![];
        for (source_arg, target_arg) in source_args.iter().zip(target_args) {
            match (source_arg, target_arg) {
                (DependentTypeArg::Type(source_type), DependentTypeArg::Type(target_type)) => {
                    if source_type != target_type {
                        return Err(source.error(&format!(
                            "transport between different type parameters is not supported: {} vs {}",
                            source_type, target_type
                        )));
                    }
                }
                (DependentTypeArg::Value(source_value), DependentTypeArg::Value(target_value)) => {
                    let source_type = source_value.get_type();
                    let target_type = target_value.get_type();
                    if source_type != target_type {
                        return Err(source.error(&format!(
                            "transport index types differ: {} vs {}",
                            source_type, target_type
                        )));
                    }
                    if source_value != target_value {
                        conditions.push(AcornValue::equals(
                            source_value.clone(),
                            target_value.clone(),
                        ));
                    }
                }
                _ => {
                    return Err(source
                        .error("transport source and target types use different parameter kinds"))
                }
            }
        }
        Ok(conditions)
    }

    fn type_conditions(
        &self,
        source_type: &AcornType,
        target_type: &AcornType,
        source: &dyn ErrorContext,
    ) -> error::Result<Vec<AcornValue>> {
        if source_type == target_type {
            return Ok(vec![]);
        }
        if let (AcornType::Function(source_fn), AcornType::Function(target_fn)) =
            (source_type, target_type)
        {
            if source_fn.arg_types.len() != target_fn.arg_types.len() {
                return Err(source.error(&format!(
                    "cannot transport between functions with different arity: {} vs {}",
                    source_type, target_type
                )));
            }
            let mut conditions = vec![];
            for (source_arg_type, target_arg_type) in
                source_fn.arg_types.iter().zip(&target_fn.arg_types)
            {
                conditions.extend(self.type_conditions(
                    source_arg_type,
                    target_arg_type,
                    source,
                )?);
            }
            conditions.extend(self.type_conditions(
                &source_fn.return_type,
                &target_fn.return_type,
                source,
            )?);
            return Ok(conditions);
        }
        let Some((source_datatype, source_args)) = datatype_args_for_type(source_type) else {
            return Err(source.error(&format!(
                "cannot transport value of type {} to {}",
                source_type, target_type
            )));
        };
        let Some((target_datatype, target_args)) = datatype_args_for_type(target_type) else {
            return Err(source.error(&format!(
                "cannot transport value of type {} to {}",
                source_type, target_type
            )));
        };
        if source_datatype != target_datatype {
            return Err(source.error(&format!(
                "cannot transport between different datatypes: {} and {}",
                source_datatype.name, target_datatype.name
            )));
        }
        self.datatype_arg_conditions(&source_args, &target_args, source)
    }

    fn datatype_attr_value(
        &self,
        receiver_type: &AcornType,
        attr_name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        let Some((_, datatype_args)) = datatype_args_for_type(receiver_type) else {
            return Err(source.error("transport attribute receiver is not a datatype"));
        };
        let (module_id, const_name) = self
            .bindings
            .resolve_datatype_attr_for_type(receiver_type, attr_name)
            .map_err(|e| source.error(&e))?;
        let attr_bindings = self.bindings.get_bindings(module_id, self.project);
        let potential = attr_bindings
            .get_constant_value(&DefinedName::Constant(const_name))
            .map_err(|e| source.error(&e))?;
        let (type_args, value_args) = split_datatype_args(&datatype_args);
        Ok(PotentialValue::Resolved(
            potential.resolve_constant_with_datatype_args(&type_args, &value_args, source)?,
        ))
    }

    fn build_witness(
        &self,
        source_type: &AcornType,
        target_type: &AcornType,
        source_value: AcornValue,
        source: &dyn ErrorContext,
        stack_size: AtomId,
        depth: usize,
    ) -> error::Result<Option<AcornValue>> {
        if depth > 32 {
            return Err(source.error("transport witness is too deeply recursive"));
        }

        if source_type == target_type {
            return Ok(Some(source_value));
        }

        if let (AcornType::Function(source_fn), AcornType::Function(target_fn)) =
            (source_type, target_type)
        {
            if source_fn.arg_types.len() != target_fn.arg_types.len() {
                return Ok(None);
            }
            let arg_count = target_fn.arg_types.len() as AtomId;
            let body_stack_size = stack_size + arg_count;
            let target_args = target_fn
                .arg_types
                .iter()
                .enumerate()
                .map(|(i, arg_type)| {
                    AcornValue::Variable(stack_size + i as AtomId, arg_type.clone())
                })
                .collect::<Vec<_>>();
            let mut source_args = vec![];
            for ((source_arg_type, target_arg_type), target_arg) in source_fn
                .arg_types
                .iter()
                .zip(&target_fn.arg_types)
                .zip(&target_args)
            {
                let Some(source_arg) = self.build_witness(
                    target_arg_type,
                    source_arg_type,
                    target_arg.clone(),
                    source,
                    body_stack_size,
                    depth + 1,
                )?
                else {
                    return Ok(None);
                };
                source_args.push(source_arg);
            }
            let source_function = source_value.insert_stack(stack_size, arg_count);
            let source_application = source_function.check_apply(source_args, None, source)?;
            let Some(body) = self.build_witness(
                &source_application.get_type(),
                &target_fn.return_type,
                source_application,
                source,
                body_stack_size,
                depth + 1,
            )?
            else {
                return Ok(None);
            };
            return Ok(Some(AcornValue::Lambda(
                target_fn.arg_types.clone(),
                Box::new(body),
            )));
        }

        let Some((source_datatype, _)) = datatype_args_for_type(source_type) else {
            return Ok(None);
        };
        let Some((target_datatype, _)) = datatype_args_for_type(target_type) else {
            return Ok(None);
        };
        if source_datatype != target_datatype {
            return Ok(None);
        }
        let Some(fields) = self
            .bindings
            .get_datatype_structure_fields(&source_datatype)
        else {
            return Ok(None);
        };
        let Ok(new_potential) = self.datatype_attr_value(target_type, "new", source) else {
            return Ok(None);
        };

        let target_placeholder = AcornValue::Variable(stack_size, target_type.clone());
        let mut field_values = vec![];
        for field in fields {
            let source_field =
                self.apply_datatype_attr(source_type, source_value.clone(), field, source)?;
            let target_field =
                self.apply_datatype_attr(target_type, target_placeholder.clone(), field, source)?;
            let Some(field_value) = self.build_witness(
                &source_field.get_type(),
                &target_field.get_type(),
                source_field,
                source,
                stack_size,
                depth + 1,
            )?
            else {
                return Ok(None);
            };
            field_values.push(field_value);
        }

        let value = self.bindings.apply_potential(
            new_potential,
            field_values,
            Some(target_type),
            source,
        )?;
        Ok(Some(value))
    }

    fn build_relation(
        &self,
        source_type: &AcornType,
        target_type: &AcornType,
        source_value: AcornValue,
        target_value: AcornValue,
        source: &dyn ErrorContext,
        stack_size: AtomId,
        depth: usize,
    ) -> error::Result<AcornValue> {
        if depth > 32 {
            return Err(source.error("transport relation is too deeply recursive"));
        }

        if source_type == target_type {
            return Ok(AcornValue::equals(target_value, source_value));
        }

        if let (AcornType::Function(source_fn), AcornType::Function(target_fn)) =
            (source_type, target_type)
        {
            if source_fn.arg_types.len() != target_fn.arg_types.len() {
                return Err(source.error(&format!(
                    "cannot transport between functions with different arity: {} vs {}",
                    source_type, target_type
                )));
            }

            let arg_count = source_fn.arg_types.len() as AtomId;
            let total_arg_count = arg_count * 2;
            let body_stack_size = stack_size + total_arg_count;
            let source_args = source_fn
                .arg_types
                .iter()
                .enumerate()
                .map(|(i, arg_type)| {
                    AcornValue::Variable(stack_size + i as AtomId, arg_type.clone())
                })
                .collect::<Vec<_>>();
            let target_args = target_fn
                .arg_types
                .iter()
                .enumerate()
                .map(|(i, arg_type)| {
                    AcornValue::Variable(stack_size + arg_count + i as AtomId, arg_type.clone())
                })
                .collect::<Vec<_>>();

            let mut premise_parts = vec![];
            let mut outer_conditions = vec![];
            for ((source_arg_type, target_arg_type), (source_arg, target_arg)) in source_fn
                .arg_types
                .iter()
                .zip(&target_fn.arg_types)
                .zip(source_args.iter().zip(&target_args))
            {
                outer_conditions.extend(self.type_conditions(
                    source_arg_type,
                    target_arg_type,
                    source,
                )?);
                premise_parts.push(self.build_relation(
                    source_arg_type,
                    target_arg_type,
                    source_arg.clone(),
                    target_arg.clone(),
                    source,
                    body_stack_size,
                    depth + 1,
                )?);
            }

            let source_function = source_value.insert_stack(stack_size, total_arg_count);
            let target_function = target_value.insert_stack(stack_size, total_arg_count);
            let source_application =
                source_function.check_apply(source_args.clone(), None, source)?;
            let target_application =
                target_function.check_apply(target_args.clone(), None, source)?;
            let return_relation = self.build_relation(
                &source_application.get_type(),
                &target_application.get_type(),
                source_application,
                target_application,
                source,
                body_stack_size,
                depth + 1,
            )?;
            let premise = conjoin(premise_parts);
            let body = if premise == AcornValue::Bool(true) {
                return_relation
            } else {
                AcornValue::implies(premise, return_relation)
            };
            let mut quant_types = source_fn.arg_types.clone();
            quant_types.extend(target_fn.arg_types.clone());
            let function_relation = AcornValue::ForAll(quant_types, Box::new(body));
            if outer_conditions.is_empty() {
                return Ok(function_relation);
            }
            outer_conditions.push(function_relation);
            return Ok(conjoin(outer_conditions));
        }

        let Some((source_datatype, source_args)) = datatype_args_for_type(source_type) else {
            return Err(source.error(&format!(
                "cannot transport value of type {} to {}",
                source_type, target_type
            )));
        };
        let Some((target_datatype, target_args)) = datatype_args_for_type(target_type) else {
            return Err(source.error(&format!(
                "cannot transport value of type {} to {}",
                source_type, target_type
            )));
        };
        if source_datatype != target_datatype {
            return Err(source.error(&format!(
                "cannot transport between different datatypes: {} and {}",
                source_datatype.name, target_datatype.name
            )));
        }

        let fields = self
            .bindings
            .get_datatype_structure_fields(&source_datatype)
            .ok_or_else(|| {
                source.error(&format!(
                    "transport is only supported for structures and functions, not {}",
                    source_datatype.name
                ))
            })?
            .to_vec();
        let mut conditions = self.datatype_arg_conditions(&source_args, &target_args, source)?;
        for field in fields {
            let source_field =
                self.apply_datatype_attr(source_type, source_value.clone(), &field, source)?;
            let target_field =
                self.apply_datatype_attr(target_type, target_value.clone(), &field, source)?;
            conditions.push(self.build_relation(
                &source_field.get_type(),
                &target_field.get_type(),
                source_field,
                target_field,
                source,
                stack_size,
                depth + 1,
            )?);
        }
        Ok(conjoin(conditions))
    }
}
