use std::collections::{HashMap, HashSet};
use std::fmt;

use tower_lsp::lsp_types::{LanguageString, MarkedString};

use crate::elaborator::acorn_type::{
    AcornType, Datatype, FunctionType, PotentialType, TypeParam, Typeclass,
};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp, ConstantInstance};
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::elaborator::type_unifier::TypeclassRegistry;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{Decomposition, Term};
use crate::kernel::variable_map::VariableMap;
use crate::module::ModuleId;
use crate::normalizer::Normalizer;
use crate::prover::proof::ConcreteStep;
use crate::syntax::expression::{Declaration, Expression};
use crate::syntax::token::TokenType;

pub type Result<T> = std::result::Result<T, Error>;

/// Collects type variable names from an AcornType in order of first appearance.
fn collect_type_var_names(acorn_type: &AcornType) -> Vec<String> {
    let mut names = Vec::new();
    collect_type_var_names_recursive(acorn_type, &mut names);
    names
}

fn collect_type_var_names_recursive(acorn_type: &AcornType, names: &mut Vec<String>) {
    match acorn_type {
        AcornType::Variable(param) | AcornType::Arbitrary(param) => {
            if !names.contains(&param.name) {
                names.push(param.name.clone());
            }
        }
        AcornType::Data(_, params) => {
            for p in params {
                collect_type_var_names_recursive(p, names);
            }
        }
        AcornType::Function(ft) => {
            for arg in &ft.arg_types {
                collect_type_var_names_recursive(arg, names);
            }
            collect_type_var_names_recursive(&ft.return_type, names);
        }
        _ => {}
    }
}

/// Collects all type variable names from an AcornValue.
fn collect_type_var_names_from_value(value: &AcornValue) -> Vec<String> {
    let mut names = Vec::new();
    collect_type_var_names_from_value_recursive(value, &mut names);
    names
}

fn collect_type_var_names_from_value_recursive(value: &AcornValue, names: &mut Vec<String>) {
    match value {
        AcornValue::Variable(_, t) => {
            collect_type_var_names_recursive(t, names);
        }
        AcornValue::Constant(c) => {
            collect_type_var_names_recursive(&c.instance_type, names);
            for p in &c.params {
                collect_type_var_names_recursive(p, names);
            }
        }
        AcornValue::Application(fa) => {
            collect_type_var_names_from_value_recursive(&fa.function, names);
            for arg in &fa.args {
                collect_type_var_names_from_value_recursive(arg, names);
            }
        }
        AcornValue::Binary(_, left, right) => {
            collect_type_var_names_from_value_recursive(left, names);
            collect_type_var_names_from_value_recursive(right, names);
        }
        AcornValue::Not(v) => {
            collect_type_var_names_from_value_recursive(v, names);
        }
        AcornValue::ForAll(quants, v) | AcornValue::Exists(quants, v) => {
            for q in quants {
                collect_type_var_names_recursive(q, names);
            }
            collect_type_var_names_from_value_recursive(v, names);
        }
        AcornValue::Lambda(args, body) => {
            for t in args {
                collect_type_var_names_recursive(t, names);
            }
            collect_type_var_names_from_value_recursive(body, names);
        }
        AcornValue::IfThenElse(cond, t, f) => {
            collect_type_var_names_from_value_recursive(cond, names);
            collect_type_var_names_from_value_recursive(t, names);
            collect_type_var_names_from_value_recursive(f, names);
        }
        AcornValue::Try(inner, unwrapped_type) => {
            collect_type_var_names_from_value_recursive(inner, names);
            collect_type_var_names_recursive(unwrapped_type, names);
        }
        AcornValue::Match(scrutinee, cases) => {
            collect_type_var_names_from_value_recursive(scrutinee, names);
            for (bound_types, pattern, result) in cases {
                for t in bound_types {
                    collect_type_var_names_recursive(t, names);
                }
                collect_type_var_names_from_value_recursive(pattern, names);
                collect_type_var_names_from_value_recursive(result, names);
            }
        }
        AcornValue::Bool(_) => {}
    }
}

/// Renames type variables in an AcornType according to the provided mapping.
/// Also handles Arbitrary types by converting them to Variable types with the new name.
fn rename_type_vars_in_type(
    acorn_type: &AcornType,
    rename_map: &HashMap<String, String>,
) -> AcornType {
    match acorn_type {
        AcornType::Variable(param) => {
            if let Some(new_name) = rename_map.get(&param.name) {
                AcornType::Variable(TypeParam {
                    name: new_name.clone(),
                    typeclass: param.typeclass.clone(),
                })
            } else {
                acorn_type.clone()
            }
        }
        AcornType::Arbitrary(param) => {
            // Convert Arbitrary types to Variable types when renaming.
            // This is needed for certificate generation where we want canonical
            // type parameter names (T0, T1) instead of specific names (G, H).
            if let Some(new_name) = rename_map.get(&param.name) {
                AcornType::Variable(TypeParam {
                    name: new_name.clone(),
                    typeclass: param.typeclass.clone(),
                })
            } else {
                acorn_type.clone()
            }
        }
        AcornType::Data(datatype, params) => {
            let new_params = params
                .iter()
                .map(|p| rename_type_vars_in_type(p, rename_map))
                .collect();
            AcornType::Data(datatype.clone(), new_params)
        }
        AcornType::Function(ft) => {
            let new_args = ft
                .arg_types
                .iter()
                .map(|a| rename_type_vars_in_type(a, rename_map))
                .collect();
            let new_ret = rename_type_vars_in_type(&ft.return_type, rename_map);
            AcornType::Function(FunctionType {
                arg_types: new_args,
                return_type: Box::new(new_ret),
            })
        }
        _ => acorn_type.clone(),
    }
}

/// Renames type variables in an AcornValue according to the provided mapping.
/// `defining_synthetics` contains the IDs of synthetics being defined in the current
/// let...satisfy block - these should NOT get type params added since they're already bound.
fn rename_type_vars_in_value(
    value: &AcornValue,
    rename_map: &HashMap<String, String>,
    defining_synthetics: &HashSet<(ModuleId, AtomId)>,
) -> AcornValue {
    match value {
        AcornValue::Variable(i, t) => {
            AcornValue::Variable(*i, rename_type_vars_in_type(t, rename_map))
        }
        AcornValue::Constant(c) => {
            let new_instance_type = rename_type_vars_in_type(&c.instance_type, rename_map);

            // If the original params is empty but the instance_type has type variables
            // that we're renaming, we need to add those as params so they get included
            // in the generated code (e.g., foo[T0] instead of just foo).
            // BUT: Don't do this for synthetics being defined in the current let...satisfy block -
            // they're defined with let s0[T0]: ... satisfy { } and the s0 inside the body
            // shouldn't have [T0] because it's already bound by the declaration.
            let is_being_defined = c
                .name
                .synthetic_id()
                .map(|id| defining_synthetics.contains(&id))
                .unwrap_or(false);
            let new_params = if is_being_defined {
                // For synthetics being defined, don't include type params - they're already in scope
                vec![]
            } else if c.params.is_empty() {
                // Extract type vars from instance_type and use renamed versions as params
                let type_vars = collect_type_var_names(&c.instance_type);
                type_vars
                    .iter()
                    .filter_map(|name| rename_map.get(name))
                    .map(|new_name| {
                        AcornType::Variable(TypeParam {
                            name: new_name.clone(),
                            typeclass: None,
                        })
                    })
                    .collect()
            } else {
                c.params
                    .iter()
                    .map(|p| rename_type_vars_in_type(p, rename_map))
                    .collect()
            };

            AcornValue::Constant(ConstantInstance {
                name: c.name.clone(),
                params: new_params,
                instance_type: new_instance_type,
                generic_type: c.generic_type.clone(),
                type_param_names: c.type_param_names.clone(),
            })
        }
        AcornValue::Application(fa) => {
            let new_func = rename_type_vars_in_value(&fa.function, rename_map, defining_synthetics);
            let new_args = fa
                .args
                .iter()
                .map(|a| rename_type_vars_in_value(a, rename_map, defining_synthetics))
                .collect();
            AcornValue::apply(new_func, new_args)
        }
        AcornValue::Binary(op, left, right) => AcornValue::Binary(
            *op,
            Box::new(rename_type_vars_in_value(
                left,
                rename_map,
                defining_synthetics,
            )),
            Box::new(rename_type_vars_in_value(
                right,
                rename_map,
                defining_synthetics,
            )),
        ),
        AcornValue::Not(v) => AcornValue::Not(Box::new(rename_type_vars_in_value(
            v,
            rename_map,
            defining_synthetics,
        ))),
        AcornValue::ForAll(quants, v) => {
            let new_quants = quants
                .iter()
                .map(|q| rename_type_vars_in_type(q, rename_map))
                .collect();
            AcornValue::ForAll(
                new_quants,
                Box::new(rename_type_vars_in_value(
                    v,
                    rename_map,
                    defining_synthetics,
                )),
            )
        }
        AcornValue::Exists(quants, v) => {
            let new_quants = quants
                .iter()
                .map(|q| rename_type_vars_in_type(q, rename_map))
                .collect();
            AcornValue::Exists(
                new_quants,
                Box::new(rename_type_vars_in_value(
                    v,
                    rename_map,
                    defining_synthetics,
                )),
            )
        }
        AcornValue::Lambda(quants, v) => {
            let new_quants = quants
                .iter()
                .map(|q| rename_type_vars_in_type(q, rename_map))
                .collect();
            AcornValue::Lambda(
                new_quants,
                Box::new(rename_type_vars_in_value(
                    v,
                    rename_map,
                    defining_synthetics,
                )),
            )
        }
        AcornValue::IfThenElse(cond, then_v, else_v) => AcornValue::IfThenElse(
            Box::new(rename_type_vars_in_value(
                cond,
                rename_map,
                defining_synthetics,
            )),
            Box::new(rename_type_vars_in_value(
                then_v,
                rename_map,
                defining_synthetics,
            )),
            Box::new(rename_type_vars_in_value(
                else_v,
                rename_map,
                defining_synthetics,
            )),
        ),
        AcornValue::Match(scrutinee, cases) => {
            let new_scrutinee =
                rename_type_vars_in_value(scrutinee, rename_map, defining_synthetics);
            let new_cases = cases
                .iter()
                .map(|(bound_types, pattern, body)| {
                    let new_bound_types = bound_types
                        .iter()
                        .map(|t| rename_type_vars_in_type(t, rename_map))
                        .collect();
                    (
                        new_bound_types,
                        rename_type_vars_in_value(pattern, rename_map, defining_synthetics),
                        rename_type_vars_in_value(body, rename_map, defining_synthetics),
                    )
                })
                .collect();
            AcornValue::Match(Box::new(new_scrutinee), new_cases)
        }
        AcornValue::Bool(_) => value.clone(),
        AcornValue::Try(v, t) => AcornValue::Try(
            Box::new(rename_type_vars_in_value(
                v,
                rename_map,
                defining_synthetics,
            )),
            rename_type_vars_in_type(t, rename_map),
        ),
    }
}

pub struct CodeGenerator<'a> {
    /// Bindings for the module we are generating code in.
    bindings: &'a BindingMap,

    /// We use variables named x0, x1, x2, etc for universal variables.
    next_x: u32,

    /// We use variables named k0, k1, k2, etc for existential variables.
    next_k: u32,

    /// We use variables named s0, s1, s2, etc for synthetic atoms.
    next_s: u32,

    /// We use variables named T0, T1, T2, etc for type parameters.
    next_t: u32,

    /// The names we have assigned to stack variables so far.
    var_names: Vec<String>,

    /// The names we have assigned to synthetic atoms so far.
    synthetic_names: HashMap<(ModuleId, AtomId), String>,

    /// The names for whenever we need an arbitrary member of a type.
    /// Maps type to the name of an element of that type.
    arbitrary_names: HashMap<Term, ConstantName>,
}

impl CodeGenerator<'_> {
    /// Creates a new code generator.
    pub fn new(bindings: &BindingMap) -> CodeGenerator<'_> {
        CodeGenerator {
            bindings,
            next_x: 0,
            next_k: 0,
            next_s: 0,
            next_t: 0,
            var_names: vec![],
            synthetic_names: HashMap::new(),
            arbitrary_names: HashMap::new(),
        }
    }

    pub fn marked(code: String) -> MarkedString {
        MarkedString::LanguageString(LanguageString {
            language: "acorn".to_string(),
            value: code.to_string(),
        })
    }

    /// Converts a ModuleId to an Expression representing that module.
    fn module_to_expr(&self, module_id: ModuleId) -> Result<Expression> {
        let Some(info) = self.bindings.get_module_info(module_id) else {
            return Err(Error::internal("reference to unreferenceable module"));
        };
        if let Some(local_name) = &info.local_name {
            return Ok(Expression::generate_identifier(local_name));
        };

        // Generate lib(module) syntax
        // Build the dot-separated module path expression
        let parts: Vec<&str> = info.full_name.iter().map(|s| s.as_str()).collect();
        let path_expr = Expression::generate_identifier_chain(&parts);
        let lib_expr = Expression::generate_lib();
        let args_expr = Expression::Grouping(
            TokenType::LeftParen.new_token("("),
            Box::new(path_expr),
            TokenType::RightParen.new_token(")"),
        );
        Ok(Expression::Concatenation(
            Box::new(lib_expr),
            Box::new(args_expr),
        ))
    }

    fn datatype_to_expr(&self, datatype: &Datatype) -> Result<Expression> {
        if datatype.module_id == self.bindings.module_id() {
            return Ok(Expression::generate_identifier(&datatype.name));
        }

        // Check if we have an alias
        if let Some(alias) = self.bindings.datatype_alias(&datatype) {
            return Ok(Expression::generate_identifier(alias));
        }

        // Reference this type via referencing the imported module
        let module = self.module_to_expr(datatype.module_id)?;
        Ok(module.add_dot_str(&datatype.name))
    }

    /// Returns an error if this type can't be encoded as an expression.
    /// This will happen when it's defined in a module that isn't directly imported.
    /// In theory we could fix this, but we would have to have a way to suggest imports.
    /// There are probably other error cases.
    pub fn type_to_expr(&self, acorn_type: &AcornType) -> Result<Expression> {
        // Check if there's a local name for this exact type
        if let Some(name) = self
            .bindings
            .get_typename_for_type(&PotentialType::Resolved(acorn_type.clone()))
        {
            return Ok(Expression::generate_identifier(name));
        }

        match acorn_type {
            AcornType::Data(datatype, params) => {
                let base_expr = self.datatype_to_expr(datatype)?;

                self.parametrize_expr(base_expr, params)
            }
            AcornType::Variable(param) | AcornType::Arbitrary(param) => {
                Ok(Expression::generate_identifier(&param.name))
            }
            AcornType::Function(ft) => {
                let mut args = vec![];
                for arg_type in &ft.arg_types {
                    args.push(self.type_to_expr(arg_type)?);
                }
                let lhs = if args.len() == 1 {
                    let arg = args.pop().unwrap();
                    // If the argument is a functional type, wrap it in parentheses
                    if ft.arg_types[0].is_functional() {
                        Expression::Grouping(
                            TokenType::LeftParen.new_token("("),
                            Box::new(arg),
                            TokenType::RightParen.new_token(")"),
                        )
                    } else {
                        arg
                    }
                } else {
                    Expression::generate_paren_grouping(args)
                };
                let rhs = self.type_to_expr(&ft.return_type)?;
                // Since -> is right-associative, we need to parenthesize functional return types
                let rhs = if ft.return_type.is_functional() {
                    Expression::Grouping(
                        TokenType::LeftParen.new_token("("),
                        Box::new(rhs),
                        TokenType::RightParen.new_token(")"),
                    )
                } else {
                    rhs
                };
                Ok(Expression::Binary(
                    Box::new(lhs),
                    TokenType::RightArrow.generate(),
                    Box::new(rhs),
                ))
            }
            AcornType::Empty => Err(Error::internal("empty type generated")),
            AcornType::Bool => Err(Error::internal("Bool unbound")),
            AcornType::Type0 => Ok(Expression::generate_identifier("Type0")),
            AcornType::TypeclassConstraint(tc) => Ok(Expression::generate_identifier(&tc.name)),
        }
    }

    /// Check if a constant name is a replaced synthetic (after replace_synthetics was called).
    /// This is needed because replaced synthetics have Unqualified names like "s0", "s1", etc.
    fn is_replaced_synthetic(&self, name: &ConstantName) -> bool {
        if let ConstantName::Unqualified(_, word) = name {
            self.synthetic_names.values().any(|s| s == word)
        } else {
            false
        }
    }

    /// Adds parameters, if there are any, to an expression representing a type.
    fn parametrize_expr(&self, base_expr: Expression, params: &[AcornType]) -> Result<Expression> {
        if params.is_empty() {
            return Ok(base_expr);
        }
        let mut param_exprs = vec![];
        for param in params {
            param_exprs.push(self.type_to_expr(&param)?);
        }
        let params_expr = Expression::generate_params(param_exprs);
        let applied = Expression::Concatenation(Box::new(base_expr), Box::new(params_expr));
        Ok(applied)
    }

    /// If this value cannot be expressed in a single chunk of code, returns an error.
    /// For example, it might refer to a constant that is not in scope.
    pub fn value_to_code(&mut self, value: &AcornValue) -> Result<String> {
        let expr = self.value_to_expr(value, false)?;
        Ok(expr.to_string())
    }

    /// Generates definitions for the given synthetic atom IDs and appends them to codes.
    /// Updates self.synthetic_names with names for all provided synthetic atom IDs.
    fn define_synthetics(
        &mut self,
        skolem_ids: Vec<(ModuleId, AtomId)>,
        normalizer: &Normalizer,
        codes: &mut Vec<String>,
    ) -> Result<()> {
        // TODO: currently all synthetics are skolems, so we can assume this catches all of them,
        // but we need to change that.
        let infos = normalizer.find_covering_synthetic_info(&skolem_ids);
        for info in &infos {
            // Check if all atoms in this info are already defined
            let all_already_defined = info
                .atoms
                .iter()
                .all(|&(m, i)| self.synthetic_names.contains_key(&(m, i)));
            if all_already_defined {
                // Skip this info - we've already generated code for it
                continue;
            }

            // Assign names to any atoms that don't have them yet
            let mut decl = vec![];
            for &(module_id, local_id) in &info.atoms {
                if self.synthetic_names.contains_key(&(module_id, local_id)) {
                    // We already have a name for this synthetic atom
                    continue;
                }
                let name = self.bindings.next_indexed_var('s', &mut self.next_s);
                self.synthetic_names
                    .insert((module_id, local_id), name.clone());
                decl.push((name, normalizer.get_synthetic_type(module_id, local_id)));
            }
            if decl.is_empty() {
                continue;
            }

            // Denormalize clauses first so we can collect all type variable names
            // Don't instantiate type vars here - they're part of the polymorphic structure
            let mut cond_parts = vec![];
            for clause in &info.clauses {
                let part = normalizer.denormalize(clause, None, None, false);
                cond_parts.push(part);
            }
            let cond_val = AcornValue::reduce(BinaryOp::And, cond_parts);

            // Collect all type variables from BOTH declaration types AND condition value
            // Declaration types may use "T{i}" naming (from BoundVariable)
            // Condition may use "x{i}" naming (from FreeVariable)
            let mut all_type_vars = Vec::new();
            for (_, ty) in &decl {
                for var_name in collect_type_var_names(ty) {
                    if !all_type_vars.contains(&var_name) {
                        all_type_vars.push(var_name);
                    }
                }
            }
            for var_name in collect_type_var_names_from_value(&cond_val) {
                if !all_type_vars.contains(&var_name) {
                    all_type_vars.push(var_name);
                }
            }

            // Build type_param_names and type_param_constraints in var_id order (0, 1, 2, ...).
            // This ensures the certificate's type params match the order used during proving,
            // which is critical for synthetic definition lookup to work correctly.
            let mut var_id_to_new_name: HashMap<u16, String> = HashMap::new();
            let mut type_param_names = Vec::new();
            let mut type_param_constraints: Vec<Option<Typeclass>> = Vec::new();

            for (id, type_var_kind) in info.type_vars.iter().enumerate() {
                let id = id as u16;
                let name = self.bindings.next_indexed_var('T', &mut self.next_t);
                var_id_to_new_name.insert(id, name.clone());
                type_param_names.push(name);

                // Look up typeclass constraint from the kind
                let constraint = type_var_kind.as_ref().as_typeclass().map(|tc_id| {
                    normalizer
                        .kernel_context()
                        .type_store
                        .get_typeclass(tc_id)
                        .clone()
                });
                type_param_constraints.push(constraint);
            }

            // Build rename map: x0 -> T0, T0 -> T0, x1 -> T1, etc.
            // Both "x{i}" and "T{i}" represent var_id i and should map to the same new name.
            let mut rename_map = HashMap::new();
            for old_name in &all_type_vars {
                // Try to extract the variable ID from the name (e.g., "x0" -> 0 or "T0" -> 0)
                let var_id = old_name
                    .strip_prefix("x")
                    .or_else(|| old_name.strip_prefix("T"))
                    .and_then(|s| s.parse::<u16>().ok());

                let new_name = if let Some(id) = var_id {
                    var_id_to_new_name
                        .get(&id)
                        .cloned()
                        .unwrap_or_else(|| old_name.clone())
                } else {
                    old_name.clone()
                };

                rename_map.insert(old_name.clone(), new_name);
            }

            // Build the type params string (shared across all synthetics)
            let type_params_str = if type_param_names.is_empty() {
                String::new()
            } else {
                let mut param_strs: Vec<String> = Vec::new();
                for (name, constraint) in type_param_names.iter().zip(type_param_constraints.iter())
                {
                    let param_str = if let Some(typeclass) = constraint {
                        // Check if the typeclass is available by name in the current bindings
                        let tc_code = if self.bindings.has_typeclass_name(&typeclass.name) {
                            typeclass.name.clone()
                        } else {
                            // Use lib(module).TypeclassName format
                            let module_expr = self.module_to_expr(typeclass.module_id)?;
                            format!("{}.{}", module_expr, typeclass.name)
                        };
                        format!("{}: {}", name, tc_code)
                    } else {
                        name.clone()
                    };
                    param_strs.push(param_str);
                }
                format!("[{}]", param_strs.join(", "))
            };

            // Create code for the declaration with renamed types
            let mut decl_parts = vec![];
            for (name, ty) in &decl {
                let renamed_ty = rename_type_vars_in_type(ty, &rename_map);
                let ty_code = self.type_to_code(&renamed_ty)?;
                decl_parts.push(format!("{}: {}", name, ty_code));
            }

            // For single synthetic: let s0[T0]: type satisfy { ... }
            // For multiple synthetics: let [T0] (s0: type0, s1: type1) satisfy { ... }
            let decl_str = if decl_parts.len() > 1 {
                // Multiple synthetics: type params go before the tuple
                format!("{} ({})", type_params_str, decl_parts.join(", "))
            } else if !type_params_str.is_empty() {
                // Single synthetic with type params: type params go after the name
                let (name, ty) = &decl[0];
                let renamed_ty = rename_type_vars_in_type(ty, &rename_map);
                let ty_code = self.type_to_code(&renamed_ty)?;
                format!("{}{}: {}", name, type_params_str, ty_code)
            } else {
                // Single synthetic without type params
                decl_parts.join("")
            };

            // Rename type variables in the condition value
            // Pass the set of synthetics being defined so they don't get type params added
            let defining_synthetics: HashSet<(ModuleId, AtomId)> =
                info.atoms.iter().copied().collect();
            let cond_val = rename_type_vars_in_value(&cond_val, &rename_map, &defining_synthetics);

            // The denormalized clauses might contain additional synthetic constants.
            // Define them first (recursively) before we use them in this definition.
            let additional_synthetic_ids = cond_val.find_synthetics();
            if !additional_synthetic_ids.is_empty() {
                self.define_synthetics(additional_synthetic_ids, normalizer, codes)?;
            }

            let cond = self.value_to_code(&cond_val)?;

            let let_statement = format!("let {} satisfy {{ {} }}", decl_str, cond);
            codes.push(let_statement);
        }
        Ok(())
    }

    /// Convert to a clause to code strings.
    /// This will generate synthetic atom definitions if necessary.
    /// Appends let statements that define arbitrary variables and synthetic atoms to definitions,
    /// and appends the actual clause content to codes.
    ///
    /// The replacement_context is the context that the var_map's replacement terms reference.
    /// This is needed to look up variable types when specializing.
    fn specialization_to_code(
        &mut self,
        generic: &Clause,
        var_map: &VariableMap,
        replacement_context: &LocalContext,
        normalizer: &Normalizer,
        definitions: &mut Vec<String>,
        codes: &mut Vec<String>,
    ) -> Result<()> {
        let mut clause = var_map.specialize_clause_with_replacement_context(
            &generic,
            replacement_context,
            normalizer.kernel_context(),
        );

        // Normalize variable IDs to ensure they are in order (0, 1, 2, ...) with no gaps.
        // This is needed because specialize_clause may produce clauses with gaps in variable
        // indices when some variables are replaced with constants.
        clause.normalize_var_ids_no_flip();

        // This is the only place where we use the feature of "denormalize" that we can
        // pass the arbitrary names like this.
        // It might make more sense to do this in value space, so that we don't have to make
        // the normalizer even more complicated.

        // Capture existing keys BEFORE adding new entries.
        // We only want to generate definitions for entries added in THIS call,
        // because those entries need the current clause's LocalContext for correct denormalization.
        // Entries from earlier calls were already processed with their own (correct) contexts.
        let keys_before: HashSet<Term> = self.arbitrary_names.keys().cloned().collect();

        self.add_arbitrary_for_clause(&clause);
        let mut value = normalizer.denormalize(&clause, Some(&self.arbitrary_names), None, true);

        // Define the arbitrary variables.
        // Use the clause's local context to look up typeclass constraints for type variables.
        let local_context = clause.get_local_context();
        for (ty, name) in self.arbitrary_names.clone() {
            if keys_before.contains(&ty) {
                continue; // Already processed in a previous call with the correct context
            }
            let denorm_type =
                normalizer.denormalize_type_with_context(ty.clone(), local_context, true);
            let ty_code = self.type_to_code(&denorm_type)?;
            let decl = format!("let {}: {} satisfy {{ true }}", name, ty_code);
            definitions.push(decl);
        }

        // Create a name and definition for each synthetic atom.
        let synthetic_ids = value.find_synthetics();
        self.define_synthetics(synthetic_ids, normalizer, definitions)?;

        value = value.replace_synthetics(&self.synthetic_names);
        let subvalues = value.remove_and();
        for subvalue in subvalues {
            codes.push(self.value_to_code(&subvalue)?);
        }
        Ok(())
    }

    /// Converts a ConcreteStep to code.
    /// Returns (definitions, code) where definitions are let statements that define
    /// arbitrary variables and synthetic atoms, and code is the actual clause content.
    pub fn concrete_step_to_code(
        &mut self,
        step: &ConcreteStep,
        normalizer: &Normalizer,
    ) -> Result<(Vec<String>, Vec<String>)> {
        let mut defs = vec![];
        let mut codes = vec![];
        for (var_map, replacement_context) in &step.var_maps {
            self.specialization_to_code(
                &step.generic,
                var_map,
                replacement_context,
                normalizer,
                &mut defs,
                &mut codes,
            )?;
        }
        // Deduplicate while preserving order (don't use sort which breaks dependency order)
        defs.dedup();
        codes.sort();
        Ok((defs, codes))
    }

    fn type_to_code(&mut self, acorn_type: &AcornType) -> Result<String> {
        let expr = self.type_to_expr(acorn_type)?;
        Ok(expr.to_string())
    }

    fn add_arbitrary_for_term(&mut self, term: &Term, local_context: &LocalContext) {
        match term.as_ref().decompose() {
            Decomposition::Atom(Atom::FreeVariable(var_id)) => {
                // For a variable term, get its type from the local context.
                let var_type = local_context
                    .get_var_type(*var_id as usize)
                    .cloned()
                    .expect("Variable should have type in LocalContext");
                // Skip type variables (those whose type is TypeSort or a typeclass).
                // Type variables are type-level parameters, not value-level, so they
                // don't need arbitrary value definitions in certificates.
                if var_type.as_ref().is_type_param_kind() {
                    return;
                }
                if !self.arbitrary_names.contains_key(&var_type) {
                    // Generate a name for this arbitrary value
                    let name = self.bindings.next_indexed_var('s', &mut self.next_s);
                    let cname = ConstantName::Unqualified(self.bindings.module_id(), name);
                    self.arbitrary_names.insert(var_type, cname);
                }
            }
            Decomposition::Atom(_) => {}
            Decomposition::Application(func, arg) => {
                self.add_arbitrary_for_term(&func.to_owned(), local_context);
                self.add_arbitrary_for_term(&arg.to_owned(), local_context);
            }
            Decomposition::Pi(input, output) => {
                self.add_arbitrary_for_term(&input.to_owned(), local_context);
                self.add_arbitrary_for_term(&output.to_owned(), local_context);
            }
        }
    }

    /// For any variables in this clause, add an arbitrary variable.
    fn add_arbitrary_for_clause(&mut self, clause: &Clause) {
        let local_context = clause.get_local_context();
        for literal in &clause.literals {
            for term in [&literal.left, &literal.right] {
                self.add_arbitrary_for_term(term, local_context);
            }
        }
    }

    /// Check if we can infer a function's type parameters from its argument types.
    ///
    /// The key insight: if a function foo[P, Q] takes argument of type P,
    /// we can't infer Q from just the argument. So we need explicit parameters.
    ///
    /// Additionally, if a type parameter appears in the return type, we can't omit
    /// the type params because the return type might be a function type, which would
    /// change the arity after un-currying. For example, compose[T, U, V] returns T -> V,
    /// and when V = Nat -> Nat, the arity changes from 3 to 4.
    fn can_infer_type_params_from_args(&self, function: &AcornValue, args: &[AcornValue]) -> bool {
        // Get the constant and its parameters
        let constant = match function {
            AcornValue::Constant(c) => c,
            _ => return true, // Not a generic constant, inference doesn't apply
        };

        if constant.params.is_empty() {
            return true; // No parameters to infer
        }

        // Get the function type
        let function_type = function.get_type();
        let fn_type = match &function_type {
            AcornType::Function(ft) => ft,
            _ => return false, // Not a function type, can't infer
        };

        // Check if the arity changed due to type param instantiation.
        // If the instance_type has a different arity than generic_type, we can't omit
        // type params because the parser would use the generic arity.
        //
        // For example:
        // - compose[T, U, V] generic: 3 args, but compose[Nat, Nat, Nat -> Nat]: 4 args
        // - double[T] generic: 1 arg, double[Bool]: still 1 arg
        if Self::type_param_could_change_arity(constant) {
            return false;
        }

        // For each type parameter, check if it appears in the argument types
        // in a way that would allow inference
        for param_type in &constant.params {
            let mut found_in_args = false;

            // Check each argument type to see if this parameter appears
            for (i, arg) in args.iter().enumerate() {
                if let Some(expected_arg_type) = fn_type.arg_types.get(i) {
                    // Check if the parameter appears in this argument position
                    // For simplicity, we just check direct equality
                    if param_type == expected_arg_type {
                        // Also check that the actual argument's type is concrete.
                        // If the arg type contains type variables (has_generic), then
                        // those variables would also need resolution, so we can't infer.
                        // E.g., has_finite_order(s0) where s0 has type Variable(T0)
                        // can't infer T from s0's type because T0 is not concrete.
                        let arg_type = arg.get_type();
                        if !arg_type.has_generic() {
                            found_in_args = true;
                            break;
                        }
                    }
                }
            }

            if !found_in_args {
                // This parameter doesn't appear in arguments, can't infer
                return false;
            }
        }

        true
    }

    /// Check if a type parameter could change the function's arity when instantiated.
    ///
    /// This happens when the type param IS the return type (after un-currying).
    /// If it gets instantiated to a function type, the function type would
    /// un-curry again, adding more arguments.
    ///
    /// Examples:
    /// - compose[T, U, V]: (U -> V, T -> U, T) -> V (after un-currying)
    ///   V is the return type. If V = Nat -> Nat, arity changes from 3 to 4.
    /// - double[T]: T -> T
    ///   T is the return type. If T = Nat -> Nat, return becomes Nat -> Nat.
    ///   But wait - does this change arity? Let me think...
    ///   Actually, for double[Nat -> Nat](f), the return type IS (Nat -> Nat), not un-curried.
    ///   So double's arity stays 1. The difference is that compose's instance_type
    ///   gets recomputed with un-currying, while double's doesn't (because the arg type
    ///   is the same as return type, and we don't un-curry based on arg types).
    ///
    /// The key insight: we need to check if the constant's INSTANCE type has a different
    /// arity from its GENERIC type.
    fn type_param_could_change_arity(constant: &ConstantInstance) -> bool {
        let generic_arity = match &constant.generic_type {
            AcornType::Function(ft) => ft.arg_types.len(),
            _ => 0,
        };
        let instance_arity = match &constant.instance_type {
            AcornType::Function(ft) => ft.arg_types.len(),
            _ => 0,
        };
        generic_arity != instance_arity
    }

    /// Create a marked-up string to display information for this value.
    pub fn value_to_marked(&mut self, value: &AcornValue) -> Result<MarkedString> {
        let value_code = self.value_to_code(value)?;
        let type_code = self.type_to_code(&value.get_type())?;
        let code = format!("{}: {}", value_code, type_code);
        Ok(Self::marked(code))
    }

    /// Create a marked-up string to display information for this type.
    pub fn type_to_marked(&mut self, acorn_type: &AcornType) -> Result<MarkedString> {
        let code = self.type_to_code(acorn_type)?;
        Ok(Self::marked(format!("type {}", code)))
    }

    /// Given a constant instance, create an expression that refers to it.
    /// This does *not* include the parameters.
    fn const_to_expr(&self, ci: &ConstantInstance) -> Result<Expression> {
        if ci.name.is_synthetic() {
            if let Some(id) = ci.name.synthetic_id() {
                if let Some(synthetic_name) = self.synthetic_names.get(&id) {
                    return Ok(Expression::generate_identifier(synthetic_name));
                }
            }
            return Err(Error::synthetic(&ci.name.to_string()));
        }
        if self.is_replaced_synthetic(&ci.name) {
            if let ConstantName::Unqualified(_, word) = &ci.name {
                return Ok(Expression::generate_identifier(word));
            }
        }

        // Handle numeric literals for datatype attributes (not typeclass attributes).
        // Typeclass attribute numerals are handled in value_to_expr where we have
        // more context about whether the datatype has its own override.
        if let Some((_, datatype_name, attr)) = ci.name.as_attribute() {
            if attr.chars().all(|ch| ch.is_ascii_digit()) && !ci.name.is_typeclass_attr() {
                let datatype = Datatype {
                    module_id: ci.name.module_id(),
                    name: datatype_name.to_string(),
                };

                let numeral = TokenType::Numeral.new_token(&attr);

                // If it's the default type, we don't need to scope it
                if self.bindings.numerals() == Some(&datatype) {
                    return Ok(Expression::Singleton(numeral));
                }

                // Otherwise, we need to scope it by the type
                let numeric_type = self.datatype_to_expr(&datatype)?;
                return Ok(Expression::generate_dot(
                    numeric_type,
                    Expression::Singleton(numeral),
                ));
            }
        }

        // Handle local constants
        if ci.name.module_id() == self.bindings.module_id() {
            return Ok(match &ci.name {
                ConstantName::Unqualified(_, word) => Expression::generate_identifier(word),
                ConstantName::DatatypeAttribute(datatype, attr) => {
                    Expression::generate_identifier(&datatype.name).add_dot_str(attr)
                }
                ConstantName::SpecificDatatypeAttribute(datatype, _types, attr) => {
                    // Generate the same expression as for generic attributes
                    // The specific type information is not needed in the generated code
                    Expression::generate_identifier(&datatype.name).add_dot_str(attr)
                }
                ConstantName::TypeclassAttribute(tc, attr) => {
                    Expression::generate_identifier(&tc.name).add_dot_str(attr)
                }
                ConstantName::Synthetic(..) => panic!("control should not get here"),
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.bindings.constant_alias(&ci.name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let Some((_, rname, attr)) = ci.name.as_attribute() {
            // Check if this is a datatype attribute
            let datatype = Datatype {
                module_id: ci.name.module_id(),
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.datatype_alias(&datatype) {
                let lhs = Expression::generate_identifier(alias);
                return Ok(lhs.add_dot_str(attr));
            }

            // Check if this is a typeclass attribute
            let typeclass = Typeclass {
                module_id: ci.name.module_id(),
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.typeclass_alias(&typeclass) {
                let lhs = Expression::generate_identifier(alias);
                return Ok(lhs.add_dot_str(attr));
            }
        }

        // Refer to this constant using its module
        let module = self.module_to_expr(ci.name.module_id())?;
        match &ci.name {
            ConstantName::Unqualified(_, name) => Ok(module.add_dot_str(name)),
            ConstantName::DatatypeAttribute(datatype, attr) => {
                Ok(module.add_dot_str(&datatype.name).add_dot_str(attr))
            }
            ConstantName::SpecificDatatypeAttribute(datatype, _types, attr) => {
                Ok(module.add_dot_str(&datatype.name).add_dot_str(attr))
            }
            ConstantName::TypeclassAttribute(tc, attr) => {
                Ok(module.add_dot_str(&tc.name).add_dot_str(attr))
            }
            ConstantName::Synthetic(..) => panic!("control should not get here"),
        }
    }

    /// If use_x is true we use x-variables; otherwise we use k-variables.
    fn generate_quantifier_expr(
        &mut self,
        token_type: TokenType,
        quants: &Vec<AcornType>,
        value: &AcornValue,
        use_x: bool,
    ) -> Result<Expression> {
        let initial_var_names_len = self.var_names.len();
        let mut decls = vec![];
        for arg_type in quants {
            let var_name = if use_x {
                self.bindings.next_indexed_var('x', &mut self.next_x)
            } else {
                self.bindings.next_indexed_var('k', &mut self.next_k)
            };
            let name_token = TokenType::Identifier.new_token(&var_name);
            self.var_names.push(var_name);
            let type_expr = self.type_to_expr(arg_type)?;
            let var_name = Declaration::Typed(name_token, type_expr);
            let decl = var_name;
            decls.push(decl);
        }
        let subresult = self.value_to_expr(value, false)?;
        self.var_names.truncate(initial_var_names_len);
        Ok(Expression::Binder(
            token_type.generate(),
            decls,
            Box::new(subresult),
            TokenType::RightBrace.generate(),
        ))
    }

    /// Convert an AcornValue to an Expression.
    /// var_names is the names we have assigned to indexed variables so far.
    /// We automatically generate variable names sometimes, using next_x and next_k.
    /// "inferrable" is true if the type of this value can be inferred, which means
    /// we don't need top level parameters.
    fn value_to_expr(&mut self, value: &AcornValue, inferrable: bool) -> Result<Expression> {
        match value {
            AcornValue::Variable(i, _) => {
                if *i >= self.var_names.len() as u16 {
                    // This is definitely wrong.
                    // We use this for the hover, but it would be better to fix it.
                    #[cfg(test)]
                    panic!(
                        "Variable index {} out of range (var_names has {} entries)",
                        i,
                        self.var_names.len()
                    );
                    #[cfg(not(test))]
                    Ok(Expression::generate_identifier(&format!("v{}", i)))
                } else {
                    Ok(Expression::generate_identifier(
                        &self.var_names[*i as usize],
                    ))
                }
            }
            AcornValue::Application(fa) => {
                let mut arg_exprs = vec![];
                for arg in &fa.args {
                    // We currently never infer the type of arguments from the type of the function.
                    // Inference only goes the other way.
                    // We could improve this at some point.
                    arg_exprs.push(self.value_to_expr(arg, false)?);
                }

                // Check if we could replace this with receiver+attribute syntax
                let receiver_type = fa.args[0].get_type();
                if let Some((module_id, entity, attr)) = fa.function.as_attribute() {
                    let is_typeclass_instance =
                        if let AcornValue::Constant(c) = fa.function.as_ref() {
                            if let ConstantName::TypeclassAttribute(typeclass, _) = &c.name {
                                if let AcornType::Data(datatype, _) = &receiver_type {
                                    if self.bindings.is_instance_of(datatype, typeclass) {
                                        // Check if the datatype has its own attribute with the same name
                                        let datatype_attr_name =
                                            DefinedName::datatype_attr(datatype, &attr);
                                        !self.bindings.constant_name_in_use(&datatype_attr_name)
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        } else {
                            false
                        };

                    let use_receiver_syntax =
                        self.bindings
                            .inherits_attributes(&receiver_type, module_id, entity)
                            || is_typeclass_instance;

                    if use_receiver_syntax {
                        // We can use receiver+attribute syntax
                        if arg_exprs.len() == 1 {
                            // Prefix operators
                            if let Some(op) = TokenType::from_prefix_magic_method_name(&attr) {
                                return Ok(Expression::generate_unary(
                                    op,
                                    arg_exprs.pop().unwrap(),
                                ));
                            }
                        }

                        if arg_exprs.len() == 2 {
                            // Infix operators
                            if let Some(op) = TokenType::from_infix_magic_method_name(&attr) {
                                let right = arg_exprs.pop().unwrap();
                                let left = arg_exprs.pop().unwrap();
                                // swap left and right for infix op `∈` and `∉` in display, e.g. display of proof step in Acorn assistance
                                if op == TokenType::ElemOf || op == TokenType::NotElemOf {
                                    return Ok(Expression::generate_binary(right, op, left));
                                }
                                return Ok(Expression::generate_binary(left, op, right));
                            }

                            // Long numeric literals
                            if attr == "read" && arg_exprs[0].is_number() {
                                if let Some(digit) = arg_exprs[1].to_digit() {
                                    let left = arg_exprs.remove(0);
                                    return Ok(Expression::generate_number(left, digit));
                                }
                            }
                        }

                        // General member functions
                        let instance = arg_exprs.remove(0);
                        let bound = Expression::generate_binary(
                            instance,
                            TokenType::Dot,
                            Expression::generate_identifier(&attr),
                        );
                        if arg_exprs.len() == 0 {
                            // Like foo.bar
                            return Ok(bound);
                        } else {
                            // Like foo.bar(baz, qux)
                            let applied = Expression::Concatenation(
                                Box::new(bound),
                                Box::new(Expression::generate_paren_grouping(arg_exprs)),
                            );
                            return Ok(applied);
                        }
                    }
                }

                // For overridden typeclass attributes, we need explicit parameters
                // to distinguish from the datatype's own attributes
                let inferrable = if let AcornValue::Constant(c) = fa.function.as_ref() {
                    // Synthetics can't have explicit type params in the syntax
                    // Check both original synthetics and replaced ones (now named s0, s1, etc.)
                    if c.name.is_synthetic() || self.is_replaced_synthetic(&c.name) {
                        true
                    } else if let ConstantName::TypeclassAttribute(typeclass, attr_name) = &c.name {
                        if let AcornType::Data(datatype, _) = &receiver_type {
                            if self.bindings.is_instance_of(datatype, typeclass) {
                                let datatype_attr_name =
                                    DefinedName::datatype_attr(datatype, attr_name);
                                // If the datatype has its own attribute, don't infer parameters
                                !self.bindings.constant_name_in_use(&datatype_attr_name)
                            } else {
                                true
                            }
                        } else {
                            true
                        }
                    } else {
                        // For regular functions, check if we can infer type parameters from arguments
                        self.can_infer_type_params_from_args(&fa.function, &fa.args)
                    }
                } else {
                    true
                };
                let f = self.value_to_expr(&fa.function, inferrable)?;
                let grouped_args = Expression::generate_paren_grouping(arg_exprs);
                Ok(Expression::Concatenation(
                    Box::new(f),
                    Box::new(grouped_args),
                ))
            }
            AcornValue::Binary(op, left, right) => {
                let mut left_expr = self.value_to_expr(left, false)?;
                let mut right_expr = self.value_to_expr(right, false)?;
                let token = op.token_type().generate();

                if let AcornValue::Binary(left_op, _, _) = left.as_ref() {
                    if left_op.token_type().binary_precedence()
                        < op.token_type().binary_precedence()
                    {
                        // We want the left op to happen first, but its precedence is lower.
                        // So we wrap the left expression in parentheses.
                        let open = TokenType::LeftParen.generate();
                        let close = TokenType::RightParen.generate();
                        left_expr = Expression::Grouping(open, Box::new(left_expr), close);
                    }
                }

                if let AcornValue::Binary(right_op, _, _) = right.as_ref() {
                    if right_op.token_type().binary_precedence()
                        <= op.token_type().binary_precedence()
                    {
                        // We want the right op to happen first, but its precedence is not higher.
                        // So we wrap the right expression in parentheses.
                        let open = TokenType::LeftParen.generate();
                        let close = TokenType::RightParen.generate();
                        right_expr = Expression::Grouping(open, Box::new(right_expr), close);
                    }
                }

                Ok(Expression::Binary(
                    Box::new(left_expr),
                    token,
                    Box::new(right_expr),
                ))
            }
            AcornValue::Not(x) => {
                let x = self.value_to_expr(x, false)?;
                Ok(Expression::generate_unary(TokenType::Not, x))
            }
            AcornValue::Try(x, _) => {
                let x = self.value_to_expr(x, false)?;
                Ok(Expression::generate_unary(TokenType::QuestionMark, x))
            }
            AcornValue::ForAll(quants, value) => {
                self.generate_quantifier_expr(TokenType::ForAll, quants, value, true)
            }
            AcornValue::Exists(quants, value) => {
                self.generate_quantifier_expr(TokenType::Exists, quants, value, false)
            }
            AcornValue::Lambda(quants, value) => {
                self.generate_quantifier_expr(TokenType::Function, quants, value, true)
            }
            AcornValue::Bool(b) => {
                let token = if *b {
                    TokenType::True.generate()
                } else {
                    TokenType::False.generate()
                };
                Ok(Expression::Singleton(token))
            }
            AcornValue::Constant(c) => {
                if c.params.len() == 1 {
                    if let Some((module_id, entity, attr)) = c.name.as_attribute() {
                        if self
                            .bindings
                            .inherits_attributes(&c.params[0], module_id, entity)
                        {
                            // We can use receiver+attribute syntax
                            let lhs = self.type_to_expr(&c.params[0])?;
                            let rhs = Expression::generate_identifier(&attr);
                            return Ok(Expression::generate_dot(lhs, rhs));
                        }

                        // Check if this is a typeclass attribute being accessed on an instance type
                        if let ConstantName::TypeclassAttribute(typeclass, _) = &c.name {
                            if let AcornType::Data(datatype, _) = &c.params[0] {
                                if self.bindings.is_instance_of(datatype, typeclass) {
                                    // Check if the datatype has its own attribute with the same name
                                    let datatype_attr_name =
                                        DefinedName::datatype_attr(datatype, &attr);
                                    let datatype_has_own_attr =
                                        self.bindings.constant_name_in_use(&datatype_attr_name);

                                    // Special case for digit attributes
                                    if attr.chars().all(|ch| ch.is_ascii_digit()) {
                                        let numeral = TokenType::Numeral.new_token(&attr);
                                        if self.bindings.numerals() == Some(datatype) {
                                            // If it's the numerals type, just return the numeral
                                            return Ok(Expression::Singleton(numeral));
                                        }
                                        // Otherwise, scope it by the type
                                        let lhs = self.type_to_expr(&c.params[0])?;
                                        return Ok(Expression::generate_dot(
                                            lhs,
                                            Expression::Singleton(numeral),
                                        ));
                                    }

                                    if !datatype_has_own_attr {
                                        // Generate DataType.attribute instead of Typeclass.attribute[DataType]
                                        // only if the datatype doesn't override this attribute
                                        let lhs = self.type_to_expr(&c.params[0])?;
                                        let rhs = Expression::generate_identifier(&attr);
                                        return Ok(Expression::generate_dot(lhs, rhs));
                                    }
                                }
                            }
                        }
                    }
                }

                let const_expr = self.const_to_expr(&c)?;

                // Synthetics can't have explicit type params in the syntax
                // Check both original synthetics and replaced ones (now named s0, s1, etc.)
                let is_synthetic_const =
                    c.name.is_synthetic() || self.is_replaced_synthetic(&c.name);
                // Only add type params if the constant itself is polymorphic.
                // A constant like `item: T` (theorem parameter) has params but empty
                // type_param_names - it uses types from enclosing scope but isn't polymorphic.
                let is_polymorphic = !c.type_param_names.is_empty();
                if !inferrable && !c.params.is_empty() && !is_synthetic_const && is_polymorphic {
                    self.parametrize_expr(const_expr, &c.params)
                } else {
                    // We don't need to parametrize because it can be inferred,
                    // it's a synthetic (type params implicit), or it's not polymorphic
                    Ok(const_expr)
                }
            }
            AcornValue::IfThenElse(condition, if_value, else_value) => {
                let condition = self.value_to_expr(condition, false)?;
                let if_value = self.value_to_expr(if_value, false)?;
                let else_value = self.value_to_expr(else_value, false)?;
                Ok(Expression::IfThenElse(
                    TokenType::If.generate(),
                    Box::new(condition),
                    Box::new(if_value),
                    Some(Box::new(else_value)),
                    TokenType::RightBrace.generate(),
                ))
            }
            AcornValue::Match(_scrutinee, _cases) => {
                todo!("codegen match expressions");
            }
        }
    }

    /// For testing. Panics if generating code for this value does not give expected.
    pub fn expect(bindings: &BindingMap, input: &str, value: &AcornValue, expected: &str) {
        let output = match CodeGenerator::new(bindings).value_to_code(&value) {
            Ok(output) => output,
            Err(e) => panic!("code generation error: {}", e),
        };

        if output != expected {
            panic!(
                "\nconverted:\n  {}\nto value:\n  {}\nand back to:\n  {}\nbut expected:\n  {}\n",
                input, value, output, expected
            );
        }
    }
}

#[derive(Debug)]
pub enum Error {
    // Trouble expressing a synthetic atom created during normalization.
    Synthetic(String),

    // Trouble referencing a module that has not been directly imported.
    UnimportedModule(ModuleId, String),

    // Trouble using a type that we can't find the name for.
    UnnamedType(String),

    // Some sort of value we could handle, but we don't yet, because it's rare.
    UnhandledValue(String),

    // The code contains the explicit goal, which we can't generate code for.
    ExplicitGoal,

    // When you try to generate code but there is no proof
    NoProof,

    // Generated code that failed checking
    GeneratedBadCode(String),

    // Something went wrong, it's our fault, and we can't figure out what it is
    InternalError(String),
}

impl Error {
    pub fn synthetic(s: &str) -> Error {
        Error::Synthetic(s.to_string())
    }

    pub fn unnamed_type(datatype: &Datatype) -> Error {
        Error::UnnamedType(datatype.name.to_string())
    }

    pub fn unhandled_value(s: &str) -> Error {
        Error::UnhandledValue(s.to_string())
    }

    pub fn internal<T: Into<String>>(s: T) -> Error {
        Error::InternalError(s.into())
    }

    pub fn error_type(&self) -> &'static str {
        match self {
            Error::Synthetic(_) => "Synthetic",
            Error::UnimportedModule(..) => "UnimportedModule",
            Error::UnnamedType(_) => "UnnamedType",
            Error::UnhandledValue(_) => "UnhandledValue",
            Error::ExplicitGoal => "ExplicitGoal",
            Error::NoProof => "NoProof",
            Error::GeneratedBadCode(_) => "GeneratedInvalidCode",
            Error::InternalError(_) => "InternalError",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Synthetic(s) => {
                write!(f, "could not find a name for the synthetic constant: {}", s)
            }
            Error::UnimportedModule(_, name) => {
                write!(
                    f,
                    "could not generate code using '{}' because it is not imported",
                    name
                )
            }
            Error::UnnamedType(s) => {
                write!(f, "could not figure out a name for the type: {}", s)
            }
            Error::UnhandledValue(s) => {
                write!(f, "codegen for '{}' values is not yet implemented", s)
            }
            Error::ExplicitGoal => {
                write!(f, "could not isolate the goal at the end of the proof")
            }
            Error::NoProof => write!(f, "no proof"),
            Error::GeneratedBadCode(s) => {
                write!(f, "generated invalid code: {}", s)
            }
            Error::InternalError(s) => {
                write!(f, "internal error: {}", s)
            }
        }
    }
}

impl From<crate::elaborator::error::Error> for Error {
    fn from(err: crate::elaborator::error::Error) -> Self {
        Error::GeneratedBadCode(err.to_string())
    }
}

impl From<String> for Error {
    fn from(err: String) -> Self {
        Error::GeneratedBadCode(err)
    }
}

#[cfg(test)]
mod tests {
    use crate::project::Project;

    #[test]
    fn test_polymorphic_synthetic_declaration() {
        use super::CodeGenerator;
        use crate::processor::Processor;

        let (processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            let foo[T]: T -> Bool = axiom
            theorem goal[T] { exists(t: T) { foo(t) } }
            "#,
        );

        let normalizer = &normalized_goal.normalizer;
        let synthetic_ids = normalizer.get_synthetic_ids();

        let mut generator = CodeGenerator::new(&bindings);
        let mut codes = vec![];
        generator
            .define_synthetics(synthetic_ids, normalizer, &mut codes)
            .unwrap();

        // The synthetic uses T0 for its type parameter (not T from the goal)
        // foo[T0](s0) needs explicit type params since s0's type is Variable(T0)
        let expected = "let s0[T0]: T0 satisfy { not goal[T0] or foo[T0](s0) and forall(x0: T0) { not foo[T0](x0) or goal[T0] } }";
        assert_eq!(codes[0], expected);

        processor.test_parse_code(&codes[0], &bindings, normalizer);
    }

    #[test]
    fn test_polymorphic_synthetic_with_typeclass() {
        use super::CodeGenerator;
        use crate::processor::Processor;

        // Similar to test_polymorphic_synthetic_declaration but with a typeclass constraint
        let (processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            let foo[T: Magma]: T -> Bool = axiom
            theorem goal[T: Magma] { exists(t: T) { foo(t) } }
            "#,
        );

        let normalizer = &normalized_goal.normalizer;
        let synthetic_ids = normalizer.get_synthetic_ids();

        let mut generator = CodeGenerator::new(&bindings);
        let mut codes = vec![];
        generator
            .define_synthetics(synthetic_ids, normalizer, &mut codes)
            .unwrap();

        // The synthetic uses T0 with typeclass constraint
        // foo[T0](s0) needs explicit type params since s0's type is Variable(T0)
        let expected = "let s0[T0: Magma]: T0 satisfy { not goal[T0] or foo[T0](s0) and forall(x0: T0) { not foo[T0](x0) or goal[T0] } }";
        assert_eq!(codes[0], expected);

        processor.test_parse_code(&codes[0], &bindings, normalizer);
    }

    #[test]
    fn test_polymorphic_synthetic_with_multi_arg_function() {
        use super::CodeGenerator;
        use crate::processor::Processor;

        // Use a pattern that creates a synthetic with type ((T, T) -> Bool) -> T
        // The is_reflexive pattern has forall inside, which when negated becomes
        // exists(t: T) { not f(t, t) } where t depends on f, giving synthetic type
        // ((T, T) -> Bool) -> T
        let (processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            define is_reflexive[T](f: (T, T) -> Bool) -> Bool {
                forall(t: T) { f(t, t) }
            }
            theorem goal[T](f: (T, T) -> Bool) { is_reflexive(f) }
            "#,
        );

        let normalizer = &normalized_goal.normalizer;
        let synthetic_ids = normalizer.get_synthetic_ids();

        let mut generator = CodeGenerator::new(&bindings);
        let mut codes = vec![];
        generator
            .define_synthetics(synthetic_ids, normalizer, &mut codes)
            .unwrap();

        // The synthetic uses T0 with type ((T0, T0) -> Bool) -> T0
        let expected = "let s0[T0]: ((T0, T0) -> Bool) -> T0 satisfy { forall(x0: (T0, T0) -> Bool, x1: T0) { not is_reflexive[T0](x0) or x0(x1, x1) } and forall(x2: (T0, T0) -> Bool) { not x2(s0(x2), s0(x2)) or is_reflexive[T0](x2) } }";
        assert_eq!(codes[0], expected);

        processor.test_parse_code(&codes[0], &bindings, normalizer);
    }

    #[test]
    fn test_code_generation() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            type MyType: axiom
            let t: MyType = axiom
        "#,
        );
        p.check_code("main", "t");
        p.check_code("main", "forall(x0: MyType) { x0 = t }");
    }

    #[test]
    fn test_code_for_imported_things() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            let thing1: Bool = axiom
            let thing2: Bool = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from stuff import thing1, thing2
            let st1: Bool = thing1
        "#,
        );
        p.check_code_into("main", "thing1", "thing1");
        p.check_code("main", "thing1");
        p.check_code("main", "thing2");
    }

    #[test]
    fn test_imported_member_functions() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolpair.ac",
            r#"
            structure BoolPair {
                first: Bool
                second: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from boolpair import BoolPair
            let first: BoolPair -> Bool = BoolPair.first
        "#,
        );
        p.expect_ok("main");
        p.check_code("main", "first");
        p.check_code_into("main", "BoolPair.first", "first");
        p.check_code_into("main", "lib(boolpair).BoolPair.first", "first");

        p.check_code("main", "BoolPair.second");
        p.check_code_into("main", "lib(boolpair).BoolPair.second", "BoolPair.second");
    }

    #[test]
    fn test_structure_aliasing() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            structure Foo {
                member: Bool
            }
            type Bar: Foo
        "#,
        );
        p.expect_ok("stuff");
        p.check_code_into("stuff", "Bar.member", "Foo.member");
    }

    #[test]
    fn test_names_imported_via_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/stuff.ac",
            r#"
            type Foo: axiom
            attributes Foo {
                let foo: Bool = true
                let foo2: Bool = false
            }
            type Bar: Foo
            let bar: Bar = axiom
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from stuff import Foo, Bar, bar
            let x: Bool = Bar.foo
            let y: Bar = bar
        "#,
        );
        p.expect_ok("stuff");
        p.expect_ok("main");
        p.check_code("main", "x");
        p.check_code_into("main", "y", "bar");
        p.check_code_into("main", "Foo.foo2", "Foo.foo2");
    }

    #[test]
    fn test_imported_numbers_codegen_basic() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            "#,
        );
        p.check_code_into("main", "Nat.0", "Nat.0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "Nat.0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "Nat.0 + Nat.0");
    }

    #[test]
    fn test_imported_numbers_codegen_with_numerals() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/nat.ac",
            r#"
            inductive Nat {
                0
                suc(Nat)
            }

            numerals Nat

            attributes Nat {
                define add(self, other: Nat) -> Nat {
                    0
                }
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from nat import Nat
            numerals Nat
            "#,
        );
        p.check_code_into("main", "Nat.0", "0");
        p.check_code_into("main", "Nat.suc(Nat.0)", "0.suc");
        p.check_code_into("main", "Nat.add(Nat.0, Nat.0)", "0 + 0");
    }

    #[test]
    fn test_import_without_from_codegen() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/boolbox.ac",
            r#"
            structure BoolBox {
                item: Bool
            }
        "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from boolbox import BoolBox
        "#,
        );
        p.check_code("main", "forall(x0: BoolBox) { true }");
    }

    #[test]
    fn test_importing_a_generic_type() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import Pair
            "#,
        );
        p.check_code("main", "forall(x0: Pair[Bool, Bool]) { true }");
        p.check_code(
            "main",
            "forall(x0: Bool, x1: Bool) { Pair.new(x0, x1).second = x1 }",
        );
    }

    #[test]
    fn test_generic_type_in_imported_module() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import Pair
            "#,
        );
        p.check_code("main", "forall(x0: Pair[Bool, Bool]) { true }");
    }

    #[test]
    fn test_aliasing_local_generic_constant() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            let pbbn: (Bool, Bool) -> Pair[Bool, Bool] = Pair[Bool, Bool].new
            "#,
        );
        p.expect_ok("pair");
        p.check_code("pair", "pbbn(false, true)");
    }

    #[test]
    fn test_importing_generic_function() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            define double[T](x: T) -> Pair[T, T] {
                Pair.new(x, x)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import double
            "#,
        );
        p.check_code("main", "double(true)");
    }

    #[test]
    fn test_generic_function_in_imported_module() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/pair.ac",
            r#"
            structure Pair[T, U] {
                first: T
                second: U
            }

            define double[T](x: T) -> Pair[T, T] {
                Pair.new(x, x)
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from pair import double
            "#,
        );
        p.check_code("main", "double(true)");
    }

    #[test]
    fn test_importing_typeclasses_with_import() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/magma.ac",
            r#"
            typeclass M: Magma {
                op: (M, M) -> M
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from magma import Magma

            inductive Z1 {
                zero
            }

            instance Z1: Magma {
                define op(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
        );
        p.check_code("main", "Z1.zero.op(Z1.zero) = Z1.zero");
    }

    #[test]
    fn test_importing_typeclasses_with_from() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/magma.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from magma import Magma

            inductive Z1 {
                zero
            }

            instance Z1: Magma {
                define mul(self, other: Z1) -> Z1 {
                    Z1.zero
                }
            }
            "#,
        );
        p.check_code("main", "Z1.zero * Z1.zero = Z1.zero");
    }

    #[test]
    fn test_codegen_typeclass_infix() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            theorem goal[M: Magma](x: M) {
                x * x = x
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x * x = x");
    }

    #[test]
    fn test_codegen_extended_infix() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass M: Magma {
                mul: (M, M) -> M
            }

            typeclass T: Thing extends Magma {
                thing_property: Bool
            }

            theorem goal[T: Thing](x: T) {
                x * x = x
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x * x = x");
    }

    #[test]
    fn test_codegen_for_imported_typeclasses() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo.ac",
            r#"
            typeclass F: Foo {
                zero: F
                add: (F, F) -> F
                neg: F -> F
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Foo

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            theorem goal[B: Bar](x: B) {
                x + -x = B.zero + B.zero
            }
            "#,
        );
        p.check_goal_code("main", "goal", "x + -x = B.zero + B.zero");
    }

    #[test]
    fn test_codegen_for_quantified_types() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                item: F
            }

            inductive List[T] {
                nil
                cons(T, List[T])
            }

            structure Bar {
                item: Bool
            }

            theorem goal1 {
                exists(a: Bar) {
                    true
                }
            }

            theorem goal2 {
                exists(a: List[Bool]) {
                    true
                }
            }

            theorem goal3[F: Foo] {
                exists(a: List[F]) {
                    true
                }
            }

            theorem goal4 {
                exists(a: Bool) {
                    a
                }
            }
            "#,
        );
        p.check_goal_code("main", "goal1", "exists(k0: Bar) { true }");
        p.check_goal_code("main", "goal2", "exists(k0: List[Bool]) { true }");
        p.check_goal_code("main", "goal3", "exists(k0: List[F]) { true }");
        p.check_goal_code("main", "goal4", "exists(k0: Bool) { k0 }");
    }

    #[test]
    fn test_codegen_indirect_attribute() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/foo_base.ac",
            r#"
            inductive Foo {
                foo
            }

            attributes Foo {
                define add(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
        "#,
        );
        p.mock(
            "/mock/foo_middle.ac",
            r#"
            from foo_base import Foo
            attributes Foo {
                define mul(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
        );
        p.mock(
            "/mock/foo.ac",
            r#"
            from foo_middle import Foo
            attributes Foo {
                define sub(self, other: Foo) -> Foo {
                    Foo.foo
                }
            }
            "#,
        );
        p.mock(
            "/mock/main.ac",
            r#"
            from foo import Foo
            "#,
        );
        p.check_code("main", "Foo.add");
        p.check_code("main", "Foo.foo.add");
        p.check_code("main", "Foo.foo + Foo.foo");
        p.check_code("main", "Foo.mul");
        p.check_code("main", "Foo.foo.mul");
        p.check_code("main", "Foo.foo * Foo.foo");
        p.check_code("main", "Foo.sub");
        p.check_code("main", "Foo.foo.sub");
        p.check_code("main", "Foo.foo - Foo.foo");
    }

    #[test]
    fn test_codegen_instance_attribute_access() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                vacuous {
                    true
                }
            }

            attributes F: Foo {
                let flag: Bool = true
                define foo(self) -> Bool {
                    true
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            theorem const_attr(b: Bar) {
                Bar.flag
            }

            theorem fn_attr(b: Bar) {
                b.foo
            }
            "#,
        );
        p.check_goal_code("main", "const_attr", "Bar.flag");
        p.check_goal_code("main", "fn_attr", "b.foo");
    }

    #[test]
    fn test_codegen_overridden_attribute() {
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass F: Foo {
                vacuous {
                    true
                }
            }

            attributes F: Foo {
                let flag: Bool = true
                define foo(self) -> Bool {
                    true
                }
            }

            inductive Bar {
                bar
            }

            instance Bar: Foo

            // These override, changing the desired codegen.
            attributes Bar {
                let flag: Bool = false
                define foo(self) -> Bool {
                    false
                }
            }

            theorem const_attr(b: Bar) {
                Foo.flag[Bar]
            }

            theorem fn_attr(b: Bar) {
                Foo.foo[Bar](b)
            }
            "#,
        );
        p.check_goal_code("main", "const_attr", "Foo.flag[Bar]");
        p.check_goal_code("main", "fn_attr", "Foo.foo[Bar](b)");
    }

    #[test]
    fn test_codegen_typeclass_digit_with_numerals() {
        // When a typeclass provides a digit (like 0 from Zero typeclass),
        // and a type Foo implements that typeclass,
        // and numerals Foo is set,
        // then Zero.0[Foo] should codegen to just "0", not "Foo.0"
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass Z: Zero {
                0: Z
            }

            inductive Foo {
                foo
            }

            instance Foo: Zero {
                let 0: Foo = Foo.foo
            }

            numerals Foo

            theorem goal {
                Zero.0[Foo] = Foo.foo
            }
            "#,
        );
        // Zero.0[Foo] should codegen to "0" when numerals Foo is set
        p.check_goal_code("main", "goal", "0 = Foo.foo");
    }

    #[test]
    fn test_codegen_typeclass_digit_with_own_attribute() {
        // When a datatype has its OWN digit attribute (not just via typeclass instance),
        // and it's also an instance of a Zero typeclass,
        // Zero.0[Type] should codegen to Type.0 (using the datatype's own attribute)
        let mut p = Project::new_mock();
        p.mock(
            "/mock/main.ac",
            r#"
            typeclass Z: Zero {
                0: Z
            }

            inductive Bar {
                bar
            }

            // Bar has its OWN 0 attribute
            attributes Bar {
                let 0: Bar = Bar.bar
            }

            // Bar is also an instance of Zero, referencing its own 0
            instance Bar: Zero {
                let 0: Bar = Bar.0
            }

            theorem goal {
                Zero.0[Bar] = Bar.bar
            }
            "#,
        );
        // Zero.0[Bar] should codegen to "Bar.0" since Bar has its own 0 attribute
        p.check_goal_code("main", "goal", "Bar.0 = Bar.bar");
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_bigcert_emits_explicit_function_application() {
        use crate::module::LoadState;
        use crate::processor::Processor;
        use crate::prover::{Outcome, ProverMode};

        let mut project = Project::new_mock();
        project.mock(
            "/mock/main.ac",
            r#"
            inductive Foo {
                foo
                bar
            }

            let f: Foo -> Bool = axiom
            let g: Foo -> Bool = axiom
            let h: Foo -> Bool = axiom

            axiom rule(x: Foo) {
                f(x) and g(x) implies h(x)
            }

            theorem goal(y: Foo) {
                f(y) and g(y) implies h(y)
            }
            "#,
        );

        let module_id = project.load_module_by_name("main").expect("load failed");
        let env = match project.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("error: {}", e),
            _ => panic!("no module"),
        };

        let cursor = env.get_node_by_goal_name("goal");
        let goal_env = cursor.goal_env().unwrap();
        let normalized_goal = cursor.normalized_goal().expect("missing normalized goal");

        let mut processor = Processor::with_imports(None, env).unwrap();
        processor.add_module_facts(&cursor).unwrap();
        processor.set_normalized_goal(normalized_goal);

        let outcome = processor.search(ProverMode::Test, &normalized_goal.normalizer);
        assert_eq!(outcome, Outcome::Success);

        let cert = processor
            .prover()
            .make_cert(&goal_env.bindings, &normalized_goal.normalizer, false)
            .expect("make_cert failed");
        let proof = cert.proof.clone().expect("expected proof");

        assert!(!proof.is_empty(), "expected non-empty certificate proof");

        processor
            .check_cert(
                &cert,
                Some(normalized_goal),
                &normalized_goal.normalizer,
                &project,
                &goal_env.bindings,
            )
            .expect("generated certificate should verify");
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_bigcert_explicit_specialization_handles_sparse_variable_ids() {
        use super::CodeGenerator;
        use crate::elaborator::binding_map::BindingMap;
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;
        use crate::module::ModuleId;
        use crate::normalizer::Normalizer;
        use crate::prover::proof::ConcreteStep;

        // Build a generic clause with a hole in variable IDs: only x2 appears in terms.
        let mut normalizer = Normalizer::new();
        let (generic, var_map) = {
            let kctx = normalizer.kernel_context_mut();
            let local = kctx.parse_local(&["Bool", "Bool", "Bool"]);
            let generic = Clause::from_literals_unnormalized(
                vec![Literal::positive(Term::new_variable(2))],
                &local,
            );

            let mut var_map = VariableMap::new();
            var_map.set(0, Term::new_true());
            var_map.set(1, Term::new_false());
            var_map.set(2, Term::new_true());
            (generic, var_map)
        };

        let step = ConcreteStep {
            generic,
            var_maps: vec![(var_map, LocalContext::empty())],
        };

        let bindings = BindingMap::new(ModuleId::PRELUDE);
        let mut generator = CodeGenerator::new(&bindings);
        let (_defs, codes) = generator
            .concrete_step_to_code(&step, &normalizer)
            .expect("sparse variable-id specialization should codegen");

        assert!(!codes.is_empty(), "expected code output, got: {:?}", codes);
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_bigcert_explicit_specialization_skips_empty_placeholder_var() {
        use super::CodeGenerator;
        use crate::elaborator::binding_map::BindingMap;
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;
        use crate::module::ModuleId;
        use crate::normalizer::Normalizer;
        use crate::prover::proof::ConcreteStep;

        // x0 is an Empty placeholder; x1..x3 are real value vars whose type references x0.
        // Bigcert explicit specialization should skip x0 instead of trying to emit an Empty arg type.
        let normalizer = Normalizer::new();
        let local = LocalContext::from_types(vec![
            Term::empty_type(),
            Term::new_variable(0),
            Term::new_variable(0),
            Term::new_variable(0),
        ]);
        let generic = Clause::from_literals_unnormalized(
            vec![Literal::equals(
                Term::new_variable(3),
                Term::new_variable(2),
            )],
            &local,
        );

        let mut var_map = VariableMap::new();
        var_map.set(1, Term::new_true());
        var_map.set(2, Term::new_false());
        var_map.set(3, Term::new_true());

        let step = ConcreteStep {
            generic,
            var_maps: vec![(var_map, LocalContext::empty())],
        };

        let bindings = BindingMap::new(ModuleId::PRELUDE);
        let mut generator = CodeGenerator::new(&bindings);
        let (_defs, codes) = generator
            .concrete_step_to_code(&step, &normalizer)
            .expect("empty placeholder vars should be skipped in bigcert specialization");

        assert!(!codes.is_empty(), "expected code output, got: {:?}", codes);
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_bigcert_explicit_specialization_substitutes_type_vars_in_value_types() {
        use super::CodeGenerator;
        use crate::elaborator::binding_map::BindingMap;
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;
        use crate::module::ModuleId;
        use crate::normalizer::Normalizer;
        use crate::prover::proof::ConcreteStep;

        // x0 is an Empty placeholder, and x1..x3 have type x0.
        // If x0 is mapped to Bool, bigcert specialization should apply that type
        // substitution and emit concrete Bool arg types, not an unbound type
        // variable like T0.
        let normalizer = Normalizer::new();
        let local = LocalContext::from_types(vec![
            Term::empty_type(),
            Term::new_variable(0),
            Term::new_variable(0),
            Term::new_variable(0),
        ]);
        let generic = Clause::from_literals_unnormalized(
            vec![Literal::equals(
                Term::new_variable(3),
                Term::new_variable(2),
            )],
            &local,
        );

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::bool_type());
        var_map.set(1, Term::new_true());
        var_map.set(2, Term::new_false());
        var_map.set(3, Term::new_true());

        let step = ConcreteStep {
            generic,
            var_maps: vec![(var_map, LocalContext::empty())],
        };

        let bindings = BindingMap::new(ModuleId::PRELUDE);
        let mut generator = CodeGenerator::new(&bindings);
        let (_defs, codes) = generator
            .concrete_step_to_code(&step, &normalizer)
            .expect("type vars appearing only in value types should still be substituted");

        assert!(!codes.is_empty(), "expected code output, got: {:?}", codes);
    }

    #[cfg(feature = "bigcert")]
    #[test]
    fn test_bigcert_explicit_specialization_type_only_mapping() {
        use super::CodeGenerator;
        use crate::elaborator::binding_map::BindingMap;
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;
        use crate::module::ModuleId;
        use crate::normalizer::Normalizer;
        use crate::prover::proof::ConcreteStep;

        // No value vars in the theorem, but var_map still has a type-only entry.
        // Bigcert specialization should still emit an explicit claim shape.
        let normalizer = Normalizer::new();
        let local = LocalContext::from_types(vec![Term::type_sort()]);
        let generic = Clause::from_literals_unnormalized(vec![Literal::true_value()], &local);

        let mut var_map = VariableMap::new();
        var_map.set(0, Term::bool_type());

        let step = ConcreteStep {
            generic,
            var_maps: vec![(var_map, LocalContext::empty())],
        };

        let bindings = BindingMap::new(ModuleId::PRELUDE);
        let mut generator = CodeGenerator::new(&bindings);
        let (_defs, codes) = generator
            .concrete_step_to_code(&step, &normalizer)
            .expect("type-only specialization should codegen");

        assert!(
            !codes.is_empty(),
            "expected code output for type-only specialization"
        );
        assert!(!codes.is_empty(), "expected code output, got: {:?}", codes);
    }
}
