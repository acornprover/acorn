use std::fmt;

use tower_lsp::lsp_types::{LanguageString, MarkedString};

use crate::elaborator::acorn_type::{AcornType, Datatype, PotentialType, Typeclass};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp, ConstantInstance};
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::names::ConstantName;
use crate::elaborator::type_unifier::TypeclassRegistry;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::certificate_step::{CertificateStep, Claim};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::{Decomposition, Term, TermRef};
use crate::kernel::variable_map::{apply_to_term, VariableMap};
use crate::module::ModuleId;
use crate::prover::proof::ConcreteStep;
use crate::syntax::expression::{Declaration, Expression, TypeParamExpr};
use crate::syntax::token::TokenType;

pub type Result<T> = std::result::Result<T, Error>;

pub struct CodeGenerator<'a> {
    /// Bindings for the module we are generating code in.
    bindings: &'a BindingMap,

    /// Whether to allow explicit typeclass-attribute calls even when receiver syntax would
    /// be out of scope at the current source location. Certificate serialization needs this
    /// so proofs can cite generic definitions with concrete type arguments.
    allow_out_of_scope_typeclass_calls: bool,

    /// When true, always emit `Type.0` instead of shortcutting to `0` for numeric literals.
    explicit_numerals: bool,

    /// We use variables named x0, x1, x2, etc for universal variables.
    next_x: u32,

    /// We use variables named k0, k1, k2, etc for existential variables.
    next_k: u32,

    /// The names we have assigned to stack variables so far.
    var_names: Vec<String>,
}

impl CodeGenerator<'_> {
    fn clause_has_only_type_param_locals(clause: &Clause) -> bool {
        clause
            .get_local_context()
            .get_var_types()
            .iter()
            .all(|var_type| {
                var_type
                    .as_ref()
                    .is_some_and(|term| term.as_ref().is_type_param_kind())
            })
    }

    /// Render a binary expression while preserving the operand grouping required by precedence.
    fn value_to_binary_expr(
        &mut self,
        op: BinaryOp,
        left: &AcornValue,
        right: &AcornValue,
    ) -> Result<Expression> {
        let mut left_expr = self.value_to_expr(left, false)?;
        let mut right_expr = self.value_to_expr(right, false)?;
        let token = op.token_type().generate();
        let paren = |expr: Expression| {
            Expression::Grouping(
                TokenType::LeftParen.generate(),
                Box::new(expr),
                TokenType::RightParen.generate(),
            )
        };

        if let AcornValue::Binary(left_op, _, _) = left {
            if left_op.token_type().binary_precedence() < op.token_type().binary_precedence() {
                left_expr = paren(left_expr);
            }
        }
        if let AcornValue::IfThenElse(_, _, _) = left {
            left_expr = paren(left_expr);
        }

        if let AcornValue::Binary(right_op, _, _) = right {
            if right_op.token_type().binary_precedence() <= op.token_type().binary_precedence() {
                right_expr = paren(right_expr);
            }
        }
        if let AcornValue::IfThenElse(_, _, _) = right {
            right_expr = paren(right_expr);
        }

        Ok(Expression::Binary(
            Box::new(left_expr),
            token,
            Box::new(right_expr),
        ))
    }

    fn ensure_explicit_inhabitant_for_type(
        kernel_context: &KernelContext,
        concrete_type: &Term,
        local_context: &LocalContext,
    ) -> Result<()> {
        if kernel_context
            .find_inhabitant(concrete_type, Some(local_context))
            .is_some()
        {
            return Ok(());
        }
        if Self::find_local_witness_for_concrete_type(kernel_context, concrete_type, local_context)?
            .is_some()
        {
            return Ok(());
        }
        Err(Error::GeneratedBadCode(format!(
            "cannot generate certificate: no explicit inhabitant found for type '{}'",
            concrete_type
        )))
    }

    fn concrete_type_for_term(
        kernel_context: &KernelContext,
        var_type: &Term,
        local_context: &LocalContext,
    ) -> Result<Term> {
        let acorn_type =
            kernel_context.quote_type_with_context(var_type.clone(), local_context, true);
        kernel_context
            .type_store
            .get_type_term(&acorn_type)
            .map_err(Error::internal)
    }

    fn find_local_witness_for_concrete_type(
        kernel_context: &KernelContext,
        concrete_type: &Term,
        local_context: &LocalContext,
    ) -> Result<Option<Term>> {
        for (var_id, candidate_type) in local_context.get_var_types().iter().enumerate() {
            let Some(candidate_type) = candidate_type else {
                continue;
            };
            if candidate_type.as_ref().is_type_param_kind() {
                continue;
            }
            let candidate_concrete =
                Self::concrete_type_for_term(kernel_context, candidate_type, local_context)?;
            if candidate_concrete == *concrete_type {
                return Ok(Some(Term::new_variable(var_id as AtomId)));
            }
        }
        Ok(None)
    }

    fn ensure_explicit_inhabitant_for_variable_type(
        kernel_context: &KernelContext,
        var_type: &Term,
        local_context: &LocalContext,
    ) -> Result<()> {
        if var_type.as_ref().is_type_param_kind() {
            return Ok(());
        }
        let concrete_type = Self::concrete_type_for_term(kernel_context, var_type, local_context)?;
        Self::ensure_explicit_inhabitant_for_type(kernel_context, &concrete_type, local_context)
    }

    fn inhabitant_for_variable_type(
        &self,
        kernel_context: &KernelContext,
        var_type: &Term,
        local_context: &LocalContext,
    ) -> Result<Option<Term>> {
        if var_type.as_ref().is_type_param_kind() {
            return Ok(None);
        }
        let concrete_type = Self::concrete_type_for_term(kernel_context, var_type, local_context)?;
        Ok(kernel_context.find_inhabitant(&concrete_type, Some(local_context)))
    }

    fn ensure_explicit_inhabitants_for_term(
        kernel_context: &KernelContext,
        term: &Term,
        local_context: &LocalContext,
    ) -> Result<()> {
        match term.as_ref().decompose() {
            Decomposition::Atom(Atom::FreeVariable(var_id)) => {
                // For a variable term, get its type from the local context.
                let var_type = local_context
                    .get_var_type(*var_id as usize)
                    .cloned()
                    .expect("Variable should have type in LocalContext");
                Self::ensure_explicit_inhabitant_for_variable_type(
                    kernel_context,
                    &var_type,
                    local_context,
                )?;
            }
            Decomposition::Atom(_) => {}
            Decomposition::Application(func, arg) => {
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &func.to_owned(),
                    local_context,
                )?;
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &arg.to_owned(),
                    local_context,
                )?;
            }
            Decomposition::Pi(input, output) => {
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &input.to_owned(),
                    local_context,
                )?;
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &output.to_owned(),
                    local_context,
                )?;
            }
            Decomposition::Lambda(input, body) => {
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &input.to_owned(),
                    local_context,
                )?;
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &body.to_owned(),
                    local_context,
                )?;
            }
            Decomposition::ForAll(binder_type, body) | Decomposition::Exists(binder_type, body) => {
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &binder_type.to_owned(),
                    local_context,
                )?;
                Self::ensure_explicit_inhabitants_for_term(
                    kernel_context,
                    &body.to_owned(),
                    local_context,
                )?;
            }
        }
        Ok(())
    }

    /// Ensure every value variable appearing in this clause has an explicit inhabitant.
    fn ensure_explicit_inhabitants_for_clause(
        &self,
        kernel_context: &KernelContext,
        clause: &Clause,
    ) -> Result<()> {
        let local_context = clause.get_local_context();
        for literal in &clause.literals {
            for term in [&literal.left, &literal.right] {
                Self::ensure_explicit_inhabitants_for_term(kernel_context, term, local_context)?;
            }
        }
        Ok(())
    }

    fn build_inhabitant_var_map(
        &self,
        kernel_context: &KernelContext,
        clause: &Clause,
    ) -> Result<VariableMap> {
        let mut var_map = VariableMap::new();
        let local_context = clause.get_local_context();
        for i in 0..local_context.len() {
            let var_type = local_context
                .get_var_type(i)
                .expect("LocalContext should have all variable types");
            if let Some(term) =
                self.inhabitant_for_variable_type(kernel_context, var_type, local_context)?
            {
                var_map.set(i as AtomId, term);
            }
        }
        Ok(var_map)
    }
}

impl CodeGenerator<'_> {
    /// Creates a new code generator.
    pub fn new(bindings: &BindingMap) -> CodeGenerator<'_> {
        CodeGenerator {
            bindings,
            allow_out_of_scope_typeclass_calls: false,
            explicit_numerals: false,
            next_x: 0,
            next_k: 0,
            var_names: vec![],
        }
    }

    /// Creates a code generator for certificate serialization.
    ///
    /// Certificates may need to mention explicit `Typeclass.attr[Type](...)` applications even
    /// when receiver syntax would be out of scope at the selected goal location.
    pub fn new_for_certificate(bindings: &BindingMap) -> CodeGenerator<'_> {
        CodeGenerator {
            allow_out_of_scope_typeclass_calls: true,
            ..Self::new(bindings)
        }
    }

    /// Returns a code generator that always emits explicit `Type.0` instead of bare `0`.
    pub fn with_explicit_numerals(mut self) -> Self {
        self.explicit_numerals = true;
        self
    }

    /// Peel ForAll layers from a value, returning (params, body_code).
    /// `param_names` provides original parameter names from the source.
    /// Falls back to generated names (x0, x1, ...) if not enough names are given.
    pub fn value_to_theorem_parts(
        &mut self,
        value: &AcornValue,
        param_names: &[String],
    ) -> Result<(Vec<(String, String)>, String)> {
        let mut params = vec![];
        let mut current = value;
        let mut name_idx = 0;

        while let AcornValue::ForAll(quants, body) = current {
            for arg_type in quants {
                let var_name = if name_idx < param_names.len() {
                    param_names[name_idx].clone()
                } else {
                    self.bindings.next_indexed_var('x', &mut self.next_x)
                };
                name_idx += 1;
                self.var_names.push(var_name.clone());
                let type_str = self.type_to_code(arg_type)?;
                params.push((var_name, type_str));
            }
            current = body;
        }

        let body_expr = self.value_to_expr(current, false)?;
        Ok((params, body_expr.to_string()))
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
            AcornType::Bool => Err(Error::internal("Bool unbound")),
            AcornType::Type0 => Ok(Expression::generate_identifier("Type0")),
            AcornType::TypeclassConstraint(tc) => {
                if let Some(alias) = self.bindings.typeclass_alias(tc) {
                    Ok(Expression::generate_identifier(alias))
                } else if self.bindings.has_typeclass_name(&tc.name) {
                    Ok(Expression::generate_identifier(&tc.name))
                } else {
                    let module = self.module_to_expr(tc.module_id)?;
                    Ok(module.add_dot_str(&tc.name))
                }
            }
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

    fn value_to_code_with_initial_vars_internal(
        &mut self,
        value: &AcornValue,
        initial_var_names: &[String],
    ) -> Result<String> {
        let initial_len = self.var_names.len();
        self.var_names.extend(initial_var_names.iter().cloned());
        let expr = self.value_to_expr(value, false)?;
        self.var_names.truncate(initial_len);
        Ok(expr.to_string())
    }

    /// Like value_to_code, but treats `initial_var_names` as already in-scope stack variables.
    pub fn value_to_code_with_initial_vars(
        &mut self,
        value: &AcornValue,
        initial_var_names: &[String],
    ) -> Result<String> {
        self.value_to_code_with_initial_vars_internal(value, initial_var_names)
    }

    pub fn type_to_code_for_display(&self, acorn_type: &AcornType) -> Result<String> {
        self.type_to_code(acorn_type)
    }

    fn infer_type_param_bindings_from_type_pattern(
        pattern: TermRef<'_>,
        concrete: TermRef<'_>,
        local_context: &LocalContext,
        var_map: &mut VariableMap,
    ) -> bool {
        match (pattern.decompose(), concrete.decompose()) {
            (Decomposition::Atom(Atom::FreeVariable(var_id)), _) => {
                let is_type_param = local_context
                    .get_var_type(*var_id as usize)
                    .map(|t| t.as_ref().is_type_param_kind())
                    .unwrap_or(false);
                if is_type_param {
                    return var_map.match_var(*var_id, concrete);
                }
                pattern == concrete
            }
            (Decomposition::Atom(pattern_atom), Decomposition::Atom(concrete_atom)) => {
                pattern_atom == concrete_atom
            }
            (
                Decomposition::Application(pattern_func, pattern_arg),
                Decomposition::Application(concrete_func, concrete_arg),
            ) => {
                Self::infer_type_param_bindings_from_type_pattern(
                    pattern_func,
                    concrete_func,
                    local_context,
                    var_map,
                ) && Self::infer_type_param_bindings_from_type_pattern(
                    pattern_arg,
                    concrete_arg,
                    local_context,
                    var_map,
                )
            }
            (
                Decomposition::Pi(pattern_input, pattern_output),
                Decomposition::Pi(concrete_input, concrete_output),
            ) => {
                Self::infer_type_param_bindings_from_type_pattern(
                    pattern_input,
                    concrete_input,
                    local_context,
                    var_map,
                ) && Self::infer_type_param_bindings_from_type_pattern(
                    pattern_output,
                    concrete_output,
                    local_context,
                    var_map,
                )
            }
            (
                Decomposition::Lambda(pattern_input, pattern_body),
                Decomposition::Lambda(concrete_input, concrete_body),
            ) => {
                Self::infer_type_param_bindings_from_type_pattern(
                    pattern_input,
                    concrete_input,
                    local_context,
                    var_map,
                ) && Self::infer_type_param_bindings_from_type_pattern(
                    pattern_body,
                    concrete_body,
                    local_context,
                    var_map,
                )
            }
            _ => false,
        }
    }

    /// Open a binder body by substituting bound variable 0 and reducing binder depth by one.
    fn open_binder_body(body: &Term, replacement: &Term) -> Term {
        body.substitute_bound(0, replacement).shift_bound(0, -1)
    }

    /// Abstract one free variable into a new outer bound variable.
    fn abstract_free_var_as_bound_at_depth(term: &Term, var_id: AtomId, depth: u16) -> Term {
        match term.as_ref().decompose() {
            Decomposition::Atom(atom) => match atom {
                Atom::FreeVariable(i) if *i == var_id => Term::atom(Atom::BoundVariable(depth)),
                Atom::BoundVariable(i) if *i >= depth => Term::atom(Atom::BoundVariable(*i + 1)),
                _ => term.clone(),
            },
            Decomposition::Application(func, arg) => {
                let new_func =
                    Self::abstract_free_var_as_bound_at_depth(&func.to_owned(), var_id, depth);
                let new_arg =
                    Self::abstract_free_var_as_bound_at_depth(&arg.to_owned(), var_id, depth);
                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input, output) => {
                let new_input =
                    Self::abstract_free_var_as_bound_at_depth(&input.to_owned(), var_id, depth);
                let new_output = Self::abstract_free_var_as_bound_at_depth(
                    &output.to_owned(),
                    var_id,
                    depth + 1,
                );
                Term::pi(new_input, new_output)
            }
            Decomposition::Lambda(input, body) => {
                let new_input =
                    Self::abstract_free_var_as_bound_at_depth(&input.to_owned(), var_id, depth);
                let new_body =
                    Self::abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::lambda(new_input, new_body)
            }
            Decomposition::ForAll(binder_type, body) => {
                let new_binder_type = Self::abstract_free_var_as_bound_at_depth(
                    &binder_type.to_owned(),
                    var_id,
                    depth,
                );
                let new_body =
                    Self::abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::forall(new_binder_type, new_body)
            }
            Decomposition::Exists(binder_type, body) => {
                let new_binder_type = Self::abstract_free_var_as_bound_at_depth(
                    &binder_type.to_owned(),
                    var_id,
                    depth,
                );
                let new_body =
                    Self::abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::exists(new_binder_type, new_body)
            }
        }
    }

    /// Like `Term::get_type_with_context`, but supports lambda terms.
    fn term_type_for_certificate(
        term: &Term,
        context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Term {
        if let Some((input, body)) = term.as_ref().split_lambda() {
            let input_type = input.to_owned();
            let fresh_var = context.len() as AtomId;
            let mut nested_context = context.clone();
            nested_context.push_type(input_type.clone());
            let opened_body =
                Self::open_binder_body(&body.to_owned(), &Term::new_variable(fresh_var));
            let body_type =
                Self::term_type_for_certificate(&opened_body, &nested_context, kernel_context);
            let output_type = Self::abstract_free_var_as_bound_at_depth(&body_type, fresh_var, 0);
            Term::pi(input_type, output_type)
        } else {
            term.get_type_with_context(context, kernel_context)
        }
    }

    fn ensure_no_foreign_scoped_constants_in_term(
        term: &Term,
        kernel_context: &KernelContext,
        current_module: ModuleId,
    ) -> Result<()> {
        for atom in term.iter_atoms() {
            let Atom::Symbol(Symbol::ScopedConstant(local_id)) = atom else {
                continue;
            };
            let name = kernel_context.symbol_table.name_for_local_id(*local_id);
            if name.module_id() != current_module {
                return Err(Error::internal(format!(
                    "foreign scoped constant '{}' (local id {}) from module {:?} leaked into certificate generation for module {:?}",
                    name,
                    local_id,
                    name.module_id(),
                    current_module
                )));
            }
        }
        Ok(())
    }

    fn ensure_no_foreign_scoped_constants_in_clause(
        clause: &Clause,
        kernel_context: &KernelContext,
        current_module: ModuleId,
    ) -> Result<()> {
        for literal in &clause.literals {
            Self::ensure_no_foreign_scoped_constants_in_term(
                &literal.left,
                kernel_context,
                current_module,
            )?;
            Self::ensure_no_foreign_scoped_constants_in_term(
                &literal.right,
                kernel_context,
                current_module,
            )?;
        }
        Ok(())
    }

    /// Convert one specialization to certificate steps.
    /// The replacement_context is the context that the var_map's replacement terms reference.
    /// This is needed to look up variable types when specializing.
    fn specialization_to_certificate_steps(
        &mut self,
        generic: &Clause,
        var_map: &VariableMap,
        replacement_context: &LocalContext,
        kernel_context: &mut KernelContext,
        steps: &mut Vec<CertificateStep>,
    ) -> Result<()> {
        let mut clause = var_map.specialize_clause_with_replacement_context_and_compact_vars(
            &generic,
            replacement_context,
            kernel_context,
        );

        self.ensure_explicit_inhabitants_for_clause(kernel_context, &clause)?;
        let clause_context = clause.get_local_context().clone();
        let inhabitant_var_map = self.build_inhabitant_var_map(kernel_context, &clause)?;
        clause = inhabitant_var_map.specialize_clause_with_replacement_context_and_compact_vars(
            &clause,
            &clause_context,
            kernel_context,
        );

        Self::ensure_no_foreign_scoped_constants_in_clause(
            &clause,
            kernel_context,
            self.bindings.module_id(),
        )?;

        // Convert replacement-context free variables into explicit inhabitants by type.
        // This yields a claim map that does not depend on concrete variable IDs.
        let mut replacement_inhabitant_map = VariableMap::new();
        for var_id in 0..replacement_context.len() {
            let Some(var_type) = replacement_context.get_var_type(var_id) else {
                continue;
            };
            if let Some(term) =
                self.inhabitant_for_variable_type(kernel_context, var_type, replacement_context)?
            {
                replacement_inhabitant_map.set(var_id as AtomId, term);
            }
        }

        // Infer replacement-context type variables from value-variable inhabitants.
        // Example: if x1: x0 and x1 is mapped to a Bool inhabitant, infer x0 = Bool.
        let mut replacement_type_map = VariableMap::new();
        for var_id in 0..replacement_context.len() {
            let Some(mapped_term) = replacement_inhabitant_map.get_mapping(var_id as AtomId) else {
                continue;
            };
            let Some(expected_type) = replacement_context.get_var_type(var_id) else {
                continue;
            };
            let mapped_type =
                Self::term_type_for_certificate(mapped_term, replacement_context, kernel_context);
            Self::infer_type_param_bindings_from_type_pattern(
                expected_type.as_ref(),
                mapped_type.as_ref(),
                replacement_context,
                &mut replacement_type_map,
            );
        }

        let generic_context = generic.get_local_context();
        let generic_len = generic_context.len();
        let mut claim_var_map = VariableMap::new();
        for (var_id, term) in var_map.iter() {
            if var_id >= generic_len {
                continue;
            }
            let Some(var_type) = generic_context.get_var_type(var_id) else {
                continue;
            };
            let specialized = apply_to_term(term.as_ref(), &replacement_inhabitant_map);
            let specialized = apply_to_term(specialized.as_ref(), &replacement_type_map);
            Self::ensure_no_foreign_scoped_constants_in_term(
                &specialized,
                kernel_context,
                self.bindings.module_id(),
            )?;
            if var_type.as_ref().is_type_param_kind() {
                let specialized_type =
                    Self::term_type_for_certificate(&specialized, generic_context, kernel_context);
                if !specialized_type.as_ref().is_type_param_kind()
                    || matches!(
                        specialized.as_ref().decompose(),
                        Decomposition::Atom(Atom::FreeVariable(_))
                    )
                {
                    // Placeholder type-parameter bindings are not concrete enough to serialize.
                    // We infer concrete bindings from mapped value types below.
                    continue;
                }
            }
            claim_var_map.set(var_id as AtomId, specialized);
        }
        for var_id in 0..generic_len {
            let Some(mapped_term) = claim_var_map.get_mapping(var_id as AtomId).cloned() else {
                continue;
            };
            if mapped_term
                .max_variable()
                .map(|id| id as usize >= generic_len)
                .unwrap_or(false)
            {
                continue;
            }
            let Some(generic_type) = generic_context.get_var_type(var_id) else {
                continue;
            };
            let mapped_type =
                Self::term_type_for_certificate(&mapped_term, generic_context, kernel_context);
            Self::infer_type_param_bindings_from_type_pattern(
                generic_type.as_ref(),
                mapped_type.as_ref(),
                generic_context,
                &mut claim_var_map,
            );
        }
        for var_id in 0..generic_len {
            let var_id = var_id as AtomId;
            if claim_var_map.has_mapping(var_id) {
                continue;
            }
            let Some(var_type) = generic_context.get_var_type(var_id as usize) else {
                continue;
            };
            if var_type.as_ref().is_type_param_kind() {
                continue;
            }
            if let Some(term) =
                self.inhabitant_for_variable_type(kernel_context, var_type, generic_context)?
            {
                claim_var_map.set(var_id, term);
            }
        }

        let used_var_count = generic
            .literals
            .iter()
            .filter_map(|lit| {
                let left_max = lit.left.max_variable();
                let right_max = lit.right.max_variable();
                match (left_max, right_max) {
                    (Some(l), Some(r)) => Some(l.max(r)),
                    (Some(l), None) => Some(l),
                    (None, Some(r)) => Some(r),
                    (None, None) => None,
                }
            })
            .max()
            .map(|max| (max + 1) as usize)
            .unwrap_or(0);
        let missing_used_mappings: Vec<usize> = (0..used_var_count)
            .filter(|var_id| {
                let var_type = generic_context
                    .get_var_type(*var_id)
                    .expect("generic context should provide all variable types");
                !var_type.as_ref().is_type_param_kind()
                    && !claim_var_map.has_mapping(*var_id as AtomId)
            })
            .collect();
        if !missing_used_mappings.is_empty() {
            return Err(Error::GeneratedBadCode(format!(
                "certificate claim map is missing mappings for used value vars {:?}; generic clause '{}'; concrete clause '{}'",
                missing_used_mappings, generic, clause
            )));
        }

        let out_of_scope_mapping = claim_var_map.iter().find_map(|(var_id, term)| {
            term.max_variable()
                .filter(|id| *id as usize >= generic_len)
                .map(|max_id| (var_id, term.clone(), max_id))
        });
        if let Some((var_id, term, max_id)) = out_of_scope_mapping {
            return Err(Error::GeneratedBadCode(format!(
                "certificate claim map has out-of-scope term for x{}: '{}' references x{} (generic context size {}); generic clause '{}'; concrete clause '{}'",
                var_id, term, max_id, generic_len, generic, clause
            )));
        }

        let incompatible_mapping = claim_var_map.iter().find_map(|(var_id, term)| {
            let expected_type = generic_context.get_var_type(var_id).cloned()?;
            if expected_type.as_ref().is_type_param_kind() {
                return None;
            }

            let expected_concrete = apply_to_term(expected_type.as_ref(), &claim_var_map);
            let mapped_type =
                Self::term_type_for_certificate(term, generic_context, kernel_context);
            let mapped_concrete = apply_to_term(mapped_type.as_ref(), &claim_var_map);
            if expected_concrete != mapped_concrete {
                Some((
                    var_id,
                    term.clone(),
                    expected_type,
                    expected_concrete,
                    mapped_type,
                    mapped_concrete,
                ))
            } else {
                None
            }
        });
        if let Some((
            var_id,
            term,
            expected_type,
            expected_concrete,
            mapped_type,
            mapped_concrete,
        )) = incompatible_mapping
        {
            return Err(Error::GeneratedBadCode(format!(
                "certificate claim map type mismatch for x{}: expected type '{}' (specialized '{}'), \
                 mapped term '{}' has type '{}' (specialized '{}'); generic clause '{}'; concrete clause '{}'",
                var_id,
                expected_type,
                expected_concrete,
                term,
                mapped_type,
                mapped_concrete,
                generic,
                clause
            )));
        }
        let replayed = claim_var_map.specialize_clause_with_compact_vars(generic, kernel_context);
        // Compare against the concrete clause after only applying inferred replacement-type
        // substitutions; applying claim_var_map here can incorrectly capture overlapping IDs.
        let concretized_clause =
            replacement_type_map.specialize_clause_with_compact_vars(&clause, kernel_context);
        if replayed != concretized_clause {
            if Self::clause_has_only_type_param_locals(&concretized_clause) {
                let claim = Claim::new(concretized_clause, VariableMap::new())
                    .map_err(Error::GeneratedBadCode)?;
                steps.push(CertificateStep::Claim(claim));
                return Ok(());
            }
            return Err(Error::GeneratedBadCode(format!(
                "certificate claim map replay mismatch: generic clause '{}' with map '{}' replays to '{}', but concretized clause is '{}' (raw specialized clause '{}')",
                generic, claim_var_map, replayed, concretized_clause, clause
            )));
        }
        let claim = Claim::new(generic.clone(), claim_var_map).map_err(Error::GeneratedBadCode)?;

        steps.push(CertificateStep::Claim(claim));
        Ok(())
    }

    /// Converts a certificate step to one line of code.
    pub fn certificate_step_to_code(
        &mut self,
        step: &CertificateStep,
        kernel_context: &KernelContext,
    ) -> Result<String> {
        match step {
            CertificateStep::Claim(claim) => {
                let clause = claim
                    .normalized_specialized_clause(kernel_context)
                    .map_err(Error::GeneratedBadCode)?;
                let value = kernel_context.quote_clause(&clause, None, None, true);
                self.value_to_code(&value)
            }
            CertificateStep::Satisfy(step) => self.satisfy_step_to_code(step),
        }
    }

    /// Converts a ConcreteStep to certificate steps.
    pub fn concrete_step_to_certificate_steps(
        &mut self,
        step: &ConcreteStep,
        kernel_context: &mut KernelContext,
    ) -> Result<Vec<CertificateStep>> {
        let mut steps = vec![];
        for (var_map, replacement_context) in &step.var_maps {
            self.specialization_to_certificate_steps(
                &step.generic,
                var_map,
                replacement_context,
                kernel_context,
                &mut steps,
            )?;
        }
        Ok(steps)
    }

    fn type_to_code(&self, acorn_type: &AcornType) -> Result<String> {
        let expr = self.type_to_expr(acorn_type)?;
        Ok(expr.to_string())
    }

    /// Render the optional `[T, U: Trait]` prefix used by witness declarations.
    fn format_type_params(
        &self,
        type_params: &[crate::elaborator::acorn_type::TypeParam],
    ) -> Result<String> {
        if type_params.is_empty() {
            return Ok(String::new());
        }
        let mut rendered = Vec::with_capacity(type_params.len());
        for param in type_params {
            if let Some(typeclass) = &param.typeclass {
                rendered.push(format!(
                    "{}: {}",
                    param.name,
                    self.type_to_code(&AcornType::TypeclassConstraint(typeclass.clone()))?
                ));
            } else {
                rendered.push(param.name.clone());
            }
        }
        Ok(format!("[{}]", rendered.join(", ")))
    }

    /// Render a structured `let ... satisfy` certificate step back to source code.
    fn satisfy_step_to_code(
        &mut self,
        step: &crate::kernel::certificate_step::SatisfyStep,
    ) -> Result<String> {
        let type_params = self.format_type_params(&step.type_params)?;
        if let Some(return_name) = &step.return_name {
            let args: Result<Vec<String>> = step
                .arguments
                .iter()
                .map(|(name, arg_type)| Ok(format!("{}: {}", name, self.type_to_code(arg_type)?)))
                .collect();
            let mut initial_vars: Vec<String> = step
                .arguments
                .iter()
                .map(|(name, _)| name.clone())
                .collect();
            initial_vars.push(return_name.clone());
            let condition = self.value_to_code_with_initial_vars(&step.condition, &initial_vars)?;
            return Ok(format!(
                "let {}{}({}) -> {}: {} satisfy {{ {} }}",
                step.name,
                type_params,
                args?.join(", "),
                return_name,
                self.type_to_code(&step.return_type)?,
                condition,
            ));
        }

        Ok(format!(
            "let {}{}: {} satisfy {{ {} }}",
            step.name,
            type_params,
            self.type_to_code(&step.return_type)?,
            self.value_to_code(&step.condition)?,
        ))
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
                        if !arg_type.has_generic() && arg_type == *param_type {
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
    pub fn type_to_marked(&self, acorn_type: &AcornType) -> Result<MarkedString> {
        let code = self.type_to_code(acorn_type)?;
        Ok(Self::marked(format!("type {}", code)))
    }

    /// Given a constant instance, create an expression that refers to it.
    /// This does *not* include the parameters.
    fn const_to_expr(&self, ci: &ConstantInstance) -> Result<Expression> {
        // Handle numeric literals for datatype attributes (not typeclass attributes).
        // Typeclass attribute numerals are handled in value_to_expr where we have
        // more context about whether the datatype has its own override.
        if let Some((receiver_module_id, datatype_name, attr)) = ci.name.as_attribute() {
            if attr.chars().all(|ch| ch.is_ascii_digit()) && !ci.name.is_typeclass_attr() {
                let datatype = Datatype {
                    module_id: receiver_module_id,
                    name: datatype_name.to_string(),
                };

                let numeral = TokenType::Numeral.new_token(&attr);

                // If it's the default type, we don't need to scope it
                if !self.explicit_numerals && self.bindings.numerals() == Some(&datatype) {
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
                ConstantName::DatatypeAttribute(_, datatype, attr) => {
                    Expression::generate_identifier(&datatype.name).add_dot_str(attr)
                }
                ConstantName::SpecificDatatypeAttribute(_, datatype, _types, attr) => {
                    // Generate the same expression as for generic attributes
                    // The specific type information is not needed in the generated code
                    Expression::generate_identifier(&datatype.name).add_dot_str(attr)
                }
                ConstantName::TypeclassAttribute(_, tc, attr) => {
                    Expression::generate_identifier(&tc.name).add_dot_str(attr)
                }
                ConstantName::InstanceAttribute(_, inst) => {
                    Expression::generate_identifier(&inst.typeclass.name)
                        .add_dot_str(&inst.attribute)
                }
            });
        }

        // Check if there's a local alias for this constant.
        if let Some(alias) = self.bindings.constant_alias(&ci.name) {
            return Ok(Expression::generate_identifier(alias));
        }

        // If it's a member function, check if there's a local alias for its receiver.
        // Note that the receiver could be either a class or a typeclass.
        if let Some((receiver_module_id, rname, attr)) = ci.name.as_attribute() {
            // Check if this is a datatype attribute
            let datatype = Datatype {
                module_id: receiver_module_id,
                name: rname.to_string(),
            };
            if let Some(alias) = self.bindings.datatype_alias(&datatype) {
                let lhs = Expression::generate_identifier(alias);
                return Ok(lhs.add_dot_str(attr));
            }

            // Check if this is a typeclass attribute
            let typeclass = Typeclass {
                module_id: receiver_module_id,
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
            ConstantName::DatatypeAttribute(_, datatype, attr) => {
                Ok(module.add_dot_str(&datatype.name).add_dot_str(attr))
            }
            ConstantName::SpecificDatatypeAttribute(_, datatype, _types, attr) => {
                Ok(module.add_dot_str(&datatype.name).add_dot_str(attr))
            }
            ConstantName::TypeclassAttribute(_, tc, attr) => {
                Ok(module.add_dot_str(&tc.name).add_dot_str(attr))
            }
            ConstantName::InstanceAttribute(_, inst) => {
                self.module_to_expr(inst.typeclass.module_id).map(|module| {
                    module
                        .add_dot_str(&inst.typeclass.name)
                        .add_dot_str(&inst.attribute)
                })
            }
        }
    }

    /// If use_x is true we use x-variables; otherwise we use k-variables.
    fn operator_ref_expr(&self, value: &AcornValue) -> Option<Expression> {
        let first_arg = self.var_names.len() as AtomId;
        let second_arg = first_arg + 1;

        let matches_var = |value: &AcornValue, index: AtomId, expected_type: &AcornType| matches!(value, AcornValue::Variable(i, actual_type) if *i == index && actual_type == expected_type);

        match value {
            AcornValue::Lambda(args, body)
                if args == &[AcornType::Bool] && matches!(body.as_ref(), AcornValue::Not(_)) =>
            {
                let AcornValue::Not(inner) = body.as_ref() else {
                    unreachable!();
                };
                matches_var(inner, first_arg, &AcornType::Bool)
                    .then(|| Expression::generate_operator_ref(TokenType::Not))
            }
            AcornValue::Lambda(args, body)
                if args == &[AcornType::Bool, AcornType::Bool]
                    && matches!(body.as_ref(), AcornValue::Binary(BinaryOp::And, _, _)) =>
            {
                let AcornValue::Binary(BinaryOp::And, left, right) = body.as_ref() else {
                    unreachable!();
                };
                (matches_var(left, first_arg, &AcornType::Bool)
                    && matches_var(right, second_arg, &AcornType::Bool))
                .then(|| Expression::generate_operator_ref(TokenType::And))
            }
            AcornValue::Lambda(args, body)
                if args == &[AcornType::Bool, AcornType::Bool]
                    && matches!(body.as_ref(), AcornValue::Binary(BinaryOp::Or, _, _)) =>
            {
                let AcornValue::Binary(BinaryOp::Or, left, right) = body.as_ref() else {
                    unreachable!();
                };
                (matches_var(left, first_arg, &AcornType::Bool)
                    && matches_var(right, second_arg, &AcornType::Bool))
                .then(|| Expression::generate_operator_ref(TokenType::Or))
            }
            AcornValue::Lambda(args, body)
                if args.len() == 2
                    && args[0] == args[1]
                    && matches!(body.as_ref(), AcornValue::Binary(BinaryOp::Equals, _, _)) =>
            {
                let AcornValue::Binary(BinaryOp::Equals, left, right) = body.as_ref() else {
                    unreachable!();
                };
                (matches_var(left, first_arg, &args[0]) && matches_var(right, second_arg, &args[1]))
                    .then(|| Expression::generate_operator_ref(TokenType::Equals))
            }
            _ => None,
        }
    }

    fn generate_quantifier_expr(
        &mut self,
        token_type: TokenType,
        quants: &[AcornType],
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
                    Ok(Expression::generate_identifier(&format!("v{}", i)))
                } else {
                    Ok(Expression::generate_identifier(
                        &self.var_names[*i as usize],
                    ))
                }
            }
            AcornValue::TypeApplication(app) => {
                if let AcornValue::Lambda(arg_types, body) = app.function.as_ref() {
                    let initial_var_names_len = self.var_names.len();
                    let mut decls = vec![];
                    for arg_type in arg_types {
                        let var_name = self.bindings.next_indexed_var('x', &mut self.next_x);
                        let name_token = TokenType::Identifier.new_token(&var_name);
                        self.var_names.push(var_name);
                        let type_expr = self.type_to_expr(arg_type)?;
                        decls.push(Declaration::Typed(name_token, type_expr));
                    }
                    let body_expr = self.value_to_expr(body, false)?;
                    self.var_names.truncate(initial_var_names_len);

                    let mut type_params = vec![];
                    for (param_name, constraint) in app
                        .type_param_names
                        .iter()
                        .zip(app.type_param_constraints.iter())
                    {
                        let typeclass = constraint
                            .as_ref()
                            .map(|tc| {
                                self.type_to_expr(&AcornType::TypeclassConstraint(tc.clone()))
                            })
                            .transpose()?;
                        type_params.push(TypeParamExpr {
                            name: TokenType::Identifier.new_token(param_name),
                            type_expr: None,
                            typeclass,
                        });
                    }

                    let generic = Expression::GenericBinder(
                        TokenType::Function.generate(),
                        type_params,
                        decls,
                        Box::new(body_expr),
                        TokenType::RightBrace.generate(),
                    );

                    let type_arg_exprs = app
                        .type_args
                        .iter()
                        .map(|t| self.type_to_expr(t))
                        .collect::<Result<Vec<_>>>()?;
                    return Ok(Expression::Concatenation(
                        Box::new(generic),
                        Box::new(Expression::generate_params(type_arg_exprs)),
                    ));
                }

                let function = self.value_to_expr(&app.function, inferrable)?;
                let type_arg_exprs = app
                    .type_args
                    .iter()
                    .map(|t| self.type_to_expr(t))
                    .collect::<Result<Vec<_>>>()?;
                Ok(Expression::Concatenation(
                    Box::new(function),
                    Box::new(Expression::generate_params(type_arg_exprs)),
                ))
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
                            if let ConstantName::TypeclassAttribute(_, typeclass, _) = &c.name {
                                if let AcornType::Data(datatype, _) = &receiver_type {
                                    if self.bindings.is_instance_of(datatype, typeclass) {
                                        // Check if the datatype has its own attribute with the same name
                                        !self.bindings.has_type_attr(datatype, &attr)
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
                    } else if let AcornValue::Constant(c) = fa.function.as_ref() {
                        if let ConstantName::TypeclassAttribute(_, typeclass, attr_name) = &c.name {
                            if let AcornType::Data(datatype, _) = &receiver_type {
                                let receiver_matches_explicit_param = c.params.is_empty()
                                    || matches!(
                                        c.params.as_slice(),
                                        [AcornType::Data(param_datatype, _)] if param_datatype == datatype
                                    );
                                if receiver_matches_explicit_param
                                    && !self.allow_out_of_scope_typeclass_calls
                                    && !self.bindings.is_instance_of(datatype, typeclass)
                                {
                                    return Err(Error::GeneratedBadCode(format!(
                                        "typeclass attribute '{}.{}' for concrete receiver '{}' is not available in the current scope while rendering '{}'",
                                        typeclass.name,
                                        attr_name,
                                        datatype.name,
                                        AcornValue::Application(fa.clone())
                                    )));
                                }
                            }
                        }
                    }
                }

                // For overridden typeclass attributes, we need explicit parameters
                // to distinguish from the datatype's own attributes
                let inferrable = if let AcornValue::Constant(c) = fa.function.as_ref() {
                    let requires_explicit_type_args =
                        if let ConstantName::TypeclassAttribute(_, typeclass, _) = &c.name {
                            c.name.module_id() != self.bindings.module_id()
                                && self.bindings.constant_alias(&c.name).is_none()
                                && self.bindings.typeclass_alias(typeclass).is_none()
                        } else {
                            false
                        };
                    if requires_explicit_type_args {
                        false
                    } else {
                        if let ConstantName::TypeclassAttribute(_, typeclass, attr_name) = &c.name {
                            if let AcornType::Data(datatype, _) = &receiver_type {
                                if self.bindings.is_instance_of(datatype, typeclass) {
                                    // If the datatype has its own attribute, don't infer parameters
                                    !self.bindings.has_type_attr(datatype, attr_name)
                                } else if self.allow_out_of_scope_typeclass_calls {
                                    false
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
            AcornValue::Binary(op, left, right) => self.value_to_binary_expr(*op, left, right),
            AcornValue::Not(x) => {
                if let AcornValue::Binary(BinaryOp::Equals, left, right) = x.as_ref() {
                    return self.value_to_binary_expr(BinaryOp::NotEquals, left, right);
                }
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
            AcornValue::Lambda(quants, body) => {
                if let Some(expr) = self.operator_ref_expr(value) {
                    return Ok(expr);
                }
                self.generate_quantifier_expr(TokenType::Function, quants, body, true)
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
                if let ConstantName::InstanceAttribute(_, inst) = &c.name {
                    let public_name = ConstantName::typeclass_attr(
                        inst.typeclass.module_id,
                        inst.typeclass.clone(),
                        &inst.attribute,
                    );
                    let public_constant = ConstantInstance {
                        name: public_name,
                        params: vec![],
                        instance_type: c.instance_type.clone(),
                        generic_type: c.instance_type.clone(),
                        type_param_names: vec![],
                    };
                    let const_expr = self.const_to_expr(&public_constant)?;
                    let datatype = AcornType::Data(inst.datatype.clone(), vec![]);
                    return self.parametrize_expr(const_expr, &[datatype]);
                }

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
                        if let ConstantName::TypeclassAttribute(_, typeclass, _) = &c.name {
                            if let AcornType::Data(datatype, _) = &c.params[0] {
                                if self.bindings.is_instance_of(datatype, typeclass) {
                                    // Check if the datatype has its own attribute with the same name
                                    let datatype_has_own_attr =
                                        self.bindings.has_type_attr(datatype, &attr);

                                    // Special case for digit attributes
                                    if attr.chars().all(|ch| ch.is_ascii_digit()) {
                                        let numeral = TokenType::Numeral.new_token(&attr);
                                        if !self.explicit_numerals
                                            && self.bindings.numerals() == Some(datatype)
                                        {
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
                // Only add type params if the constant itself is polymorphic.
                // A constant like `item: T` (theorem parameter) has params but empty
                // type_param_names - it uses types from enclosing scope but isn't polymorphic.
                let is_polymorphic = !c.type_param_names.is_empty()
                    || matches!(c.name, ConstantName::TypeclassAttribute(..));
                if !inferrable && !c.params.is_empty() && is_polymorphic {
                    self.parametrize_expr(const_expr, &c.params)
                } else {
                    // We don't need to parametrize because it can be inferred
                    // or it's not polymorphic.
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
            AcornValue::Match(scrutinee, cases) => {
                let scrutinee_expr = self.value_to_expr(scrutinee, false)?;
                let mut case_pairs = Vec::new();
                for case in cases {
                    let pattern_expr = self.value_to_expr(&case.pattern, false)?;
                    let result_expr = self.value_to_expr(&case.result, false)?;
                    case_pairs.push((pattern_expr, result_expr));
                }
                Ok(Expression::Match(
                    TokenType::Match.generate(),
                    Box::new(scrutinee_expr),
                    case_pairs,
                    TokenType::RightBrace.generate(),
                ))
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
mod tests;
