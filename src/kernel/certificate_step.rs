use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::term_normalization::beta_reduce_clause_subterms;
use crate::kernel::variable_map::VariableMap;

/// A certificate claim line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Claim {
    /// The generic clause we are specializing.
    pub clause: Clause,

    /// Variable substitutions used for this claim.
    pub var_map: VariableMap,
}

impl Claim {
    fn validate_var_map_scope(&self) -> Result<(), String> {
        let generic_len = self.clause.get_local_context().len();
        for (var_id, term) in self.var_map.iter() {
            if var_id >= generic_len {
                return Err(format!(
                    "claim var map binds out-of-scope variable x{}",
                    var_id
                ));
            }
            if let Some(max_var) = term.max_variable() {
                if max_var as usize >= generic_len {
                    return Err(format!(
                        "claim var map term references out-of-scope variable x{}",
                        max_var
                    ));
                }
            }
        }
        Ok(())
    }

    pub fn normalized_generic_clause(&self) -> Clause {
        let mut clause = self.clause.clone();
        clause.normalize();
        clause
    }

    pub fn specialize_clause(&self, kernel_context: &KernelContext) -> Result<Clause, String> {
        self.validate_var_map_scope()?;
        Ok(self.var_map.specialize_clause(&self.clause, kernel_context))
    }

    pub fn normalized_specialized_clause(
        &self,
        kernel_context: &KernelContext,
    ) -> Result<Clause, String> {
        let mut clause = beta_reduce_clause_subterms(&self.specialize_clause(kernel_context)?);
        clause.normalize();
        Ok(clause)
    }
}

/// A single kernel-level step in certificate generation/checking.
///
/// Parsing and generation both use this representation. Each step corresponds to one
/// line of certificate code.
#[derive(Clone, PartialEq, Eq)]
pub enum CertificateStep {
    /// A claim statement with a generic clause plus specialization map.
    Claim(Claim),
}
