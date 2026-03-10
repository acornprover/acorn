use serde::{Deserialize, Serialize};
use std::cmp::Ordering;
use std::fmt;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::{PathStep, Term};

/// A Literal stores an equation (or inequality) between two terms.
/// Type information is stored separately in the TypeStore and SymbolTable.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Literal {
    pub positive: bool,
    pub left: Term,
    pub right: Term,
}

impl Literal {
    pub fn new(positive: bool, left: Term, right: Term) -> Literal {
        let (lit, _) = Literal::new_with_flip(positive, left, right);
        lit
    }

    /// Create a positive literal from a single term (term = true).
    pub fn positive(term: Term) -> Literal {
        Literal::new(true, term, Term::new_true())
    }

    /// Create a negative literal from a single term (not term, i.e., term != true).
    pub fn negative(term: Term) -> Literal {
        Literal::new(false, term, Term::new_true())
    }

    /// Create an equality literal (left = right).
    pub fn equals(left: Term, right: Term) -> Literal {
        Literal::new(true, left, right)
    }

    /// Create an inequality literal (left != right).
    pub fn not_equals(left: Term, right: Term) -> Literal {
        Literal::new(false, left, right)
    }

    /// Parse a Literal from a string representation.
    /// Format: "left = right", "left != right", "not term", or just "term".
    pub fn parse(s: &str) -> Literal {
        if s.contains(" != ") {
            let mut parts = s.split(" != ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::not_equals(left, right)
        } else if s.contains(" = ") {
            let mut parts = s.split(" = ");
            let left = Term::parse(parts.next().unwrap());
            let right = Term::parse(parts.next().unwrap());
            Literal::equals(left, right)
        } else if s.starts_with("not ") {
            let term = Term::parse(&s[4..]);
            Literal::negative(term)
        } else {
            let term = Term::parse(s);
            Literal::positive(term)
        }
    }

    /// Create a literal representing the value "true" (true = true).
    pub fn true_value() -> Literal {
        Literal::new(true, Term::new_true(), Term::new_true())
    }

    /// Create a literal representing the value "false" (true != true).
    pub fn false_value() -> Literal {
        Literal::new(false, Term::new_true(), Term::new_true())
    }

    /// Negate this literal (flip positive/negative).
    pub fn negate(&self) -> Literal {
        Literal {
            positive: !self.positive,
            left: self.left.clone(),
            right: self.right.clone(),
        }
    }

    /// Check if this literal is a tautology (foo = foo with positive=true).
    pub fn is_tautology(&self) -> bool {
        self.positive && self.left == self.right
    }

    /// Check if this literal is impossible (foo != foo).
    pub fn is_impossible(&self) -> bool {
        !self.positive && self.left == self.right
    }

    /// Check if this is a signed term (right side is "true").
    pub fn is_signed_term(&self) -> bool {
        self.right.is_true()
    }

    /// Check if this literal represents the value "true" (true = true).
    pub fn is_true_value(&self) -> bool {
        self.positive && self.left.is_true() && self.right.is_true()
    }

    /// Check if this literal represents the value "false" (true != true).
    pub fn is_false_value(&self) -> bool {
        !self.positive && self.left.is_true() && self.right.is_true()
    }

    /// Check if this literal contains any variables.
    pub fn has_any_variable(&self) -> bool {
        self.left.has_any_variable() || self.right.has_any_variable()
    }

    /// Check if this literal contains any local constants.
    pub fn has_scoped_constant(&self) -> bool {
        self.left.has_scoped_constant() || self.right.has_scoped_constant()
    }

    /// Count the total number of atoms in both terms.
    pub fn atom_count(&self) -> u32 {
        self.left.atom_count() + self.right.atom_count()
    }

    /// Get the least unused variable index across both terms.
    pub fn least_unused_variable(&self) -> AtomId {
        self.left
            .least_unused_variable()
            .max(self.right.least_unused_variable())
    }

    /// Iterate over all atoms in both terms.
    pub fn iter_atoms(&self) -> impl Iterator<Item = &Atom> + '_ {
        self.left.iter_atoms().chain(self.right.iter_atoms())
    }

    /// Get both term pairs for matching (for use in equality reasoning).
    /// Returns (forward, left, right) and (backward, right, left).
    pub fn both_term_pairs(&self) -> Vec<(bool, &Term, &Term)> {
        vec![
            (true, &self.left, &self.right),
            (false, &self.right, &self.left),
        ]
    }

    /// Check if this literal is normalized.
    /// A literal is normalized if it doesn't need to flip its terms.
    /// The larger term (by KBO ordering) should be on the left.
    pub fn is_normalized(&self) -> bool {
        !needs_to_flip(&self.left, &self.right)
    }

    /// Flip the left and right terms of this literal.
    pub fn flip(&mut self) {
        std::mem::swap(&mut self.left, &mut self.right);
    }

    /// Normalize variable IDs in place, ensuring type dependencies come first.
    /// When a variable is encountered for the first time, any variables in its type
    /// are added before the variable itself. This ensures the resulting ordering
    /// satisfies type dependency constraints.
    /// Returns true if the literal was flipped during normalization.
    pub fn normalize_var_ids_with_context(
        &mut self,
        var_ids: &mut Vec<AtomId>,
        context: &LocalContext,
    ) -> bool {
        self.left.normalize_var_ids_with_context(var_ids, context);
        self.right.normalize_var_ids_with_context(var_ids, context);
        if needs_to_flip(&self.left, &self.right) {
            self.flip();
            true
        } else {
            false
        }
    }

    /// Normalizes the direction and returns whether it was flipped.
    /// The larger term should be on the left of the literal.
    pub fn new_with_flip(positive: bool, left: Term, right: Term) -> (Literal, bool) {
        if needs_to_flip(&left, &right) {
            (
                Literal {
                    positive,
                    left: right,
                    right: left,
                },
                true,
            )
        } else {
            (
                Literal {
                    positive,
                    left,
                    right,
                },
                false,
            )
        }
    }

    /// Create a literal from a term with a sign.
    pub fn from_signed_term(term: Term, positive: bool) -> Literal {
        Literal::new(positive, term, Term::new_true())
    }

    /// Whether the components of this literal are strictly ordered according to the KBO.
    pub fn strict_kbo(&self) -> bool {
        match self.left.kbo_cmp(&self.right) {
            Ordering::Less => panic!("kbo inconsistency"),
            Ordering::Equal => false,
            Ordering::Greater => true,
        }
    }

    /// An extension of the kbo ordering on literals.
    /// Ignores sign.
    pub fn extended_kbo_cmp(&self, other: &Literal) -> Ordering {
        let left_cmp = self.left.extended_kbo_cmp(&other.left);
        if left_cmp != Ordering::Equal {
            return left_cmp;
        }
        self.right.extended_kbo_cmp(&other.right)
    }

    /// Comparison that is stable under variable renaming (alpha-equivalence).
    /// Two literals that differ only in variable naming will compare as Equal.
    /// Includes sign in comparison.
    pub fn stable_cmp(&self, other: &Literal) -> Ordering {
        let positive_cmp = self.positive.cmp(&other.positive);
        if positive_cmp != Ordering::Equal {
            return positive_cmp;
        }

        let left_cmp = self.left.stable_cmp(&other.left);
        if left_cmp != Ordering::Equal {
            return left_cmp;
        }
        self.right.stable_cmp(&other.right)
    }

    /// Returns (right, left, output_context) with normalized var ids.
    /// The output_context contains the types of the renumbered variables.
    /// The input_context provides the types of variables before renumbering.
    pub fn normalized_reversed(&self, input_context: &LocalContext) -> (Term, Term, LocalContext) {
        let mut var_ids: Vec<AtomId> = vec![];
        let mut right = self.right.clone();
        right.normalize_var_ids_with_context(&mut var_ids, input_context);
        let mut left = self.left.clone();
        left.normalize_var_ids_with_context(&mut var_ids, input_context);
        let output_context = input_context.remap(&var_ids);
        (right, left, output_context)
    }

    /// Validate that both sides of the literal have the same type.
    ///
    /// This validation only runs in test builds or when the "validate" feature is enabled.
    /// It's skipped in production for performance reasons.
    pub fn validate_type(&self, local_context: &LocalContext, kernel_context: &KernelContext) {
        #[cfg(not(any(test, feature = "validate")))]
        {
            let _ = (local_context, kernel_context);
            return;
        }

        #[cfg(any(test, feature = "validate"))]
        {
            // Validate term structure
            self.left.validate();
            self.right.validate();

            // Validate types in local context
            for (i, var_type) in local_context.get_var_types().iter().enumerate() {
                let Some(var_type) = var_type else {
                    continue;
                };
                if !var_type.validate_structure_impl() {
                    panic!(
                        "Malformed type in LocalContext for variable x{}: {:?}",
                        i, var_type
                    );
                }
            }

            // Validate type consistency
            let left_type = self
                .left
                .get_type_with_context(local_context, kernel_context);
            let right_type = self
                .right
                .get_type_with_context(local_context, kernel_context);
            if left_type != right_type {
                panic!(
                    "Literal type mismatch: {} has type {:?} but {} has type {:?}\n  Context: {:?}",
                    self.left,
                    left_type,
                    self.right,
                    right_type,
                    local_context.get_var_types()
                );
            }
        }
    }

    /// Extracts the polarity from this literal, returning a positive version and the original polarity.
    /// If the literal is already positive, returns (self, true).
    /// If the literal is negative, returns (positive version, false).
    pub fn extract_polarity(&self) -> (Literal, bool) {
        if self.positive {
            (self.clone(), true)
        } else {
            (self.negate(), false)
        }
    }

    /// Whether either side of the literal has this as its head.
    pub fn has_head(&self, head: &Atom) -> bool {
        self.left.get_head_atom() == head || self.right.get_head_atom() == head
    }

    /// Get the subterm at the given path.
    /// If `left` is true, navigate into the left term, otherwise the right term.
    /// A path uses PathStep::Function/Argument to navigate the curried term structure.
    pub fn get_term_at_path(&self, left: bool, path: &[PathStep]) -> Option<Term> {
        if left {
            self.left.get_term_at_path(path)
        } else {
            self.right.get_term_at_path(path)
        }
    }

    /// Replace the subterm at the given path with a new term.
    /// If `left` is true, replace in the left term, otherwise the right term.
    /// A path uses PathStep::Function/Argument to navigate the curried term structure.
    /// Returns a new literal (may be flipped for normalization) and whether it was flipped.
    pub fn replace_at_path(
        &self,
        left: bool,
        path: &[PathStep],
        new_subterm: Term,
    ) -> (Literal, bool) {
        let (new_left, new_right) = if left {
            (
                self.left.replace_at_path(path, new_subterm),
                self.right.clone(),
            )
        } else {
            (
                self.left.clone(),
                self.right.replace_at_path(path, new_subterm),
            )
        };

        Literal::new_with_flip(self.positive, new_left, new_right)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.positive {
            if self.is_signed_term() {
                write!(f, "{}", self.left)
            } else {
                write!(f, "{} = {}", self.left, self.right)
            }
        } else if self.is_signed_term() {
            write!(f, "not {}", self.left)
        } else {
            write!(f, "{} != {}", self.left, self.right)
        }
    }
}

impl PartialOrd for Literal {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;

        let positive_cmp = self.positive.cmp(&other.positive);
        if positive_cmp != Ordering::Equal {
            return Some(positive_cmp);
        }

        let left_cmp = other.left.extended_kbo_cmp(&self.left);
        if left_cmp != Ordering::Equal {
            return Some(left_cmp);
        }

        Some(other.right.extended_kbo_cmp(&self.right))
    }
}

impl Ord for Literal {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// Helper function to check if a literal needs to flip its terms.
/// Returns true if left < right in extended KBO ordering.
fn needs_to_flip(left: &Term, right: &Term) -> bool {
    use std::cmp::Ordering;
    left.extended_kbo_cmp(right) == Ordering::Less
}
