// Perfect Discrimination Tree (PDT): A pattern matching tree that ignores types during matching.
//
// Key design decisions:
// 1. Types are NOT encoded in keys - matching is purely structural
// 2. Variables are numbered by first occurrence (same as Pdt)
// 3. When inserting a pattern, we store the types of each pattern variable
// 4. When matching, we find structural matches first, then verify type compatibility
//
// This approach naturally handles polymorphic patterns because:
// - Pattern: add[R](x, y) encodes as just the structure (ignoring that R is a type variable)
// - Query: add[Int](c, d) encodes as the same structure
// - After finding the match, we verify that the type bindings are compatible

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use qp_trie::{Entry, SubTrie, Trie};

use super::atom::{Atom as KernelAtom, AtomId};
use super::clause::Clause;
use super::kernel_context::KernelContext;
use super::literal::Literal;
use super::local_context::LocalContext;
use super::symbol::Symbol;
use super::term::Term;
use super::term::{Decomposition, TermRef};
use super::unifier::{Scope, Unifier};
use super::variable_map::VariableMap;
use crate::module::ModuleId;

const MAX_STACK_LIMIT_WARNINGS: usize = 20;
static STACK_LIMIT_WARNING_COUNT: AtomicUsize = AtomicUsize::new(0);

fn stack_limit_warning_message(warning_index: usize) -> Option<&'static str> {
    if warning_index < MAX_STACK_LIMIT_WARNINGS {
        Some("WARNING: PDT stack_limit exhausted - consider increasing the limit")
    } else if warning_index == MAX_STACK_LIMIT_WARNINGS {
        Some("WARNING: PDT stack_limit exhausted - subsequent warnings silenced")
    } else {
        None
    }
}

/// Atoms are the leaf nodes in the PDT.
/// Types are NOT represented - only symbols and variables.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Atom {
    /// Pattern variable, numbered by first occurrence.
    Variable(AtomId),

    /// Named constants and functions.
    Symbol(Symbol),

    /// Boolean constant true.
    True,

    /// Boolean constant false.
    False,

    /// De Bruijn bound variable index (structural, not a pattern wildcard).
    BoundVariable(u16),
}

/// Edges form the structure of paths through the PDT.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Edge {
    /// Application: followed by function, argument.
    /// Note: we don't encode domain type.
    Application,

    /// Arrow (Pi type): followed by input type, output type.
    /// Used when function types appear as values (e.g., id[Bool -> Bool]).
    Arrow,

    /// Lambda binder: followed by input type, body.
    Lambda,

    /// ForAll binder: followed by binder type, body.
    ForAll,

    /// Exists binder: followed by binder type, body.
    Exists,

    /// A leaf atom.
    Atom(Atom),

    /// Indicates a literal with the given sign (true = positive).
    LiteralForm(bool),
}

// Byte constants for serialization
const APPLICATION: u8 = 0;
const LITERAL_POSITIVE: u8 = 1;
const LITERAL_NEGATIVE: u8 = 2;
const ATOM_VARIABLE: u8 = 3;
const ATOM_TRUE: u8 = 4;
const ATOM_FALSE: u8 = 5;
const ATOM_SYMBOL_GLOBAL: u8 = 6;
const ATOM_SYMBOL_SCOPED: u8 = 7;
const ATOM_SYMBOL_BOOL: u8 = 10;
const ATOM_SYMBOL_TYPESORT: u8 = 11;
const ATOM_SYMBOL_TYPE: u8 = 12;
const ATOM_SYMBOL_TYPECLASS: u8 = 13;
const ARROW: u8 = 14;
const ATOM_SYMBOL_NOT: u8 = 15;
const ATOM_SYMBOL_AND: u8 = 16;
const ATOM_SYMBOL_OR: u8 = 17;
const ATOM_SYMBOL_EQ: u8 = 18;
const ATOM_SYMBOL_ITE: u8 = 19;
const ATOM_BOUND_VARIABLE: u8 = 20;
const LAMBDA: u8 = 21;
const FORALL: u8 = 22;
const EXISTS: u8 = 23;

impl Edge {
    /// Returns the discriminant byte for this edge.
    fn discriminant(&self) -> u8 {
        match self {
            Edge::Application => APPLICATION,
            Edge::Arrow => ARROW,
            Edge::Lambda => LAMBDA,
            Edge::ForAll => FORALL,
            Edge::Exists => EXISTS,
            Edge::LiteralForm(true) => LITERAL_POSITIVE,
            Edge::LiteralForm(false) => LITERAL_NEGATIVE,
            Edge::Atom(atom) => match atom {
                Atom::Variable(_) => ATOM_VARIABLE,
                Atom::True => ATOM_TRUE,
                Atom::False => ATOM_FALSE,
                Atom::BoundVariable(_) => ATOM_BOUND_VARIABLE,
                Atom::Symbol(Symbol::True) => ATOM_TRUE,
                Atom::Symbol(Symbol::False) => ATOM_FALSE,
                Atom::Symbol(Symbol::Bool) => ATOM_SYMBOL_BOOL,
                Atom::Symbol(Symbol::Type0) => ATOM_SYMBOL_TYPESORT,
                Atom::Symbol(Symbol::Type(_)) => ATOM_SYMBOL_TYPE,
                Atom::Symbol(Symbol::Typeclass(_)) => ATOM_SYMBOL_TYPECLASS,
                Atom::Symbol(Symbol::Not) => ATOM_SYMBOL_NOT,
                Atom::Symbol(Symbol::And) => ATOM_SYMBOL_AND,
                Atom::Symbol(Symbol::Or) => ATOM_SYMBOL_OR,
                Atom::Symbol(Symbol::Eq) => ATOM_SYMBOL_EQ,
                Atom::Symbol(Symbol::Ite) => ATOM_SYMBOL_ITE,
                Atom::Symbol(Symbol::GlobalConstant(..)) => ATOM_SYMBOL_GLOBAL,
                Atom::Symbol(Symbol::ScopedConstant(_)) => ATOM_SYMBOL_SCOPED,
            },
        }
    }

    /// Appends the byte representation of this edge to the vector.
    /// Most edges are 3 bytes: discriminant + 2 bytes for ID.
    /// GlobalConstant is 5 bytes: discriminant + 2 bytes module_id + 2 bytes local_id.
    fn append_to(&self, v: &mut Vec<u8>) {
        v.push(self.discriminant());
        match self {
            Edge::Application
            | Edge::Arrow
            | Edge::Lambda
            | Edge::ForAll
            | Edge::Exists
            | Edge::LiteralForm(_) => {
                v.extend_from_slice(&0u16.to_ne_bytes());
            }
            Edge::Atom(atom) => match atom {
                Atom::Variable(i) => v.extend_from_slice(&i.to_ne_bytes()),
                Atom::BoundVariable(i) => v.extend_from_slice(&i.to_ne_bytes()),
                Atom::True | Atom::False => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::True) | Atom::Symbol(Symbol::False) => {
                    v.extend_from_slice(&0u16.to_ne_bytes())
                }
                Atom::Symbol(Symbol::Bool) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::Type0) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::Not) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::And) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::Or) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::Eq) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::Ite) => v.extend_from_slice(&0u16.to_ne_bytes()),
                Atom::Symbol(Symbol::Type(t)) => {
                    // Type uses 4 bytes: module_id (2) + local_id (2)
                    v.extend_from_slice(&t.module_id().get().to_ne_bytes());
                    v.extend_from_slice(&t.local_id().to_ne_bytes());
                }
                Atom::Symbol(Symbol::Typeclass(tc)) => {
                    // Typeclass uses 4 bytes: module_id (2) + local_id (2)
                    v.extend_from_slice(&tc.module_id().get().to_ne_bytes());
                    v.extend_from_slice(&tc.local_id().to_ne_bytes());
                }
                Atom::Symbol(Symbol::GlobalConstant(m, c)) => {
                    // GlobalConstant uses 4 bytes: module_id (2) + local_id (2)
                    v.extend_from_slice(&m.get().to_ne_bytes());
                    v.extend_from_slice(&c.to_ne_bytes());
                }
                Atom::Symbol(Symbol::ScopedConstant(c)) => v.extend_from_slice(&c.to_ne_bytes()),
            },
        }
    }

    /// Parses an edge from bytes. Returns the edge and the number of bytes consumed.
    /// Most edges consume 3 bytes, GlobalConstant consumes 5 bytes.
    fn from_bytes(bytes: &[u8]) -> (Edge, usize) {
        use super::types::GroundTypeId;
        let discriminant = bytes[0];
        match discriminant {
            APPLICATION => (Edge::Application, 3),
            ARROW => (Edge::Arrow, 3),
            LAMBDA => (Edge::Lambda, 3),
            FORALL => (Edge::ForAll, 3),
            EXISTS => (Edge::Exists, 3),
            LITERAL_POSITIVE => (Edge::LiteralForm(true), 3),
            LITERAL_NEGATIVE => (Edge::LiteralForm(false), 3),
            ATOM_VARIABLE => {
                let id = u16::from_ne_bytes([bytes[1], bytes[2]]);
                (Edge::Atom(Atom::Variable(id)), 3)
            }
            ATOM_TRUE => (Edge::Atom(Atom::True), 3),
            ATOM_FALSE => (Edge::Atom(Atom::False), 3),
            ATOM_BOUND_VARIABLE => {
                let id = u16::from_ne_bytes([bytes[1], bytes[2]]);
                (Edge::Atom(Atom::BoundVariable(id)), 3)
            }
            ATOM_SYMBOL_GLOBAL => {
                // GlobalConstant uses 5 bytes: 1 discriminant + 2 module_id + 2 local_id
                let module_id = u16::from_ne_bytes([bytes[1], bytes[2]]);
                let local_id = u16::from_ne_bytes([bytes[3], bytes[4]]);
                (
                    Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(
                        ModuleId(module_id),
                        local_id,
                    ))),
                    5,
                )
            }
            ATOM_SYMBOL_SCOPED => {
                let id = u16::from_ne_bytes([bytes[1], bytes[2]]);
                (Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(id))), 3)
            }
            ATOM_SYMBOL_BOOL => (Edge::Atom(Atom::Symbol(Symbol::Bool)), 3),
            ATOM_SYMBOL_TYPESORT => (Edge::Atom(Atom::Symbol(Symbol::Type0)), 3),
            ATOM_SYMBOL_NOT => (Edge::Atom(Atom::Symbol(Symbol::Not)), 3),
            ATOM_SYMBOL_AND => (Edge::Atom(Atom::Symbol(Symbol::And)), 3),
            ATOM_SYMBOL_OR => (Edge::Atom(Atom::Symbol(Symbol::Or)), 3),
            ATOM_SYMBOL_EQ => (Edge::Atom(Atom::Symbol(Symbol::Eq)), 3),
            ATOM_SYMBOL_ITE => (Edge::Atom(Atom::Symbol(Symbol::Ite)), 3),
            ATOM_SYMBOL_TYPE => {
                // Type uses 5 bytes: 1 discriminant + 2 module_id + 2 local_id
                let module_id = u16::from_ne_bytes([bytes[1], bytes[2]]);
                let local_id = u16::from_ne_bytes([bytes[3], bytes[4]]);
                (
                    Edge::Atom(Atom::Symbol(Symbol::Type(GroundTypeId::new(
                        ModuleId(module_id),
                        local_id,
                    )))),
                    5,
                )
            }
            ATOM_SYMBOL_TYPECLASS => {
                // Typeclass uses 5 bytes: 1 discriminant + 2 module_id + 2 local_id
                let module_id = u16::from_ne_bytes([bytes[1], bytes[2]]);
                let local_id = u16::from_ne_bytes([bytes[3], bytes[4]]);
                (
                    Edge::Atom(Atom::Symbol(Symbol::Typeclass(
                        super::types::TypeclassId::new(ModuleId(module_id), local_id),
                    ))),
                    5,
                )
            }
            _ => panic!("invalid PDT edge discriminant: {}", discriminant),
        }
    }

    /// Debug helper to convert a byte sequence to a string of edges.
    #[allow(dead_code)]
    fn debug_bytes(bytes: &[u8]) -> String {
        let mut i = 0;
        let mut parts: Vec<String> = vec![];
        while i < bytes.len() {
            // Check if we have at least 3 bytes (minimum edge size)
            if i + 3 <= bytes.len() {
                let (edge, consumed) = Edge::from_bytes(&bytes[i..]);
                parts.push(format!("{:?}", edge));
                i += consumed;
            } else {
                parts.push(format!("plus extra bytes {:?}", &bytes[i..]));
                break;
            }
        }
        parts.join(", ")
    }
}

/// Encodes the structure of a term (ignoring types).
fn key_from_term_structure(term: TermRef, key: &mut Vec<u8>) {
    match term.decompose() {
        Decomposition::Atom(atom) => {
            let edge_atom = match atom {
                KernelAtom::FreeVariable(v) => Atom::Variable(*v),
                KernelAtom::BoundVariable(i) => Atom::BoundVariable(*i),
                KernelAtom::Symbol(Symbol::True) => Atom::True,
                KernelAtom::Symbol(Symbol::False) => Atom::False,
                KernelAtom::Symbol(Symbol::Typeclass(_)) => {
                    // Typeclasses are handled as part of type-checking, not structure
                    panic!("Typeclass in PDT term structure - should be in type context")
                }
                KernelAtom::Symbol(s) => Atom::Symbol(*s),
            };
            Edge::Atom(edge_atom).append_to(key);
        }
        Decomposition::Application(func, arg) => {
            // Application: just encode func and arg, no type info
            Edge::Application.append_to(key);
            key_from_term_structure(func, key);
            key_from_term_structure(arg, key);
        }
        Decomposition::Pi(input, output) => {
            // Pi types can appear as values when polymorphic functions are applied to function types
            // e.g., id[Bool -> Bool](not) has (Bool -> Bool) as a subterm
            Edge::Arrow.append_to(key);
            key_from_term_structure(input, key);
            key_from_term_structure(output, key);
        }
        Decomposition::Lambda(input, body) => {
            Edge::Lambda.append_to(key);
            key_from_term_structure(input, key);
            key_from_term_structure(body, key);
        }
        Decomposition::ForAll(binder_type, body) => {
            Edge::ForAll.append_to(key);
            key_from_term_structure(binder_type, key);
            key_from_term_structure(body, key);
        }
        Decomposition::Exists(binder_type, body) => {
            Edge::Exists.append_to(key);
            key_from_term_structure(binder_type, key);
            key_from_term_structure(body, key);
        }
    }
}

/// Generates a complete key for a term (ignoring types).
fn key_from_term(term: &Term) -> Vec<u8> {
    let mut key = Vec::new();
    key_from_term_structure(term.as_ref(), &mut key);
    key
}

/// Generates a key for a term pair (like a literal without sign).
fn key_from_pair(term1: &Term, term2: &Term) -> Vec<u8> {
    let mut key = Vec::new();
    key_from_term_structure(term1.as_ref(), &mut key);
    key_from_term_structure(term2.as_ref(), &mut key);
    key
}

/// Generates a key for a clause.
fn key_from_clause(clause: &Clause) -> Vec<u8> {
    let mut key = Vec::new();
    for literal in &clause.literals {
        Edge::LiteralForm(literal.positive).append_to(&mut key);
    }
    for literal in &clause.literals {
        key_from_term_structure(literal.left.as_ref(), &mut key);
        key_from_term_structure(literal.right.as_ref(), &mut key);
    }
    key
}

/// Creates a key prefix for a term (currently empty).
pub fn term_key_prefix() -> Vec<u8> {
    Vec::new()
}

/// Stored metadata for a pattern: the types of each variable in the pattern.
#[derive(Clone, Debug)]
struct PatternMetadata {
    /// The pattern's local context, containing variable types.
    context: LocalContext,
}

impl PatternMetadata {
    fn from_clause(clause: &Clause) -> PatternMetadata {
        PatternMetadata {
            context: clause.get_local_context().clone(),
        }
    }

    fn from_local_context(lctx: &LocalContext) -> PatternMetadata {
        PatternMetadata {
            context: lctx.clone(),
        }
    }
}

/// Perfect Discrimination Tree: pattern matching that ignores types during structural matching.
#[derive(Clone, Debug)]
pub struct Pdt<T> {
    /// Maps byte keys to indices into the values vector.
    trie: Trie<Vec<u8>, usize>,

    /// Values stored in the tree.
    pub values: Vec<T>,

    /// Metadata for each pattern (variable types for type-checking).
    metadata: Vec<PatternMetadata>,
}

impl<T> Pdt<T> {
    pub fn new() -> Pdt<T> {
        Pdt {
            trie: Trie::new(),
            values: vec![],
            metadata: vec![],
        }
    }

    /// Inserts a term pair with its associated value.
    fn insert_pair(&mut self, term1: &Term, term2: &Term, value: T, local_context: &LocalContext) {
        let key = key_from_pair(term1, term2);
        let value_id = self.values.len();
        self.values.push(value);
        self.metadata
            .push(PatternMetadata::from_local_context(local_context));
        self.trie.insert(key, value_id);
    }

    /// Inserts a clause with its associated value.
    pub fn insert_clause(&mut self, clause: &Clause, value: T) {
        let key = key_from_clause(clause);
        let value_id = self.values.len();
        self.values.push(value);
        self.metadata.push(PatternMetadata::from_clause(clause));
        self.trie.insert(key, value_id);
    }

    /// Finds matches for a term, calling the callback for each match.
    /// Returns false if callback returns false, otherwise true.
    ///
    /// The key parameter is used as a prefix (e.g., type info for API compatibility).
    /// The type checking happens via the metadata after structural matching.
    pub fn find_term_matches_while<'a, F>(
        &self,
        key: &mut Vec<u8>,
        terms: &[TermRef<'a>],
        local_context: &LocalContext,
        kernel_context: &KernelContext,
        replacements: &mut Vec<TermRef<'a>>,
        callback: &mut F,
    ) -> bool
    where
        F: FnMut(usize, &Vec<TermRef<'a>>) -> bool,
    {
        // Get subtrie based on any prefix in key
        let subtrie = self.trie.subtrie(key);
        find_matches_while(
            &subtrie,
            key,
            terms,
            local_context,
            kernel_context,
            &self.metadata,
            500,
            replacements,
            callback,
        )
    }

    /// Finds a pair in the tree.
    fn find_pair<'a>(
        &'a self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<&'a T> {
        self.find_pair_with_replacements(left, right, local_context, kernel_context)
            .map(|(value, _)| value)
    }

    fn find_pair_with_replacements<'a>(
        &'a self,
        left: &Term,
        right: &Term,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<(&'a T, Vec<Term>)> {
        let terms = [left.as_ref(), right.as_ref()];
        let mut replacements: Vec<TermRef> = vec![];
        let mut found = None;
        let mut key = Vec::new();
        self.find_term_matches_while(
            &mut key,
            &terms,
            local_context,
            kernel_context,
            &mut replacements,
            &mut |value_id, matched_replacements| {
                found = Some((
                    value_id,
                    matched_replacements
                        .iter()
                        .map(|replacement| replacement.to_owned())
                        .collect::<Vec<_>>(),
                ));
                false // Stop after first match
            },
        );
        found.map(|(id, replacements)| (&self.values[id], replacements))
    }

    /// Finds a clause in the tree.
    pub fn find_clause<'a>(
        &'a self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<&'a T> {
        let local_context = clause.get_local_context();

        // Build the terms array from all literals in the clause
        let mut terms: Vec<TermRef> = vec![];
        for literal in &clause.literals {
            terms.push(literal.left.as_ref());
            terms.push(literal.right.as_ref());
        }

        // Build prefix key (just literal signs)
        let mut prefix_key = Vec::new();
        for literal in &clause.literals {
            Edge::LiteralForm(literal.positive).append_to(&mut prefix_key);
        }

        let subtrie = self.trie.subtrie(&prefix_key);

        let mut replacements: Vec<TermRef> = vec![];
        let mut found_id = None;
        find_matches_while(
            &subtrie,
            &mut prefix_key,
            &terms,
            local_context,
            kernel_context,
            &self.metadata,
            500,
            &mut replacements,
            &mut |value_id, _| {
                found_id = Some(value_id);
                false // Stop after first match
            },
        );
        found_id.map(|id| &self.values[id])
    }
}

impl Pdt<()> {
    /// Appends to the existing value if possible. Otherwise, inserts a vec![U].
    pub fn insert_or_append<U>(
        pt: &mut Pdt<Vec<U>>,
        term: &Term,
        value: U,
        local_context: &LocalContext,
    ) {
        let key = key_from_term(term);
        match pt.trie.entry(key) {
            Entry::Occupied(entry) => {
                let value_id = entry.get();
                pt.values[*value_id].push(value);
            }
            Entry::Vacant(entry) => {
                let value_id = pt.values.len();
                pt.values.push(vec![value]);
                pt.metadata
                    .push(PatternMetadata::from_local_context(local_context));
                entry.insert(value_id);
            }
        }
    }
}

/// The LiteralSet stores literals using a PDT.
#[derive(Clone)]
pub struct LiteralSet {
    /// Stores literal metadata for each indexed literal.
    tree: Pdt<LiteralEntry>,
}

#[derive(Clone, Debug)]
struct LiteralEntry {
    sign: bool,
    id: usize,
    flipped: bool,
    /// When `flipped` is true, `reversed_var_ids[new_id] = old_id` maps the
    /// reversed literal's normalized variable numbering back to the original
    /// clause-local numbering.
    reversed_var_ids: Vec<AtomId>,
}

impl LiteralSet {
    pub fn new() -> LiteralSet {
        LiteralSet { tree: Pdt::new() }
    }

    /// Inserts a literal along with its id.
    pub fn insert(&mut self, literal: &Literal, id: usize, local_context: &LocalContext) {
        self.tree.insert_pair(
            &literal.left,
            &literal.right,
            LiteralEntry {
                sign: literal.positive,
                id,
                flipped: false,
                reversed_var_ids: vec![],
            },
            local_context,
        );
        if !literal.strict_kbo() {
            let (right, left, reversed_context) = literal.normalized_reversed(local_context);
            let reversed_var_ids = literal.reversed_var_ids(local_context);
            self.tree.insert_pair(
                &right,
                &left,
                LiteralEntry {
                    sign: literal.positive,
                    id,
                    flipped: true,
                    reversed_var_ids,
                },
                &reversed_context,
            );
        }
    }

    /// Checks whether any literal in the tree is a generalization of the provided literal.
    pub fn find_generalization(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<(bool, usize, bool)> {
        match self
            .tree
            .find_pair(&literal.left, &literal.right, local_context, kernel_context)
        {
            Some(entry) => Some((entry.sign == literal.positive, entry.id, entry.flipped)),
            None => None,
        }
    }

    /// Like `find_generalization`, but also returns the specializing variable map.
    pub fn find_generalization_with_map(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        kernel_context: &KernelContext,
    ) -> Option<(bool, usize, bool, VariableMap)> {
        let (entry, replacements) = self
            .tree
            .find_pair_with_replacements(
                &literal.left,
                &literal.right,
                local_context,
                kernel_context,
            )
            .map(|(value, replacements)| (value.clone(), replacements))?;
        let mut var_map = VariableMap::new();
        if entry.flipped {
            for (new_id, replacement) in replacements.into_iter().enumerate() {
                let original_id = *entry.reversed_var_ids.get(new_id)?;
                var_map.set(original_id, replacement);
            }
        } else {
            for (var_id, replacement) in replacements.into_iter().enumerate() {
                var_map.set(var_id as AtomId, replacement);
            }
        }
        Some((
            entry.sign == literal.positive,
            entry.id,
            entry.flipped,
            var_map,
        ))
    }
}

/// Checks if a binding is type-compatible with the pattern variable's type.
///
/// For polymorphic patterns, this checks that the bound term's type can be obtained
/// by instantiating the pattern variable's type. Uses the Unifier to check if the
/// bound type is a valid instance of the pattern type (e.g., List[Int] matches List[T]).
fn types_compatible(
    bound_term: TermRef,
    pattern_var_type: &Term,
    pattern_context: &LocalContext,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> bool {
    fn typeclass_binding_is_compatible(
        actual_tc_id: crate::kernel::types::TypeclassId,
        required_tc_id: crate::kernel::types::TypeclassId,
        kernel_context: &KernelContext,
    ) -> bool {
        actual_tc_id == required_tc_id
            || kernel_context
                .type_store
                .typeclass_extends(actual_tc_id, required_tc_id)
    }

    fn resolve_typeclass_constraint(
        type_term: TermRef,
        context: &LocalContext,
    ) -> Option<crate::kernel::types::TypeclassId> {
        if let Some(tc_id) = type_term.as_typeclass() {
            return Some(tc_id);
        }
        let var_id = type_term.atomic_variable()?;
        let var_type = context.get_var_type(var_id as usize)?;
        resolve_typeclass_constraint(var_type.as_ref(), context)
    }

    let bound_type = match bound_term.decompose() {
        Decomposition::Atom(KernelAtom::BoundVariable(i)) => {
            // Bound variables are indexed from the innermost binder.
            // In the query context, binders are appended as we descend, so b0 is the last entry.
            let i = *i as usize;
            let context_idx = match query_context.len().checked_sub(i + 1) {
                Some(idx) => idx,
                None => return false,
            };
            match query_context.get_var_type(context_idx) {
                Some(var_type) => var_type.clone(),
                None => return false,
            }
        }
        _ => bound_term.get_type_with_context(query_context, kernel_context),
    };

    // Universe level check: when pattern_var_type is TypeSort (expecting a type like Foo, Nat),
    // we should only accept proper types, not value-level expressions that compute to Type.
    //
    // Valid matches:
    // - Type symbols: Foo, Bool (Symbol::Type, Symbol::Bool)
    // - Type constructor applications: List[Int] (Symbol::Type applied to args)
    //
    // Invalid matches:
    // - TypeSort itself (would cause universe polymorphism issues)
    // - Value functions returning Type: second[T, Type, p] returns Type if U=Type
    if matches!(
        pattern_var_type.as_ref().decompose(),
        Decomposition::Atom(KernelAtom::Symbol(Symbol::Type0))
    ) {
        // Check that bound_term is a proper type, not a value-level expression
        match bound_term.get_head_atom() {
            // Type-level terms: type symbols and type constructors
            KernelAtom::Symbol(Symbol::Type(_))
            | KernelAtom::Symbol(Symbol::Bool)
            | KernelAtom::FreeVariable(_) => {
                // Accept: proper types and type variables
            }
            KernelAtom::Symbol(Symbol::Type0) => {
                // Reject: TypeSort itself shouldn't match a type variable
                return false;
            }
            _ => {
                // Reject: value-level expressions (GlobalConstant, ScopedConstant, etc.)
                return false;
            }
        }
    }

    // Fast path: exact equality
    if bound_type == *pattern_var_type {
        return true;
    }

    // Special case: pattern variable type is a typeclass constraint
    // E.g., x0: Ring means x0 is a type that implements Ring
    // If bound_term is a concrete type (like Int), check if it implements the typeclass
    if let Decomposition::Atom(KernelAtom::Symbol(Symbol::Typeclass(tc_id))) =
        pattern_var_type.as_ref().decompose()
    {
        // The bound term should be a type that implements this typeclass
        if let Some(ground_id) = bound_term.as_type_atom() {
            // is_instance_of handles both explicit instances and arbitrary types with
            // compatible typeclass constraints
            return kernel_context.type_store.is_instance_of(ground_id, *tc_id);
        }
        if let Some(var_id) = bound_term.atomic_variable() {
            let Some(var_type) = query_context.get_var_type(var_id as usize) else {
                return false;
            };
            let Some(actual_tc_id) = resolve_typeclass_constraint(var_type.as_ref(), query_context)
            else {
                return false;
            };
            return typeclass_binding_is_compatible(actual_tc_id, *tc_id, kernel_context);
        }
        return false;
    }

    // Special case: pattern variable type is a type variable (FreeVariable)
    // E.g., x1: x0 where x0 is a type variable. We need to check if bound_type
    // is compatible with x0's constraints.
    if let Decomposition::Atom(KernelAtom::FreeVariable(var_id)) =
        pattern_var_type.as_ref().decompose()
    {
        // Look up what x0's type is (should be a typeclass like Ring, or Type)
        if let Some(var_type) = pattern_context.get_var_type(*var_id as usize) {
            if let Decomposition::Atom(KernelAtom::Symbol(Symbol::Typeclass(tc_id))) =
                var_type.as_ref().decompose()
            {
                // bound_type should implement this typeclass
                if let Some(ground_id) = bound_type.as_ref().as_type_atom() {
                    // is_instance_of handles both explicit instances and arbitrary types with
                    // compatible typeclass constraints
                    return kernel_context.type_store.is_instance_of(ground_id, *tc_id);
                }
                if let Some(bound_var_id) = bound_type.as_ref().atomic_variable() {
                    let Some(bound_var_type) = query_context.get_var_type(bound_var_id as usize)
                    else {
                        return false;
                    };
                    let Some(actual_tc_id) =
                        resolve_typeclass_constraint(bound_var_type.as_ref(), query_context)
                    else {
                        return false;
                    };
                    return typeclass_binding_is_compatible(actual_tc_id, *tc_id, kernel_context);
                }
                return false;
            }
            // If x0's type is Type/TypeSort (not a typeclass constraint), check universe level.
            // x0: TypeSort means x0 is a type variable that can be bound to types like Foo, Nat.
            // For a value x1: x0 to match bound_term, bound_type must be a concrete type
            // (like Foo), NOT TypeSort itself.
            //
            // Example:
            // - c1: Foo where Foo: TypeSort → bound_type = Foo → valid (c1 is a value)
            // - Foo: TypeSort → bound_type = TypeSort → invalid (Foo is a type, not a value)
            if matches!(
                var_type.as_ref().decompose(),
                Decomposition::Atom(KernelAtom::Symbol(Symbol::Type0))
            ) {
                // Reject if bound_type IS TypeSort (meaning bound_term is a type, not a value)
                if matches!(
                    bound_type.as_ref().decompose(),
                    Decomposition::Atom(KernelAtom::Symbol(Symbol::Type0))
                ) {
                    return false; // Reject: bound_term is a type, not a value
                }
                return true; // Accept: bound_type is a concrete type like Foo
            }
        }
        // Otherwise, try regular unification
    }

    // Use Unifier to check if bound_type is an instance of pattern_var_type
    // This handles cases like List[Int] matching List[T] where T is a type variable
    let mut unifier = Unifier::new(3, kernel_context);
    unifier.set_input_context(Scope::LEFT, pattern_context);
    unifier.set_input_context(Scope::RIGHT, query_context);

    // Try to unify pattern_var_type (LEFT) with bound_type (RIGHT)
    unifier.unify(Scope::LEFT, pattern_var_type, Scope::RIGHT, &bound_type)
}

/// Matches a sequence of terms against patterns in the trie.
///
/// This matches purely on structure (ignoring types).
/// After finding a structural match, it verifies type compatibility.
///
/// The key insight is that we navigate the trie by trying different edges:
/// - Variable(n) edges represent pattern variables that can match any query term
/// - Structural edges (Application, Symbol atoms) must match the query term exactly
fn find_matches_while<'a, F>(
    subtrie: &SubTrie<Vec<u8>, usize>,
    key: &mut Vec<u8>,
    terms: &[TermRef<'a>],
    local_context: &LocalContext,
    kernel_context: &KernelContext,
    all_metadata: &[PatternMetadata],
    stack_limit: usize,
    replacements: &mut Vec<TermRef<'a>>,
    callback: &mut F,
) -> bool
where
    F: FnMut(usize, &Vec<TermRef<'a>>) -> bool,
{
    if subtrie.is_empty() {
        return true;
    }

    if stack_limit == 0 {
        let warning_index = STACK_LIMIT_WARNING_COUNT.fetch_add(1, Ordering::Relaxed);
        if let Some(message) = stack_limit_warning_message(warning_index) {
            eprintln!("{}", message);
        }
        return false;
    }

    if terms.is_empty() {
        match subtrie.get(key as &[u8]) {
            Some(value_id) => {
                // Structural match found - verify type compatibility
                let metadata = &all_metadata[*value_id];
                if verify_type_compatibility(replacements, metadata, local_context, kernel_context)
                {
                    return callback(*value_id, replacements);
                }
                return true; // Type mismatch, continue searching
            }
            None => {
                let (sample, _) = subtrie.iter().next().unwrap();
                panic!(
                    "\nPDT key mismatch.\nquerying: {}\nexisting: {}\n",
                    Edge::debug_bytes(key),
                    Edge::debug_bytes(sample)
                );
            }
        }
    }

    let initial_key_len = key.len();
    let first = terms[0];
    let rest = &terms[1..];

    // Case 1: the first query term could match an existing replacement (backreference)
    // This means the pattern has Variable(i) where i is an already-bound variable
    for i in 0..replacements.len() {
        if first == replacements[i] {
            Edge::Atom(Atom::Variable(i as u16)).append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);
            if !new_subtrie.is_empty() {
                if !find_matches_while(
                    &new_subtrie,
                    key,
                    rest,
                    local_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
            key.truncate(initial_key_len);
        }
    }

    // Case 2: the first query term could match a new pattern variable
    // This means the pattern has Variable(n) where n is the next new variable
    {
        Edge::Atom(Atom::Variable(replacements.len() as u16)).append_to(key);
        let new_subtrie = subtrie.subtrie(key as &[u8]);
        if !new_subtrie.is_empty() {
            replacements.push(first);
            if !find_matches_while(
                &new_subtrie,
                key,
                rest,
                local_context,
                kernel_context,
                all_metadata,
                stack_limit - 1,
                replacements,
                callback,
            ) {
                return false;
            }
            replacements.pop();
        }
        key.truncate(initial_key_len);
    }

    // Case 3: structural match - the pattern has the same structure as the query
    // FreeVariables in the query should only match via Cases 1/2 (pattern variables),
    // not via structural matching. All Variables in patterns are wildcards.
    match first.decompose() {
        Decomposition::Atom(atom) => {
            let edge_atom = match atom {
                KernelAtom::FreeVariable(_) => {
                    // Query has a variable - it can only match pattern variables via Cases 1/2
                    // Skip structural matching for FreeVariables
                    None
                }
                KernelAtom::BoundVariable(i) => Some(Atom::BoundVariable(*i)),
                KernelAtom::Symbol(Symbol::True) => Some(Atom::True),
                KernelAtom::Symbol(Symbol::False) => Some(Atom::False),
                KernelAtom::Symbol(Symbol::Typeclass(_)) => return true, // Skip typeclasses in structure
                KernelAtom::Symbol(s) => Some(Atom::Symbol(*s)),
            };
            if let Some(edge_atom) = edge_atom {
                Edge::Atom(edge_atom).append_to(key);
                let new_subtrie = subtrie.subtrie(key as &[u8]);
                if !new_subtrie.is_empty() {
                    if !find_matches_while(
                        &new_subtrie,
                        key,
                        rest,
                        local_context,
                        kernel_context,
                        all_metadata,
                        stack_limit - 1,
                        replacements,
                        callback,
                    ) {
                        return false;
                    }
                }
            }
        }
        Decomposition::Application(func, arg) => {
            Edge::Application.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            if !new_subtrie.is_empty() {
                // Build new terms: [func, arg, ...rest]
                let mut new_terms: Vec<TermRef<'a>> = Vec::with_capacity(2 + rest.len());
                new_terms.push(func);
                new_terms.push(arg);
                new_terms.extend_from_slice(rest);

                if !find_matches_while(
                    &new_subtrie,
                    key,
                    &new_terms,
                    local_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
        }
        Decomposition::Pi(input, output) => {
            // Pi types can appear as values when polymorphic functions are applied to function types
            // e.g., id[Bool -> Bool](not) has (Bool -> Bool) as a subterm
            Edge::Arrow.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            if !new_subtrie.is_empty() {
                // Build new terms: [input, output, ...rest]
                let mut new_terms: Vec<TermRef<'a>> = Vec::with_capacity(2 + rest.len());
                new_terms.push(input);
                new_terms.push(output);
                new_terms.extend_from_slice(rest);

                let mut extended_context = local_context.clone();
                extended_context.push_type(input.to_owned());
                if !find_matches_while(
                    &new_subtrie,
                    key,
                    &new_terms,
                    &extended_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
        }
        Decomposition::Lambda(input, body) => {
            Edge::Lambda.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            if !new_subtrie.is_empty() {
                let mut new_terms: Vec<TermRef<'a>> = Vec::with_capacity(2 + rest.len());
                new_terms.push(input);
                new_terms.push(body);
                new_terms.extend_from_slice(rest);

                let mut extended_context = local_context.clone();
                extended_context.push_type(input.to_owned());
                if !find_matches_while(
                    &new_subtrie,
                    key,
                    &new_terms,
                    &extended_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
        }
        Decomposition::ForAll(binder_type, body) => {
            Edge::ForAll.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            if !new_subtrie.is_empty() {
                let mut new_terms: Vec<TermRef<'a>> = Vec::with_capacity(2 + rest.len());
                new_terms.push(binder_type);
                new_terms.push(body);
                new_terms.extend_from_slice(rest);

                let mut extended_context = local_context.clone();
                extended_context.push_type(binder_type.to_owned());
                if !find_matches_while(
                    &new_subtrie,
                    key,
                    &new_terms,
                    &extended_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
        }
        Decomposition::Exists(binder_type, body) => {
            Edge::Exists.append_to(key);
            let new_subtrie = subtrie.subtrie(key as &[u8]);

            if !new_subtrie.is_empty() {
                let mut new_terms: Vec<TermRef<'a>> = Vec::with_capacity(2 + rest.len());
                new_terms.push(binder_type);
                new_terms.push(body);
                new_terms.extend_from_slice(rest);

                let mut extended_context = local_context.clone();
                extended_context.push_type(binder_type.to_owned());
                if !find_matches_while(
                    &new_subtrie,
                    key,
                    &new_terms,
                    &extended_context,
                    kernel_context,
                    all_metadata,
                    stack_limit - 1,
                    replacements,
                    callback,
                ) {
                    return false;
                }
            }
        }
    }

    key.truncate(initial_key_len);
    true
}

/// Verify that the replacements have types compatible with the pattern variables.
fn verify_type_compatibility(
    replacements: &[TermRef],
    metadata: &PatternMetadata,
    query_context: &LocalContext,
    kernel_context: &KernelContext,
) -> bool {
    let pattern_var_types = metadata.context.get_var_types();
    for (i, &replacement) in replacements.iter().enumerate() {
        if replacement.to_owned().has_escaping_bound_variable() {
            // Pattern variables may not bind to terms that depend on an ambient binder
            // outside the matched subterm.
            return false;
        }
        if i >= pattern_var_types.len() {
            // Pattern didn't have this many variables - that's fine
            continue;
        }
        let Some(pattern_var_type) = &pattern_var_types[i] else {
            continue;
        };
        if !types_compatible(
            replacement,
            pattern_var_type,
            &metadata.context,
            query_context,
            kernel_context,
        ) {
            return false;
        }
    }
    true
}

/// Replaces variables in a term with corresponding replacement terms.
///
/// This function takes a term with pattern variables and replaces each variable
/// with the corresponding replacement term. Variables that don't have a replacement
/// are shifted by the `shift` amount (if provided).
///
/// Returns the replaced term and an updated local context with the types of any
/// shifted variables.
pub fn replace_term_variables(
    term: &Term,
    term_context: &LocalContext,
    replacements: &[TermRef],
    replacement_context: &LocalContext,
    shift: Option<AtomId>,
) -> (Term, LocalContext) {
    let mut output_context = replacement_context.clone();

    fn replace_recursive(
        term: TermRef,
        term_context: &LocalContext,
        replacements: &[TermRef],
        shift: Option<AtomId>,
        output_context: &mut LocalContext,
    ) -> Term {
        match term.decompose() {
            Decomposition::Atom(KernelAtom::FreeVariable(var_id)) => {
                let idx = *var_id as usize;
                let has_replacement =
                    idx < replacements.len() && output_context.get_var_type(idx).is_some();
                if has_replacement {
                    // Replace with the replacement term
                    replacements[idx].to_owned()
                } else {
                    // Shift the variable
                    let new_var_id = match shift {
                        Some(s) => *var_id + s,
                        None => panic!("no replacement for variable x{}", var_id),
                    };
                    // Track the type for the shifted variable
                    let new_idx = new_var_id as usize;
                    let var_type = term_context
                        .get_var_type(idx)
                        .cloned()
                        .expect("variable type not found in term_context");
                    output_context.set_type(new_idx, var_type);
                    Term::atom(KernelAtom::FreeVariable(new_var_id))
                }
            }
            Decomposition::Atom(_) => term.to_owned(),
            Decomposition::Application(func, arg) => {
                let replaced_func =
                    replace_recursive(func, term_context, replacements, shift, output_context);
                let replaced_arg =
                    replace_recursive(arg, term_context, replacements, shift, output_context);
                replaced_func.apply(&[replaced_arg])
            }
            Decomposition::Pi(input, output) => {
                let replaced_input =
                    replace_recursive(input, term_context, replacements, shift, output_context);
                let replaced_output =
                    replace_recursive(output, term_context, replacements, shift, output_context);
                Term::pi(replaced_input, replaced_output)
            }
            Decomposition::Lambda(input, body) => {
                let replaced_input =
                    replace_recursive(input, term_context, replacements, shift, output_context);
                let replaced_body =
                    replace_recursive(body, term_context, replacements, shift, output_context);
                Term::lambda(replaced_input, replaced_body)
            }
            Decomposition::ForAll(binder_type, body) => {
                let replaced_binder_type = replace_recursive(
                    binder_type,
                    term_context,
                    replacements,
                    shift,
                    output_context,
                );
                let replaced_body =
                    replace_recursive(body, term_context, replacements, shift, output_context);
                Term::forall(replaced_binder_type, replaced_body)
            }
            Decomposition::Exists(binder_type, body) => {
                let replaced_binder_type = replace_recursive(
                    binder_type,
                    term_context,
                    replacements,
                    shift,
                    output_context,
                );
                let replaced_body =
                    replace_recursive(body, term_context, replacements, shift, output_context);
                Term::exists(replaced_binder_type, replaced_body)
            }
        }
    }

    let result_term = replace_recursive(
        term.as_ref(),
        term_context,
        replacements,
        shift,
        &mut output_context,
    );
    (result_term, output_context)
}

/// Substitutes variables in a term using explicit binding and remapping maps.
///
/// - `bindings`: Maps pattern variable IDs to their replacement terms (concrete values or types)
/// - `var_remap`: Maps unbound pattern variable IDs to new output variable IDs
///
/// Every variable in the term must be either in bindings or var_remap.
pub fn substitute_term(
    term: &Term,
    bindings: &HashMap<AtomId, Term>,
    var_remap: &HashMap<AtomId, AtomId>,
) -> Term {
    fn substitute_recursive(
        term: TermRef,
        bindings: &HashMap<AtomId, Term>,
        var_remap: &HashMap<AtomId, AtomId>,
    ) -> Term {
        match term.decompose() {
            Decomposition::Atom(KernelAtom::FreeVariable(var_id)) => {
                if let Some(replacement) = bindings.get(var_id) {
                    replacement.clone()
                } else if let Some(&new_var_id) = var_remap.get(var_id) {
                    Term::atom(KernelAtom::FreeVariable(new_var_id))
                } else {
                    panic!(
                        "Variable x{} has no binding or remap. Bindings: {:?}, Remap: {:?}",
                        var_id,
                        bindings.keys().collect::<Vec<_>>(),
                        var_remap
                    );
                }
            }
            Decomposition::Atom(_) => term.to_owned(),
            Decomposition::Application(func, arg) => {
                let new_func = substitute_recursive(func, bindings, var_remap);
                let new_arg = substitute_recursive(arg, bindings, var_remap);
                new_func.apply(&[new_arg])
            }
            Decomposition::Pi(input, output) => {
                let new_input = substitute_recursive(input, bindings, var_remap);
                let new_output = substitute_recursive(output, bindings, var_remap);
                Term::pi(new_input, new_output)
            }
            Decomposition::Lambda(input, body) => {
                let new_input = substitute_recursive(input, bindings, var_remap);
                let new_body = substitute_recursive(body, bindings, var_remap);
                Term::lambda(new_input, new_body)
            }
            Decomposition::ForAll(binder_type, body) => {
                let new_binder_type = substitute_recursive(binder_type, bindings, var_remap);
                let new_body = substitute_recursive(body, bindings, var_remap);
                Term::forall(new_binder_type, new_body)
            }
            Decomposition::Exists(binder_type, body) => {
                let new_binder_type = substitute_recursive(binder_type, bindings, var_remap);
                let new_body = substitute_recursive(body, bindings, var_remap);
                Term::exists(new_binder_type, new_body)
            }
        }
    }

    substitute_recursive(term.as_ref(), bindings, var_remap)
}

/// Computes the var_remap and output context for unbound variables.
///
/// Given:
/// - `output_term`: The term we're substituting into
/// - `pattern_context`: Types of pattern variables
/// - `bindings`: Already-known bindings for pattern variables
/// - `start_var_id`: The first variable ID to use for new output variables
///
/// Returns:
/// - `var_remap`: Maps unbound pattern var IDs to new output var IDs
/// - `output_context`: LocalContext with types for the new output variables
///
/// Variables are ordered so that type dependencies come first (type variables before
/// variables whose type references other variables).
pub fn compute_unbound_var_remap(
    output_term: &Term,
    pattern_context: &LocalContext,
    base_context: &LocalContext,
    bindings: &HashMap<AtomId, Term>,
    start_var_id: AtomId,
) -> (HashMap<AtomId, AtomId>, LocalContext) {
    // Collect all variables in the output term
    let mut unbound_vars: Vec<AtomId> = Vec::new();
    for atom in output_term.iter_atoms() {
        if let super::atom::Atom::FreeVariable(var_id) = atom {
            if !bindings.contains_key(var_id) && !unbound_vars.contains(var_id) {
                unbound_vars.push(*var_id);
            }
        }
    }

    if unbound_vars.is_empty() {
        return (HashMap::new(), base_context.clone());
    }

    // Sort unbound variables by type dependency:
    // Type variables (those with type=Type) come before value variables
    // (those whose type references other variables)
    let is_type0 = |t: &Term| -> bool {
        matches!(
            t.as_ref().decompose(),
            Decomposition::Atom(KernelAtom::Symbol(Symbol::Type0))
        )
    };

    // Partition into type vars and value vars
    let mut type_vars: Vec<AtomId> = Vec::new();
    let mut value_vars: Vec<AtomId> = Vec::new();
    for var_id in &unbound_vars {
        if let Some(var_type) = pattern_context.get_var_type(*var_id as usize) {
            if is_type0(var_type) {
                type_vars.push(*var_id);
            } else {
                value_vars.push(*var_id);
            }
        } else {
            // No type info, treat as value var
            value_vars.push(*var_id);
        }
    }

    // Build var_remap: type vars first, then value vars
    // Start from start_var_id to avoid conflicts with existing variables
    let mut var_remap: HashMap<AtomId, AtomId> = HashMap::new();
    let mut next_output_var: AtomId = start_var_id;

    for var_id in &type_vars {
        var_remap.insert(*var_id, next_output_var);
        next_output_var += 1;
    }
    for var_id in &value_vars {
        var_remap.insert(*var_id, next_output_var);
        next_output_var += 1;
    }

    // Build output context: start from existing local types and then add new variables.
    let mut output_context = base_context.clone();

    // Process in order of output var ID (type vars first, so dependencies are satisfied)
    let mut ordered_vars: Vec<(AtomId, AtomId)> = var_remap.iter().map(|(&k, &v)| (k, v)).collect();
    ordered_vars.sort_by_key(|(_, output_id)| *output_id);

    for (pattern_var, output_var) in ordered_vars {
        if let Some(pattern_type) = pattern_context.get_var_type(pattern_var as usize) {
            // Substitute into the type using bindings and var_remap
            let output_type = substitute_term(pattern_type, bindings, &var_remap);
            output_context.set_type(output_var as usize, output_type);
        }
    }

    (var_remap, output_context)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::atom::Atom as KernelAtom;
    use crate::kernel::literal::Literal;

    #[test]
    fn test_stack_limit_warning_message_is_capped() {
        assert_eq!(
            stack_limit_warning_message(0),
            Some("WARNING: PDT stack_limit exhausted - consider increasing the limit")
        );
        assert_eq!(
            stack_limit_warning_message(MAX_STACK_LIMIT_WARNINGS - 1),
            Some("WARNING: PDT stack_limit exhausted - consider increasing the limit")
        );
        assert_eq!(
            stack_limit_warning_message(MAX_STACK_LIMIT_WARNINGS),
            Some("WARNING: PDT stack_limit exhausted - subsequent warnings silenced")
        );
        assert_eq!(
            stack_limit_warning_message(MAX_STACK_LIMIT_WARNINGS + 1),
            None
        );
    }

    #[test]
    fn test_edge_roundtrip() {
        // Edges with 3-byte encoding
        let edges_3_bytes = vec![
            Edge::Application,
            Edge::Arrow,
            Edge::LiteralForm(true),
            Edge::LiteralForm(false),
            Edge::Atom(Atom::Variable(0)),
            Edge::Atom(Atom::Variable(42)),
            Edge::Atom(Atom::True),
            Edge::Atom(Atom::False),
            Edge::Atom(Atom::Symbol(Symbol::ScopedConstant(20))),
        ];

        for edge in edges_3_bytes {
            let mut bytes = Vec::new();
            edge.append_to(&mut bytes);
            assert_eq!(bytes.len(), 3, "expected 3 bytes for {:?}", edge);
            let (parsed, consumed) = Edge::from_bytes(&bytes);
            assert_eq!(consumed, 3);
            assert_eq!(edge, parsed, "roundtrip failed for {:?}", edge);
        }

        // Edges with 5-byte encoding (module-scoped)
        let edges_5_bytes = vec![Edge::Atom(Atom::Symbol(Symbol::GlobalConstant(
            ModuleId(5),
            10,
        )))];

        for edge in edges_5_bytes {
            let mut bytes = Vec::new();
            edge.append_to(&mut bytes);
            assert_eq!(bytes.len(), 5, "expected 5 bytes for {:?}", edge);
            let (parsed, consumed) = Edge::from_bytes(&bytes);
            assert_eq!(consumed, 5);
            assert_eq!(edge, parsed, "roundtrip failed for {:?}", edge);
        }
    }

    #[test]
    fn test_pdt_insert_and_find_clause() {
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern: x0 = x0
        let clause = kctx.parse_clause("x0 = x0", &["Bool"]);
        tree.insert_clause(&clause, 42);

        // Query: c5 = c5 should match
        kctx.parse_constant("c5", "Bool");
        let special = kctx.parse_clause("c5 = c5", &[]);
        let found = tree.find_clause(&special, &kctx);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_pdt_variable_matching() {
        // Test that patterns with variables match concrete terms
        let mut kctx = KernelContext::new();
        kctx.parse_constants(&["c0", "c1", "c2", "c3", "c4"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern "x0 = c0" - a variable equals a constant
        let pattern_left = Term::parse("x0");
        let pattern_right = Term::parse("c0");
        tree.insert_pair(&pattern_left, &pattern_right, 7, &lctx);

        // Query "c1 = c0" should match (c1 can be matched by variable x0)
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c1");
        let query_right = Term::parse("c0");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);
        assert_eq!(found, Some(&7));
    }

    #[test]
    fn test_pdt_application() {
        // Test that patterns with function applications and variables match correctly
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");
        let lctx = kctx.parse_local(&["Bool"]);

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern "c1(x0) = c5" - a function applied to a variable equals a constant
        let pattern_left = Term::parse("c1(x0)");
        let pattern_right = Term::parse("c5");
        tree.insert_pair(&pattern_left, &pattern_right, 42, &lctx);

        // Query "c1(c6) = c5" should match (c6 : Bool can be matched by variable x0)
        let query_lctx = kctx.parse_local(&[]);
        let query_left = Term::parse("c1(c6)");
        let query_right = Term::parse("c5");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);
        assert_eq!(found, Some(&42));
    }

    #[test]
    fn test_pdt_polymorphic_clause_matching() {
        // Test: Pattern is `add[R](x, y) = add[R](y, x)` for any R: Ring
        // Query is `add[Int](c, f(d)) = add[Int](f(d), c)` where Int: Ring
        // The query should match the pattern.

        let mut kctx = KernelContext::new();

        // Register Ring typeclass and mark Int as implementing Ring
        kctx.parse_typeclass("Ring").parse_instance("Int", "Ring");

        // Create `add` with polymorphic type: Π(R: Ring). R -> R -> R
        kctx.parse_polymorphic_constant("c0", "R: Ring", "R -> R -> R"); // add

        // Create constants for the query
        kctx.parse_constant("c1", "Int -> Int"); // f
        kctx.parse_constants(&["c2", "c3"], "Int"); // c, d

        // Pattern clause: add[R](x, y) = add[R](y, x)
        // x0: Ring (type variable R), x1: x0 (value x), x2: x0 (value y)
        let pattern_clause =
            kctx.parse_clause("c0(x0, x1, x2) = c0(x0, x2, x1)", &["Ring", "x0", "x0"]);

        // Insert pattern into tree
        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_clause(&pattern_clause, "commutativity");

        // Query clause: add[Int](c, f(d)) = add[Int](f(d), c)
        let query_clause = kctx.parse_clause("c0(Int, c2, c1(c3)) = c0(Int, c1(c3), c2)", &[]);

        // Try to find the pattern
        let found = tree.find_clause(&query_clause, &kctx);

        assert_eq!(
            found,
            Some(&"commutativity"),
            "Query should match the polymorphic commutativity pattern"
        );
    }

    #[test]
    fn test_pdt_parameterized_type_matching() {
        // Tests that types_compatible() handles type instantiation correctly.
        //
        // Pattern: reverse(x) = x where x : List[T] (T is a type variable)
        // Query: reverse(mylist) = mylist where mylist : List[Int]
        //
        // The pattern variable x has type List[T] (a parameterized type with type variable).
        // The query term mylist has type List[Int] (a concrete instantiation).
        //
        // For this to match, we need to recognize that List[Int] is an instance of List[T]
        // by binding T -> Int. The current simple equality check fails because:
        // - List[T] != List[Int]
        // - List[T] is not a FreeVariable atom (it's an Application)

        let mut kctx = KernelContext::new();

        // Set up types
        kctx.parse_datatype("Int");
        kctx.parse_type_constructor("List", 1);

        // reverse : forall T. List[T] -> List[T]
        kctx.parse_polymorphic_constant("c0", "T: Type", "List[T] -> List[T]"); // reverse

        // mylist : List[Int]
        kctx.parse_constant("c1", "List[Int]"); // mylist

        let mut tree: Pdt<&str> = Pdt::new();

        // Pattern clause: reverse[T](x) = x where T: Type, x : List[T]
        // x0 is a type variable T (type: Type)
        // x1 has type List[x0] = List[T]
        let pattern_clause = kctx.parse_clause("c0(x0, x1) = x1", &["Type", "List[x0]"]);
        tree.insert_clause(&pattern_clause, "reverse_identity");

        // Query clause: reverse[Int](mylist) = mylist where mylist : List[Int]
        let query_clause = kctx.parse_clause("c0(Int, c1) = c1", &[]);

        let found = tree.find_clause(&query_clause, &kctx);

        // This should match with T -> Int, x -> mylist
        // Currently fails because List[T] != List[Int] and we don't do type instantiation
        assert_eq!(
            found,
            Some(&"reverse_identity"),
            "Query with List[Int] should match pattern with List[T]"
        );
    }

    #[test]
    fn test_pdt_query_variable_matches_pattern_variable() {
        // Tests that a FreeVariable in the query can match a pattern variable,
        // even when the variable IDs differ.
        //
        // This test uses find_term_matches_while directly to avoid clause normalization.
        //
        // Pattern: c0(x0) where x0 is variable 0
        // Query: c0(x1) where x1 is variable 1 (different ID)
        //
        // The pattern variable x0 should match the query's FreeVariable x1.

        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "Bool -> Bool");

        // Pattern: c0(x0) with x0 : Bool (variable ID 0)
        let pattern_lctx = kctx.parse_local(&["Bool"]);
        let pattern_term = Term::parse("c0(x0)");

        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_pair(&pattern_term, &Term::new_true(), "pattern", &pattern_lctx);

        // Query: c0(x1) with x1 as variable ID 1 (different from pattern's x0)
        // We create a context where x0 is unused and x1 is Bool
        let query_lctx = kctx.parse_local(&["Bool", "Bool"]);
        // Build c0(x1) manually: apply c0 to FreeVariable(1)
        let x1 = Term::atom(KernelAtom::FreeVariable(1));
        let query_term = Term::parse("c0").apply(&[x1]);

        let mut key = Vec::new();
        let mut replacements = vec![];
        let mut found = false;

        tree.find_term_matches_while(
            &mut key,
            &[query_term.as_ref(), Term::new_true().as_ref()],
            &query_lctx,
            &kctx,
            &mut replacements,
            &mut |_value_id, _replacements| {
                found = true;
                true
            },
        );

        assert!(
            found,
            "Pattern c0(x0) should match query c0(x1) even with different variable IDs"
        );
    }

    #[test]
    fn test_pdt_pi_type_as_value() {
        // Tests that PDT can handle Pi types (function types) appearing as values.
        //
        // Example: A polymorphic function `id[T](x: T) -> T` applied to a function type:
        //   id[Bool -> Bool](not)
        //
        // The type argument `Bool -> Bool` is a Pi type appearing as a VALUE,
        // not just as a type annotation.

        let mut kctx = KernelContext::new();

        // Create a polymorphic function that takes a type argument
        // c0 : Type -> Bool (takes a type, returns Bool)
        kctx.parse_constant("c0", "Type -> Bool");

        // Pattern: c0(x0) where x0 : Type (x0 is a type variable)
        let pattern_lctx = kctx.parse_local(&["Type"]);
        let pattern_term = kctx.parse_term("c0(x0)");

        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_pair(&pattern_term, &Term::new_true(), "pattern", &pattern_lctx);

        // Query: c0(Bool -> Bool) - applying to a function type (Pi type)
        // Use parse_type to create the function type properly
        let func_type = kctx.parse_type("Bool -> Bool");

        // Now apply c0 to this function type
        let c0 = kctx.parse_term("c0");
        let query_term = c0.apply(&[func_type]);
        let query_lctx = kctx.parse_local(&[]);

        let mut key = Vec::new();
        let mut replacements = vec![];
        let mut found = false;

        tree.find_term_matches_while(
            &mut key,
            &[query_term.as_ref(), Term::new_true().as_ref()],
            &query_lctx,
            &kctx,
            &mut replacements,
            &mut |_value_id, _replacements| {
                found = true;
                true
            },
        );

        // This should match: pattern variable x0 (of type Type) matches the Pi type Bool -> Bool
        assert!(
            found,
            "Pattern c0(x0: Type) should match query c0(Bool -> Bool)"
        );
    }

    #[test]
    fn test_pdt_curried_variable_matches_partial_application() {
        // Test that PDT can match a partial application against a function variable.
        // This is a key capability of curried representation.
        //
        // c0 : (Bool, Bool) -> Bool (2-arg function)
        // c1 : Bool -> Bool (1-arg function)
        // c5, c6 : Bool
        //
        // Pattern: x0(c6) where x0 : Bool -> Bool
        // Query: c0(c5, c6) = ((Bool, Bool) -> Bool)(Bool, Bool) = Bool
        //
        // In curried form:
        // - c0(c5, c6) becomes Application(Application(c0, c5), c6)
        // - x0(c6) becomes Application(x0, c6)
        //
        // The match should succeed with x0 = c0(c5), which has type Bool -> Bool.
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool, Bool) -> Bool")
            .parse_constant("c1", "Bool -> Bool")
            .parse_constants(&["c5", "c6"], "Bool");

        // x0: Bool -> Bool
        let lctx = kctx.parse_local(&["Bool -> Bool"]);

        let mut tree: Pdt<usize> = Pdt::new();

        // Insert pattern: x0(c6) = c5
        let pattern_left = kctx.parse_term("x0(c6)");
        let pattern_right = kctx.parse_term("c5");
        tree.insert_pair(&pattern_left, &pattern_right, 42, &lctx);

        // First verify that the partial application c0(c5) has type Bool -> Bool
        let partial_app = kctx.parse_term("c0(c5)");
        let partial_type = partial_app.get_type_with_context(&lctx, &kctx);
        let x0_type = lctx.get_var_type(0);
        assert_eq!(
            partial_type,
            *x0_type.unwrap(),
            "c0(c5) should have the same type as x0 (Bool -> Bool)"
        );

        // Query: c0(c5, c6) = c5
        // c0(c5) is a partial application of type Bool -> Bool, which should match x0
        let query_lctx = kctx.parse_local(&[]);
        let query_left = kctx.parse_term("c0(c5, c6)");
        let query_right = kctx.parse_term("c5");
        let found = tree.find_pair(&query_left, &query_right, &query_lctx, &kctx);

        // The PDT should find this match because:
        // - c0(c5, c6) curries to Application(Application(c0, c5), c6)
        // - Pattern x0(c6) curries to Application(x0, c6)
        // - x0 (a variable of type Bool -> Bool) can match Application(c0, c5)
        assert_eq!(
            found,
            Some(&42),
            "Curried matching should allow variable to match partial application"
        );
    }

    #[test]
    fn test_pdt_structural_variable_ordering() {
        // This test verifies that variables are numbered by structural occurrence
        // for PDT matching, using GeneralizationSet which applies the normalization.
        //
        // The key insight: when a type variable (T: Type) appears as an argument
        // in a function call, it appears STRUCTURALLY and should be numbered by
        // its position in the clause, not pushed to the end.

        use crate::kernel::generalization_set::GeneralizationSet;

        let mut kctx = KernelContext::new();

        // Set up: Foo is a concrete type, g1 is polymorphic.
        // Avoid names like T0 here because the kernel test parser reserves that syntax for
        // type variables.
        kctx.parse_datatype("Foo");
        kctx.parse_polymorphic_constant("g1", "T: Type", "(T, T) -> Bool");
        kctx.parse_constants(&["c1", "c2"], "Foo");

        let mut gset = GeneralizationSet::new();

        // Pattern: g1(T, x, y) where T: Type, x: T, y: T
        // Structural order: T appears first as arg to g1, then x, then y
        // After normalization: T->x0, x->x1, y->x2
        let pattern_clause = kctx.parse_clause("g1(x0, x1, x2)", &["Type", "x0", "x0"]);
        gset.insert(pattern_clause, 42, &kctx);

        // Query: g1(Foo, c1, c2) - concrete instantiation
        // Should match with T->Foo, x->c1, y->c2
        let query_clause = kctx.parse_clause("g1(Foo, c1, c2)", &[]);
        let found = gset.find_generalization(query_clause, &kctx);

        assert_eq!(
            found,
            Some(42),
            "Pattern with type variable as first arg should match concrete query"
        );
    }

    #[test]
    fn test_pdt_type_level_term_should_not_match_value_pattern_variable() {
        // Tests that a type-level term should NOT match a pattern variable of type x0
        // where x0: Type (i.e., a value-level pattern variable).
        //
        // Pattern: c0(x0, x1) where x0: Type, x1: x0
        //          x0 is a type variable, x1 is a VALUE of type x0
        // Query:   c0(Foo, Foo) where Foo: Type
        //          The second Foo is a TYPE, not a value!
        //
        // This should NOT match because:
        // - x1 is a value pattern variable (x1: x0)
        // - Foo (query's second arg) is a type (Foo: Type)
        // - Types cannot match value pattern variables

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");

        // c0 : forall T: Type. T -> Bool
        kctx.parse_polymorphic_constant("c0", "T: Type", "T -> Bool");

        // Pattern: c0(x0, x1) where x0: Type, x1: x0
        let pattern_lctx = kctx.parse_local(&["Type", "x0"]);
        let pattern_term = kctx.parse_term("c0(x0, x1)");

        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_pair(&pattern_term, &Term::new_true(), "pattern", &pattern_lctx);

        // Query: c0(Foo, Foo) where first Foo is type arg, second Foo is... also Foo (a type!)
        // This is a type-level query: we're using Foo (a type) where a value is expected.
        let query_lctx = LocalContext::empty();
        let query_term = kctx.parse_term("c0(Foo, Foo)");

        let mut key = Vec::new();
        let mut replacements = vec![];
        let mut found = false;

        tree.find_term_matches_while(
            &mut key,
            &[query_term.as_ref(), Term::new_true().as_ref()],
            &query_lctx,
            &kctx,
            &mut replacements,
            &mut |_value_id, _replacements| {
                found = true;
                true
            },
        );

        // The second Foo (a type) should NOT match x1 (a value of type x0).
        assert!(
            !found,
            "Type-level term Foo should NOT match value pattern variable x1: x0"
        );
    }

    #[test]
    fn test_literal_set_rejects_specialization_to_escaping_bound_variable() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("c0", "(Bool -> Bool) -> Bool");

        let mut literals = LiteralSet::new();
        let pattern_context = LocalContext::from_types(vec![Term::bool_type()]);
        let pattern = Literal::positive(
            Term::parse("c0").apply(&[Term::lambda(Term::bool_type(), Term::new_variable(0))]),
        );
        literals.insert(&pattern, 0, &pattern_context);

        let query_context = LocalContext::empty();
        let query = Literal::positive(Term::parse("c0").apply(&[Term::lambda(
            Term::bool_type(),
            Term::atom(KernelAtom::BoundVariable(0)),
        )]));

        assert_eq!(
            literals.find_generalization_with_map(&query, &query_context, &kctx),
            None,
            "free pattern variables should not bind to escaping bound variables"
        );
    }

    #[test]
    fn test_pdt_typesort_should_not_match_type_variable() {
        // Tests that TypeSort (Type itself) should NOT match a pattern type variable.
        //
        // Pattern: c0(x0) where x0: Type (TypeSort)
        //          x0 is a type variable that can be bound to types like Foo, Nat
        // Query:   c0(Type) where Type is the type of types (TypeSort)
        //
        // This should NOT match because:
        // - x0: TypeSort means x0 is expected to be a concrete type like Foo
        // - Type (TypeSort) is the meta-type, not a concrete type
        // - Allowing this would cause universe polymorphism issues

        let mut kctx = KernelContext::new();
        kctx.parse_datatype("Foo");

        // c0 : forall T: Type. T -> Bool
        kctx.parse_polymorphic_constant("c0", "T: Type", "T -> Bool");

        // Pattern: c0(x0) where x0: Type (TypeSort)
        let pattern_lctx = kctx.parse_local(&["Type"]);
        let pattern_term = kctx.parse_term("c0(x0)");

        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_pair(&pattern_term, &Term::new_true(), "pattern", &pattern_lctx);

        // Query: c0(Type) where Type is TypeSort
        let query_lctx = LocalContext::empty();
        let query_term = kctx.parse_term("c0(Type)");

        let mut key = Vec::new();
        let mut replacements = vec![];
        let mut found = false;

        tree.find_term_matches_while(
            &mut key,
            &[query_term.as_ref(), Term::new_true().as_ref()],
            &query_lctx,
            &kctx,
            &mut replacements,
            &mut |_value_id, _replacements| {
                found = true;
                true
            },
        );

        // TypeSort should NOT match x0 (a type variable expecting concrete types)
        assert!(!found, "TypeSort should NOT match type variable x0: Type");
    }

    #[test]
    fn test_pdt_rejects_specialization_to_escaping_bound_variable_under_lambda() {
        // Pattern: lambda(Bool => x0), with x0 : Bool.
        // Query:   lambda(Bool => b0), where b0 is bound by the lambda.
        // Matching should not panic, and it should reject the escaping-bound-variable
        // specialization instead of treating it as a valid binding for x0.
        let kctx = KernelContext::new();
        let pattern_lctx = kctx.parse_local(&["Bool"]);
        let pattern_term = Term::lambda(Term::bool_type(), Term::atom(KernelAtom::FreeVariable(0)));

        let mut tree: Pdt<&str> = Pdt::new();
        tree.insert_pair(
            &pattern_term,
            &Term::new_true(),
            "lambda_pattern",
            &pattern_lctx,
        );

        let query_term = Term::lambda(Term::bool_type(), Term::atom(KernelAtom::BoundVariable(0)));
        let query_lctx = LocalContext::empty();

        let result = std::panic::catch_unwind(|| {
            tree.find_pair(&query_term, &Term::new_true(), &query_lctx, &kctx)
        });

        assert!(result.is_ok(), "PDT match should not panic under binders");
        assert_eq!(result.unwrap(), None);
    }
}
