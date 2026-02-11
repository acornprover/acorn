use core::panic;
use std::collections::{BTreeMap, HashMap, HashSet};

use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind, Range};

use crate::code_generator::CodeGenerator;
use crate::elaborator::acorn_type::{
    AcornType, Datatype, PotentialType, TypeParam, Typeclass, UnresolvedType, Variance,
};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::error::{self, ErrorContext};
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::{ConstantName, DefinedName, InstanceName};
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::stack::Stack;
use crate::elaborator::termination_checker::TerminationChecker;
use crate::elaborator::type_unifier::{TypeUnifier, TypeclassRegistry};
use crate::elaborator::unresolved_constant::UnresolvedConstant;
use crate::kernel::atom::AtomId;
use crate::module::ModuleId;
use crate::project::Project;
use crate::syntax::expression::{Declaration, Expression, TypeParamExpr};
use crate::syntax::token::{self, Token, TokenType};
use crate::syntax::token_map::TokenMap;

/// The BindingMap contains all of the mappings needed to figure out what a string refers to
/// in a particular environment.
/// Variables, constants, types, typeclasses, modules, numeric literals.
/// This representation does not have to be efficient enough to run in the inner loop of the prover.
#[derive(Clone)]
pub struct BindingMap {
    /// The module all these names are in.
    module_id: ModuleId,

    /// Maps the name of a constant defined in this scope to information about its definition.
    /// Doesn't handle variables defined on the stack, only ones that will be in scope for the
    /// entirety of this environment.
    /// This also includes aliases.
    constant_defs: HashMap<ConstantName, ConstantDefinition>,

    /// Maps the name of a type to the type object.
    /// Includes unresolved names like List that don't have enough information
    /// to get a specific type.
    typename_to_type: BTreeMap<String, PotentialType>,

    /// Maps the type object to its name in this environment.
    type_to_typename: HashMap<PotentialType, String>,

    /// Stores definition information about every datatype accessible from this module.
    datatype_defs: HashMap<Datatype, DatatypeDefinition>,

    /// Maps the name of a typeclass to the typeclass.
    /// Includes typeclasses that were imported from other modules.
    name_to_typeclass: BTreeMap<String, Typeclass>,

    /// Stores definition information about every typeclass accessible from this module.
    typeclass_defs: HashMap<Typeclass, TypeclassDefinition>,

    /// A map whose keys are the unqualified constants in this module.
    /// Used for completion.
    unqualified: BTreeMap<String, ()>,

    /// Whenever a name from some other scope has a local alias in this one,
    /// if we're generating code, we prefer to use the local name.
    /// This contains constants, types, and typenames.
    /// For this reason, canonical_to_alias maps the global name to the preferred local alias.
    constant_to_alias: HashMap<ConstantName, String>,

    /// Names that refer to other modules.
    /// After "import foo", "foo" refers to a module.
    /// It's important that these are in alphabetical order, so that dependency hashes are consistent.
    name_to_module: BTreeMap<String, ModuleId>,

    /// Information about imported modules.
    module_info: HashMap<ModuleId, ModuleInfo>,

    /// The default data type to use for numeric literals.
    numerals: Option<Datatype>,

    /// The definitions of the instance attributes defined in this module.
    instance_attr_defs: HashMap<InstanceName, InstanceAttributeDefinition>,
}

impl BindingMap {
    pub fn new(module: ModuleId) -> Self {
        let mut answer = BindingMap {
            module_id: module,
            constant_defs: HashMap::new(),
            typename_to_type: BTreeMap::new(),
            type_to_typename: HashMap::new(),
            name_to_typeclass: BTreeMap::new(),
            typeclass_defs: HashMap::new(),
            unqualified: BTreeMap::new(),
            constant_to_alias: HashMap::new(),
            name_to_module: BTreeMap::new(),
            module_info: HashMap::new(),
            numerals: None,
            instance_attr_defs: HashMap::new(),
            datatype_defs: HashMap::new(),
        };
        let dummy_token = Token::empty();
        answer
            .add_type_alias(
                "Bool",
                PotentialType::Resolved(AcornType::Bool),
                &dummy_token,
            )
            .expect("Bool type should not already be bound");
        answer
    }

    pub fn module_id(&self) -> ModuleId {
        self.module_id
    }

    /// Returns the default data type for numeric literals, if set.
    pub fn numerals(&self) -> Option<&Datatype> {
        self.numerals.as_ref()
    }

    /// Whether this type has this attribute in the current context.
    pub fn has_type_attr(&self, datatype: &Datatype, var_name: &str) -> bool {
        self.datatype_defs
            .get(datatype)
            .map_or(false, |info| info.attributes.contains_key(var_name))
    }

    /// For a given typeclass attribute, find the typeclass that defines it.
    /// This can return the typeclass argument itself, or a base typeclass that it extends.
    /// Returns None if there is no such attribute.
    pub fn typeclass_attr_lookup(&self, typeclass: &Typeclass, attr: &str) -> Option<&Typeclass> {
        self.typeclass_defs
            .get(typeclass)?
            .attributes
            .get(attr)
            .map(|(_, tc)| tc)
    }

    /// Gets the local alias to use for a given constant.
    pub fn constant_alias(&self, name: &ConstantName) -> Option<&String> {
        self.constant_to_alias.get(name)
    }

    /// Returns preferred unqualified names for synthetic IDs visible in this scope.
    ///
    /// This is used for user-facing code generation so checked proof steps can reuse
    /// names that came from parsed certificate lines.
    pub fn synthetic_name_map(&self) -> HashMap<(ModuleId, AtomId), String> {
        let mut names = HashMap::new();
        for (name, info) in &self.constant_defs {
            let ConstantName::Unqualified(_, alias) = name else {
                continue;
            };

            let synthetic_id = match &info.value {
                PotentialValue::Unresolved(unresolved) => unresolved.name.synthetic_id(),
                PotentialValue::Resolved(value) => {
                    value.as_name().and_then(|name| name.synthetic_id())
                }
            };

            let Some(synthetic_id) = synthetic_id else {
                continue;
            };

            names
                .entry(synthetic_id)
                .and_modify(|existing: &mut String| {
                    if alias < existing {
                        *existing = alias.clone();
                    }
                })
                .or_insert_with(|| alias.clone());
        }
        names
    }

    /// Gets the local alias to use for a given datatype.
    pub fn datatype_alias(&self, datatype: &Datatype) -> Option<&String> {
        self.datatype_defs.get(datatype)?.alias.as_ref()
    }

    fn add_datatype_alias(&mut self, datatype: &Datatype, alias: &str) {
        if !self.datatype_defs.contains_key(datatype) {
            self.datatype_defs
                .insert(datatype.clone(), DatatypeDefinition::new());
        }
        let info = self.datatype_defs.get_mut(datatype).unwrap();
        if info.alias.is_none() {
            info.alias = Some(alias.to_string());
        }
    }

    fn add_typeclass_alias(&mut self, typeclass: &Typeclass, alias: &str) {
        if !self.typeclass_defs.contains_key(typeclass) {
            self.typeclass_defs
                .insert(typeclass.clone(), TypeclassDefinition::new());
        }
        let info = self.typeclass_defs.get_mut(typeclass).unwrap();
        if info.alias.is_none() {
            info.alias = Some(alias.to_string());
        }
    }

    /// Gets the local alias to use for a given typeclass.
    pub fn typeclass_alias(&self, typeclass: &Typeclass) -> Option<&String> {
        self.typeclass_defs.get(typeclass)?.alias.as_ref()
    }

    pub fn check_defined_name_available(
        &self,
        defined_name: &DefinedName,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        if self.constant_name_in_use(defined_name) {
            return Err(source.error(&format!("constant name {} is already in use", defined_name)));
        }
        Ok(())
    }

    /// Note: Doesn't work correctly for typeclass attributes.
    pub fn constant_name_in_use(&self, name: &DefinedName) -> bool {
        match name {
            DefinedName::Constant(constant_name) => {
                if self.constant_defs.contains_key(constant_name) {
                    return true;
                }
                match constant_name {
                    ConstantName::Unqualified(_, name) => {
                        self.unqualified.contains_key(name)
                            || self.name_to_module.contains_key(name)
                    }
                    ConstantName::DatatypeAttribute(datatype, attr) => {
                        self.has_type_attr(datatype, attr)
                    }
                    ConstantName::SpecificDatatypeAttribute(datatype, _types, attr) => {
                        // For specific attributes, check if they're in the constant_defs
                        // (already checked above, so this should always be false here)
                        self.has_type_attr(datatype, attr)
                    }
                    ConstantName::TypeclassAttribute(..) => {
                        // This doesn't seem right!
                        false
                    }
                    ConstantName::Synthetic(m, i) => {
                        let name = format!("s{}_{}", m.0, i);
                        self.unqualified.contains_key(&name)
                            || self.name_to_module.contains_key(&name)
                    }
                }
            }
            DefinedName::Instance(instance_name) => {
                self.instance_attr_defs.contains_key(instance_name)
            }
        }
    }

    /// Get the set of all typeclasses that this one extends.
    /// This is the transitive closure, ie when A extends B and B extends C, A's set
    /// will include both B and C.
    pub fn get_extends_set(&self, typeclass: &Typeclass) -> Option<&HashSet<Typeclass>> {
        Some(&self.typeclass_defs.get(typeclass)?.extends)
    }

    pub fn unifier(&self) -> TypeUnifier<'_> {
        TypeUnifier::new(self)
    }

    /// Returns a PotentialValue representing this name, if there is one.
    /// This can be either a resolved or unresolved value.
    /// This function assumes that you are calling the correct binding map.
    pub fn get_constant_value(&self, name: &DefinedName) -> Result<PotentialValue, String> {
        match name {
            DefinedName::Constant(constant_name) => match self.constant_defs.get(constant_name) {
                Some(info) => Ok(info.value.clone()),
                None => Err(format!("local constant {} not found", name)),
            },
            DefinedName::Instance(instance_name) => {
                let definition = self
                    .instance_attr_defs
                    .get(instance_name)
                    .ok_or_else(|| format!("instance constant {} not found", name))?;
                let value = AcornValue::instance_constant(
                    instance_name.clone(),
                    definition.value.get_type(),
                );
                Ok(PotentialValue::Resolved(value))
            }
        }
    }

    /// Gets the type for a type name, not for an identifier.
    pub fn get_type_for_typename(&self, type_name: &str) -> Option<&PotentialType> {
        self.typename_to_type.get(type_name)
    }

    pub fn get_typename_for_type(&self, potential_type: &PotentialType) -> Option<&String> {
        self.type_to_typename.get(potential_type)
    }

    pub fn has_typename(&self, type_name: &str) -> bool {
        self.typename_to_type.contains_key(type_name)
    }

    pub fn get_typeclass_for_name(&self, typeclass_name: &str) -> Option<&Typeclass> {
        self.name_to_typeclass.get(typeclass_name)
    }

    pub fn has_typeclass_name(&self, typeclass_name: &str) -> bool {
        self.name_to_typeclass.contains_key(typeclass_name)
    }

    pub fn get_module_id_for_name(&self, name: &str) -> Option<ModuleId> {
        self.name_to_module.get(name).copied()
    }

    pub fn get_module_info(&self, module_id: ModuleId) -> Option<&ModuleInfo> {
        self.module_info.get(&module_id)
    }

    /// Just use this for testing.
    pub fn has_constant_name(&self, name: &str) -> bool {
        let constant_name = ConstantName::unqualified(self.module_id, name);
        self.constant_defs.contains_key(&constant_name)
    }

    /// Returns the defined value, if there is a defined value.
    /// If there isn't, returns None.
    pub fn get_definition(&self, name: &DefinedName) -> Option<&AcornValue> {
        match name {
            DefinedName::Constant(constant_name) => {
                self.constant_defs.get(constant_name)?.definition.as_ref()
            }
            DefinedName::Instance(instance_name) => self
                .instance_attr_defs
                .get(instance_name)
                .map(|def| &def.value),
        }
    }

    /// Returns the range where this name was defined, if available.
    pub fn get_definition_range(&self, name: &DefinedName) -> Option<&Range> {
        match name {
            DefinedName::Constant(constant_name) => {
                self.constant_defs.get(constant_name)?.range.as_ref()
            }
            DefinedName::Instance(instance_name) => self
                .instance_attr_defs
                .get(instance_name)
                .and_then(|def| def.range.as_ref()),
        }
    }

    /// Returns the defined value and its parameters in their canonical order.
    /// Returns None if there is no definition.
    pub fn get_definition_and_params(
        &self,
        constant_name: &ConstantName,
    ) -> Option<(&AcornValue, &[TypeParam])> {
        let info = self.constant_defs.get(constant_name)?;
        Some((info.definition.as_ref()?, info.value.unresolved_params()))
    }

    /// Iterate through all the typeclasses that this typeclass extends.
    pub fn get_extends(&self, typeclass: &Typeclass) -> impl Iterator<Item = &Typeclass> {
        self.typeclass_defs
            .get(typeclass)
            .into_iter()
            .flat_map(|info| info.extends.iter())
    }

    /// Get all typeclasses that this datatype is an instance of.
    pub fn get_instance_typeclasses(
        &self,
        datatype: &Datatype,
    ) -> impl Iterator<Item = &Typeclass> {
        self.datatype_defs
            .get(datatype)
            .into_iter()
            .flat_map(|info| info.typeclasses.keys())
    }

    /// A helper to get the bindings from the project if needed bindings.
    pub fn get_bindings<'a>(&'a self, module_id: ModuleId, project: &'a Project) -> &'a BindingMap {
        if module_id == self.module_id {
            self
        } else {
            project.get_bindings(module_id).unwrap()
        }
    }

    pub fn get_typeclass_attributes<'a>(
        &'a self,
        typeclass: &Typeclass,
        project: &'a Project,
    ) -> &'a BTreeMap<String, (ModuleId, Typeclass)> {
        &self
            .get_bindings(typeclass.module_id, project)
            .typeclass_defs
            .get(typeclass)
            .unwrap()
            .attributes
    }

    pub fn get_constructor_info(&self, name: &ConstantName) -> Option<&ConstructorInfo> {
        self.constant_defs
            .get(name)
            .and_then(|info| info.constructor.as_ref())
    }

    pub fn get_module_for_datatype_attr(
        &self,
        datatype: &Datatype,
        attr: &str,
    ) -> Option<ModuleId> {
        self.datatype_defs
            .get(datatype)
            .and_then(|info| info.attributes.get(attr))
            .copied()
    }

    /// Figures out whether a datatype attribute is defined directly or by inheritance,
    /// returning both the module id and the originally defined name.
    pub fn resolve_datatype_attr(
        &self,
        datatype: &Datatype,
        attr_name: &str,
    ) -> Result<(ModuleId, ConstantName), String> {
        if let Some(module_id) = self.get_module_for_datatype_attr(datatype, attr_name) {
            let name = ConstantName::datatype_attr(datatype.clone(), attr_name);
            return Ok((module_id, name));
        }

        // If no direct type attribute, check if this datatype is an instance
        // of any typeclass that has this attribute
        let mut base_typeclass: Option<&Typeclass> = None;

        for typeclass in self.get_instance_typeclasses(datatype) {
            let Some(base_tc) = self.typeclass_attr_lookup(typeclass, attr_name) else {
                continue;
            };
            if let Some(existing_base) = base_typeclass {
                // If we find a different base typeclass, it's ambiguous
                if existing_base != base_tc {
                    return Err(format!(
                        "attribute '{}' is ambiguous: defined in multiple typeclasses: {}, {}",
                        attr_name, existing_base.name, base_tc.name
                    ));
                }
            } else {
                base_typeclass = Some(base_tc);
            }
        }

        match base_typeclass {
            Some(typeclass) => self
                .resolve_typeclass_attr(typeclass, attr_name)
                .ok_or_else(|| {
                    format!(
                        "attribute {}.{} not found via typeclass {}",
                        &datatype.name, attr_name, typeclass.name
                    )
                }),
            None => Err(format!(
                "attribute {}.{} not found",
                &datatype.name, attr_name
            )),
        }
    }

    /// Resolves a datatype attribute, checking for specific parameterized attributes first,
    /// then falling back to generic attributes.
    /// This is used when we have concrete type parameters available (e.g., resolving
    /// `my_set.has_red` where `my_set: Set[Color]`).
    pub fn resolve_datatype_attr_with_params(
        &self,
        datatype: &Datatype,
        type_params: &[AcornType],
        attr_name: &str,
    ) -> Result<(ModuleId, ConstantName), String> {
        // First, try to find a specific attribute that matches the exact type parameters
        if !type_params.is_empty() {
            let specific_name = ConstantName::datatype_specific_attr(
                datatype.clone(),
                type_params.to_vec(),
                attr_name,
            );
            if self.constant_defs.contains_key(&specific_name) {
                // Specific attributes are defined in the current module
                return Ok((self.module_id, specific_name));
            }
        }

        // Fall back to generic attribute resolution
        self.resolve_datatype_attr(datatype, attr_name)
    }

    /// Figures out whether a typeclass attribute is defined directly or by inheritance.
    /// Returns the module ID and defined name where the attribute was originally defined.
    pub fn resolve_typeclass_attr(
        &self,
        typeclass: &Typeclass,
        attr_name: &str,
    ) -> Option<(ModuleId, ConstantName)> {
        // Check if this attribute is defined anywhere (including inherited ones)
        let info = self.typeclass_defs.get(typeclass)?;
        let (attr_module_id, attr_typeclass) = info.attributes.get(attr_name)?;
        let name = ConstantName::typeclass_attr(attr_typeclass.clone(), attr_name);
        Some((*attr_module_id, name))
    }

    /// Figures out where this name was originally defined.
    pub fn resolve_name(&self, name: &ConstantName) -> Option<(ModuleId, ConstantName)> {
        match name {
            ConstantName::Unqualified(module_id, _) => {
                // This is a local name, so it was defined in this module.
                Some((*module_id, name.clone()))
            }
            ConstantName::DatatypeAttribute(datatype, attr) => {
                self.resolve_datatype_attr(datatype, attr).ok()
            }
            ConstantName::SpecificDatatypeAttribute(datatype, _types, _attr) => {
                // Specific attributes are always defined locally
                Some((datatype.module_id, name.clone()))
            }
            ConstantName::TypeclassAttribute(typeclass, attr) => {
                self.resolve_typeclass_attr(typeclass, attr)
            }
            ConstantName::Synthetic(..) => None,
        }
    }

    /// Get all attribute names for a datatype.
    /// This returns only the direct attributes of the datatype itself,
    /// NOT including attributes from typeclasses that this type is an instance of.
    pub fn get_datatype_attributes(&self, datatype: &Datatype) -> Vec<String> {
        self.datatype_defs
            .get(datatype)
            .map(|info| info.attributes.keys().cloned().collect())
            .unwrap_or_default()
    }

    /// Get the module where a specific datatype attribute is defined.
    pub fn get_datatype_attribute_module(
        &self,
        datatype: &Datatype,
        attribute: &str,
    ) -> Option<ModuleId> {
        self.datatype_defs
            .get(datatype)
            .and_then(|info| info.attributes.get(attribute).copied())
    }

    /// Get the module where a specific typeclass attribute is defined.
    pub fn get_typeclass_attribute_module(
        &self,
        typeclass: &Typeclass,
        attribute: &str,
    ) -> Option<ModuleId> {
        self.typeclass_defs.get(typeclass).and_then(|def| {
            def.attributes
                .get(attribute)
                .map(|(module_id, _)| *module_id)
        })
    }

    /// Checks against names for both types and typeclasses because they can conflict.
    pub fn check_typename_available(
        &self,
        name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        if self.typename_to_type.contains_key(name) || self.name_to_typeclass.contains_key(name) {
            return Err(source.error(&format!("typename {} is already in use", name)));
        }
        Ok(())
    }

    /// Returns an error if this name is already in use.
    pub fn check_unqualified_name_available(
        &self,
        name: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        let defined_name = DefinedName::unqualified(self.module_id, name);
        self.check_defined_name_available(&defined_name, source)
    }

    /// We use variables named x0, x1, x2, etc when new temporary variables are needed.
    /// Find the next one that's available.
    /// 'x' is the prefix here.
    pub fn next_indexed_var(&self, prefix: char, next_index: &mut u32) -> String {
        loop {
            let name =
                DefinedName::unqualified(self.module_id, &format!("{}{}", prefix, next_index));
            *next_index += 1;
            if !self.constant_name_in_use(&name) {
                return name.to_string();
            }
        }
    }

    /// Adds both directions for a name iff type correspondence.
    /// Returns an error if the name is already bound.
    fn insert_type_name(
        &mut self,
        name: String,
        potential_type: PotentialType,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        // There can be multiple names for a type.
        // If we already have a name for the reverse lookup, we don't overwrite it.
        if !self.type_to_typename.contains_key(&potential_type) {
            self.type_to_typename
                .insert(potential_type.clone(), name.clone());
        }

        match self.typename_to_type.entry(name.clone()) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(potential_type);
                Ok(())
            }
            std::collections::btree_map::Entry::Occupied(_) => {
                Err(source.error(&format!("typename {} already bound", name)))
            }
        }
    }

    /// Adds a new data type to the binding map.
    /// Panics if the name is already bound.
    pub fn add_data_type(
        &mut self,
        name: &str,
        doc_comments: Vec<String>,
        range: Option<Range>,
        definition_string: Option<String>,
    ) -> AcornType {
        let datatype = Datatype {
            module_id: self.module_id,
            name: name.to_string(),
        };
        // Store the doc comments, range, and definition string for this datatype
        let info = self
            .datatype_defs
            .entry(datatype.clone())
            .or_insert_with(DatatypeDefinition::new);
        info.doc_comments = doc_comments;
        info.range = range;
        info.definition_string = definition_string;
        let t = AcornType::Data(datatype, vec![]);
        let dummy_token = Token::empty();
        self.insert_type_name(
            name.to_string(),
            PotentialType::Resolved(t.clone()),
            &dummy_token,
        )
        .expect("typename should not already be bound");
        t
    }

    /// Panics if the name is already bound.
    pub fn add_potential_type(
        &mut self,
        name_token: &Token,
        params: Vec<Option<Typeclass>>,
        doc_comments: Vec<String>,
        range: Option<Range>,
        definition_string: Option<String>,
    ) -> PotentialType {
        let name = name_token.text();
        if params.is_empty() {
            return PotentialType::Resolved(self.add_data_type(
                name,
                doc_comments,
                range,
                definition_string,
            ));
        }
        let datatype = Datatype {
            module_id: self.module_id,
            name: name.to_string(),
        };
        // Store the doc comments, range, and definition string for this datatype
        let info = self
            .datatype_defs
            .entry(datatype.clone())
            .or_insert_with(DatatypeDefinition::new);
        info.doc_comments = doc_comments;
        info.range = range;
        info.definition_string = definition_string;
        let ut = UnresolvedType { datatype, params };
        let potential = PotentialType::Unresolved(ut);
        self.insert_type_name(name.to_string(), potential.clone(), name_token)
            .expect("typename should not already be bound");
        potential
    }

    /// Adds an arbitrary type to the binding map.
    /// This indicates a type parameter that is coming into scope.
    /// Panics if the param name is already bound.
    pub fn add_arbitrary_type(&mut self, param: TypeParam) -> AcornType {
        let name = param.name.to_string();
        let arbitrary_type = AcornType::Arbitrary(param);
        let potential = PotentialType::Resolved(arbitrary_type.clone());
        let dummy_token = Token::empty();
        self.insert_type_name(name, potential, &dummy_token)
            .expect("typename should not already be bound");
        arbitrary_type
    }

    /// Adds a new type name that's an alias for an existing type.
    /// Bindings are the bindings that we are importing the type from.
    /// If the alias is a local one, bindings is None.
    /// Returns an error if the alias is already bound.
    pub fn add_type_alias(
        &mut self,
        alias: &str,
        potential: PotentialType,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        // Local type aliases for concrete types should be preferred.
        if let PotentialType::Resolved(AcornType::Data(datatype, params)) = &potential {
            if params.is_empty() {
                self.add_datatype_alias(datatype, alias);
            }
        }

        // Local type aliases should also be preferred to the canonical name for
        // unresolved generic types.
        if let PotentialType::Unresolved(u) = &potential {
            self.add_datatype_alias(&u.datatype, alias);
        }

        self.insert_type_name(alias.to_string(), potential, source)
    }

    /// Adds a newly-defined typeclass to this environment.
    pub fn add_typeclass(
        &mut self,
        name: &str,
        extends: Vec<Typeclass>,
        doc_comments: Vec<String>,
        range: Option<Range>,
        definition_string: Option<String>,
        project: &Project,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        let mut info = TypeclassDefinition::new();
        info.doc_comments = doc_comments;
        info.range = range;
        info.definition_string = definition_string;
        for base in extends {
            info.extends.insert(base.clone());
            let bindings = self.get_bindings(base.module_id, project);
            let base_info = bindings.typeclass_defs.get(&base).unwrap();
            for base_base in &base_info.extends {
                if !info.extends.contains(base_base) {
                    info.extends.insert(base_base.clone());
                }
            }
            for (attr, (original_module, original_typeclass)) in base_info.attributes.iter() {
                if let Some((_current_module, current_typeclass)) = info.attributes.get(attr) {
                    if current_typeclass != original_typeclass {
                        return Err(source.error(&format!(
                            "you cannot extend both '{}' and '{}' because they both define the attribute '{}'",
                            &current_typeclass.name, &original_typeclass.name, attr
                        )));
                    }
                } else {
                    info.attributes
                        .insert(attr.clone(), (*original_module, original_typeclass.clone()));
                }
            }
        }

        let typeclass = Typeclass {
            module_id: self.module_id,
            name: name.to_string(),
        };
        match self.typeclass_defs.entry(typeclass.clone()) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(info);
            }
            std::collections::hash_map::Entry::Occupied(entry) => {
                return Err(
                    source.error(&format!("typeclass {} is already bound", entry.key().name))
                );
            }
        }
        self.add_typeclass_name(name, typeclass, source)?;
        Ok(())
    }

    /// Adds a local name for this typeclass.
    /// Returns an error if the name is already bound.
    fn add_typeclass_name(
        &mut self,
        name: &str,
        typeclass: Typeclass,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        self.add_typeclass_alias(&typeclass, name);

        match self.name_to_typeclass.entry(name.to_string()) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(typeclass);
                Ok(())
            }
            std::collections::btree_map::Entry::Occupied(_) => {
                Err(source.error(&format!("typeclass name {} is already bound", name)))
            }
        }
    }

    /// Call this after an instance attribute has been defined to typecheck it.
    /// Returns (resolved typeclass attribute, defined instance attribute).
    /// The resolved typeclass attribute is like
    /// Ring.add<Int>
    /// and the defined instance attribute is the one that we defined, before
    /// proving that Int was actually a Ring.
    pub fn check_instance_attribute(
        &self,
        instance_type: &AcornType,
        typeclass: &Typeclass,
        attr_name: &str,
        project: &Project,
        source: &dyn ErrorContext,
    ) -> error::Result<(AcornValue, AcornValue)> {
        // Get the relevant properties of the typeclass.
        let typeclass_attr_name = DefinedName::typeclass_attr(typeclass, attr_name);
        let typeclass_attr = self
            .get_bindings(typeclass.module_id, project)
            .get_constant_value(&typeclass_attr_name)
            .map_err(|e| source.error(&e))?;
        let uc = typeclass_attr.to_unresolved(source)?;
        let resolved_attr = uc.resolve(source, vec![instance_type.clone()])?;
        let resolved_attr_type = resolved_attr.get_type();

        // Get the relevant properties of the instance datatype.
        let instance_datatype = instance_type.get_datatype(source)?;
        let instance_attr_name =
            DefinedName::instance(typeclass.clone(), attr_name, instance_datatype.clone());
        let instance_attr = self
            .get_constant_value(&instance_attr_name)
            .map_err(|e| source.error(&e))?;
        let instance_attr = instance_attr.as_value(source)?;
        let instance_attr_type = instance_attr.get_type();
        if instance_attr_type != resolved_attr_type {
            return Err(source.error(&format!(
                "type mismatch for attribute '{}': expected {}, found {}",
                attr_name, resolved_attr_type, instance_attr_type
            )));
        }
        Ok((resolved_attr, instance_attr))
    }

    pub fn add_instance_of(&mut self, datatype: Datatype, typeclass: Typeclass) {
        self.datatype_defs
            .entry(datatype)
            .or_insert_with(DatatypeDefinition::new)
            .typeclasses
            .insert(typeclass, self.module_id);
    }

    /// All other modules that we directly depend on, besides this one.
    /// Sorted by the module name, so that the order will be consistent.
    pub fn direct_dependencies(&self) -> Vec<ModuleId> {
        let mut deps: Vec<(ModuleId, &Vec<String>)> = self
            .module_info
            .iter()
            .filter(|(&id, _)| id != self.module_id)
            .map(|(&id, info)| (id, &info.full_name))
            .collect();
        // Sort by full name for consistent ordering
        deps.sort_by(|a, b| a.1.cmp(b.1));
        deps.into_iter().map(|(id, _)| id).collect()
    }

    pub fn set_numerals(&mut self, datatype: Datatype) {
        self.numerals = Some(datatype);
    }

    /// Adds a definition for a name that can either be a normal constant, or an instance.
    /// Panics if the name is already bound.
    /// The type and definition can be generic. If so, the parameters must be listed in params.
    /// Don't call this for aliases, this doesn't handle aliases intelligently.
    /// Returns the value for the newly created constant.
    pub fn add_defined_name(
        &mut self,
        defined_name: &DefinedName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<ConstructorInfo>,
        doc_comments: Vec<String>,
        range: Option<Range>,
        definition_string: Option<String>,
    ) -> PotentialValue {
        match defined_name {
            DefinedName::Constant(constant_name) => self.add_constant_name(
                constant_name,
                params,
                constant_type,
                definition,
                constructor,
                doc_comments,
                range,
                definition_string,
            ),
            DefinedName::Instance(instance_name) => {
                let definition = definition.expect("instance must have a definition");
                if !params.is_empty() {
                    panic!("instance may not have parameters");
                }
                if constructor.is_some() {
                    panic!("instance may not be a constructor");
                }
                self.instance_attr_defs.insert(
                    instance_name.clone(),
                    InstanceAttributeDefinition {
                        value: definition,
                        range,
                    },
                );
                let value = AcornValue::instance_constant(instance_name.clone(), constant_type);
                PotentialValue::Resolved(value)
            }
        }
    }

    /// Adds a constant that is an attribute of a datatype.
    pub fn add_datatype_attribute(
        &mut self,
        datatype: &Datatype,
        attr: &str,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<ConstructorInfo>,
        doc_comments: Vec<String>,
        definition_string: String,
    ) -> PotentialValue {
        let constant_name = ConstantName::datatype_attr(datatype.clone(), attr);
        self.add_constant_name(
            &constant_name,
            params,
            constant_type,
            definition,
            constructor,
            doc_comments,
            None,
            Some(definition_string),
        )
    }

    pub fn add_typeclass_attribute(
        &mut self,
        typeclass: &Typeclass,
        attr: &str,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<ConstructorInfo>,
        doc_comments: Vec<String>,
        definition_string: String,
    ) -> PotentialValue {
        let constant_name = ConstantName::typeclass_attr(typeclass.clone(), attr);
        self.add_constant_name(
            &constant_name,
            params,
            constant_type,
            definition,
            constructor,
            doc_comments,
            None,
            Some(definition_string),
        )
    }

    /// Marks a typeclass attribute as required (must be implemented by instances).
    /// This is called when processing the initial typeclass definition.
    pub fn mark_typeclass_attr_required(&mut self, typeclass: &Typeclass, attr: &str) {
        if !self.typeclass_defs.contains_key(typeclass) {
            self.typeclass_defs
                .insert(typeclass.clone(), TypeclassDefinition::new());
        }
        let info = self.typeclass_defs.get_mut(typeclass).unwrap();
        info.required.insert(attr.to_string());
    }

    /// Checks if a typeclass attribute is required to be implemented by instances.
    pub fn is_typeclass_attr_required(&self, typeclass: &Typeclass, attr: &str) -> bool {
        self.typeclass_defs
            .get(typeclass)
            .map(|info| info.required.contains(attr))
            .unwrap_or(false)
    }

    /// Adds a constant that is not an attribute of anything.
    pub fn add_unqualified_constant(
        &mut self,
        name: &str,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<ConstructorInfo>,
        doc_comments: Vec<String>,
        range: Option<Range>,
        definition_string: String,
    ) -> PotentialValue {
        let constant_name = ConstantName::unqualified(self.module_id, name);
        self.add_constant_name(
            &constant_name,
            params,
            constant_type,
            definition,
            constructor,
            doc_comments,
            range,
            Some(definition_string),
        )
    }

    /// Adds a definition for a constant.
    /// Panics if the name is already bound.
    /// The type and definition can be generic. If so, the parameters must be listed in params.
    /// Don't call this for aliases, this doesn't handle aliases intelligently.
    /// Returns the value for the newly created constant.
    fn add_constant_name(
        &mut self,
        constant_name: &ConstantName,
        params: Vec<TypeParam>,
        constant_type: AcornType,
        definition: Option<AcornValue>,
        constructor: Option<ConstructorInfo>,
        doc_comments: Vec<String>,
        range: Option<Range>,
        definition_string: Option<String>,
    ) -> PotentialValue {
        if let Some(definition) = &definition {
            if let Err(e) = definition.validate() {
                panic!("invalid definition for constant {}: {}", constant_name, e);
            }
            if params.is_empty() && definition.has_generic() {
                panic!("there should not be generic types in non-parameterized definitions");
            }
            if !params.is_empty() && definition.has_arbitrary() {
                panic!("there should not be arbitrary types in parameterized definitions");
            }
        }

        let value = if params.is_empty() {
            if constant_type.has_generic() {
                panic!("there should not be generic types in non-parameterized constant types");
            }
            // Non-generic: generic_type equals instance_type
            PotentialValue::Resolved(AcornValue::constant(
                constant_name.clone(),
                vec![],
                constant_type.clone(),
                constant_type,
                vec![],
            ))
        } else {
            // For parameterized constants, the type should only contain arbitrary types
            // that correspond to the declared parameters.
            // This is a sanity check - we don't fully validate here, just check that
            // if there are params, the type is generic-like (not fully concrete with unexpected types).
            // The actual validation of matching arbitrary types to params happens elsewhere.
            PotentialValue::Unresolved(UnresolvedConstant {
                name: constant_name.clone(),
                params,
                generic_type: constant_type,
                args: vec![],
            })
        };

        // New constants start out not being theorems and are marked as a theorem later.
        let info = ConstantDefinition {
            value: value.clone(),
            canonical: true,
            definition: definition.clone(),
            theorem: false,
            constructor,
            doc_comments,
            range,
            definition_string,
        };

        self.add_constant_def(constant_name.clone(), info);

        // Validate constants after adding the definition, so recursive references can be checked
        if let Some(definition) = &definition {
            if let Err(e) = definition.validate_constants(self) {
                panic!(
                    "invalid constant params in definition for {}: {}",
                    constant_name, e
                );
            }
        }

        value
    }

    /// Adds information for either a newly defined constant, or an alias.
    fn add_constant_def(&mut self, constant_name: ConstantName, info: ConstantDefinition) {
        match &constant_name {
            ConstantName::DatatypeAttribute(datatype, attribute) => {
                // We are defining a new datatype attribute.
                self.datatype_defs
                    .entry(datatype.clone())
                    .or_insert_with(DatatypeDefinition::new)
                    .attributes
                    .insert(attribute.clone(), self.module_id);
            }
            ConstantName::SpecificDatatypeAttribute(datatype, _types, attribute) => {
                // For specific attributes, we also add them to the datatype's attribute list
                // This allows them to be found during resolution
                self.datatype_defs
                    .entry(datatype.clone())
                    .or_insert_with(DatatypeDefinition::new)
                    .attributes
                    .insert(attribute.clone(), self.module_id);
            }
            ConstantName::TypeclassAttribute(typeclass, attribute) => {
                self.typeclass_defs
                    .entry(typeclass.clone())
                    .or_insert_with(TypeclassDefinition::new)
                    .attributes
                    .insert(attribute.clone(), (self.module_id, typeclass.clone()));
            }
            ConstantName::Unqualified(_, name) => {
                self.unqualified.insert(name.clone(), ());
            }
            ConstantName::Synthetic(m, i) => {
                let name = format!("s{}_{}", m.0, i);
                self.unqualified.insert(name, ());
            }
        }

        self.constant_defs.insert(constant_name, info);
    }

    /// Be really careful about this, it seems likely to break things.
    pub fn remove_constant(&mut self, constant_name: &ConstantName) {
        if let ConstantName::Unqualified(_, word) = constant_name {
            // Remove the unqualified name from the list of unqualified names.
            self.unqualified.remove(word);
        }
        self.constant_defs
            .remove(constant_name)
            .expect("constant name not in use");
    }

    /// Adds a local alias for an already-existing constant value.
    /// TODO: is aliasing theorems supposed to work?
    pub fn add_constant_alias(
        &mut self,
        alias: ConstantName,
        canonical: ConstantName,
        value: PotentialValue,
        doc_comments: Vec<String>,
        definition_string: Option<String>,
    ) {
        if !canonical.is_synthetic() && canonical.module_id() != self.module_id {
            // Prefer this alias locally to using the qualified, canonical name
            self.constant_to_alias
                .entry(canonical)
                .or_insert(alias.to_string());
        }
        let info = ConstantDefinition {
            value,
            canonical: false,
            theorem: false,
            definition: None,
            constructor: None,
            doc_comments,
            range: None,
            definition_string,
        };
        self.add_constant_def(alias, info);
    }

    pub fn mark_as_theorem(&mut self, name: &ConstantName) {
        self.constant_defs
            .get_mut(name)
            .expect("marking theorem that doesn't exist")
            .theorem = true;
    }

    pub fn is_theorem(&self, name: &ConstantName) -> bool {
        self.constant_defs
            .get(name)
            .map_or(false, |info| info.theorem)
    }

    /// Get the doc comments for a constant.
    pub fn get_constant_doc_comments(&self, name: &ConstantName) -> Option<&Vec<String>> {
        self.constant_defs.get(name).and_then(|info| {
            if info.doc_comments.is_empty() {
                None
            } else {
                Some(&info.doc_comments)
            }
        })
    }

    /// Get the definition string for a constant, if it has one.
    pub fn get_constant_definition_string(&self, name: &ConstantName) -> Option<&String> {
        self.constant_defs.get(name)?.definition_string.as_ref()
    }

    /// Get the doc comment for a datatype.
    pub fn get_datatype_doc_comments(&self, datatype: &Datatype) -> Option<&Vec<String>> {
        self.datatype_defs.get(datatype).and_then(|info| {
            if info.doc_comments.is_empty() {
                None
            } else {
                Some(&info.doc_comments)
            }
        })
    }

    /// Get the definition string for a datatype.
    pub fn get_datatype_definition_string(&self, datatype: &Datatype) -> Option<&String> {
        self.datatype_defs.get(datatype)?.definition_string.as_ref()
    }

    /// Get the definition range for a datatype.
    pub fn get_datatype_range(&self, datatype: &Datatype) -> Option<&Range> {
        self.datatype_defs
            .get(datatype)
            .and_then(|info| info.range.as_ref())
    }

    /// Get the variance information for a datatype's type parameters.
    pub fn get_datatype_variances(&self, datatype: &Datatype) -> Option<&Vec<Variance>> {
        self.datatype_defs
            .get(datatype)
            .and_then(|info| info.variances.as_ref())
    }

    /// Set the variance information for a datatype's type parameters.
    /// This is used to update variance after computing it for inductive types.
    pub fn set_datatype_variances(&mut self, datatype: &Datatype, variances: Vec<Variance>) {
        if let Some(info) = self.datatype_defs.get_mut(datatype) {
            info.variances = Some(variances);
        }
    }

    /// Set the arity (number of type parameters) for a datatype.
    pub fn set_datatype_arity(&mut self, datatype: &Datatype, arity: u8) {
        if let Some(info) = self.datatype_defs.get_mut(datatype) {
            info.arity = arity;
        }
    }

    /// Get the arity (number of type parameters) for a datatype.
    pub fn get_datatype_arity(&self, datatype: &Datatype) -> u8 {
        self.datatype_defs
            .get(datatype)
            .map(|info| info.arity)
            .unwrap_or(0)
    }

    /// Get the doc comment for a typeclass.
    pub fn get_typeclass_doc_comments(&self, typeclass: &Typeclass) -> Option<&Vec<String>> {
        self.typeclass_defs.get(typeclass).and_then(|info| {
            if info.doc_comments.is_empty() {
                None
            } else {
                Some(&info.doc_comments)
            }
        })
    }

    /// Get the definition string for a typeclass.
    pub fn get_typeclass_definition_string(&self, typeclass: &Typeclass) -> Option<&String> {
        self.typeclass_defs
            .get(typeclass)?
            .definition_string
            .as_ref()
    }

    /// Get the definition range for a typeclass.
    pub fn get_typeclass_range(&self, typeclass: &Typeclass) -> Option<&Range> {
        self.typeclass_defs
            .get(typeclass)
            .and_then(|info| info.range.as_ref())
    }

    /// Find any datatype that implements the given typeclass.
    /// Returns the first one found (order is non-deterministic).
    pub fn find_type_implementing(&self, typeclass: &Typeclass) -> Option<Datatype> {
        for (datatype, info) in &self.datatype_defs {
            if info.typeclasses.contains_key(typeclass) {
                return Some(datatype.clone());
            }
        }
        None
    }

    /// Type variables and arbitrary variables should get removed when they go out of scope.
    /// Other sorts of types shouldn't be getting removed.
    pub fn remove_type(&mut self, name: &str) {
        match self.typename_to_type.remove(name) {
            Some(p) => match &p {
                PotentialType::Unresolved(ut) => {
                    panic!("removing type {} which is unresolved", ut.datatype.name);
                }
                PotentialType::Resolved(t) => {
                    match &t {
                        AcornType::Variable(..) | AcornType::Arbitrary(..) => {}
                        _ => panic!("unexpectedly removing type: {}", name),
                    }
                    self.type_to_typename.remove(&p);
                }
            },
            None => panic!("removing type {} which is already not present", name),
        }
    }

    /// Imports a module's typeclass and datatype info.
    /// Does NOT bind the module name - used for "from foo import bar" syntax.
    /// Copies over all the datatype_defs from the module's bindings.
    /// This enables "mixins".
    /// Also copy over all the typeclass_defs from the module's bindings.
    pub fn import_module(
        &mut self,
        full_name: Vec<String>,
        bindings: &BindingMap,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        // Copy over module info from the imported module, but don't override entries with local names
        for (module_id, imported_info) in bindings.module_info.iter() {
            if !self.module_info.contains_key(module_id) {
                // Only add if we don't already have info for this module
                let info = ModuleInfo {
                    local_name: None, // Imported modules from another module don't have local names here
                    full_name: imported_info.full_name.clone(),
                };
                self.module_info.insert(*module_id, info);
            }
        }

        // Add the directly imported module WITHOUT a local name (no name binding)
        let module_info = ModuleInfo {
            local_name: None,
            full_name,
        };
        self.module_info.insert(bindings.module_id, module_info);

        // Copy over the datatype info.
        for (datatype, imported_info) in bindings.datatype_defs.iter() {
            let entry = self
                .datatype_defs
                .entry(datatype.clone())
                .or_insert_with(DatatypeDefinition::new);
            entry.import(imported_info, &datatype.name, source)?;
        }

        // Copy over the typeclass info, but drop any aliases.
        for (typeclass, imported_info) in bindings.typeclass_defs.iter() {
            let entry = self
                .typeclass_defs
                .entry(typeclass.clone())
                .or_insert_with(TypeclassDefinition::new);

            // Merge attributes from the imported typeclass
            for (attr_name, (attr_module_id, attr_typeclass)) in imported_info.attributes.iter() {
                match entry.attributes.get(attr_name) {
                    None => {
                        entry
                            .attributes
                            .insert(attr_name.clone(), (*attr_module_id, attr_typeclass.clone()));
                    }
                    Some((existing_module_id, _existing_typeclass)) => {
                        // Check for conflicts: different modules defining the same attribute
                        if *existing_module_id != *attr_module_id {
                            return Err(source.error(&format!(
                                "typeclass attribute {}.{} is defined in two different modules",
                                typeclass.name, attr_name
                            )));
                        }
                    }
                }
            }

            // Merge other fields if this is a new typeclass (but we already handle attributes above)
            if entry.doc_comments.is_empty() {
                entry.doc_comments = imported_info.doc_comments.clone();
            }
            if entry.range.is_none() {
                entry.range = imported_info.range;
            }
            // Merge extends and required sets
            for extends_tc in &imported_info.extends {
                entry.extends.insert(extends_tc.clone());
            }
            for required_attr in &imported_info.required {
                entry.required.insert(required_attr.clone());
            }
        }
        Ok(())
    }

    /// Imports all exportable names from a prelude module.
    /// This is similar to import_module + import_name for all names, but done automatically.
    /// Used to auto-import prelude.ac into every module.
    pub fn import_prelude(
        &mut self,
        prelude_bindings: &BindingMap,
        project: &Project,
    ) -> error::Result<()> {
        // First, import the module's typeclass and datatype info
        self.import_module(
            vec!["prelude".to_string()],
            prelude_bindings,
            &Token::empty(),
        )?;

        // Import all unqualified names from prelude
        // We need to clone the keys because we'll be mutating self
        let names: Vec<String> = prelude_bindings.unqualified.keys().cloned().collect();

        for name in names {
            // Create a token for this name for error reporting
            let name_token = TokenType::Identifier.new_token(&name);

            // Use the existing import_name logic to import each name
            let _ = self.import_name(project, prelude_bindings.module_id, &name_token)?;
        }

        // Import all type names that aren't already imported via unqualified constants
        for typename in prelude_bindings.typename_to_type.keys() {
            // Skip Bool since it's a built-in
            if typename != "Bool" && !self.typename_to_type.contains_key(typename) {
                if let Some(potential_type) = prelude_bindings.typename_to_type.get(typename) {
                    let _ = self.add_type_alias(typename, potential_type.clone(), &Token::empty());
                }
            }
        }

        // Import all typeclass names
        for (tc_name, typeclass) in &prelude_bindings.name_to_typeclass {
            if !self.name_to_typeclass.contains_key(tc_name) {
                let _ = self.add_typeclass_name(tc_name, typeclass.clone(), &Token::empty());
            }
        }

        Ok(())
    }

    pub fn is_module(&self, name: &str) -> bool {
        self.name_to_module.contains_key(name)
    }

    /// Whether this value is calling a theorem on some arguments.
    pub fn is_citation(&self, claim: &AcornValue, project: &Project) -> bool {
        match claim.is_named_function_call() {
            Some(constant_name) => {
                let bindings = self.get_bindings(constant_name.module_id(), project);
                bindings.is_theorem(constant_name)
            }
            None => false,
        }
    }

    fn get_typeclass_attr_completions(
        &self,
        typeclass: &Typeclass,
        prefix: &str,
        project: &Project,
    ) -> Option<Vec<CompletionItem>> {
        let mut answer = vec![];
        if let Some(info) = self
            .get_bindings(typeclass.module_id, project)
            .typeclass_defs
            .get(typeclass)
        {
            for key in keys_with_prefix(&info.attributes, prefix) {
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::FIELD),
                    ..Default::default()
                };
                answer.push(completion);
            }
        }
        Some(answer)
    }

    /// Gets completions when we are typing a member name.
    fn get_type_attr_completions(
        &self,
        t: &AcornType,
        prefix: &str,
    ) -> Option<Vec<CompletionItem>> {
        if let AcornType::Data(datatype, _) = t {
            let info = self.datatype_defs.get(datatype)?;
            let mut answer = vec![];
            for key in keys_with_prefix(&info.attributes, prefix) {
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::FIELD),
                    ..Default::default()
                };
                answer.push(completion);
            }
            Some(answer)
        } else {
            None
        }
    }

    /// The prefix is just of a single identifier.
    /// If importing is true, we are looking for names to import. This means that we don't
    /// want to suggest names unless this is the canonical location for them, and we don't
    /// want to suggest theorems.
    pub fn get_completions(
        &self,
        prefix: &str,
        importing: bool,
        project: &Project,
    ) -> Option<Vec<CompletionItem>> {
        if prefix.contains('.') {
            if importing {
                // Syntactically invalid
                return None;
            }
            let mut name_chain = prefix.split('.').collect::<Vec<&str>>();
            let partial = name_chain.pop()?;
            let namespace = Evaluator::new(project, self, None).evaluate_name_chain(&name_chain)?;
            match namespace {
                NamedEntity::Module(module) => {
                    let bindings = project.get_bindings(module)?;
                    return bindings.get_completions(partial, true, project);
                }
                NamedEntity::Type(t) => {
                    return self.get_type_attr_completions(&t, partial);
                }
                NamedEntity::Value(v) => {
                    let t = v.get_type();
                    return self.get_type_attr_completions(&t, partial);
                }
                NamedEntity::Typeclass(tc) => {
                    return self.get_typeclass_attr_completions(&tc, partial, project);
                }
                NamedEntity::UnresolvedValue(u) => {
                    return self.get_type_attr_completions(&u.generic_type, partial);
                }
                NamedEntity::UnresolvedType(ut) => {
                    let display_type = ut.to_display_type();
                    return self.get_type_attr_completions(&display_type, partial);
                }
            }
        }

        let first_char = prefix.chars().next();
        let mut answer = vec![];

        if first_char.map(|c| c.is_lowercase()).unwrap_or(true) {
            // Keywords
            if !importing {
                for key in token::keywords_with_prefix(prefix) {
                    let completion = CompletionItem {
                        label: key.to_string(),
                        kind: Some(CompletionItemKind::KEYWORD),
                        ..Default::default()
                    };
                    answer.push(completion);
                }
            }
            // Constants
            for key in keys_with_prefix(&self.unqualified, prefix) {
                if key.contains('.') {
                    continue;
                }
                let constant_name = ConstantName::unqualified(self.module_id, key);
                if importing {
                    match self.constant_defs.get(&constant_name) {
                        Some(info) => {
                            if !info.canonical || info.theorem {
                                // Don't suggest aliases or theorems when importing
                                continue;
                            }
                        }
                        None => continue,
                    }
                }
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::CONSTANT),
                    ..Default::default()
                };
                answer.push(completion);
            }
        }

        if first_char.map(|c| c.is_uppercase()).unwrap_or(true) {
            // Types
            for key in keys_with_prefix(&self.typename_to_type, prefix) {
                if importing {
                    let data_type = self.typename_to_type.get(key)?;
                    match data_type {
                        PotentialType::Resolved(AcornType::Data(dt, _)) => {
                            if dt.module_id != self.module_id || &dt.name != key {
                                continue;
                            }
                        }
                        _ => continue,
                    }
                }
                let completion = CompletionItem {
                    label: key.clone(),
                    kind: Some(CompletionItemKind::CLASS),
                    ..Default::default()
                };
                answer.push(completion);
            }
        }

        Some(answer)
    }

    /// Imports a name from another module.
    /// The name could either be a type or a value.
    pub fn import_name(
        &mut self,
        project: &Project,
        module: ModuleId,
        name_token: &Token,
    ) -> error::Result<NamedEntity> {
        // Check if this name is lowercase
        let name = name_token.text();
        if name.chars().next().map(char::is_lowercase).unwrap_or(false) {
            let defined_name = DefinedName::unqualified(module, name);
            self.check_defined_name_available(&defined_name, name_token)?;
        }

        let bindings = match project.get_bindings(module) {
            Some(b) => b,
            None => return Err(name_token.error("could not load bindings for imported module")),
        };
        let entity = Evaluator::new(project, bindings, None).evaluate_name(
            name_token,
            &Stack::new(),
            None,
        )?;

        match &entity {
            NamedEntity::Value(value) => {
                // Add a local alias that mirrors this constant's name in the imported module.
                if let Some(constant_name) = value.as_simple_constant() {
                    self.add_constant_alias(
                        ConstantName::unqualified(self.module_id, name),
                        constant_name.clone(),
                        PotentialValue::Resolved(value.clone()),
                        vec![],
                        None,
                    );
                    Ok(entity)
                } else {
                    // I don't see how this branch can be reached.
                    Err(name_token.error("cannot import non-constant values"))
                }
            }
            NamedEntity::Type(acorn_type) => {
                self.add_type_alias(
                    name,
                    PotentialType::Resolved(acorn_type.clone()),
                    name_token,
                )?;
                Ok(entity)
            }
            NamedEntity::Module(_) => Err(name_token.error("cannot import modules indirectly")),
            NamedEntity::Typeclass(tc) => {
                self.add_typeclass_name(name, tc.clone(), name_token)?;
                Ok(entity)
            }

            NamedEntity::UnresolvedValue(uc) => {
                self.add_constant_alias(
                    ConstantName::unqualified(self.module_id, name),
                    uc.name.clone(),
                    PotentialValue::Unresolved(uc.clone()),
                    vec![],
                    None,
                );
                Ok(entity)
            }

            NamedEntity::UnresolvedType(u) => {
                self.add_type_alias(name, PotentialType::Unresolved(u.clone()), name_token)?;
                Ok(entity)
            }
        }
    }

    /// Apply a potential value to arguments, inferring the types.
    pub fn apply_potential(
        &self,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        let value = match potential {
            PotentialValue::Resolved(f) => f.check_apply(args, expected_type, source)?,
            PotentialValue::Unresolved(u) => {
                self.unifier()
                    .resolve_with_inference(u, args, expected_type, source)?
            }
        };
        Ok(value)
    }

    /// Try to apply a potential value to arguments, allowing partial resolution.
    /// If all type parameters can be inferred, returns a resolved value.
    /// If some type parameters cannot be inferred, returns an unresolved value.
    pub fn try_apply_potential(
        &self,
        potential: PotentialValue,
        args: Vec<AcornValue>,
        expected_type: Option<&AcornType>,
        source: &dyn ErrorContext,
    ) -> error::Result<PotentialValue> {
        match potential {
            PotentialValue::Resolved(f) => {
                let value = f.check_apply(args, expected_type, source)?;
                Ok(PotentialValue::Resolved(value))
            }
            PotentialValue::Unresolved(u) => {
                self.unifier()
                    .try_resolve_with_inference(u, args, expected_type, source)
            }
        }
    }

    /// Apply an unresolved name to arguments, inferring the types.
    pub fn infer_and_apply(
        &self,
        stack: &mut Stack,
        unresolved: UnresolvedConstant,
        arg_exprs: Vec<&Expression>,
        expected_type: Option<&AcornType>,
        project: &Project,
        source: &dyn ErrorContext,
        token_map: Option<&mut TokenMap>,
    ) -> error::Result<AcornValue> {
        // Evaluate the arguments as generic values, allowing unresolved constants
        // to be converted to their generic form. This is needed for type inference
        // when arguments may contain in-scope type variables.
        let mut args = vec![];
        let mut evaluator = Evaluator::new(project, self, token_map);
        for arg_expr in &arg_exprs {
            let arg = evaluator.evaluate_as_generic_value(stack, arg_expr)?;
            args.push(arg);
        }

        self.unifier()
            .resolve_with_inference(unresolved, args, expected_type, source)
    }

    /// This creates a version of a typeclass condition that is specialized to a particular
    /// class that isn't an instance of the typeclass.
    /// The *class* must be defined in this module. The typeclass may not be.
    ///
    /// We use this when we haven't proven that a type is an instance of a typeclass yet.
    /// So for example we can resolve:
    ///   Ring.add<T: Ring> -> Ring.add<Int>
    /// even though Int has not been proven to be an instance of Ring.
    ///
    /// TODO: does this work right for typeclasses outside this module?
    pub fn unsafe_instantiate_condition(
        &self,
        typeclass: &Typeclass,
        condition_name: &str,
        instance_type: &AcornType,
        project: &Project,
        source: &dyn ErrorContext,
    ) -> error::Result<AcornValue> {
        let tc_condition_name = ConstantName::typeclass_attr(typeclass.clone(), condition_name);
        let tc_bindings = self.get_bindings(typeclass.module_id, project);
        let (def, params) = match tc_bindings.get_definition_and_params(&tc_condition_name) {
            Some((def, params)) => (def, params),
            None => {
                return Err(source.error(&format!(
                    "could not find definition for typeclass condition {}",
                    tc_condition_name
                )));
            }
        };
        if params.len() != 1 {
            return Err(source.error(&format!(
                "typeclass condition {} should have one parameter",
                tc_condition_name
            )));
        }
        // We are explicitly instantiating in a way that would fail typechecking.
        let universal = match def.clone() {
            AcornValue::Lambda(args, val) => AcornValue::ForAll(args, val),
            v => v,
        };
        let unsafe_param = (params[0].name.clone(), instance_type.clone());
        let unsafe_instance = universal.instantiate(&[unsafe_param]);

        Ok(unsafe_instance)
    }

    /// Evaluate an expression that creates a new scope for a single value inside it.
    /// This could be the statement of a theorem, the definition of a function, or other similar things.
    ///
    /// It has declarations, introducing new variables and types that exist just for this value,
    /// and it has the value itself, which can use those declarations.
    ///
    /// type_param_exprs is a list of tokens for the generic types introduced for this scope.
    /// args is a list of the new variables declared for this scope.
    /// value_type_expr is an optional expression for the type of the value.
    ///   (None means expect a boolean value.)
    /// value_expr is the expression for the value itself.
    /// function_name, when it is provided, can be used recursively.
    /// datatype_params: if this is a method on a parameterized datatype, these are the datatype's params.
    ///
    /// This function mutates the binding map but sets it back to its original state when finished.
    ///
    /// Returns a tuple with:
    ///   a list of type parameters
    ///   a list of argument names
    ///   a list of argument types
    ///   an optional unbound value. (None means axiom.)
    ///   the value type
    ///
    /// The type parameters are treated as arbitrary types internally to the new scope, but externally
    /// they are replaced with type variables.
    ///
    /// class_type should be provided, fully instantiated, if this is the definition of a member function.
    ///
    /// The return value is "unbound" in the sense that it has variable atoms that are not
    /// bound within any lambda, exists, or forall value. It also may have references to a
    /// recursive function that is not yet defined.
    pub fn evaluate_scoped_value(
        &mut self,
        type_param_exprs: &[TypeParamExpr],
        args: &[Declaration],
        value_type_expr: Option<&Expression>,
        value_expr: &Expression,
        class_type: Option<&AcornType>,
        function_name: Option<&ConstantName>,
        datatype_params: Option<&Vec<TypeParam>>,
        project: &Project,
        mut token_map: Option<&mut TokenMap>,
    ) -> error::Result<(
        Vec<TypeParam>,
        Vec<String>,
        Vec<AcornType>,
        Option<AcornValue>,
        AcornType,
    )> {
        // Bind all the type parameters and arguments
        let mut evaluator = Evaluator::new(project, self, token_map.as_deref_mut());
        let type_params = evaluator.evaluate_type_params(type_param_exprs)?;
        for param in &type_params {
            self.add_arbitrary_type(param.clone());
        }
        let mut stack = Stack::new();
        let mut evaluator = Evaluator::new(project, self, token_map.as_deref_mut());
        let (arg_names, internal_arg_types) = evaluator.bind_args(&mut stack, args, class_type)?;

        // Figure out types.
        let internal_value_type = match value_type_expr {
            Some(e) => evaluator.evaluate_type(e)?,
            None => AcornType::Bool,
        };

        if let Some(function_name) = function_name {
            let mut fn_type =
                AcornType::functional(internal_arg_types.clone(), internal_value_type.clone());
            // The function is bound to its name locally, to handle recursive definitions.
            // Internally to the definition, this function is not polymorphic, but it may have
            // type parameters from both the datatype (if it's a method) and the function itself.
            let mut all_params = datatype_params.cloned().unwrap_or_default();
            all_params.extend(type_params.clone());

            // If we have params, genericize the type so it uses type variables instead of arbitrary types
            if !all_params.is_empty() {
                fn_type = fn_type.genericize(&all_params);
            }

            self.add_constant_name(
                function_name,
                all_params,
                fn_type,
                None,
                None,
                vec![],
                None,
                None,
            );
        }

        // Evaluate the internal value using our modified bindings
        let internal_value = if value_expr.is_axiom() {
            None
        } else {
            let mut evaluator = Evaluator::new(project, self, token_map);
            let value = evaluator.evaluate_value_with_stack(
                &mut stack,
                value_expr,
                Some(&internal_value_type),
            )?;

            if let Some(function_name) = function_name {
                let mut checker =
                    TerminationChecker::new(function_name.clone(), internal_arg_types.len());
                if !checker.check(&value) {
                    return Err(
                        value_expr.error("the elaborator thinks this looks like an infinite loop")
                    );
                }
            }

            Some(value)
        };

        // Reset the bindings
        for param in type_params.iter().rev() {
            self.remove_type(&param.name);
        }
        if let Some(function_name) = function_name {
            self.remove_constant(function_name);
        }

        // We might have types parameterized on this function, or they might be parameterized on the
        // datatype definition. We only want to genericize the parameters that we created.
        if type_params.is_empty() {
            // Just keep the types as they are.
            Ok((
                type_params,
                arg_names,
                internal_arg_types,
                internal_value,
                internal_value_type,
            ))
        } else {
            // Convert to external type variables
            let external_value = if let Some(internal_value) = internal_value {
                if let Some(function_name) = function_name {
                    // We might have defined this function recursively.
                    // In this case, internally it's not polymorphic. It's just a constant
                    // with a type that depends on the arbitrary types we introduced.
                    // But, externally we need to make it polymorphic.
                    // For methods on parameterized datatypes, we need to include both
                    // the datatype params and the function's own params.
                    let mut all_params_for_genericize =
                        datatype_params.cloned().unwrap_or_default();
                    all_params_for_genericize.extend(type_params.clone());
                    let generic_params: Vec<_> = all_params_for_genericize
                        .iter()
                        .map(|param| AcornType::Variable(param.clone()))
                        .collect();
                    let derecursed = internal_value.set_params(function_name, &generic_params);
                    Some(derecursed.genericize(&all_params_for_genericize))
                } else {
                    // There's no name for this function so it can't possibly be recursive.
                    // This is simpler, but we still need to remove arbitrary local types.
                    // We only genericize the function's own type params, not datatype params
                    // since this isn't recursive.
                    Some(internal_value.genericize(&type_params))
                }
            } else {
                // No internal value, no external value.
                None
            };
            let external_arg_types = internal_arg_types
                .iter()
                .map(|t| t.genericize(&type_params))
                .collect();
            let external_value_type = internal_value_type.genericize(&type_params);

            Ok((
                type_params,
                arg_names,
                external_arg_types,
                external_value,
                external_value_type,
            ))
        }
    }

    /// Finds the names of all constants that are in this module but unknown to this binding map.
    /// The unknown constants may not be polymorphic.
    pub fn find_unknown_scoped_constants(
        &self,
        value: &AcornValue,
        answer: &mut BTreeMap<String, AcornType>,
    ) {
        match value {
            AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
            AcornValue::Constant(c) => {
                if c.name.module_id() == self.module_id && !self.constant_defs.contains_key(&c.name)
                {
                    assert!(c.params.is_empty());
                    answer.insert(c.name.to_string(), c.instance_type.clone());
                }
            }

            AcornValue::Application(app) => {
                self.find_unknown_scoped_constants(&app.function, answer);
                for arg in &app.args {
                    self.find_unknown_scoped_constants(arg, answer);
                }
            }
            AcornValue::TypeApplication(app) => {
                self.find_unknown_scoped_constants(&app.function, answer);
            }
            AcornValue::Lambda(_, value)
            | AcornValue::ForAll(_, value)
            | AcornValue::Exists(_, value)
            | AcornValue::Not(value) => {
                self.find_unknown_scoped_constants(value, answer);
            }
            AcornValue::Try(value, _) => {
                self.find_unknown_scoped_constants(value, answer);
            }
            AcornValue::Binary(_, left, right) => {
                self.find_unknown_scoped_constants(left, answer);
                self.find_unknown_scoped_constants(right, answer);
            }
            AcornValue::IfThenElse(cond, then_value, else_value) => {
                self.find_unknown_scoped_constants(cond, answer);
                self.find_unknown_scoped_constants(then_value, answer);
                self.find_unknown_scoped_constants(else_value, answer);
            }
            AcornValue::Match(scrutinee, cases) => {
                self.find_unknown_scoped_constants(scrutinee, answer);
                for (_, pattern, result) in cases {
                    self.find_unknown_scoped_constants(pattern, answer);
                    self.find_unknown_scoped_constants(result, answer);
                }
            }
        }
    }

    /// Replaces all theorems in the proposition with their definitions.
    /// This is admittedly weird.
    /// Note that it needs to work with templated theorems, which makes it tricky to do the
    /// type inference.
    pub fn expand_theorems(&self, proposition: Proposition, project: &Project) -> Proposition {
        proposition
            .value
            .validate()
            .unwrap_or_else(|e| panic!("invalid claim: {} ({})", proposition.value, e));

        let value = proposition.value.replace_constants(0, &|c| {
            let bindings = self.get_bindings(c.name.module_id(), project);
            if bindings.is_theorem(&c.name) {
                match bindings.get_definition_and_params(&c.name) {
                    Some((def, params)) => {
                        let mut pairs = vec![];
                        for (param, t) in params.iter().zip(c.params.iter()) {
                            pairs.push((param.name.clone(), t.clone()));
                        }
                        Some(def.instantiate(&pairs))
                    }
                    None => None,
                }
            } else {
                None
            }
        });
        proposition.with_value(value)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Tools for testing.
    ////////////////////////////////////////////////////////////////////////////////

    /// Check that the given name actually does have this type in the environment.
    pub fn expect_type(&self, name: &str, type_string: &str) {
        let name = DefinedName::unqualified(self.module_id, name);
        let value = self.get_constant_value(&name).expect("no such constant");
        let env_type = value.get_type();
        assert_eq!(env_type.to_string(), type_string);
    }

    /// Check that this code, when converted to a value and back to code, is the same.
    pub fn expect_good_code(&self, input_code: &str) {
        let project = Project::new_mock();
        let expression = Expression::expect_value(input_code);
        let value = Evaluator::new(&project, self, None)
            .evaluate_value(&expression, None)
            .expect("evaluate_value failed");
        let output_code = CodeGenerator::new(self)
            .value_to_code(&value)
            .expect("value_to_code failed");
        assert_eq!(input_code, output_code);
    }

    /// Returns an iterator over all type names and their corresponding types accessible from these bindings.
    /// This includes types defined in this module as well as imported types.
    pub fn iter_types(&self) -> impl Iterator<Item = (&String, &PotentialType)> {
        self.typename_to_type.iter()
    }

    pub fn iter_typeclasses(&self) -> impl Iterator<Item = (&String, &Typeclass)> {
        self.name_to_typeclass.iter()
    }
}

/// Information about a constructor.
#[derive(Clone)]
pub struct ConstructorInfo {
    /// The datatype that this constructor constructs.
    pub datatype: Datatype,

    /// The index of this constructor in the datatype.
    pub index: usize,

    /// The total number of constructors for this datatype.
    pub total: usize,
}

/// Information about a datatype that is accessible from this module.
#[derive(Clone, Debug)]
struct DatatypeDefinition {
    /// What module defines each of the attributes of this datatype.
    attributes: BTreeMap<String, ModuleId>,

    /// Maps typeclasses this datatype is an instance of to the module with the instance statement.
    typeclasses: HashMap<Typeclass, ModuleId>,

    /// The preferred local name for this datatype.
    alias: Option<String>,

    /// The doc comment for this datatype.
    doc_comments: Vec<String>,

    /// The range in the source code where this datatype was defined.
    range: Option<Range>,

    /// The stringified form of the statement that defined this datatype.
    definition_string: Option<String>,

    /// Variance information for each type parameter.
    /// None means variance hasn't been computed yet (for inductive types being defined).
    /// Some(vec) means variance has been computed, with one entry per type parameter.
    variances: Option<Vec<Variance>>,

    /// The number of type parameters this datatype takes.
    /// This is used to generate the proper kind (e.g., Type -> Type for List).
    arity: u8,
}

impl DatatypeDefinition {
    fn new() -> Self {
        DatatypeDefinition {
            attributes: BTreeMap::new(),
            typeclasses: HashMap::new(),
            alias: None,
            doc_comments: Vec::new(),
            range: None,
            definition_string: None,
            variances: None,
            arity: 0,
        }
    }

    fn import(
        &mut self,
        info: &DatatypeDefinition,
        typename: &str,
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        for (attr, other_module_id) in info.attributes.iter() {
            match self.attributes.get(attr) {
                None => {
                    self.attributes.insert(attr.clone(), *other_module_id);
                }
                Some(module_id) => {
                    if *module_id != *other_module_id {
                        return Err(source.error(&format!(
                            "attribute {}.{} is defined in two different modules",
                            typename, attr
                        )));
                    }
                }
            }
        }
        for (typeclass, other_module_id) in info.typeclasses.iter() {
            if let Some(module_id) = self.typeclasses.insert(typeclass.clone(), *other_module_id) {
                if module_id != *other_module_id {
                    return Err(source.error(&format!(
                        "instance relation {}: {} is defined in two different modules",
                        typename, typeclass.name
                    )));
                }
            }
        }
        Ok(())
    }
}

/// Information about a typeclass that is defined in this module.
#[derive(Clone, Debug)]
struct TypeclassDefinition {
    /// The attributes available to this typeclass.
    /// The value stores (module_id, typeclass) where:
    /// - module_id is the module where this attribute was defined
    /// - typeclass is the typeclass on which this attribute was originally defined (for inheritance)
    attributes: BTreeMap<String, (ModuleId, Typeclass)>,

    /// The attributes that are required to be implemented by instances.
    /// These come from the initial typeclass definition block.
    required: HashSet<String>,

    /// The typeclasses that this typeclass extends.
    extends: HashSet<Typeclass>,

    /// The preferred local name for this typeclass.
    alias: Option<String>,

    /// The documentation comments for this typeclass.
    doc_comments: Vec<String>,

    /// The range in the source code where this typeclass was defined.
    range: Option<Range>,

    /// The stringified form of the statement that defined this typeclass.
    definition_string: Option<String>,
}

impl TypeclassDefinition {
    fn new() -> Self {
        TypeclassDefinition {
            attributes: BTreeMap::new(),
            required: HashSet::new(),
            extends: HashSet::new(),
            alias: None,
            doc_comments: vec![],
            range: None,
            definition_string: None,
        }
    }
}

/// Information that the BindingMap stores about a constant.
#[derive(Clone)]
struct ConstantDefinition {
    /// The value for this constant. Not the definition, but the constant itself.
    /// If this is a generic constant, this value is unresolved.
    value: PotentialValue,

    /// The definition of this constant, if it has one.
    /// Not included for aliases.
    definition: Option<AcornValue>,

    /// Whether this is the canonical name for a constant, as opposed to an alias or an import.
    canonical: bool,

    /// Whether this is a theorem.
    theorem: bool,

    /// If this constant is a constructor and this is its canonical name, store:
    ///   the datatype it constructs
    ///   an index of which constructor it is
    ///   how many total constructors there are
    /// Not included for aliases.
    constructor: Option<ConstructorInfo>,

    /// The doc comments by the definition of this constant.
    doc_comments: Vec<String>,

    /// The range in the source code where this constant was defined.
    range: Option<Range>,

    /// The stringified form of the statement that defined this constant.
    definition_string: Option<String>,
}

/// The way that a typeclass attribute has been defined for a particular instance of a typeclass.
#[derive(Clone)]
struct InstanceAttributeDefinition {
    /// How the attribute is defined.
    value: AcornValue,

    /// The range in the source code where this instance attribute was defined.
    range: Option<Range>,
}

/// Helper for autocomplete.
fn keys_with_prefix<'a, T>(
    map: &'a BTreeMap<String, T>,
    prefix: &'a str,
) -> impl Iterator<Item = &'a String> {
    map.range(prefix.to_string()..)
        .take_while(move |(key, _)| key.starts_with(prefix))
        .map(|(key, _)| key)
}

impl TypeclassRegistry for BindingMap {
    fn is_instance_of(&self, dt: &Datatype, typeclass: &Typeclass) -> bool {
        self.datatype_defs
            .get(dt)
            .map_or(false, |info| info.typeclasses.contains_key(typeclass))
    }

    fn extends(&self, typeclass: &Typeclass, base: &Typeclass) -> bool {
        if let Some(info) = self.typeclass_defs.get(typeclass) {
            info.extends.contains(base)
        } else {
            false
        }
    }
}

#[derive(Clone)]
pub struct ModuleInfo {
    /// The local name of the module, if it has one.
    pub local_name: Option<String>,

    /// The import chain used in the module descriptor.
    pub full_name: Vec<String>,
}
