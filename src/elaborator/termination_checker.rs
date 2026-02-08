use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::AtomId;

// The TerminationChecker determines whether recursive functions will always terminate,
// because they always get called on a substructure of the input.
pub struct TerminationChecker {
    // The function whose definition we are checking.
    name: ConstantName,

    // substructure[i] = j if x_i is a ubstructure of x_j, due to match relationships.
    // j is the smallest such j.
    // This includes the non-strict substructures.
    substructure_map: Vec<Option<AtomId>>,

    // always_sub[i] is true if the ith argument to the recursive function is always a *strict*
    // substructure of the original ith argument.
    always_strict_sub: Vec<bool>,
}

impl TerminationChecker {
    pub fn new(name: ConstantName, num_args: usize) -> Self {
        let substructure_map = (0..num_args).map(|i| Some(i as AtomId)).collect();
        let always_strict_sub = vec![true; num_args];
        TerminationChecker {
            name,
            substructure_map,
            always_strict_sub,
        }
    }

    // Traverse the value, updating substructure_map and always_sub.
    fn traverse(&mut self, value: &AcornValue) {
        match value {
            AcornValue::Variable(..) | AcornValue::Bool(..) => {
                // These values can't contain function calls within them, so they don't matter.
            }
            AcornValue::Constant(c) => {
                if &c.name == &self.name {
                    // We are using the recursive function without calling it, so we can't
                    // really say that any of its arguments are always strict any more.
                    self.always_strict_sub = vec![false; self.always_strict_sub.len()];
                }
            }
            AcornValue::TypeApplication(app) => {
                self.traverse(&app.function);
            }
            AcornValue::Lambda(arg_types, value)
            | AcornValue::ForAll(arg_types, value)
            | AcornValue::Exists(arg_types, value) => {
                // These arguments are not substructures of anything.
                let stack_size = self.substructure_map.len();
                for _ in 0..arg_types.len() {
                    self.substructure_map.push(None);
                }
                self.traverse(value);
                self.substructure_map.truncate(stack_size);
            }
            AcornValue::Not(value) => {
                self.traverse(value);
            }
            AcornValue::Try(value, _) => {
                self.traverse(value);
            }
            AcornValue::Binary(_, left, right) => {
                self.traverse(left);
                self.traverse(right);
            }
            AcornValue::IfThenElse(a, b, c) => {
                self.traverse(a);
                self.traverse(b);
                self.traverse(c);
            }
            AcornValue::Application(app) => {
                if let AcornValue::Application(subapp) = &*app.function {
                    // This is a curried function call.
                    // Let's just uncurry it. There's an extraneous clone but it's probably fine.
                    let combined_args =
                        subapp.args.iter().chain(app.args.iter()).cloned().collect();
                    let uncurried = AcornValue::apply(*subapp.function.clone(), combined_args);
                    self.traverse(&uncurried);
                    return;
                }

                if Some(&self.name) == app.function.as_name() {
                    // This is a recursive call. Check the arguments for substructures.
                    for i in 0..self.always_strict_sub.len() {
                        if i >= app.args.len() {
                            // This corresponds to partially binding the function arguments.
                            // I think this is okay as long as some bound argument adheres to
                            // the substructure argument.
                            self.always_strict_sub[i] = false;
                            continue;
                        }

                        let arg = &app.args[i];
                        let strict_sub = if let AcornValue::Variable(j, _) = arg {
                            let j = *j as usize;
                            i != j && self.substructure_map[j] == Some(i as AtomId)
                        } else {
                            false
                        };
                        self.always_strict_sub[i] &= strict_sub;
                    }
                } else {
                    self.traverse(app.function.as_ref());
                }
                for arg in &app.args {
                    self.traverse(arg);
                }
            }
            AcornValue::Match(scrutinee, cases) => {
                self.traverse(scrutinee);
                let superstructure = match scrutinee.as_ref() {
                    AcornValue::Variable(i, _) => Some(*i as AtomId),
                    _ => None,
                };
                let stack_size = self.substructure_map.len();
                for (args, pattern, result) in cases {
                    for _ in args {
                        self.substructure_map.push(superstructure);
                    }
                    self.traverse(pattern);
                    self.traverse(result);
                    self.substructure_map.truncate(stack_size);
                }
            }
        }
    }

    pub fn check(&mut self, value: &AcornValue) -> bool {
        self.traverse(value);

        // If any of the arguments is always a substructure, that is a proof of termination.
        self.always_strict_sub.contains(&true)
    }
}
