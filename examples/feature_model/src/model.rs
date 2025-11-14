use std::collections::{HashMap, HashSet};

/// Represents a feature in a feature model
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Feature {
    pub id: u32,
    pub name: String,
}

/// Types of constraints in a feature model
#[derive(Debug, Clone, PartialEq)]
pub enum Constraint {
    /// A feature requires another feature
    Requires(u32, u32), // f1 -> f2
    /// Two features are mutually exclusive
    Excludes(u32, u32), // NOT (f1 AND f2)
    /// At least one feature from the set must be selected
    AtLeastOne(Vec<u32>),
    /// Exactly one feature from the set must be selected
    ExactlyOne(Vec<u32>),
    /// A feature is mandatory (always selected)
    Mandatory(u32),
    /// A feature is optional but conflicts with another
    Optional(u32),
    /// Generic clause (disjunction of literals)
    Clause(Vec<i32>),
}

/// Represents a complete feature model
#[derive(Debug, Clone)]
pub struct FeatureModel {
    pub features: HashMap<u32, Feature>,
    pub constraints: Vec<Constraint>,
    pub root: Option<u32>,
}

impl FeatureModel {
    pub fn new() -> Self {
        Self {
            features: HashMap::new(),
            constraints: Vec::new(),
            root: None,
        }
    }

    /// Add a feature to the model
    pub fn add_feature(&mut self, id: u32, name: String) {
        self.features.insert(id, Feature { id, name });
    }

    /// Add a constraint to the model
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Set the root feature (mandatory)
    pub fn set_root(&mut self, feature_id: u32) {
        self.root = Some(feature_id);
        self.add_constraint(Constraint::Mandatory(feature_id));
    }

    /// Get the number of features
    pub fn num_features(&self) -> usize {
        self.features.len()
    }

    /// Get all feature IDs
    pub fn feature_ids(&self) -> Vec<u32> {
        let mut ids: Vec<_> = self.features.keys().copied().collect();
        ids.sort();
        ids
    }

    /// Get feature name by ID
    pub fn feature_name(&self, id: u32) -> Option<&str> {
        self.features.get(&id).map(|f| f.name.as_str())
    }

    /// Collect all features mentioned in constraints
    pub fn used_features(&self) -> HashSet<u32> {
        let mut used = HashSet::new();

        for constraint in &self.constraints {
            match constraint {
                Constraint::Requires(f1, f2) => {
                    used.insert(*f1);
                    used.insert(*f2);
                }
                Constraint::Excludes(f1, f2) => {
                    used.insert(*f1);
                    used.insert(*f2);
                }
                Constraint::AtLeastOne(features) | Constraint::ExactlyOne(features) => {
                    used.extend(features.iter());
                }
                Constraint::Mandatory(f) | Constraint::Optional(f) => {
                    used.insert(*f);
                }
                Constraint::Clause(literals) => {
                    used.extend(literals.iter().map(|lit| lit.unsigned_abs()));
                }
            }
        }

        used
    }
}

impl Default for FeatureModel {
    fn default() -> Self {
        Self::new()
    }
}
