use std::collections::HashMap;

use ananke_bdd::bdd::Bdd;
use ananke_bdd::reference::Ref;
use num_bigint::BigUint;

use crate::model::FeatureModel;

/// Analyzer for feature model queries
pub struct FeatureAnalyzer<'a> {
    pub model: &'a FeatureModel,
    pub bdd: &'a Bdd,
    pub valid_configs: Ref,
}

impl<'a> FeatureAnalyzer<'a> {
    pub fn new(model: &'a FeatureModel, bdd: &'a Bdd, valid_configs: Ref) -> Self {
        Self { model, bdd, valid_configs }
    }

    /// Check if the feature model has any valid configuration
    pub fn is_valid(&self) -> bool {
        !self.bdd.is_zero(self.valid_configs)
    }

    /// Count the number of valid configurations
    pub fn count_configurations(&self) -> BigUint {
        let num_features = self.model.num_features();
        self.bdd.sat_count(self.valid_configs, num_features)
    }

    /// Check if a specific configuration is valid
    pub fn is_configuration_valid(&self, config: &HashMap<u32, bool>) -> bool {
        let mut partial = self.valid_configs;

        for (&feature_id, &value) in config {
            let var = self.bdd.mk_var(feature_id);
            let assignment = if value { var } else { -var };
            partial = self.bdd.apply_and(partial, assignment);

            if self.bdd.is_zero(partial) {
                return false;
            }
        }

        true
    }

    /// Find one valid configuration
    pub fn find_one_configuration(&self) -> Option<HashMap<u32, bool>> {
        let assignment = self.bdd.one_sat(self.valid_configs)?;

        let mut config = HashMap::new();
        for lit in assignment {
            let feature_id = lit.var().id();
            let value = lit.is_positive();
            config.insert(feature_id, value);
        }

        Some(config)
    }

    /// Find all core features (features that appear in ALL valid configurations)
    pub fn core_features(&self) -> Vec<u32> {
        let mut core = Vec::new();

        for &feature_id in self.model.features.keys() {
            let var = self.bdd.mk_var(feature_id);

            // Feature is core if valid_configs -> feature
            // Which is equivalent to: valid_configs AND NOT feature == false
            let without_feature = self.bdd.apply_and(self.valid_configs, -var);

            if self.bdd.is_zero(without_feature) {
                core.push(feature_id);
            }
        }

        core.sort();
        core
    }

    /// Find all dead features (features that appear in NO valid configuration)
    pub fn dead_features(&self) -> Vec<u32> {
        let mut dead = Vec::new();

        for &feature_id in self.model.features.keys() {
            let var = self.bdd.mk_var(feature_id);

            // Feature is dead if valid_configs AND feature == false
            let with_feature = self.bdd.apply_and(self.valid_configs, var);

            if self.bdd.is_zero(with_feature) {
                dead.push(feature_id);
            }
        }

        dead.sort();
        dead
    }

    /// Compute commonality of a feature (percentage of configs where it's selected)
    /// Returns a value between 0.0 and 1.0
    pub fn feature_commonality(&self, feature_id: u32) -> f64 {
        let total = self.count_configurations();

        if total == BigUint::ZERO {
            return 0.0;
        }

        let var = self.bdd.mk_var(feature_id);
        let with_feature = self.bdd.apply_and(self.valid_configs, var);
        let count_with = self.bdd.sat_count(with_feature, self.model.num_features());

        // Convert to f64 for division
        let total_f64 = bigint_to_f64(&total);
        let count_f64 = bigint_to_f64(&count_with);

        if total_f64 > 0.0 {
            count_f64 / total_f64
        } else {
            0.0
        }
    }

    /// Find all false optional features (features that could be removed)
    /// These are features that are not core and not dead
    pub fn optional_features(&self) -> Vec<u32> {
        let core_set: std::collections::HashSet<_> = self.core_features().into_iter().collect();
        let dead_set: std::collections::HashSet<_> = self.dead_features().into_iter().collect();

        let mut optional = Vec::new();
        for &feature_id in self.model.features.keys() {
            if !core_set.contains(&feature_id) && !dead_set.contains(&feature_id) {
                optional.push(feature_id);
            }
        }

        optional.sort();
        optional
    }

    /// Check if two features are mutually exclusive in all valid configurations
    pub fn are_mutually_exclusive(&self, f1: u32, f2: u32) -> bool {
        let var1 = self.bdd.mk_var(f1);
        let var2 = self.bdd.mk_var(f2);

        // Both features selected simultaneously
        let both = self.bdd.apply_and(var1, var2);
        let both_in_valid = self.bdd.apply_and(self.valid_configs, both);

        // If no valid config has both, they're mutually exclusive
        self.bdd.is_zero(both_in_valid)
    }

    /// Check if feature f1 requires feature f2 in all valid configurations
    pub fn implies(&self, f1: u32, f2: u32) -> bool {
        let var1 = self.bdd.mk_var(f1);
        let var2 = self.bdd.mk_var(f2);

        // f1 selected but f2 not selected
        let f1_without_f2 = self.bdd.apply_and(var1, -var2);
        let invalid = self.bdd.apply_and(self.valid_configs, f1_without_f2);

        // If no valid config has f1 without f2, then f1 implies f2
        self.bdd.is_zero(invalid)
    }

    /// Get statistics about the feature model
    pub fn statistics(&self) -> FeatureModelStatistics {
        let num_features = self.model.num_features();
        let num_constraints = self.model.constraints.len();
        let num_configs = self.count_configurations();
        let core = self.core_features();
        let dead = self.dead_features();
        let optional = self.optional_features();

        FeatureModelStatistics {
            num_features,
            num_constraints,
            num_configurations: num_configs.clone(),
            num_core_features: core.len(),
            num_dead_features: dead.len(),
            num_optional_features: optional.len(),
            bdd_size: self.bdd.size(self.valid_configs),
            config_space_size: BigUint::from(2u32).pow(num_features as u32),
            coverage_ratio: if num_features > 0 {
                bigint_to_f64(&num_configs) / bigint_to_f64(&BigUint::from(2u32).pow(num_features as u32))
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct FeatureModelStatistics {
    pub num_features: usize,
    pub num_constraints: usize,
    pub num_configurations: BigUint,
    pub num_core_features: usize,
    pub num_dead_features: usize,
    pub num_optional_features: usize,
    pub bdd_size: u64,
    pub config_space_size: BigUint,
    pub coverage_ratio: f64,
}

impl std::fmt::Display for FeatureModelStatistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Feature Model Statistics:")?;
        writeln!(f, "  Features:       {}", self.num_features)?;
        writeln!(f, "  Constraints:    {}", self.num_constraints)?;
        writeln!(f, "  Valid configs:  {}", self.num_configurations)?;
        writeln!(f, "  Config space:   {}", self.config_space_size)?;
        writeln!(f, "  Coverage:       {:.2}%", self.coverage_ratio * 100.0)?;
        writeln!(f, "  Core features:  {}", self.num_core_features)?;
        writeln!(f, "  Dead features:  {}", self.num_dead_features)?;
        writeln!(f, "  Optional:       {}", self.num_optional_features)?;
        writeln!(f, "  BDD size:       {} nodes", self.bdd_size)?;
        Ok(())
    }
}

/// Convert BigUint to f64 (with potential precision loss for very large numbers)
fn bigint_to_f64(n: &BigUint) -> f64 {
    // Convert to string and parse (simple but works for reasonable sizes)
    n.to_string().parse::<f64>().unwrap_or(f64::INFINITY)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoder::encode_to_bdd;

    #[test]
    fn test_simple_analysis() {
        let bdd = Bdd::default();
        let mut model = FeatureModel::new();

        model.add_feature(1, "Base".to_string());
        model.add_feature(2, "FeatureA".to_string());

        model.add_constraint(crate::model::Constraint::Mandatory(1));

        let valid_configs = encode_to_bdd(&model, &bdd);
        let analyzer = FeatureAnalyzer::new(&model, &bdd, valid_configs);

        assert!(analyzer.is_valid());
        assert_eq!(analyzer.count_configurations(), 2u32.into()); // Base=true, FeatureA can be true/false

        let core = analyzer.core_features();
        assert_eq!(core, vec![1]); // Base is mandatory
    }

    #[test]
    fn test_dead_feature() {
        let bdd = Bdd::default();
        let mut model = FeatureModel::new();

        model.add_feature(1, "Feature1".to_string());
        model.add_feature(2, "Feature2".to_string());

        // Feature2 requires Feature1
        model.add_constraint(crate::model::Constraint::Requires(2, 1));
        // But Feature1 cannot be selected
        model.add_constraint(crate::model::Constraint::Clause(vec![-1]));

        let valid_configs = encode_to_bdd(&model, &bdd);
        let analyzer = FeatureAnalyzer::new(&model, &bdd, valid_configs);

        let dead = analyzer.dead_features();
        assert!(dead.contains(&2)); // Feature2 is dead (can never be selected)
    }

    #[test]
    fn test_mutual_exclusion() {
        let bdd = Bdd::default();
        let mut model = FeatureModel::new();

        model.add_feature(1, "GUI".to_string());
        model.add_feature(2, "CLI".to_string());

        model.add_constraint(crate::model::Constraint::Excludes(1, 2));

        let valid_configs = encode_to_bdd(&model, &bdd);
        let analyzer = FeatureAnalyzer::new(&model, &bdd, valid_configs);

        assert!(analyzer.are_mutually_exclusive(1, 2));

        // 3 valid configs: (0,0), (1,0), (0,1)
        assert_eq!(analyzer.count_configurations(), 3u32.into());
    }
}
