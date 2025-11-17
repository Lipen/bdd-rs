use bdd_rs::bdd::Bdd;
use bdd_rs::reference::Ref;

use crate::model::{Constraint, FeatureModel};

/// Encode a feature model as a BDD
///
/// Each feature is represented by a variable in the BDD.
/// The resulting BDD represents all valid configurations.
pub fn encode_to_bdd(model: &FeatureModel, bdd: &Bdd) -> Ref {
    let mut result = bdd.one;

    for constraint in &model.constraints {
        let constraint_bdd = encode_constraint(constraint, bdd);
        result = bdd.apply_and(result, constraint_bdd);
    }

    result
}

/// Encode a single constraint as a BDD
fn encode_constraint(constraint: &Constraint, bdd: &Bdd) -> Ref {
    match constraint {
        Constraint::Requires(f1, f2) => {
            // f1 -> f2  equiv  NOT f1 OR f2
            let v1 = bdd.mk_var(*f1);
            let v2 = bdd.mk_var(*f2);
            bdd.apply_or(-v1, v2)
        }

        Constraint::Excludes(f1, f2) => {
            // NOT (f1 AND f2)  equiv  NOT f1 OR NOT f2
            let v1 = bdd.mk_var(*f1);
            let v2 = bdd.mk_var(*f2);
            -bdd.apply_and(v1, v2)
        }

        Constraint::AtLeastOne(features) => {
            // f1 OR f2 OR ... OR fn
            if features.is_empty() {
                return bdd.zero;
            }
            let vars: Vec<Ref> = features.iter().map(|&f| bdd.mk_var(f)).collect();
            bdd.apply_or_many(vars)
        }

        Constraint::ExactlyOne(features) => {
            // Exactly one: at least one AND at most one
            if features.is_empty() {
                return bdd.zero;
            }

            let at_least_one = encode_constraint(&Constraint::AtLeastOne(features.clone()), bdd);

            // At most one: pairwise exclusion
            let mut at_most_one = bdd.one;
            for i in 0..features.len() {
                for j in (i + 1)..features.len() {
                    let excl = encode_constraint(&Constraint::Excludes(features[i], features[j]), bdd);
                    at_most_one = bdd.apply_and(at_most_one, excl);
                }
            }

            bdd.apply_and(at_least_one, at_most_one)
        }

        Constraint::Mandatory(f) => {
            // Feature must be true
            bdd.mk_var(*f)
        }

        Constraint::Optional(_f) => {
            // No constraint (always satisfiable)
            bdd.one
        }

        Constraint::Clause(literals) => {
            // Disjunction of literals
            if literals.is_empty() {
                return bdd.zero;
            }

            let vars: Vec<Ref> = literals
                .iter()
                .map(|&lit| {
                    let var = bdd.mk_var(lit.unsigned_abs());
                    if lit > 0 {
                        var
                    } else {
                        -var
                    }
                })
                .collect();

            bdd.apply_or_many(vars)
        }
    }
}

/// Encode a partial configuration as a BDD
///
/// A configuration is represented as a mapping from feature IDs to boolean values.
/// Returns a BDD representing the cube of assignments.
pub fn encode_configuration(config: &[(u32, bool)], bdd: &Bdd) -> Ref {
    let literals: Vec<i32> = config
        .iter()
        .map(|(feature, value)| {
            let f = *feature as i32;
            if *value {
                f
            } else {
                -f
            }
        })
        .collect();

    if literals.is_empty() {
        bdd.one
    } else {
        bdd.mk_cube(literals)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_requires() {
        let bdd = Bdd::default();
        let constraint = Constraint::Requires(1, 2);
        let result = encode_constraint(&constraint, &bdd);

        // f1 -> f2 should be satisfied by: (0,0), (0,1), (1,1)
        // Not satisfied by: (1,0)
        assert!(!bdd.is_zero(result));

        // Test specific configuration: f1=true, f2=false should be invalid
        let f1 = bdd.mk_var(1);
        let f2 = bdd.mk_var(2);
        let invalid_config = bdd.apply_and(f1, -f2);
        let check = bdd.apply_and(result, invalid_config);
        assert!(bdd.is_zero(check));
    }

    #[test]
    fn test_encode_excludes() {
        let bdd = Bdd::default();
        let constraint = Constraint::Excludes(1, 2);
        let result = encode_constraint(&constraint, &bdd);

        // NOT (f1 AND f2): satisfied by (0,0), (0,1), (1,0)
        // Not satisfied by: (1,1)
        let f1 = bdd.mk_var(1);
        let f2 = bdd.mk_var(2);
        let invalid_config = bdd.apply_and(f1, f2);
        let check = bdd.apply_and(result, invalid_config);
        assert!(bdd.is_zero(check));
    }

    #[test]
    fn test_encode_at_least_one() {
        let bdd = Bdd::default();
        let constraint = Constraint::AtLeastOne(vec![1, 2, 3]);
        let result = encode_constraint(&constraint, &bdd);

        // At least one must be true
        assert!(!bdd.is_zero(result));

        // Check that all false is invalid
        let all_false = bdd.apply_and_many([-bdd.mk_var(1), -bdd.mk_var(2), -bdd.mk_var(3)]);
        let check = bdd.apply_and(result, all_false);
        assert!(bdd.is_zero(check));
    }

    #[test]
    fn test_encode_exactly_one() {
        let bdd = Bdd::default();
        let constraint = Constraint::ExactlyOne(vec![1, 2, 3]);
        let result = encode_constraint(&constraint, &bdd);

        // Exactly one must be true
        assert!(!bdd.is_zero(result));

        // Check that having two true is invalid
        let f1 = bdd.mk_var(1);
        let f2 = bdd.mk_var(2);
        let two_true = bdd.apply_and(f1, f2);
        let check = bdd.apply_and(result, two_true);
        assert!(bdd.is_zero(check));

        // Check that having one true is valid
        let one_true = bdd.apply_and(f1, bdd.apply_and(-f2, -bdd.mk_var(3)));
        let check = bdd.apply_and(result, one_true);
        assert!(!bdd.is_zero(check));
    }

    #[test]
    fn test_encode_full_model() {
        let bdd = Bdd::default();
        let mut model = FeatureModel::new();

        model.add_feature(1, "Base".to_string());
        model.add_feature(2, "GUI".to_string());
        model.add_feature(3, "CLI".to_string());

        model.set_root(1);
        model.add_constraint(Constraint::AtLeastOne(vec![2, 3]));
        model.add_constraint(Constraint::Excludes(2, 3));

        let result = encode_to_bdd(&model, &bdd);

        // Should have exactly 2 valid configurations:
        // (Base=true, GUI=true, CLI=false) and (Base=true, GUI=false, CLI=true)
        let count = bdd.sat_count(result, 3);
        assert_eq!(count, 2u32.into());
    }
}
