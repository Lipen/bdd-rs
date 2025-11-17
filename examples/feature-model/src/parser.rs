use std::collections::HashMap;
use std::io::{BufRead, BufReader, Read};

use crate::model::{Constraint, FeatureModel};

/// Parse a feature model from DIMACS CNF format
///
/// DIMACS CNF format:
/// - Comments start with 'c'
/// - Problem line: p cnf <num_vars> <num_clauses>
/// - Each clause is a line of space-separated integers, terminated by 0
/// - Positive integers represent features, negative represent NOT feature
/// - Feature names can be specified in comments: c feature <id> <name>
pub fn parse_dimacs<R: Read>(reader: R) -> Result<FeatureModel, String> {
    let mut model = FeatureModel::new();
    let buf_reader = BufReader::new(reader);
    let mut feature_names: HashMap<u32, String> = HashMap::new();
    let mut num_vars = 0;
    let mut num_clauses = 0;
    let mut clauses_parsed = 0;

    for line in buf_reader.lines() {
        let line = line.map_err(|e| format!("IO error: {}", e))?;
        let line = line.trim();

        // Skip empty lines
        if line.is_empty() {
            continue;
        }

        // Parse comments
        if line.starts_with('c') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() >= 3 && parts[1] == "feature" {
                // Comment format: c feature <id> <name>
                if let Ok(id) = parts[2].parse::<u32>() {
                    let name = parts[3..].join(" ");
                    feature_names.insert(id, name);
                }
            }
            continue;
        }

        // Parse problem line
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err("Invalid problem line format".to_string());
            }
            num_vars = parts[2].parse::<usize>().map_err(|_| "Invalid number of variables".to_string())?;
            num_clauses = parts[3].parse::<usize>().map_err(|_| "Invalid number of clauses".to_string())?;
            continue;
        }

        // Parse clause
        let literals: Result<Vec<i32>, _> = line
            .split_whitespace()
            .filter(|s| !s.is_empty())
            .map(|s| s.parse::<i32>())
            .collect();

        let mut literals = literals.map_err(|_| format!("Invalid literal in clause: {}", line))?;

        // Remove trailing zero
        if literals.last() == Some(&0) {
            literals.pop();
        }

        if !literals.is_empty() {
            model.add_constraint(Constraint::Clause(literals));
            clauses_parsed += 1;
        }
    }

    // Add features based on num_vars
    for id in 1..=num_vars as u32 {
        let name = feature_names.remove(&id).unwrap_or_else(|| format!("f{}", id));
        model.add_feature(id, name);
    }

    if clauses_parsed != num_clauses {
        log::warn!("Expected {} clauses but parsed {}", num_clauses, clauses_parsed);
    }

    Ok(model)
}

/// Parse a feature model from a simple text format
///
/// Format:
/// - One constraint per line
/// - `feature <id> <name>` - Define a feature
/// - `root <id>` - Set root feature (mandatory)
/// - `requires <f1> <f2>` - f1 requires f2
/// - `excludes <f1> <f2>` - f1 and f2 are mutually exclusive
/// - `atleastone <f1> <f2> ...` - At least one must be selected
/// - `exactlyone <f1> <f2> ...` - Exactly one must be selected
/// - `mandatory <f>` - Feature is mandatory
/// - Lines starting with '#' are comments
pub fn parse_simple<R: Read>(reader: R) -> Result<FeatureModel, String> {
    let mut model = FeatureModel::new();
    let buf_reader = BufReader::new(reader);

    for (line_num, line) in buf_reader.lines().enumerate() {
        let line = line.map_err(|e| format!("IO error at line {}: {}", line_num + 1, e))?;
        let line = line.trim();

        // Skip empty lines and comments
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            continue;
        }

        match parts[0] {
            "feature" => {
                if parts.len() < 3 {
                    return Err(format!("Line {}: feature requires id and name", line_num + 1));
                }
                let id = parts[1]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                let name = parts[2..].join(" ");
                model.add_feature(id, name);
            }
            "root" => {
                if parts.len() != 2 {
                    return Err(format!("Line {}: root requires feature id", line_num + 1));
                }
                let id = parts[1]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                model.set_root(id);
            }
            "requires" => {
                if parts.len() != 3 {
                    return Err(format!("Line {}: requires needs two feature ids", line_num + 1));
                }
                let f1 = parts[1]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                let f2 = parts[2]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                model.add_constraint(Constraint::Requires(f1, f2));
            }
            "excludes" => {
                if parts.len() != 3 {
                    return Err(format!("Line {}: excludes needs two feature ids", line_num + 1));
                }
                let f1 = parts[1]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                let f2 = parts[2]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                model.add_constraint(Constraint::Excludes(f1, f2));
            }
            "atleastone" => {
                if parts.len() < 2 {
                    return Err(format!("Line {}: atleastone needs feature ids", line_num + 1));
                }
                let features: Result<Vec<u32>, _> = parts[1..].iter().map(|s| s.parse::<u32>()).collect();
                let features = features.map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                model.add_constraint(Constraint::AtLeastOne(features));
            }
            "exactlyone" => {
                if parts.len() < 2 {
                    return Err(format!("Line {}: exactlyone needs feature ids", line_num + 1));
                }
                let features: Result<Vec<u32>, _> = parts[1..].iter().map(|s| s.parse::<u32>()).collect();
                let features = features.map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                model.add_constraint(Constraint::ExactlyOne(features));
            }
            "mandatory" => {
                if parts.len() != 2 {
                    return Err(format!("Line {}: mandatory requires feature id", line_num + 1));
                }
                let id = parts[1]
                    .parse::<u32>()
                    .map_err(|_| format!("Line {}: invalid feature id", line_num + 1))?;
                model.add_constraint(Constraint::Mandatory(id));
            }
            _ => {
                return Err(format!("Line {}: unknown constraint type '{}'", line_num + 1, parts[0]));
            }
        }
    }

    Ok(model)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_dimacs() {
        let input = r#"
c Simple feature model
c feature 1 Base
c feature 2 FeatureA
c feature 3 FeatureB
p cnf 3 3
1 0
-2 1 0
-2 -3 0
"#;
        let model = parse_dimacs(input.as_bytes()).unwrap();
        assert_eq!(model.num_features(), 3);
        assert_eq!(model.constraints.len(), 3);
    }

    #[test]
    fn test_parse_simple() {
        let input = r#"
# Simple feature model
feature 1 Base
feature 2 GUI
feature 3 CLI
root 1
requires 2 1
excludes 2 3
"#;
        let model = parse_simple(input.as_bytes()).unwrap();
        assert_eq!(model.num_features(), 3);
        assert_eq!(model.root, Some(1));
    }
}
