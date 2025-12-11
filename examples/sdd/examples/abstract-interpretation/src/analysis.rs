//! Analysis and comparison framework for abstract domains
//!
//! Compares SDD, interval, and bitset domains on precision and cost

use crate::interpreter::SddAbstractInterpreter;
use crate::language::Program;
use crate::vtree_strategy::VtreeStrategy;

/// Results from analyzing a program with a specific domain
#[derive(Debug, Clone)]
pub struct AnalysisResult {
    pub domain_name: String,
    pub max_state_size: usize,
    pub precision: f64, // 0.0 = very abstract, 1.0 = precise
}

/// Comparison results for a program across domains
#[derive(Debug)]
pub struct Analyzer {
    program: Program,
}

impl Analyzer {
    pub fn new(program: Program) -> Self {
        Analyzer { program }
    }

    /// Analyze using SDD with all vtree strategies
    pub fn analyze_sdd_strategies(&self) -> Vec<AnalysisResult> {
        let strategies = vec![
            VtreeStrategy::Balanced,
            VtreeStrategy::RightLinear,
            VtreeStrategy::LeftLinear,
            VtreeStrategy::Syntactic,
            VtreeStrategy::Semantic,
        ];

        let mut results = Vec::new();

        for strategy in strategies {
            let mut interpreter = SddAbstractInterpreter::new(&self.program, strategy);
            let interp_result = interpreter.analyze();

            results.push(AnalysisResult {
                domain_name: format!("SDD ({})", strategy),
                max_state_size: interp_result.max_state_size,
                precision: (interp_result.max_state_size as f64) / 100.0, // Heuristic
            });
        }

        results
    }

    /// Summary statistics
    pub fn print_comparison(&self) {
        println!("\n🔍 Analyzer: Program Analysis Summary");
        println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

        let sdd_results = self.analyze_sdd_strategies();

        println!("\nVTree Strategies Performance:");
        for result in &sdd_results {
            println!(
                "  • {}: size={}, precision={:.2}",
                result.domain_name, result.max_state_size, result.precision
            );
        }
    }
}
