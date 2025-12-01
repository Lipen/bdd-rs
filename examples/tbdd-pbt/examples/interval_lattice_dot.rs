//! Interval Lattice DOT Visualization
//!
//! Generates a DOT graph of the interval domain lattice for bounded intervals [a, b]
//! where a, b ∈ {0, ..., N}. Edges represent the ⊑ (less than or equal) relation.
//!
//! Run with: `cargo run -p tbdd-pbt --example interval_lattice_dot > interval_lattice.dot`
//! Then: `dot interval_lattice.dot -Tpdf -O`

use tbdd_pbt::domain::{AbstractDomain, Bound, Interval};

/// Generate all valid intervals [a, b] where 0 <= a <= b <= max_bound
fn generate_intervals(max_bound: i64) -> Vec<Interval> {
    let mut intervals = Vec::new();

    // Add bottom (empty interval)
    intervals.push(Interval::bottom());

    // Add all finite intervals [a, b] where a <= b
    for a in 0..=max_bound {
        for b in a..=max_bound {
            intervals.push(Interval::from_bounds(a, b));
        }
    }

    // Add top (all integers) - but for visualization we skip it
    // since it would connect to everything
    // intervals.push(Interval::top());

    intervals
}

/// Get a unique node ID for an interval
fn node_id(interval: &Interval) -> String {
    if interval.is_bottom() {
        "bot".to_string()
    } else if interval.is_top() {
        "top".to_string()
    } else {
        match (interval.low(), interval.high()) {
            (Bound::Finite(a), Bound::Finite(b)) => format!("i_{}_{}", a, b),
            _ => "unknown".to_string(),
        }
    }
}

/// Get a human-readable label for an interval
fn node_label(interval: &Interval) -> String {
    if interval.is_bottom() {
        "⊥".to_string()
    } else if interval.is_top() {
        "⊤".to_string()
    } else {
        match (interval.low(), interval.high()) {
            (Bound::Finite(a), Bound::Finite(b)) if a == b => format!("{{{}}}", a),
            (Bound::Finite(a), Bound::Finite(b)) => format!("[{}, {}]", a, b),
            _ => format!("{:?}", interval),
        }
    }
}

/// Check if interval `a` is an immediate predecessor of `b` in the lattice
/// (i.e., a ⊑ b and there's no c such that a ⊏ c ⊏ b)
fn is_immediate_predecessor(a: &Interval, b: &Interval, all: &[Interval]) -> bool {
    if !a.leq(b) || a == b {
        return false;
    }

    // Check that no interval c exists where a ⊏ c ⊏ b
    for c in all {
        if c != a && c != b && a.leq(c) && c.leq(b) {
            return false;
        }
    }

    true
}

/// Compute the "level" of an interval in the lattice (for ranking)
/// Level = width of interval + 1 (bottom is level 0)
fn interval_level(interval: &Interval) -> i64 {
    if interval.is_bottom() {
        0
    } else if interval.is_top() {
        i64::MAX
    } else {
        match (interval.low(), interval.high()) {
            (Bound::Finite(a), Bound::Finite(b)) => (b - a) + 1,
            _ => i64::MAX,
        }
    }
}

fn main() {
    // Use max_bound = 4 for a manageable lattice
    // This gives: 1 bottom + C(5,2) + 5 = 1 + 10 + 5 = 16 intervals
    // Actually: 1 bottom + sum(i=0..4)(5-i) = 1 + 5+4+3+2+1 = 16 intervals
    let max_bound = 4;

    let intervals = generate_intervals(max_bound);

    eprintln!("Generated {} intervals for bounds [0, {}]", intervals.len(), max_bound);

    // Compute Hasse diagram edges (immediate predecessors only)
    let mut edges: Vec<(usize, usize)> = Vec::new();

    for (i, a) in intervals.iter().enumerate() {
        for (j, b) in intervals.iter().enumerate() {
            if is_immediate_predecessor(a, b, &intervals) {
                edges.push((i, j));
            }
        }
    }

    eprintln!("Found {} Hasse diagram edges", edges.len());

    // Group intervals by level for ranking
    let mut levels: std::collections::BTreeMap<i64, Vec<usize>> = std::collections::BTreeMap::new();
    for (i, interval) in intervals.iter().enumerate() {
        let level = interval_level(interval);
        levels.entry(level).or_default().push(i);
    }

    // Output DOT
    println!("// Interval lattice for [0, {}]", max_bound);
    println!("// {} nodes, {} edges", intervals.len(), edges.len());
    println!("digraph IntervalLattice {{");
    println!("    rankdir=BT;  // Bottom to top");
    println!("    node [shape=box, fontname=\"Helvetica\", fontsize=10];");
    println!("    edge [arrowsize=0.5];");
    println!();

    // Output nodes grouped by rank
    for (level, indices) in &levels {
        println!("    // Level {} (width {})", level, level);
        println!("    {{ rank=same;");
        for &i in indices {
            let interval = &intervals[i];
            let id = node_id(interval);
            let label = node_label(interval);

            // Style bottom specially
            if interval.is_bottom() {
                println!(
                    "        {} [label=\"{}\", shape=diamond, style=filled, fillcolor=lightgray];",
                    id, label
                );
            } else {
                // Color by width: singletons are darker
                let width = match (interval.low(), interval.high()) {
                    (Bound::Finite(a), Bound::Finite(b)) => (b - a) as f64,
                    _ => 0.0,
                };
                let hue = 0.6; // Blue
                let saturation = 0.3 - (width / (max_bound as f64 + 1.0)) * 0.25;
                let value = 1.0;
                println!(
                    "        {} [label=\"{}\", style=filled, fillcolor=\"{} {} {}\"];",
                    id, label, hue, saturation, value
                );
            }
        }
        println!("    }}");
        println!();
    }

    // Output edges
    println!("    // Hasse diagram edges (immediate ⊑ relations)");
    for (i, j) in &edges {
        let from_id = node_id(&intervals[*i]);
        let to_id = node_id(&intervals[*j]);
        println!("    {} -> {};", from_id, to_id);
    }

    println!("}}");

    eprintln!();
    eprintln!("To render: dot -Tpdf interval_lattice.dot -o interval_lattice.pdf");
    eprintln!("       or: dot -Tsvg interval_lattice.dot -o interval_lattice.svg");
}
