//! BDD-level cache benchmarks.
//!
//! These benchmarks measure cache performance in the context of actual BDD operations,
//! providing realistic workload patterns.
//!
//! Run with:
//! ```bash
//! cargo bench --bench bdd_cache
//! ```

use bdd_rs::bdd::{Bdd, BddConfig};
use bdd_rs::reference::Ref;
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

// ============================================================================
// Helper: N-Queens Problem (canonical BDD benchmark)
// ============================================================================

/// Solve N-Queens and return the result BDD along with cache stats.
fn solve_queens(bdd: &Bdd, n: usize) -> (Ref, usize, usize) {
    // Variables: q[i][j] = queen at row i, column j
    // Using 1-indexed variables: var(i, j) = i * n + j + 1
    let var = |i: usize, j: usize| -> Ref { bdd.mk_var((i * n + j + 1) as u32) };

    let mut result = bdd.one();

    // Row constraints: exactly one queen per row
    for i in 0..n {
        // At least one: OR of all columns
        let mut at_least_one = bdd.zero();
        for j in 0..n {
            at_least_one = bdd.apply_or(at_least_one, var(i, j));
        }
        result = bdd.apply_and(result, at_least_one);

        // At most one: no two queens in same row
        for j1 in 0..n {
            for j2 in (j1 + 1)..n {
                let not_both = bdd.apply_or(-var(i, j1), -var(i, j2));
                result = bdd.apply_and(result, not_both);
            }
        }
    }

    // Column constraints: at most one queen per column
    for j in 0..n {
        for i1 in 0..n {
            for i2 in (i1 + 1)..n {
                let not_both = bdd.apply_or(-var(i1, j), -var(i2, j));
                result = bdd.apply_and(result, not_both);
            }
        }
    }

    // Diagonal constraints
    for i1 in 0..n {
        for j1 in 0..n {
            for i2 in (i1 + 1)..n {
                for j2 in 0..n {
                    // Check if on same diagonal
                    let di = i2 - i1;
                    if j2 == j1 + di || (j1 >= di && j2 == j1 - di) {
                        let not_both = bdd.apply_or(-var(i1, j1), -var(i2, j2));
                        result = bdd.apply_and(result, not_both);
                    }
                }
            }
        }
    }

    let cache = bdd.cache();
    (result, cache.hits(), cache.misses())
}

// ============================================================================
// Helper: Random Boolean Formula
// ============================================================================

/// Build a random boolean formula with specified depth and width.
fn build_random_formula(bdd: &Bdd, num_vars: usize, num_ops: usize, seed: u64) -> Ref {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);

    // Create variables
    let vars: Vec<Ref> = (1..=num_vars).map(|i| bdd.mk_var(i as u32)).collect();

    // Start with some random literals
    let mut nodes: Vec<Ref> = vars.iter().map(|&v| if rng.random_bool(0.5) { v } else { -v }).collect();

    // Build formula by random operations
    for _ in 0..num_ops {
        if nodes.len() < 2 {
            break;
        }

        let i = rng.random_range(0..nodes.len());
        let j = rng.random_range(0..nodes.len());
        if i == j {
            continue;
        }

        let a = nodes[i];
        let b = nodes[j];

        let result = match rng.random_range(0..4) {
            0 => bdd.apply_and(a, b),
            1 => bdd.apply_or(a, b),
            2 => bdd.apply_xor(a, b),
            _ => bdd.apply_imply(a, b),
        };

        // Replace one operand with result
        nodes[i] = result;
    }

    // Combine all remaining nodes
    nodes.into_iter().fold(bdd.one(), |acc, n| bdd.apply_and(acc, n))
}

// ============================================================================
// Benchmark: N-Queens with different cache sizes
// ============================================================================

fn bench_queens_cache_size(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/queens_cache_size");
    group.sample_size(10); // Queens can be slow

    let n = 6; // 6-queens is fast enough for benchmarking

    for cache_bits in [12, 14, 16, 18, 20] {
        group.bench_with_input(
            BenchmarkId::new(format!("n={}", n), format!("2^{}", cache_bits)),
            &cache_bits,
            |b, &cache_bits| {
                b.iter(|| {
                    let config = BddConfig::default().with_cache_bits(cache_bits);
                    let bdd = Bdd::with_config(config);
                    let (result, hits, misses) = solve_queens(&bdd, n);
                    (result, hits, misses)
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Queens scaling (N=4 to N=8)
// ============================================================================

fn bench_queens_scaling(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/queens_scaling");
    group.sample_size(10);

    let cache_bits = 18; // 256K entries

    for n in [4, 5, 6, 7] {
        group.bench_with_input(BenchmarkId::new("queens", n), &n, |b, &n| {
            b.iter(|| {
                let config = BddConfig::default().with_cache_bits(cache_bits);
                let bdd = Bdd::with_config(config);
                let (result, hits, misses) = solve_queens(&bdd, n);
                (result, hits, misses)
            });
        });
    }

    group.finish();
}

// ============================================================================
// Benchmark: Random formulas (tests diverse operation patterns)
// ============================================================================

fn bench_random_formula(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/random_formula");

    let num_vars: usize = 20;
    let num_ops = 1000;
    let seed = 42;

    for cache_bits in [14, 16, 18] {
        let config = BddConfig::default().with_cache_bits(cache_bits);

        group.bench_with_input(
            BenchmarkId::new("v=20,ops=1000", format!("2^{}", cache_bits)),
            &config,
            |b, config| {
                b.iter(|| {
                    let bdd = Bdd::with_config(config.clone());
                    let result = build_random_formula(&bdd, num_vars, num_ops, seed);
                    result
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Repeated substructure (tests cache effectiveness)
// ============================================================================

fn bench_shared_substructure(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/shared_substructure");

    let num_vars: usize = 10;
    let num_repeats = 50;

    for cache_bits in [14, 16, 18] {
        group.bench_with_input(
            BenchmarkId::new("v=10,shared", format!("2^{}", cache_bits)),
            &cache_bits,
            |b, &cache_bits| {
                b.iter(|| {
                    let config = BddConfig::default().with_cache_bits(cache_bits);
                    let bdd = Bdd::with_config(config);

                    // Create variables
                    let vars: Vec<Ref> = (1..=num_vars).map(|i| bdd.mk_var(i as u32)).collect();

                    // Build shared subexpressions
                    let sub1 = bdd.apply_and(vars[0], vars[1]);
                    let sub2 = bdd.apply_and(vars[2], vars[3]);
                    let sub3 = bdd.apply_or(sub1, sub2);

                    // Reuse subexpressions many times (cache should help)
                    let mut result = bdd.one();
                    for i in 0..num_repeats {
                        let x = vars[i % vars.len()];
                        let term = bdd.apply_and(x, sub3);
                        result = bdd.apply_or(result, term);

                        // Also do operations that recompute sub3 components
                        let _recomputed = bdd.apply_and(vars[0], vars[1]);
                        let _recomputed2 = bdd.apply_or(sub1, sub2);
                    }

                    result
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Apply chain (linear dependency, minimal cache benefit)
// ============================================================================

fn bench_apply_chain(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/apply_chain");

    for num_vars in [50usize, 100, 200] {
        group.bench_with_input(BenchmarkId::new("and_chain", num_vars), &num_vars, |b, &num_vars| {
            b.iter(|| {
                let config = BddConfig::default().with_cache_bits(16);
                let bdd = Bdd::with_config(config);

                // Create a long chain: x1 AND x2 AND x3 AND ... AND xn
                let vars: Vec<Ref> = (1..=num_vars).map(|i| bdd.mk_var(i as u32)).collect();

                let result = vars.iter().fold(bdd.one(), |acc, &v| bdd.apply_and(acc, v));

                result
            });
        });
    }

    group.finish();
}

// ============================================================================
// Benchmark: Quantification (stresses cache differently)
// ============================================================================

fn bench_quantification(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/quantification");
    group.sample_size(20);

    let num_vars: usize = 10;

    for cache_bits in [14, 16, 18] {
        group.bench_with_input(
            BenchmarkId::new("exists", format!("2^{}", cache_bits)),
            &cache_bits,
            |b, &cache_bits| {
                b.iter(|| {
                    let config = BddConfig::default().with_cache_bits(cache_bits);
                    let bdd = Bdd::with_config(config);

                    // Build a formula over 10 variables
                    let vars: Vec<Ref> = (1..=num_vars).map(|i| bdd.mk_var(i as u32)).collect();

                    // (x1 AND x2) OR (x3 AND x4) OR ...
                    let mut formula = bdd.zero();
                    for pair in vars.chunks(2) {
                        if pair.len() == 2 {
                            let term = bdd.apply_and(pair[0], pair[1]);
                            formula = bdd.apply_or(formula, term);
                        }
                    }

                    // Existentially quantify out some variables
                    let result = bdd.exists(formula, [1u32]);
                    let result = bdd.exists(result, [2u32]);
                    let result = bdd.exists(result, [3u32]);

                    result
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Cache pressure (many unique operations)
// ============================================================================

fn bench_cache_pressure(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/cache_pressure");

    let num_vars: usize = 100;

    // This benchmark creates many unique operations to stress the cache
    for cache_bits in [12, 14, 16] {
        let cache_size = 1 << cache_bits;
        let num_ops = cache_size * 4; // 4x more operations than cache slots

        group.throughput(Throughput::Elements(num_ops as u64));
        group.bench_with_input(
            BenchmarkId::new("4x_overfill", format!("2^{}", cache_bits)),
            &(cache_bits, num_ops),
            |b, &(cache_bits, num_ops)| {
                b.iter(|| {
                    let config = BddConfig::default().with_cache_bits(cache_bits);
                    let bdd = Bdd::with_config(config);

                    // Create many unique operations by varying operands
                    let vars: Vec<Ref> = (1..=num_vars).map(|i| bdd.mk_var(i as u32)).collect();

                    let mut rng = ChaCha8Rng::seed_from_u64(42);
                    let mut last = bdd.one();

                    for _ in 0..num_ops {
                        let i = rng.random_range(0..vars.len());
                        let j = rng.random_range(0..vars.len());
                        last = bdd.apply_and(vars[i], vars[j]);
                    }

                    last
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Hit rate measurement (diagnostic)
// ============================================================================

fn bench_hit_rate_measurement(c: &mut Criterion) {
    let mut group = c.benchmark_group("bdd/hit_rate");
    group.sample_size(10);

    // This benchmark is for measuring hit rates, not raw speed
    // It prints hit rate information for analysis

    let cache_bits = 18;

    group.bench_function("queens_6_hitrate", |b| {
        b.iter(|| {
            let config = BddConfig::default().with_cache_bits(cache_bits);
            let bdd = Bdd::with_config(config);
            let (result, hits, misses) = solve_queens(&bdd, 6);

            let total = hits + misses;
            let hit_rate = if total > 0 { hits as f64 / total as f64 } else { 0.0 };

            (result, hit_rate)
        });
    });

    group.bench_function("random_1000_hitrate", |b| {
        let num_vars = 30;
        let num_ops = 1000;
        let seed = 42;
        b.iter(|| {
            let config = BddConfig::default().with_cache_bits(cache_bits);
            let bdd = Bdd::with_config(config);
            let result = build_random_formula(&bdd, num_vars, num_ops, seed);

            let cache = bdd.cache();
            let hits = cache.hits();
            let misses = cache.misses();
            let total = hits + misses;
            let hit_rate = if total > 0 { hits as f64 / total as f64 } else { 0.0 };

            (result, hit_rate)
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_queens_cache_size,
    bench_queens_scaling,
    bench_random_formula,
    bench_shared_substructure,
    bench_apply_chain,
    bench_quantification,
    bench_cache_pressure,
    bench_hit_rate_measurement,
);

criterion_main!(benches);
