//! Micro-benchmarks for the BDD operation cache.
//!
//! These benchmarks measure the raw performance of cache operations
//! in isolation, without the overhead of BDD graph operations.
//!
//! Run with:
//! ```bash
//! cargo bench --bench cache_micro
//! ```

use bdd_rs::cache::Cache;
use bdd_rs::reference::Ref;
use bdd_rs::utils::{MyHash, OpKey};
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use rand::prelude::*;
use rand_chacha::ChaCha8Rng;

/// Generate deterministic random Refs for reproducible benchmarks.
fn random_refs(seed: u64, count: usize) -> Vec<Ref> {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    (0..count)
        .map(|_| {
            let id = rng.random_range(2..10000u32);
            let negated = rng.random_bool(0.3);
            if negated {
                Ref::negative_from(id)
            } else {
                Ref::positive_from(id)
            }
        })
        .collect()
}

/// Generate OpKeys from Refs.
fn make_keys(refs: &[Ref]) -> Vec<OpKey> {
    refs.chunks(3)
        .filter(|chunk| chunk.len() == 3)
        .map(|chunk| OpKey::Ite(chunk[0], chunk[1], chunk[2]))
        .collect()
}

/// Generate sequential Refs (worst case for some hash functions).
fn sequential_refs(start: u32, count: usize) -> Vec<Ref> {
    (start..start + count as u32).map(Ref::positive_from).collect()
}

// ============================================================================
// Benchmark: Random Insert
// ============================================================================

fn bench_random_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/insert");

    for cache_bits in [14, 16, 18, 20] {
        let size = 1 << cache_bits;
        let refs = random_refs(42, size * 3);
        let keys = make_keys(&refs);
        let values: Vec<Ref> = random_refs(123, keys.len());

        group.throughput(Throughput::Elements(keys.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("random", format!("2^{}", cache_bits)),
            &(keys.clone(), values.clone()),
            |b, (keys, values)| {
                b.iter_with_setup(
                    || Cache::<OpKey, Ref>::new(cache_bits),
                    |mut cache| {
                        for (key, value) in keys.iter().zip(values.iter()) {
                            cache.insert(key.clone(), *value);
                        }
                        cache
                    },
                );
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Random Lookup (100% hit rate scenario)
// ============================================================================

fn bench_random_lookup_hit(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/lookup_hit");

    for cache_bits in [14, 16, 18, 20] {
        let size = 1 << cache_bits;
        // Use fewer keys to ensure high hit rate (no collisions)
        let num_keys = size / 4;
        let refs = random_refs(42, num_keys * 3);
        let keys = make_keys(&refs);
        let values: Vec<Ref> = random_refs(123, keys.len());

        // Pre-populate cache
        let mut cache = Cache::<OpKey, Ref>::new(cache_bits);
        for (key, value) in keys.iter().zip(values.iter()) {
            cache.insert(key.clone(), *value);
        }

        group.throughput(Throughput::Elements(keys.len() as u64));
        group.bench_with_input(BenchmarkId::new("random", format!("2^{}", cache_bits)), &keys, |b, keys| {
            b.iter(|| {
                let mut hits = 0usize;
                for key in keys.iter() {
                    if cache.get(key).is_some() {
                        hits += 1;
                    }
                }
                hits
            });
        });
    }

    group.finish();
}

// ============================================================================
// Benchmark: Random Lookup (mixed hit/miss scenario)
// ============================================================================

fn bench_random_lookup_mixed(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/lookup_mixed");

    for cache_bits in [14, 16, 18] {
        let size = 1 << cache_bits;
        // Insert more keys than cache can hold to create collisions
        let num_insert = size * 2;
        let refs_insert = random_refs(42, num_insert * 3);
        let keys_insert = make_keys(&refs_insert);
        let values: Vec<Ref> = random_refs(123, keys_insert.len());

        // Pre-populate cache (with collisions)
        let mut cache = Cache::<OpKey, Ref>::new(cache_bits);
        for (key, value) in keys_insert.iter().zip(values.iter()) {
            cache.insert(key.clone(), *value);
        }

        // Lookup a mix of inserted and random keys
        let refs_lookup = random_refs(999, size * 3);
        let keys_lookup = make_keys(&refs_lookup);

        group.throughput(Throughput::Elements(keys_lookup.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("2x_overfill", format!("2^{}", cache_bits)),
            &keys_lookup,
            |b, keys| {
                b.iter(|| {
                    let mut hits = 0usize;
                    for key in keys.iter() {
                        if cache.get(key).is_some() {
                            hits += 1;
                        }
                    }
                    hits
                });
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Sequential Keys (tests hash quality)
// ============================================================================

fn bench_sequential_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/sequential");

    for cache_bits in [14, 16, 18] {
        let size = 1 << cache_bits;
        let refs = sequential_refs(2, size * 3);
        let keys = make_keys(&refs);
        let values: Vec<Ref> = sequential_refs(10000, keys.len());

        group.throughput(Throughput::Elements(keys.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("insert", format!("2^{}", cache_bits)),
            &(keys.clone(), values.clone()),
            |b, (keys, values)| {
                b.iter_with_setup(
                    || Cache::<OpKey, Ref>::new(cache_bits),
                    |mut cache| {
                        for (key, value) in keys.iter().zip(values.iter()) {
                            cache.insert(key.clone(), *value);
                        }
                        cache
                    },
                );
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Clear Operation (should be O(1))
// ============================================================================

fn bench_clear(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/clear");

    for cache_bits in [14, 16, 18, 20, 22] {
        let size = 1 << cache_bits;
        let refs = random_refs(42, size * 3);
        let keys = make_keys(&refs);
        let values: Vec<Ref> = random_refs(123, keys.len());

        // Pre-populate cache
        let mut cache = Cache::<OpKey, Ref>::new(cache_bits);
        for (key, value) in keys.iter().zip(values.iter()) {
            cache.insert(key.clone(), *value);
        }

        group.bench_with_input(BenchmarkId::new("generation_clear", format!("2^{}", cache_bits)), &(), |b, _| {
            b.iter(|| {
                cache.clear();
            });
        });
    }

    group.finish();
}

// ============================================================================
// Benchmark: Hash Function Quality
// ============================================================================

fn bench_hash_function(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/hash");

    // Random keys
    let refs = random_refs(42, 100_000 * 3);
    let keys: Vec<(Ref, Ref, Ref)> = refs.chunks(3).filter(|c| c.len() == 3).map(|c| (c[0], c[1], c[2])).collect();

    group.throughput(Throughput::Elements(keys.len() as u64));
    group.bench_function("hash_triple_random", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for key in keys.iter() {
                sum = sum.wrapping_add(key.hash());
            }
            sum
        });
    });

    // Sequential keys (stress test)
    let refs_seq = sequential_refs(2, 100_000 * 3);
    let keys_seq: Vec<(Ref, Ref, Ref)> = refs_seq.chunks(3).filter(|c| c.len() == 3).map(|c| (c[0], c[1], c[2])).collect();

    group.bench_function("hash_triple_sequential", |b| {
        b.iter(|| {
            let mut sum = 0u64;
            for key in keys_seq.iter() {
                sum = sum.wrapping_add(key.hash());
            }
            sum
        });
    });

    group.finish();
}

// ============================================================================
// Benchmark: Collision Rate Analysis
// ============================================================================

fn bench_collision_analysis(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/collision_stress");

    // This benchmark intentionally creates many collisions
    // by using keys that hash to similar buckets
    for cache_bits in [10, 12, 14] {
        let size = 1 << cache_bits;

        // Insert 10x more keys than slots (guaranteed collisions)
        let num_keys = size * 10;
        let refs = random_refs(42, num_keys * 3);
        let keys = make_keys(&refs);
        let values: Vec<Ref> = random_refs(123, keys.len());

        group.throughput(Throughput::Elements(keys.len() as u64));
        group.bench_with_input(
            BenchmarkId::new("10x_overfill", format!("2^{}", cache_bits)),
            &(keys.clone(), values.clone()),
            |b, (keys, values)| {
                b.iter_with_setup(
                    || Cache::<OpKey, Ref>::new(cache_bits),
                    |mut cache| {
                        for (key, value) in keys.iter().zip(values.iter()) {
                            cache.insert(key.clone(), *value);
                        }
                        // Now lookup - most should miss due to eviction
                        let mut hits = 0usize;
                        for key in keys.iter() {
                            if cache.get(key).is_some() {
                                hits += 1;
                            }
                        }
                        hits
                    },
                );
            },
        );
    }

    group.finish();
}

// ============================================================================
// Benchmark: Interleaved Insert/Lookup (realistic pattern)
// ============================================================================

fn bench_interleaved(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache/interleaved");

    for cache_bits in [14, 16, 18] {
        let size = 1 << cache_bits;
        let refs = random_refs(42, size * 3);
        let keys = make_keys(&refs);
        let values: Vec<Ref> = random_refs(123, keys.len());

        group.throughput(Throughput::Elements((keys.len() * 2) as u64)); // insert + lookup
        group.bench_with_input(
            BenchmarkId::new("insert_then_lookup", format!("2^{}", cache_bits)),
            &(keys.clone(), values.clone()),
            |b, (keys, values)| {
                b.iter_with_setup(
                    || Cache::<OpKey, Ref>::new(cache_bits),
                    |mut cache| {
                        // Simulate BDD pattern: compute, cache, sometimes re-lookup
                        let mut hits = 0usize;
                        for (i, (key, value)) in keys.iter().zip(values.iter()).enumerate() {
                            // First lookup (miss expected for new keys)
                            if cache.get(key).is_some() {
                                hits += 1;
                            } else {
                                cache.insert(key.clone(), *value);
                            }

                            // Sometimes re-lookup a previous key (simulates shared substructure)
                            if i > 10 && i % 5 == 0 {
                                let prev_idx = i - (i % 7 + 1);
                                if cache.get(&keys[prev_idx]).is_some() {
                                    hits += 1;
                                }
                            }
                        }
                        hits
                    },
                );
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_random_insert,
    bench_random_lookup_hit,
    bench_random_lookup_mixed,
    bench_sequential_insert,
    bench_clear,
    bench_hash_function,
    bench_collision_analysis,
    bench_interleaved,
);

criterion_main!(benches);
