use std::fs::File;
use std::path::PathBuf;

use bdd_rs::bdd::{Bdd, BddConfig};
use clap::{Parser, Subcommand};
use color_eyre::Result;
use feature_model::{encode_to_bdd, parse_dimacs, parse_simple, FeatureAnalyzer, FeatureModel};

#[derive(Parser)]
#[command(author, version, about = "Feature Model Analyzer using BDDs")]
struct Cli {
    /// Input file (DIMACS CNF or simple format)
    #[arg(short, long, value_name = "FILE")]
    input: PathBuf,

    /// Input format: dimacs or simple
    #[arg(short, long, default_value = "simple")]
    format: String,

    /// BDD storage size in bits
    #[arg(long, value_name = "INT")]
    bdd_size: Option<usize>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Show statistics about the feature model
    Stats,

    /// Count valid configurations
    Count,

    /// Check if the model is valid (has at least one configuration)
    Valid,

    /// Find one valid configuration
    FindOne,

    /// List core features (appear in all configurations)
    Core,

    /// List dead features (appear in no configuration)
    Dead,

    /// List optional features (neither core nor dead)
    Optional,

    /// Show commonality of each feature
    Commonality,

    /// Check if a specific configuration is valid
    Check {
        /// Configuration as comma-separated feature=value pairs
        /// Example: "1=true,2=false,3=true"
        config: String,
    },

    /// Check if two features are mutually exclusive
    Excludes {
        /// First feature ID
        f1: u32,
        /// Second feature ID
        f2: u32,
    },

    /// Check if first feature implies second feature
    Implies {
        /// First feature ID (antecedent)
        f1: u32,
        /// Second feature ID (consequent)
        f2: u32,
    },
}

fn main() -> Result<()> {
    color_eyre::install()?;

    simplelog::TermLogger::init(
        simplelog::LevelFilter::Info,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let cli = Cli::parse();

    // Parse the feature model
    log::info!("Loading feature model from {:?}", cli.input);
    let file = File::open(&cli.input)?;

    let model: FeatureModel = match cli.format.as_str() {
        "dimacs" => parse_dimacs(file).map_err(|e| color_eyre::eyre::eyre!(e))?,
        "simple" => parse_simple(file).map_err(|e| color_eyre::eyre::eyre!(e))?,
        _ => return Err(color_eyre::eyre::eyre!("Unknown format: {}", cli.format)),
    };

    log::info!(
        "Loaded model with {} features and {} constraints",
        model.num_features(),
        model.constraints.len()
    );

    // Create BDD and encode the model
    let bdd = if let Some(size) = cli.bdd_size {
        log::info!("Creating BDD with size 2^{}...", size);
        Bdd::with_config(BddConfig::default().with_initial_nodes(1 << size))
    } else {
        log::info!("Creating BDD with default size...");
        Bdd::default()
    };

    log::info!("Encoding feature model as BDD...");
    let valid_configs = encode_to_bdd(&model, &bdd);

    log::info!("BDD encoding complete. Size: {} nodes", bdd.size(valid_configs));

    // Create analyzer
    let analyzer = FeatureAnalyzer::new(&model, &bdd, valid_configs);

    // Execute command
    match cli.command {
        Commands::Stats => {
            let stats = analyzer.statistics();
            println!("{}", stats);
        }

        Commands::Count => {
            let count = analyzer.count_configurations();
            println!("Valid configurations: {}", count);
        }

        Commands::Valid => {
            if analyzer.is_valid() {
                println!("✓ Feature model is valid (has at least one configuration)");
            } else {
                println!("✗ Feature model is invalid (no valid configurations)");
            }
        }

        Commands::FindOne => match analyzer.find_one_configuration() {
            Some(config) => {
                println!("Found valid configuration:");
                let mut features: Vec<_> = config.iter().collect();
                features.sort_by_key(|(id, _)| *id);
                for (feature_id, value) in features {
                    let name = model.feature_name(*feature_id).unwrap_or("unknown");
                    println!("  {}: {} = {}", feature_id, name, value);
                }
            }
            None => {
                println!("No valid configuration found");
            }
        },

        Commands::Core => {
            let core = analyzer.core_features();
            if core.is_empty() {
                println!("No core features");
            } else {
                println!("Core features ({}):", core.len());
                for feature_id in core {
                    let name = model.feature_name(feature_id).unwrap_or("unknown");
                    println!("  {}: {}", feature_id, name);
                }
            }
        }

        Commands::Dead => {
            let dead = analyzer.dead_features();
            if dead.is_empty() {
                println!("No dead features");
            } else {
                println!("Dead features ({}):", dead.len());
                for feature_id in dead {
                    let name = model.feature_name(feature_id).unwrap_or("unknown");
                    println!("  {}: {}", feature_id, name);
                }
            }
        }

        Commands::Optional => {
            let optional = analyzer.optional_features();
            if optional.is_empty() {
                println!("No optional features");
            } else {
                println!("Optional features ({}):", optional.len());
                for feature_id in optional {
                    let name = model.feature_name(feature_id).unwrap_or("unknown");
                    println!("  {}: {}", feature_id, name);
                }
            }
        }

        Commands::Commonality => {
            println!("Feature commonality:");
            let mut features: Vec<_> = model.feature_ids();
            features.sort();
            for feature_id in features {
                let name = model.feature_name(feature_id).unwrap_or("unknown");
                let commonality = analyzer.feature_commonality(feature_id);
                println!("  {}: {} = {:.2}%", feature_id, name, commonality * 100.0);
            }
        }

        Commands::Check { config } => {
            let parsed_config = parse_config(&config)?;
            if analyzer.is_configuration_valid(&parsed_config) {
                println!("✓ Configuration is valid");
            } else {
                println!("✗ Configuration is invalid");
            }
        }

        Commands::Excludes { f1, f2 } => {
            let name1 = model.feature_name(f1).unwrap_or("unknown");
            let name2 = model.feature_name(f2).unwrap_or("unknown");

            if analyzer.are_mutually_exclusive(f1, f2) {
                println!("✓ {} and {} are mutually exclusive", name1, name2);
            } else {
                println!("✗ {} and {} are NOT mutually exclusive", name1, name2);
            }
        }

        Commands::Implies { f1, f2 } => {
            let name1 = model.feature_name(f1).unwrap_or("unknown");
            let name2 = model.feature_name(f2).unwrap_or("unknown");

            if analyzer.implies(f1, f2) {
                println!("✓ {} implies {}", name1, name2);
            } else {
                println!("✗ {} does NOT imply {}", name1, name2);
            }
        }
    }

    Ok(())
}

fn parse_config(config_str: &str) -> Result<std::collections::HashMap<u32, bool>> {
    let mut config = std::collections::HashMap::new();

    for part in config_str.split(',') {
        let parts: Vec<&str> = part.split('=').collect();
        if parts.len() != 2 {
            return Err(color_eyre::eyre::eyre!("Invalid config format: {}", part));
        }

        let feature_id: u32 = parts[0].trim().parse()?;
        let value: bool = parts[1].trim().parse()?;

        config.insert(feature_id, value);
    }

    Ok(config)
}
