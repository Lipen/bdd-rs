use std::fs::File;

use bdd_rs::aig::{Literal, Reader, Record};
use bdd_rs::bdd::Bdd;
use bdd_rs::gate::{BinaryType, Gate, NaryType, TernaryType};
use bdd_rs::network::Network;
use bdd_rs::reference::Ref;
use bdd_rs::signal::Signal;

fn main() -> color_eyre::Result<()> {
    color_eyre::install()?;

    simplelog::TermLogger::init(
        simplelog::LevelFilter::Info,
        simplelog::Config::default(),
        simplelog::TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )?;

    let time_total = std::time::Instant::now();

    let bdd = Bdd::default();
    println!("bdd = {:?}", bdd);

    let pattern = "data/aag/**/*.aag";
    println!("pattern = {:?}", pattern);
    for file in glob::glob(pattern)?.filter_map(|r| r.ok()) {
        println!("----------------------------------");
        println!("file: {}", file.display());
        let file = File::open(file)?;
        match Reader::from_reader(file) {
            Ok(reader) => {
                let header = reader.header().clone();
                println!("header = {:?}", header);
                if header.l > 0 {
                    println!("Skipping AIGER file with latches");
                    continue;
                }
                let records = reader.records().collect::<Result<Vec<_>, _>>()?;
                println!("records: {}", records.len());
                for record in records.iter() {
                    println!("- {:?}", record);
                }
                let mut network = Network::new();
                let lit2sig = |literal: Literal| {
                    let signal = if literal.variable() == 0 {
                        Signal::zero()
                    } else if literal.variable() <= header.i as u32 {
                        Signal::from_input(literal.variable() - 1)
                    } else {
                        Signal::from_var(literal.variable() - 1)
                    };
                    if literal.is_negated() {
                        !signal
                    } else {
                        signal
                    }
                };
                for record in records.iter() {
                    match record {
                        Record::Input(literal) => {
                            let signal = network.add_input();
                            assert_eq!(signal, lit2sig(*literal));
                        }
                        Record::Latch { .. } => {
                            // TODO
                        }
                        Record::Output(output) => {
                            let signal = lit2sig(*output);
                            network.add_output(signal);
                        }
                        Record::AndGate {
                            output,
                            inputs: [left, right],
                        } => {
                            let left_signal = lit2sig(*left);
                            let right_signal = lit2sig(*right);
                            let gate = Gate::and(left_signal, right_signal);
                            let output_signal = network.add_gate(output.variable() - 1, gate);
                            assert_eq!(output_signal, lit2sig(*output));
                        }
                        Record::Symbol { .. } => {
                            // TODO
                        }
                    }
                }
                println!("network = {:?}", network);

                let outputs = encode_network(&bdd, &network);
                println!("outputs: {}", outputs.len());
                for &output in outputs.iter() {
                    println!(
                        "- {} of size {} = {}",
                        output,
                        bdd.size(output),
                        bdd.to_bracket_string(output)
                    );
                }
            }
            Err(e) => println!("error: {:?}", e),
        }
    }

    let time_total = time_total.elapsed();
    println!("Done in {:.3} s", time_total.as_secs_f64());

    Ok(())
}

fn encode_network(bdd: &Bdd, network: &Network) -> Vec<Ref> {
    let mut outputs = Vec::new();
    for &signal in network.outputs() {
        let out = encode_signal(bdd, signal, network);
        outputs.push(out);
    }
    outputs
}

fn encode_signal(bdd: &Bdd, signal: Signal, network: &Network) -> Ref {
    if signal.is_const() {
        if signal.is_negated() {
            bdd.one
        } else {
            bdd.zero
        }
    } else if signal.is_input() {
        bdd.mk_var(signal.input() + 1)
    } else {
        if network.gate(signal.var()).is_none() {
            println!(
                "no gate for signal = {}, signal.var() = {}",
                signal,
                signal.var()
            );
        }
        let gate = network.gate(signal.var()).unwrap();
        match gate {
            Gate::Binary(kind, [left, right]) => {
                let left = encode_signal(bdd, *left, network);
                let right = encode_signal(bdd, *right, network);
                match kind {
                    BinaryType::And => bdd.apply_and(left, right),
                    BinaryType::Xor => bdd.apply_xor(left, right),
                }
            }
            Gate::Ternary(kind, [a, b, c]) => {
                let a = encode_signal(bdd, *a, network);
                let b = encode_signal(bdd, *b, network);
                let c = encode_signal(bdd, *c, network);
                match kind {
                    TernaryType::And => bdd.apply_and(bdd.apply_and(a, b), c),
                    TernaryType::Xor => bdd.apply_xor(bdd.apply_xor(a, b), c),
                    TernaryType::Maj => {
                        // TODO: bdd.apply_maj(a, b, c)
                        let ab = bdd.apply_and(a, b);
                        let bc = bdd.apply_and(b, c);
                        let ac = bdd.apply_and(a, c);
                        bdd.apply_or(bdd.apply_or(ab, bc), ac)
                    }
                    TernaryType::Ite => bdd.apply_ite(a, b, c),
                }
            }
            Gate::Nary(kind, inputs) => match kind {
                NaryType::And => {
                    let mut res = bdd.one;
                    for &input in inputs.iter() {
                        let input = encode_signal(bdd, input, network);
                        res = bdd.apply_and(res, input);
                    }
                    res
                }
                NaryType::Or => {
                    let mut res = bdd.zero;
                    for &input in inputs.iter() {
                        let input = encode_signal(bdd, input, network);
                        res = bdd.apply_or(res, input);
                    }
                    res
                }
                NaryType::Xor => {
                    let mut res = bdd.zero;
                    for &input in inputs.iter() {
                        let input = encode_signal(bdd, input, network);
                        res = bdd.apply_xor(res, input);
                    }
                    res
                }
                NaryType::Nand => todo!(),
                NaryType::Nor => todo!(),
                NaryType::Xnor => todo!(),
            },
        }
    }
}
