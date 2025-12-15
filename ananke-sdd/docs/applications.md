# Applications of SDDs

Sentential Decision Diagrams have found applications across many domains. This document surveys the key application areas.

## 1. Probabilistic Reasoning

### Bayesian Networks

SDDs enable efficient inference in Bayesian networks through weighted model counting (WMC):

1. **Compile** the network structure into an SDD
2. **Weight** literals according to conditional probability tables
3. **Query** probabilities in O(|SDD|) time

Example applications:

- Medical diagnosis systems
- Fault diagnosis in complex systems
- Genetic linkage analysis

### Probabilistic Programs

SDDs serve as the compiled representation for probabilistic programming languages:

- **Dice** (probabilistic programming language)
- **ProbLog** (probabilistic logic programming)
- **Probabilistic sentential decision diagrams (PSDDs)**

## 2. Knowledge Compilation

### Configuration Management

SDDs represent valid product configurations:

```
Knowledge Base:
  • Feature A requires Feature B
  • Feature C conflicts with Feature D
  • At least one of E or F must be selected

Compile → SDD

Queries (all O(|SDD|)):
  • Is configuration valid?
  • How many valid configurations exist?
  • What features are implied by a choice?
```

### Constraint Satisfaction

SDDs can represent constraint satisfaction problem solutions:

- Compile constraints incrementally
- Answer solution queries efficiently
- Support explanation generation

## 3. Machine Learning

### Tractable Probabilistic Models

SDDs are used in **tractable probabilistic models** (TPMs):

- **Sum-Product Networks (SPNs)**: Can be compiled to SDDs
- **Probabilistic Circuits**: SDDs are a subclass
- **Structured-Decomposable NNF**: SDDs satisfy this property

### Tractable Inference

Key ML operations become tractable:

- Marginal inference
- Maximum a posteriori (MAP) inference
- Expectation computation

### Learning

SDDs support:

- Learning from data (structure learning)
- Parameter estimation
- Regularization through structure constraints

## 4. Verification

### Model Checking

SDDs can represent:

- State spaces of finite systems
- Transition relations
- Temporal logic formulas

Advantages over BDDs:

- Potentially more compact for hierarchical systems
- Support for same symbolic operations

### Hardware Verification

Applications in:

- Equivalence checking
- Property verification
- Fault simulation

## 5. Automated Planning

### Classical Planning

SDDs represent:

- State spaces
- Action preconditions and effects
- Goal conditions

### Conformant Planning

Handle uncertainty through:

- Belief state representation
- Observation modeling
- Information-theoretic metrics

## 6. Natural Language Processing

### Semantic Parsing

SDDs represent meaning representations:

- Logical forms of sentences
- Compositional semantics
- Ambiguity resolution

### Information Extraction

Applications:

- Named entity recognition constraints
- Relation extraction
- Knowledge base population

## 7. Cryptographic Analysis

SDDs can analyze:

- Boolean functions in cryptographic primitives
- Key schedule properties
- Differential characteristics

## 8. Database Query Optimization

### Query Compilation

Compile queries for:

- Efficient repeated execution
- Cardinality estimation
- Join order optimization

### Provenance

Track data lineage through SDD-based provenance semirings.

## Case Study: Laptop Configurator

See `examples/knowledge_compilation.rs` for a complete example:

```rust
// Constraints
let c1 = mgr.implies(gpu, battery);      // GPU needs battery
let c2 = mgr.implies(slim, mgr.neg(battery)); // Slim excludes battery

// Compile
let kb = mgr.and_all([c1, c2, c3, c4, c5]);

// Queries
let valid_slim = mgr.model_count(mgr.and(kb, slim));
let gpu_possible = mgr.is_satisfiable(mgr.and(kb, gpu));
```

## Tools and Libraries

### Reference Implementations

- **SDD Package** (UCLA): Reference C library
- **PySDD**: Python bindings
- **rsdd**: Rust implementation (different from this one)

### Applications Built on SDDs

- **Juice**: Probabilistic inference engine
- **Dice**: Probabilistic programming language
- **LearnSPN**: Structure learning for SPNs

## Further Reading

1. Darwiche, A. (2011). SDD: A New Canonical Representation of Propositional Knowledge Bases.

2. Kisa, D., et al. (2014). Probabilistic Sentential Decision Diagrams.

3. Choi, A., et al. (2015). Compiling Probabilistic Graphical Models using SDDs.

4. Shen, Y., et al. (2016). Tractable Operations for Arithmetic Circuits of Probabilistic Models.
