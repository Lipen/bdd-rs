use crate::signal::Signal;

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum BinaryType {
    And,
    Xor,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TernaryType {
    And,
    Xor,
    Maj,
    Ite,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum NaryType {
    And,
    Or,
    Xor,
    Nand,
    Nor,
    Xnor,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Gate {
    Binary(BinaryType, [Signal; 2]),
    Ternary(TernaryType, [Signal; 3]),
    Nary(NaryType, Box<[Signal]>),
}

// Constructors
impl Gate {
    pub fn and(a: Signal, b: Signal) -> Gate {
        Gate::Binary(BinaryType::And, [a, b])
    }

    pub fn xor(a: Signal, b: Signal) -> Gate {
        Gate::Binary(BinaryType::Xor, [a, b])
    }

    pub fn and3(a: Signal, b: Signal, c: Signal) -> Gate {
        Gate::Ternary(TernaryType::And, [a, b, c])
    }

    pub fn maj(a: Signal, b: Signal, c: Signal) -> Gate {
        Gate::Ternary(TernaryType::Maj, [a, b, c])
    }

    pub fn ite(a: Signal, b: Signal, c: Signal) -> Gate {
        Gate::Ternary(TernaryType::Ite, [a, b, c])
    }

    pub fn andn(signals: &[Signal]) -> Gate {
        Gate::Nary(NaryType::And, signals.into())
    }

    pub fn orn(signals: &[Signal]) -> Gate {
        Gate::Nary(NaryType::Or, signals.into())
    }

    pub fn xorn(signals: &[Signal]) -> Gate {
        Gate::Nary(NaryType::Xor, signals.into())
    }

    pub fn nandn(signals: &[Signal]) -> Gate {
        Gate::Nary(NaryType::Nand, signals.into())
    }

    pub fn norn(signals: &[Signal]) -> Gate {
        Gate::Nary(NaryType::Nor, signals.into())
    }

    pub fn xnorn(signals: &[Signal]) -> Gate {
        Gate::Nary(NaryType::Xnor, signals.into())
    }
}

// Getters
impl Gate {
    pub fn inputs(&self) -> &[Signal] {
        match self {
            Gate::Binary(_, inputs) => inputs,
            Gate::Ternary(_, inputs) => inputs,
            Gate::Nary(_, inputs) => inputs,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_gate_and() {
        let a = Signal::from_input(1);
        let b = Signal::from_input(2);
        let gate = Gate::and(a, b);
        assert_eq!(gate.inputs(), &[a, b]);
    }

    #[test]
    fn test_gate_xor() {
        let a = Signal::from_input(1);
        let b = Signal::from_input(2);
        let gate = Gate::xor(a, b);
        assert_eq!(gate.inputs(), &[a, b]);
    }
}
