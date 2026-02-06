//! ZK Proof Circuits
//!
//! Simple ZK circuit implementations demonstrating core concepts

use std::collections::HashMap;

/// Field element (simplified as u64 for demonstration)
pub type FieldElement = u64;
/// A simple prime modulus for demonstration
pub const PRIME: u64 = 21888242871839u64;

/// Wire type in a circuit
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Wire {
    Input(usize),
    Output(usize),
    Intermediate(usize),
    Constant(FieldElement),
}

/// Gate types
#[derive(Debug, Clone)]
pub enum Gate {
    Add { left: Wire, right: Wire, out: Wire },
    Mul { left: Wire, right: Wire, out: Wire },
    Const { value: FieldElement, out: Wire },
    AssertEq { left: Wire, right: Wire },
}

/// A simple arithmetic circuit
#[derive(Debug)]
pub struct Circuit {
    pub num_inputs: usize,
    pub num_outputs: usize,
    pub gates: Vec<Gate>,
}

impl Circuit {
    pub fn new(num_inputs: usize, num_outputs: usize) -> Self {
        Self {
            num_inputs,
            num_outputs,
            gates: Vec::new(),
        }
    }

    pub fn add_gate(&mut self, gate: Gate) {
        self.gates.push(gate);
    }

    /// Evaluate the circuit with given inputs
    pub fn evaluate(&self, inputs: &[FieldElement]) -> Result<HashMap<Wire, FieldElement>, &'static str> {
        if inputs.len() != self.num_inputs {
            return Err("Invalid number of inputs");
        }

        let mut values: HashMap<Wire, FieldElement> = HashMap::new();
        
        for (i, &val) in inputs.iter().enumerate() {
            values.insert(Wire::Input(i), val);
        }

        for gate in &self.gates {
            match gate {
                Gate::Add { left, right, out } => {
                    let l = self.get_value(&values, left)?;
                    let r = self.get_value(&values, right)?;
                    values.insert(*out, l.wrapping_add(r));
                }
                Gate::Mul { left, right, out } => {
                    let l = self.get_value(&values, left)?;
                    let r = self.get_value(&values, right)?;
                    values.insert(*out, l.wrapping_mul(r));
                }
                Gate::Const { value, out } => {
                    values.insert(*out, *value);
                }
                Gate::AssertEq { left, right } => {
                    let l = self.get_value(&values, left)?;
                    let r = self.get_value(&values, right)?;
                    if l != r {
                        return Err("Assertion failed");
                    }
                }
            }
        }

        Ok(values)
    }

    fn get_value(&self, values: &HashMap<Wire, FieldElement>, wire: &Wire) -> Result<FieldElement, &'static str> {
        match wire {
            Wire::Constant(c) => Ok(*c),
            _ => values.get(wire).copied().ok_or("Wire value not found"),
        }
    }
}

/// Simple hash circuit (x^2 + x + 1)
pub fn create_hash_circuit() -> Circuit {
    let mut circuit = Circuit::new(1, 1);
    
    circuit.add_gate(Gate::Mul {
        left: Wire::Input(0),
        right: Wire::Input(0),
        out: Wire::Intermediate(0),
    });
    
    circuit.add_gate(Gate::Add {
        left: Wire::Intermediate(0),
        right: Wire::Input(0),
        out: Wire::Intermediate(1),
    });
    
    circuit.add_gate(Gate::Add {
        left: Wire::Intermediate(1),
        right: Wire::Constant(1),
        out: Wire::Output(0),
    });
    
    circuit
}

/// Range proof circuit (proves x < 2^n)
pub fn create_range_proof_circuit(bits: usize) -> Circuit {
    let mut circuit = Circuit::new(bits, 1);
    
    for i in 0..bits {
        circuit.add_gate(Gate::Mul {
            left: Wire::Input(i),
            right: Wire::Input(i),
            out: Wire::Intermediate(i),
        });
        
        circuit.add_gate(Gate::AssertEq {
            left: Wire::Intermediate(i),
            right: Wire::Input(i),
        });
    }
    
    circuit
}

/// Merkle proof verification
pub fn simple_hash(left: FieldElement, right: FieldElement) -> FieldElement {
    left.wrapping_mul(31).wrapping_add(right)
}

pub fn verify_merkle_path(leaf: FieldElement, path: &[(FieldElement, bool)], root: FieldElement) -> bool {
    let mut current = leaf;
    
    for (sibling, is_left) in path {
        current = if *is_left {
            simple_hash(*sibling, current)
        } else {
            simple_hash(current, *sibling)
        };
    }
    
    current == root
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_circuit() {
        let circuit = create_hash_circuit();
        let result = circuit.evaluate(&[5]).unwrap();
        
        assert_eq!(result[&Wire::Output(0)], 31);
    }

    #[test]
    fn test_range_proof_valid() {
        let circuit = create_range_proof_circuit(3);
        let result = circuit.evaluate(&[0, 1, 1]);
        assert!(result.is_ok());
    }

    #[test]
    fn test_range_proof_invalid() {
        let circuit = create_range_proof_circuit(3);
        let result = circuit.evaluate(&[2, 1, 1]);
        assert!(result.is_err());
    }

    #[test]
    fn test_merkle_verification() {
        let leaf = 42;
        let sibling1 = 10;
        let sibling2 = 20;
        
        let node1 = simple_hash(leaf, sibling1);
        let root = simple_hash(node1, sibling2);
        
        let path = vec![(sibling1, false), (sibling2, false)];
        assert!(verify_merkle_path(leaf, &path, root));
    }

    #[test]
    fn test_circuit_evaluation() {
        let mut circuit = Circuit::new(2, 1);
        
        circuit.add_gate(Gate::Add {
            left: Wire::Input(0),
            right: Wire::Input(1),
            out: Wire::Output(0),
        });
        
        let result = circuit.evaluate(&[10, 20]).unwrap();
        assert_eq!(result[&Wire::Output(0)], 30);
    }
}
