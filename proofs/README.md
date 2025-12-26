# Asya Proof Library

This directory contains Lean 4 formalizations of mathematical theorems used in the Asya platform.

## Structure

```
proofs/
├── basic_arithmetic.lean   # Elementary arithmetic proofs
├── pythagorean.lean         # Pythagorean theorem and applications
└── README.md                # This file
```

## How to Use

### Verify a proof

```bash
# Install Lean 4 first: https://leanprover.github.io/lean4/doc/quickstart.html

# Verify a proof file
lean proofs/basic_arithmetic.lean
```

### Add a new proof

1. Create a new `.lean` file in this directory
2. Import necessary libraries:
   ```lean
   import Mathlib.Data.Nat.Basic
   import Mathlib.Tactic
   ```
3. Write your theorem:
   ```lean
   theorem my_theorem : statement := by
     proof_steps
   ```
4. Verify with `lean proofs/my_theorem.lean`
5. Register in Asya's knowledge graph

## Proof Categories

### Level 1-3: Basic Arithmetic
- `basic_arithmetic.lean` - Addition, multiplication, identities

### Level 4-6: Geometry
- `pythagorean.lean` - Right triangles, distance formula

### Level 7-9: Algebra (TODO)
- Polynomials, equations, inequalities

### Level 10+: Advanced (TODO)
- Calculus, linear algebra, abstract algebra

## Integration with Asya

When Asya guides a user to formalize a proof:
1. User explores concept (Void phase)
2. User discovers pattern (Flow phase)
3. Asya helps formalize (Solution phase)
4. Proof is verified with Lean
5. Proof is added to knowledge graph
6. Future users benefit from verified proof

## Contributing

To add a proof:
1. Ensure it verifies with Lean 4
2. Add clear comments explaining the theorem
3. Link to knowledge graph concepts
4. Add to appropriate difficulty level

## Resources

- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) - Learn Lean through game!

---

Built with mathematical rigor for universal learning! 🔍✨
