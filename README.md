[![](logo.svg)](https://axiommath.ai/)

# ζ(5) is Irrational

This is a Lean formalization of Aabir Fauzan's proof that ζ(5) is irrational (https://zenodo.org/records/22826419).

## Main Results

* ζ(5) is irrational.
* The series ∑_{v ≥ 1} v⁻⁵ is irrational.

See [§Formal Challenge](#formal-challenge) for a formal certificate.

## Dependencies

This depends on [Mathlib](https://github.com/leanprover-community/mathlib4) and on Axiom Math's fork of [PrimeNumberTheoremAnd](https://github.com/AxiomMath/PrimeNumberTheoremAnd).

## Formal Challenge

A formal challenge file certifying that this repository does formalize the results
claimed above is located at [Challenge/Basic.lean](Challenge/Basic.lean). This file only
depends on Mathlib. It contains formal statements of
[§Main Results](#main-results) with `sorry` as proof.

This repository can be verified against the formal challenge with the Lean
comparator on a Linux machine. First, follow the instructions in
https://github.com/leanprover/comparator to install `comparator`. Then, run the following command:

```
lake env comparator Comparator/comparator.json
```

This repository has been locally verified with the comparator.
