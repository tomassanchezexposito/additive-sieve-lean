# Release v2.0.0 — Formal verification of the original additive sieve

This release provides the publication-oriented Lean 4 / Mathlib verification of the algorithm described in:

Tomás Sánchez Expósito, *An Additive Sieve on an Arithmetic Progression for Prime Number Generation*.

SSRN Abstract ID: 5705571  
Paper DOI: 10.2139/ssrn.5705571

## What is formally proved

- correctness of the arithmetic progression `C n = 3 + 2*n`;
- correctness of the additive composite-marking rule;
- exact operational semantics of the dictionary-based sieve;
- marker soundness and candidate coverage;
- preservation of the global marker-scheduling invariant;
- `unmarked current candidate ↔ prime`;
- generation of exactly all primes greater than 2;
- strict increasing order of the output;
- eventual generation of every odd prime;
- exact verification of the 1000-entry table published in the paper.

The main bundled theorem is:

`paper1_final_validation`

## Reproducibility

```text
lake update
lake exe cache get
lake build
```

This release is intended to accompany the revised SSRN manuscript adding the Lean formal verification.
