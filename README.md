[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22806926.svg)](https://doi.org/10.5281/zenodo.22806926)

# Additive Sieve — Lean 4 Formal Verification

Formal Lean 4 / Mathlib verification accompanying the additive-sieve work by **Tomás Sánchez Expósito**.

## Main file

- `AdditiveSieveFormalization.lean`

The development formalizes:

- the progression `C n = 3 + 2*n`;
- additive composite marking;
- the `p²` square boundary;
- adjacent candidates and the `6m ± 1` twin-prime form;
- forbidden modular classes;
- finite sieve batches and independent shards;
- batch-product / `gcd` equivalence;
- modular reduction of a large reference base;
- compressed `κ` coordinates and explicit forbidden residues;
- completeness of a finite odd-prime batch up to the square-root boundary;
- the final equivalence between twin-prime status and the compressed residue-only batch test, under the completeness hypothesis.

## Important scope condition

The final theorem is **conditional** on `CompleteOddPrimeBatchUpTo`.

The Lean development verifies the correctness of the sieve and its compressed implementation. A concrete numerical candidate is certified as prime/twin-prime only after the required completeness hypothesis is established for that candidate.

## Validation environment

The source was checked on **2026-09-17** using:

- Lean `v4.35.0-rc1`
- Mathlib pinned through the Lake project
- Result: `All Messages (0)`
- Local build: successful

## Archived release

Version `v1.0.1` is permanently archived on Zenodo.

**DOI:** `10.5281/zenodo.22806926`

## Citation

Sánchez Expósito, Tomás. *Formal Verification of an Additive Sieve on an Arithmetic Progression*. Lean 4 / Mathlib formalization, version 1.0.1, Zenodo, 2026. DOI: 10.5281/zenodo.22806926.
