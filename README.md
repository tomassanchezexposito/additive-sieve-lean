# additive-sieve-lean

Formal verification in **Lean 4 + Mathlib** of the algorithm introduced in:

**Tomás Sánchez Expósito, _An Additive Sieve on an Arithmetic Progression for Prime Number Generation_.**

Related paper:
- SSRN Abstract ID: **5705571**
- DOI: **10.2139/ssrn.5705571**

## Scope of version 2.0.0

Version 2.0.0 reorganizes this repository around the formal verification of the original additive-sieve paper.

The formal development proves the correctness of the algorithm on the arithmetic progression

`C n = 3 + 2*n`

and models the paper's dictionary `M` extensionally as a finite set of marker pairs `(composite, prime)`.

The later compressed/twin-prime work is intentionally not part of the current main formalization and is intended to be maintained as a separate research work.

## Main verified results

The Lean development proves that:

- every prime greater than `2` occurs in the base progression;
- the additive marking identity is correct;
- the first marker introduced for a newly discovered prime is its square;
- every stored marker is mathematically sound;
- the global scheduling invariant is preserved by every state transition;
- the current candidate is unmarked **if and only if** it is prime;
- prime candidates are appended and non-prime candidates are skipped;
- after every finite number of iterations, the output contains exactly the primes different from `2` below the next candidate;
- the output is strictly increasing;
- every odd prime is eventually generated;
- the 1000 values printed in Table 1 of the paper are verified exactly, from `3` through `7927`.

## Principal theorems

- `runSteps_unmarked_iff_prime`
- `mem_runSteps_primes_iff`
- `runSteps_primes_strictlyIncreasing`
- `every_odd_prime_eventually_generated`
- `additiveSieve_algorithm_correct_at_every_step`
- `additiveSieve_generates_exactly_odd_primes`
- `paper_table_end_to_end_validation`
- `paper1_final_validation`

## Build

Requirements are pinned by `lean-toolchain` and `lakefile.toml`.

```text
lake update
lake exe cache get
lake build
```

A successful build should finish without Lean errors.

## Source file

The main formalization is:

```text
AdditiveSieveAlgorithm.lean
```

## Validation

The cumulative development used to create this publication version was checked in Lean Web on **2026-09-19** and returned:

```text
All Messages (0)
```

The repository build should also be checked locally before creating the GitHub release.

## Versioning

- `v1.0.1` remains preserved in Git history and the existing GitHub/Zenodo release history.
- `v2.0.0` is the publication-oriented formalization of the original 2025 additive-sieve paper.

## Citation

Until the Zenodo DOI for the `v2.0.0` software release is minted, cite the related paper as:

> Sánchez Expósito, Tomás. _An Additive Sieve on an Arithmetic Progression for Prime Number Generation_. SSRN, DOI: 10.2139/ssrn.5705571.

After the `v2.0.0` GitHub release is archived by Zenodo, the version-specific Zenodo DOI should be added here and to `CITATION.cff`.

## License

MIT. See `LICENSE`.
