# Additive Sieve Lean Formalization

Formal verification in Lean 4 / Mathlib of the additive sieve presented in:

**Tomás Sánchez Expósito, _An Additive Sieve on an Arithmetic Progression for Prime Number Generation_**

SSRN Abstract ID: **5705571**  
SSRN DOI: **10.2139/ssrn.5705571**

## Release v2.0.0

Version **v2.0.0** formalizes the exact operational additive-sieve algorithm from the original paper.

The development proves, for the modeled algorithm, that:

- the dictionary branch condition is equivalent to primality at every processed candidate;
- the output after any finite number of steps contains exactly the primes greater than 2 below the next candidate;
- the output is strictly increasing;
- every odd prime is eventually generated;
- the exact 1000-prime table printed in the original paper is reproduced and formally verified;
- after 3962 candidate iterations the output ends at 7927 and the next candidate is 7929.

The formal result concerns **functional correctness of the specified algorithm**. Comparative complexity, performance, and implementation optimization are separate questions.

## Reproducibility

The release pins Lean `v4.35.0-rc2` and Mathlib `v4.35.0-rc2`.

```bash
lake update
lake exe cache get
lake build
```

## Archived release

GitHub release: **v2.0.0**

Zenodo DOI for version v2.0.0: **10.5281/zenodo.22843511**

## Citation

Sánchez Expósito, T. (2026). *Formal Verification of the Additive Sieve Algorithm* (Version 2.0.0) [Computer software]. Zenodo. DOI: **10.5281/zenodo.22843511**.

The associated revised article remains under SSRN Abstract ID **5705571**, DOI **10.2139/ssrn.5705571**.

## Scope

This repository concerns the original additive sieve on the arithmetic progression `C_n = 3 + 2n`. Later work on compressed candidate spaces and twin-prime searches is a separate research line.
