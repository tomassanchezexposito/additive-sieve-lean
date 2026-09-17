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
In other words, the Lean development verifies the correctness of the sieve and its compressed implementation. A concrete numerical candidate is certified as prime/twin-prime only after the required completeness hypothesis is established for that candidate.

## Validation environment

The source was checked in Lean Web on **2026-09-17** using:

- Lean `v4.35.0-rc1`
- Mathlib available in the Lean Web environment
- Result: `All Messages (0)`

For a long-term reproducible archive, create a local Lake project, pin the Lean/Mathlib dependency, run the build, and commit the generated `lake-manifest.json`.

## Suggested repository structure

```text
AdditiveSieveFormalization/
├── AdditiveSieveFormalization.lean
├── README.md
└── CITATION.cff
```

For stronger reproducibility, also include:

```text
lean-toolchain
lakefile.toml   (or lakefile.lean)
lake-manifest.json
```

## Local Lean / Mathlib project

The official Lean documentation provides a Mathlib project template. A typical starting command is:

```bash
lake +leanprover-community/mathlib4:lean-toolchain new AdditiveSieveFormalization math
```

Then place the Lean source in the generated project, obtain the Mathlib cache, and build:

```bash
lake exe cache get
lake build
```

Commit the resulting dependency manifest so that the Mathlib revision is recorded.

## Citation

A `CITATION.cff` file is included so GitHub and archival services can expose citation metadata.

## License

Choose a software license before the public release. A permissive license such as MIT is common for research code, but the choice is yours. Add the corresponding `LICENSE` file to the repository before publishing a release.
