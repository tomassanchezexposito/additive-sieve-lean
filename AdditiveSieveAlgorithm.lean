import Mathlib

/-!
# Formal Verification of the Additive Sieve Algorithm

This file provides a self-contained Lean 4 / Mathlib formalization of the
algorithm described in:

Tomás Sánchez Expósito,
"An Additive Sieve on an Arithmetic Progression for Prime Number Generation"
(August 16, 2025).

This formalization is independent of the author's later work on a compressed
sieve for twin-prime candidates. It models the paper's dictionary `M` extensionally as a
finite set of `(composite, prime-marker)` pairs:

* `(c,p) ∈ M` means that `p` occurs in the list stored at dictionary key `c`;
* several pairs may have the same first coordinate, representing several
  prime markers stored under the same dictionary key;
* when `c` is processed, every marker `(c,p)` is moved to `(c+2p,p)`;
* when `c` is unmarked, the algorithm appends `c` to the prime list and
  inserts the new marker `(c*c,c)`.

This is the exact mathematical state transition of Algorithm 3.1, abstracting
only from the concrete hash-table implementation.
-/

namespace AdditiveSieveAlgorithm

/-!
## 1. Base arithmetic progression
-/

/-- The paper's base sequence: all odd integers from 3 onward. -/
def C (n : ℕ) : ℕ :=
  3 + 2 * n

theorem C_odd (n : ℕ) :
    Odd (C n) := by
  refine ⟨n + 1, ?_⟩
  simp [C]
  omega

/--
Every prime different from 2 occurs in the sequence `C`.
-/
theorem odd_prime_mem_C
    {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2) :
    ∃ n : ℕ, C n = p := by

  have hodd : Odd p :=
    hp.odd_of_ne_two hp2

  rcases hodd with ⟨k, hk⟩

  have hp3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    omega

  have hk1 : 1 ≤ k := by
    omega

  refine ⟨k - 1, ?_⟩

  simp [C]

  omega

/--
If `C s = p`, then the index of `p` is `(p-3)/2`.
-/
theorem index_formula
    {p s : ℕ}
    (hps : C s = p) :
    s = (p - 3) / 2 := by

  simp [C] at hps

  omega

/--
The additive marking rule from the paper:
starting from the index `s` of `p`, advancing by `k*p` indices gives
the odd multiple `(2k+1)p`.
-/
theorem composite_index_identity
    {p s k : ℕ}
    (hps : C s = p) :
    C (s + k * p) =
      (2 * k + 1) * p := by

  rw [← hps]

  simp [C]

  ring

/--
Every marked value with `k ≥ 1` is non-prime.
-/
theorem composite_at_marked_index
    {p s k : ℕ}
    (hp : Nat.Prime p)
    (hk : 1 ≤ k)
    (hps : C s = p) :
    ¬ Nat.Prime (C (s + k * p)) := by

  rw [composite_index_identity hps]

  apply Nat.not_prime_mul

  · omega

  · have hp2 : 2 ≤ p := hp.two_le
    omega

/--
The square `p²` lies on the marking progression of `p`.
-/
theorem square_at_index
    {p s : ℕ}
    (hps : C s = p) :
    C (s + (s + 1) * p) =
      p * p := by

  rw [
    composite_index_identity
      (k := s + 1)
      hps
  ]

  have h :
      2 * (s + 1) + 1 = p := by
    simp [C] at hps
    omega

  rw [h]

/-!
## 2. Exact operational model of Algorithm 3.1

The Python dictionary maps a composite candidate to a list of prime markers.
For formal reasoning we use the extensionally equivalent finite relation
`MarkerMap = Finset (ℕ × ℕ)`.

A pair `(c,p)` means: dictionary key `c` contains marker `p`.
-/

abbrev Marker := ℕ × ℕ
abbrev MarkerMap := Finset Marker

/--
All prime markers currently stored under dictionary key `c`.
-/
def factorsAt
    (M : MarkerMap)
    (c : ℕ) :
    Finset ℕ :=
  (M.filter (fun xp => xp.1 = c)).image
    (fun xp => xp.2)

/--
The key `c` is present precisely when at least one marker is stored there.
-/
def HasKey
    (M : MarkerMap)
    (c : ℕ) : Prop :=
  factorsAt M c ≠ ∅

/--
Composite branch of Algorithm 3.1.

All markers stored at key `c` are removed and each `(c,p)` is rescheduled
at `c + 2*p`. Every marker stored at another key is left unchanged.
-/
def advanceAt
    (M : MarkerMap)
    (c : ℕ) :
    MarkerMap :=
  (M.filter (fun xp => xp.1 ≠ c)) ∪
  ((M.filter (fun xp => xp.1 = c)).image
    (fun xp => (c + 2 * xp.2, xp.2)))

/--
Complete mutable state of the paper's algorithm.

`candidate` is the next odd number to process.
`primes` is the list discovered so far, in discovery order.
`markers` is the extensional model of dictionary `M`.
-/
structure SieveState where
  candidate : ℕ
  primes : List ℕ
  markers : MarkerMap
deriving DecidableEq

/--
Initial state from Algorithm 3.1:

* `P = [3]`;
* `M[9] = [3]`;
* the first candidate to inspect is `5`.
-/
def initialState : SieveState :=
  {
    candidate := 5
    primes := [3]
    markers := {(9, 3)}
  }

/--
One exact state transition of Algorithm 3.1.

If `candidate` is absent from `M`, the algorithm treats it as prime,
appends it to `P`, and inserts its square.

If `candidate` is present, every prime marker stored at that key is
advanced by `2*p`.

In either branch the next candidate is `candidate + 2`.
-/
def step
    (s : SieveState) :
    SieveState :=
  let c := s.candidate
  if factorsAt s.markers c = ∅ then
    {
      candidate := c + 2
      primes := s.primes ++ [c]
      markers := insert (c * c, c) s.markers
    }
  else
    {
      candidate := c + 2
      primes := s.primes
      markers := advanceAt s.markers c
    }

/--
Run exactly `steps` candidate-processing iterations.
-/
def runSteps :
    ℕ → SieveState
  | 0 =>
      initialState
  | steps + 1 =>
      step (runSteps steps)

/-!
## 3. Elementary operational facts
-/

theorem initial_candidate :
    initialState.candidate = 5 := by
  rfl

theorem initial_primes :
    initialState.primes = [3] := by
  rfl

theorem initial_three_marker :
    (9, 3) ∈ initialState.markers := by
  simp [initialState]

/--
Every call to `step` advances the candidate by exactly two.
-/
theorem step_candidate
    (s : SieveState) :
    (step s).candidate =
      s.candidate + 2 := by

  by_cases h :
      factorsAt s.markers s.candidate = ∅

  · simp [step, h]

  · simp [step, h]

/--
The candidate after `steps` iterations is exactly `5 + 2*steps`.
-/
theorem runSteps_candidate
    (steps : ℕ) :
    (runSteps steps).candidate =
      5 + 2 * steps := by

  induction steps with

  | zero =>
      simp [runSteps, initialState]

  | succ steps ih =>
      rw [runSteps]
      rw [step_candidate]
      rw [ih]
      omega

/--
Exact prime branch of the operational algorithm.
-/
theorem step_of_unmarked
    (s : SieveState)
    (h :
      factorsAt
        s.markers
        s.candidate = ∅) :
    step s =
      {
        candidate := s.candidate + 2
        primes := s.primes ++ [s.candidate]
        markers :=
          insert
            (s.candidate * s.candidate,
             s.candidate)
            s.markers
      } := by

  simp [step, h]

/--
Exact composite branch of the operational algorithm.
-/
theorem step_of_marked
    (s : SieveState)
    (h :
      factorsAt
        s.markers
        s.candidate ≠ ∅) :
    step s =
      {
        candidate := s.candidate + 2
        primes := s.primes
        markers :=
          advanceAt
            s.markers
            s.candidate
      } := by

  simp [step, h]

/-!
## 4. Executable sanity checks

These are not the final correctness proof. They confirm that the formal
transition system reproduces the beginning of Algorithm 3.1 exactly.
-/

example :
    (runSteps 1).primes =
      [3, 5] := by
  native_decide

example :
    (runSteps 2).primes =
      [3, 5, 7] := by
  native_decide

/--
After processing `5,7,9`, the value `9` has correctly been recognized
as marked/composite and therefore has not been appended.
-/
example :
    (runSteps 3).primes =
      [3, 5, 7] := by
  native_decide

/--
After the first ten candidates `5,7,...,23`, the discovered list is
the correct initial prime sequence.
-/
example :
    (runSteps 10).primes =
      [3, 5, 7, 11, 13, 17, 19, 23] := by
  native_decide

example :
    (runSteps 10).candidate = 25 := by
  native_decide


/-!
## 5. Soundness invariant for the marker dictionary

The first global invariant states that every marker stored in `M` is
mathematically sound.

If `(m,p)` is stored while the current candidate is `c`, then:

* `p` is an odd prime;
* `p < c`, so the marker prime has already been discovered;
* `p ∣ m`;
* `m` is odd;
* `m ≥ c`, so markers never point backwards.

Consequently every key currently stored in the dictionary is composite.
-/

/-- Mathematical facts carried by one marker `(m,p)`. -/
structure MarkerFacts
    (c m p : ℕ) : Prop where
  prime : Nat.Prime p
  oddPrime : Odd p
  prime_lt_candidate : p < c
  divides : p ∣ m
  oddKey : Odd m
  candidate_le_key : c ≤ m

/--
Soundness invariant for a marker map at current candidate `c`.
-/
def MarkerInvariantAt
    (c : ℕ)
    (M : MarkerMap) : Prop :=
  5 ≤ c ∧
  Odd c ∧
  ∀ m p,
    (m, p) ∈ M →
    MarkerFacts c m p

/-- State-level form of the marker invariant. -/
def MarkerInvariant
    (s : SieveState) : Prop :=
  MarkerInvariantAt
    s.candidate
    s.markers

/--
Membership in `factorsAt M c` is exactly membership of `(c,p)` in
the extensional dictionary representation.
-/
theorem mem_factorsAt_iff
    {M : MarkerMap}
    {c p : ℕ} :
    p ∈ factorsAt M c ↔
      (c, p) ∈ M := by

  constructor

  · intro hp

    unfold factorsAt at hp

    rcases Finset.mem_image.mp hp with
      ⟨xp, hxp, hvalue⟩

    rcases Finset.mem_filter.mp hxp with
      ⟨hmem, hkey⟩

    rcases xp with ⟨m, q⟩

    change m = c at hkey
    change q = p at hvalue

    subst m
    subst q

    exact hmem

  · intro hmem

    unfold factorsAt

    apply Finset.mem_image.mpr

    refine
      ⟨(c, p), ?_, rfl⟩

    exact
      Finset.mem_filter.mpr
        ⟨hmem, rfl⟩

/--
If the factor set at `c` is empty, no marker `(c,p)` is present.
-/
theorem no_marker_at_of_factorsAt_empty
    {M : MarkerMap}
    {c p : ℕ}
    (hEmpty :
      factorsAt M c = ∅) :
    (c, p) ∉ M := by

  intro hmem

  have hp :
      p ∈ factorsAt M c := by

    exact
      mem_factorsAt_iff.mpr
        hmem

  rw [hEmpty] at hp

  simp at hp

/--
If the factor set at `c` is nonempty, at least one marker `(c,p)`
is present.
-/
theorem exists_marker_at_of_factorsAt_nonempty
    {M : MarkerMap}
    {c : ℕ}
    (hNonempty :
      factorsAt M c ≠ ∅) :
    ∃ p, (c, p) ∈ M := by

  have hFinsetNonempty :
      (factorsAt M c).Nonempty := by

    exact
      Finset.nonempty_iff_ne_empty.mpr
        hNonempty

  rcases hFinsetNonempty with
    ⟨p, hp⟩

  exact
    ⟨p,
      mem_factorsAt_iff.mp hp⟩

/--
Two distinct odd naturals cannot differ by only one.
Thus if `a ≤ b`, both are odd, and `a ≠ b`, then `a+2 ≤ b`.
-/
theorem add_two_le_of_odd_le_ne
    {a b : ℕ}
    (ha : Odd a)
    (hb : Odd b)
    (hab : a ≤ b)
    (hne : b ≠ a) :
    a + 2 ≤ b := by

  rcases ha with ⟨x, hx⟩
  rcases hb with ⟨y, hy⟩

  omega

/--
Every sound marker key is composite.
-/
theorem markerFacts_not_prime
    {c m p : ℕ}
    (h : MarkerFacts c m p) :
    ¬ Nat.Prime m := by

  intro hmPrime

  have hpEq :
      p = m := by

    exact
      (Nat.dvd_prime_two_le
        hmPrime
        h.prime.two_le).mp
        h.divides

  have hpm :
      p < m := by
    exact
      lt_of_lt_of_le
        h.prime_lt_candidate
        h.candidate_le_key

  exact
    (ne_of_lt hpm)
      hpEq

/--
State-level consequence: every key represented in the dictionary is
non-prime.
-/
theorem marker_key_not_prime
    {s : SieveState}
    (hInv : MarkerInvariant s)
    {m p : ℕ}
    (hmem :
      (m, p) ∈ s.markers) :
    ¬ Nat.Prime m := by

  unfold MarkerInvariant at hInv
  unfold MarkerInvariantAt at hInv

  exact
    markerFacts_not_prime
      (hInv.2.2 m p hmem)

/-!
### Preservation under the composite branch
-/

/--
A marker whose key is not the current candidate remains sound after
the candidate advances by two.
-/
theorem markerFacts_after_skipping_key
    {c m p : ℕ}
    (hcOdd : Odd c)
    (h : MarkerFacts c m p)
    (hne : m ≠ c) :
    MarkerFacts (c + 2) m p := by

  have hNextLe :
      c + 2 ≤ m := by

    exact
      add_two_le_of_odd_le_ne
        hcOdd
        h.oddKey
        h.candidate_le_key
        hne

  exact
    {
      prime := h.prime
      oddPrime := h.oddPrime
      prime_lt_candidate := by
        exact
          lt_trans
            h.prime_lt_candidate
            (by omega)
      divides := h.divides
      oddKey := h.oddKey
      candidate_le_key := hNextLe
    }

/--
A marker `(c,p)` moved to `(c+2p,p)` remains mathematically sound.
-/
theorem markerFacts_after_advance
    {c p : ℕ}
    (hcOdd : Odd c)
    (h : MarkerFacts c c p) :
    MarkerFacts
      (c + 2)
      (c + 2 * p)
      p := by

  have hMovedOdd :
      Odd (c + 2 * p) := by

    rcases hcOdd with ⟨k, hk⟩

    refine
      ⟨k + p, ?_⟩

    rw [hk]

    ring

  have hMovedDiv :
      p ∣ c + 2 * p := by

    rcases h.divides with
      ⟨k, hk⟩

    refine
      ⟨k + 2, ?_⟩

    rw [hk]

    ring

  have hp2 :
      2 ≤ p :=
    h.prime.two_le

  exact
    {
      prime := h.prime
      oddPrime := h.oddPrime
      prime_lt_candidate := by
        exact
          lt_trans
            h.prime_lt_candidate
            (by omega)
      divides := hMovedDiv
      oddKey := hMovedOdd
      candidate_le_key := by
        omega
    }

/--
`advanceAt` preserves marker soundness when the current candidate moves
from `c` to `c+2`.
-/
theorem advanceAt_preserves_markerInvariantAt
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M) :
    MarkerInvariantAt
      (c + 2)
      (advanceAt M c) := by

  rcases hInv with
    ⟨hc5, hcOdd, hMarkers⟩

  have hNextOdd :
      Odd (c + 2) := by

    rcases hcOdd with ⟨k, hk⟩

    refine
      ⟨k + 1, ?_⟩

    omega

  refine
    ⟨by omega,
     hNextOdd,
     ?_⟩

  intro m p hmem

  unfold advanceAt at hmem

  rcases Finset.mem_union.mp hmem with
    hKeep | hMove

  · rcases Finset.mem_filter.mp hKeep with
      ⟨hOld, hne⟩

    exact
      markerFacts_after_skipping_key
        hcOdd
        (hMarkers m p hOld)
        hne

  · rcases Finset.mem_image.mp hMove with
      ⟨xp, hxp, heq⟩

    rcases Finset.mem_filter.mp hxp with
      ⟨hOld, hCurrent⟩

    rcases xp with ⟨x, r⟩

    change x = c at hCurrent

    subst x

    have hm :
        c + 2 * r = m := by

      exact
        congrArg Prod.fst heq

    have hp :
        r = p := by

      exact
        congrArg Prod.snd heq

    subst m
    subst p

    exact
      markerFacts_after_advance
        hcOdd
        (hMarkers c r hOld)

/-!
### Preservation under the prime branch
-/

/--
If the current candidate `c` is prime, the newly inserted square marker
`(c²,c)` satisfies the invariant for the next candidate `c+2`.
-/
theorem square_markerFacts
    {c : ℕ}
    (hc5 : 5 ≤ c)
    (hcOdd : Odd c)
    (hcPrime : Nat.Prime c) :
    MarkerFacts
      (c + 2)
      (c * c)
      c := by

  have hSquareOdd :
      Odd (c * c) := by

    rcases hcOdd with ⟨k, hk⟩

    refine
      ⟨2 * k * k + 2 * k, ?_⟩

    rw [hk]

    ring

  have hSquareDiv :
      c ∣ c * c := by

    refine
      ⟨c, ?_⟩

    ring

  exact
    {
      prime := hcPrime
      oddPrime := hcOdd
      prime_lt_candidate := by
        omega
      divides := hSquareDiv
      oddKey := hSquareOdd
      candidate_le_key := by
        nlinarith
    }

/--
If `c` is unmarked and prime, inserting `(c²,c)` while advancing the
candidate preserves the marker invariant.
-/
theorem insert_square_preserves_markerInvariantAt
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M)
    (hEmpty :
      factorsAt M c = ∅)
    (hcPrime :
      Nat.Prime c) :
    MarkerInvariantAt
      (c + 2)
      (insert (c * c, c) M) := by

  rcases hInv with
    ⟨hc5, hcOdd, hMarkers⟩

  have hNextOdd :
      Odd (c + 2) := by

    rcases hcOdd with ⟨k, hk⟩

    refine
      ⟨k + 1, ?_⟩

    omega

  refine
    ⟨by omega,
     hNextOdd,
     ?_⟩

  intro m p hmem

  simp only [Finset.mem_insert] at hmem

  rcases hmem with
    hNew | hOld

  · cases hNew

    exact
      square_markerFacts
        hc5
        hcOdd
        hcPrime

  · have hne :
        m ≠ c := by

      intro hmc

      subst m

      exact
        no_marker_at_of_factorsAt_empty
          hEmpty
          hOld

    exact
      markerFacts_after_skipping_key
        hcOdd
        (hMarkers m p hOld)
        hne

/-!
### Initial state and branch-level preservation
-/

/--
The initial dictionary `M[9]=[3]` satisfies the marker invariant.
-/
theorem initial_markerInvariant :
    MarkerInvariant initialState := by

  unfold MarkerInvariant
  unfold MarkerInvariantAt

  refine
    ⟨by norm_num [initialState],
     ?_,
     ?_⟩

  · norm_num [initialState]

  · intro m p hmem

    have hpair :
        (m, p) = (9, 3) := by

      simpa [initialState] using hmem

    cases hpair

    exact
      {
        prime := by norm_num
        oddPrime := by norm_num
        prime_lt_candidate := by
          norm_num [initialState]
        divides := by norm_num
        oddKey := by norm_num
        candidate_le_key := by
          norm_num [initialState]
      }

/--
The composite branch of `step` preserves the marker invariant.
-/
theorem markerInvariant_step_of_marked
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hMarked :
      factorsAt
        s.markers
        s.candidate ≠ ∅) :
    MarkerInvariant (step s) := by

  rw [
    step_of_marked
      s
      hMarked
  ]

  unfold MarkerInvariant

  exact
    advanceAt_preserves_markerInvariantAt
      hInv

/--
The prime branch of `step` preserves the marker invariant, provided
the current unmarked candidate is indeed prime.

The next block will prove that the algorithm's coverage invariant makes
this primality hypothesis automatic.
-/
theorem markerInvariant_step_of_unmarked_prime
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hEmpty :
      factorsAt
        s.markers
        s.candidate = ∅)
    (hPrime :
      Nat.Prime s.candidate) :
    MarkerInvariant (step s) := by

  rw [
    step_of_unmarked
      s
      hEmpty
  ]

  unfold MarkerInvariant

  exact
    insert_square_preserves_markerInvariantAt
      hInv
      hEmpty
      hPrime


/-!
## 6. Coverage of the candidate currently being processed

Marker soundness proves that a present dictionary key is composite.
For the converse direction we isolate the exact coverage property needed
at the current candidate:

if an odd prime `p` can witness compositeness of `c` at the square-root
boundary, then the marker `(c,p)` is already present.

This section proves that this coverage property turns dictionary membership
into a correct primality decision.
-/

/--
Coverage property at the candidate currently being processed.

Every odd prime divisor `p` satisfying `p² ≤ c` already has its marker
at the current key `c`.
-/
def CandidateCoverageAt
    (c : ℕ)
    (M : MarkerMap) : Prop :=
  ∀ p,
    Nat.Prime p →
    p ≠ 2 →
    p * p ≤ c →
    p ∣ c →
    (c, p) ∈ M

/-- State-level form of `CandidateCoverageAt`. -/
def CandidateCoverage
    (s : SieveState) : Prop :=
  CandidateCoverageAt
    s.candidate
    s.markers

/--
Every odd composite candidate `c ≥ 5` has an odd prime divisor `p`
with `p² ≤ c` and `p < c`.

We use `Nat.minFac c` as the canonical witness.
-/
theorem odd_composite_has_small_prime_divisor
    {c : ℕ}
    (hc5 : 5 ≤ c)
    (hcOdd : Odd c)
    (hcNotPrime : ¬ Nat.Prime c) :
    ∃ p,
      Nat.Prime p ∧
      p ≠ 2 ∧
      p * p ≤ c ∧
      p < c ∧
      p ∣ c := by

  have hcPos :
      0 < c := by
    omega

  have hcNeOne :
      c ≠ 1 := by
    omega

  let p := c.minFac

  have hpPrime :
      Nat.Prime p := by

    dsimp [p]

    exact
      Nat.minFac_prime
        hcNeOne

  have hpDiv :
      p ∣ c := by

    dsimp [p]

    exact
      Nat.minFac_dvd c

  have hpNeTwo :
      p ≠ 2 := by

    intro hpTwo

    have hTwoDiv :
        2 ∣ c := by

      rw [← hpTwo]

      exact hpDiv

    rcases hcOdd with
      ⟨k, hk⟩

    rcases hTwoDiv with
      ⟨t, ht⟩

    omega

  have hpSqPow :
      p ^ 2 ≤ c := by

    dsimp [p]

    exact
      Nat.minFac_sq_le_self
        hcPos
        hcNotPrime

  have hpSq :
      p * p ≤ c := by

    simpa [pow_two] using hpSqPow

  have hpTwoLe :
      2 ≤ p :=
    hpPrime.two_le

  have hpLt :
      p < c := by

    nlinarith

  exact
    ⟨p,
     hpPrime,
     hpNeTwo,
     hpSq,
     hpLt,
     hpDiv⟩

/--
Candidate coverage implies that every odd composite candidate is
present as a dictionary key.
-/
theorem composite_candidate_is_marked
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M)
    (hCoverage :
      CandidateCoverageAt c M)
    (hNotPrime :
      ¬ Nat.Prime c) :
    HasKey M c := by

  rcases hInv with
    ⟨hc5, hcOdd, hMarkers⟩

  obtain
    ⟨p,
     hpPrime,
     hpNeTwo,
     hpSq,
     hpLt,
     hpDiv⟩ :=
    odd_composite_has_small_prime_divisor
      hc5
      hcOdd
      hNotPrime

  have hMarker :
      (c, p) ∈ M := by

    exact
      hCoverage
        p
        hpPrime
        hpNeTwo
        hpSq
        hpDiv

  have hpAt :
      p ∈ factorsAt M c := by

    exact
      mem_factorsAt_iff.mpr
        hMarker

  unfold HasKey

  intro hEmpty

  rw [hEmpty] at hpAt

  simp at hpAt

/--
Conversely, marker soundness implies that every present current key is
non-prime.
-/
theorem marked_candidate_is_not_prime
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M)
    (hMarked :
      HasKey M c) :
    ¬ Nat.Prime c := by

  unfold HasKey at hMarked

  obtain
    ⟨p, hMarker⟩ :=
    exists_marker_at_of_factorsAt_nonempty
      hMarked

  exact
    markerFacts_not_prime
      (hInv.2.2
        c
        p
        hMarker)

/--
Under soundness and candidate coverage, dictionary membership at the
current candidate is equivalent to compositeness.
-/
theorem marked_iff_not_prime
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M)
    (hCoverage :
      CandidateCoverageAt c M) :
    HasKey M c ↔
      ¬ Nat.Prime c := by

  constructor

  · intro hMarked

    exact
      marked_candidate_is_not_prime
        hInv
        hMarked

  · intro hNotPrime

    exact
      composite_candidate_is_marked
        hInv
        hCoverage
        hNotPrime

/--
Equivalent operational statement in the exact form used by `step`:

the current dictionary factor set is empty iff the current candidate
is prime.
-/
theorem factorsAt_empty_iff_prime
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M)
    (hCoverage :
      CandidateCoverageAt c M) :
    factorsAt M c = ∅ ↔
      Nat.Prime c := by

  constructor

  · intro hEmpty

    by_contra hNotPrime

    have hMarked :
        HasKey M c := by

      exact
        composite_candidate_is_marked
          hInv
          hCoverage
          hNotPrime

    unfold HasKey at hMarked

    exact
      hMarked
        hEmpty

  · intro hPrime

    by_contra hNotEmpty

    have hMarked :
        HasKey M c := by

      exact hNotEmpty

    have hNotPrime :
        ¬ Nat.Prime c := by

      exact
        marked_candidate_is_not_prime
          hInv
          hMarked

    exact
      hNotPrime
        hPrime

/--
State-level version: at a sound and covered state, the branch condition
of the algorithm is a correct primality test for the current candidate.
-/
theorem current_unmarked_iff_prime
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hCoverage :
      CandidateCoverage s) :
    factorsAt
        s.markers
        s.candidate = ∅
    ↔
    Nat.Prime s.candidate := by

  unfold MarkerInvariant at hInv
  unfold CandidateCoverage at hCoverage

  exact
    factorsAt_empty_iff_prime
      hInv
      hCoverage

/-!
### Initial candidate coverage
-/

/--
The initial state satisfies candidate coverage.

There is no odd prime `p` with `p² ≤ 5` that can divide the first
candidate `5`, so the property is vacuous at initialization.
-/
theorem initial_candidateCoverage :
    CandidateCoverage initialState := by

  unfold CandidateCoverage
  unfold CandidateCoverageAt

  intro p hpPrime hpNeTwo hpSq hpDiv

  have hpTwoLe :
      2 ≤ p :=
    hpPrime.two_le

  have hpLeTwo :
      p ≤ 2 := by

    norm_num [initialState] at hpSq

    nlinarith

  have hpEqTwo :
      p = 2 := by
    omega

  exact
    (hpNeTwo hpEqTwo).elim

/--
At the initial state, the branch condition already agrees with primality.
-/
theorem initial_unmarked_iff_prime :
    factorsAt
        initialState.markers
        initialState.candidate = ∅
    ↔
    Nat.Prime initialState.candidate := by

  exact
    current_unmarked_iff_prime
      initialState
      initial_markerInvariant
      initial_candidateCoverage


/-!
## 7. Local scheduling laws of the dictionary

We now prove the exact operational facts that will be used to establish
global coverage.

There are only two ways in which a marker `(m,p)` can behave during one
iteration:

* if its key `m` is not the current candidate, it remains unchanged;
* if its key is the current candidate `c`, it is moved exactly to
  `(c + 2*p, p)`.

Likewise, when an unmarked prime `c` is discovered, `(c²,c)` is inserted.
These are the formal scheduling laws corresponding directly to Algorithm 3.1.
-/

/--
A marker whose key is not the current candidate survives `advanceAt`
unchanged.
-/
theorem mem_advanceAt_of_key_ne
    {M : MarkerMap}
    {c m p : ℕ}
    (hmem :
      (m, p) ∈ M)
    (hne :
      m ≠ c) :
    (m, p) ∈ advanceAt M c := by

  unfold advanceAt

  apply Finset.mem_union.mpr

  left

  exact
    Finset.mem_filter.mpr
      ⟨hmem, hne⟩

/--
A marker located at the current candidate is moved by exactly `2*p`.
-/
theorem mem_advanceAt_moved
    {M : MarkerMap}
    {c p : ℕ}
    (hmem :
      (c, p) ∈ M) :
    (c + 2 * p, p) ∈
      advanceAt M c := by

  unfold advanceAt

  apply Finset.mem_union.mpr

  right

  apply Finset.mem_image.mpr

  refine
    ⟨(c, p), ?_, rfl⟩

  exact
    Finset.mem_filter.mpr
      ⟨hmem, rfl⟩

/--
If a marker is stored at a future key, one call to `step` preserves it.
This holds in both the prime and composite branches.
-/
theorem step_preserves_marker_of_key_ne
    (s : SieveState)
    {m p : ℕ}
    (hmem :
      (m, p) ∈ s.markers)
    (hne :
      m ≠ s.candidate) :
    (m, p) ∈ (step s).markers := by

  by_cases hEmpty :
      factorsAt
        s.markers
        s.candidate = ∅

  · rw [
      step_of_unmarked
        s
        hEmpty
    ]

    exact
      Finset.mem_insert.mpr
        (Or.inr hmem)

  · rw [
      step_of_marked
        s
        hEmpty
    ]

    exact
      mem_advanceAt_of_key_ne
        hmem
        hne

/--
If `(candidate,p)` is present, then the composite branch is necessarily
taken and the marker `(candidate+2p,p)` is present after the step.
-/
theorem step_moves_current_marker
    (s : SieveState)
    {p : ℕ}
    (hmem :
      (s.candidate, p) ∈
        s.markers) :
    (s.candidate + 2 * p, p) ∈
      (step s).markers := by

  have hpAt :
      p ∈
        factorsAt
          s.markers
          s.candidate := by

    exact
      mem_factorsAt_iff.mpr
        hmem

  have hMarked :
      factorsAt
          s.markers
          s.candidate ≠ ∅ := by

    intro hEmpty

    rw [hEmpty] at hpAt

    simp at hpAt

  rw [
    step_of_marked
      s
      hMarked
  ]

  exact
    mem_advanceAt_moved
      hmem

/--
When the current candidate is unmarked, the prime branch inserts its square
as a new marker.
-/
theorem step_inserts_square_of_unmarked
    (s : SieveState)
    (hEmpty :
      factorsAt
        s.markers
        s.candidate = ∅) :
    (s.candidate * s.candidate,
     s.candidate) ∈
      (step s).markers := by

  rw [
    step_of_unmarked
      s
      hEmpty
  ]

  exact
    Finset.mem_insert_self
      (s.candidate * s.candidate,
       s.candidate)
      s.markers

/--
Under the already-proved soundness and candidate-coverage hypotheses,
every prime candidate inserts its square.
-/
theorem step_inserts_square_of_prime
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hCoverage :
      CandidateCoverage s)
    (hPrime :
      Nat.Prime s.candidate) :
    (s.candidate * s.candidate,
     s.candidate) ∈
      (step s).markers := by

  have hEmpty :
      factorsAt
        s.markers
        s.candidate = ∅ := by

    exact
      (current_unmarked_iff_prime
        s
        hInv
        hCoverage).2
        hPrime

  exact
    step_inserts_square_of_unmarked
      s
      hEmpty

/--
A future marker remains present for one execution step.
-/
theorem step_preserves_future_marker
    (s : SieveState)
    {m p : ℕ}
    (hmem :
      (m, p) ∈ s.markers)
    (hFuture :
      s.candidate < m) :
    (m, p) ∈ (step s).markers := by

  exact
    step_preserves_marker_of_key_ne
      s
      hmem
      (ne_of_gt hFuture)

/--
Specialization to `runSteps`: a marker strictly beyond the current
candidate persists into the next iteration.
-/
theorem runSteps_future_marker_persists
    {steps m p : ℕ}
    (hmem :
      (m, p) ∈
        (runSteps steps).markers)
    (hFuture :
      (runSteps steps).candidate < m) :
    (m, p) ∈
      (runSteps (steps + 1)).markers := by

  rw [runSteps]

  exact
    step_preserves_future_marker
      (runSteps steps)
      hmem
      hFuture

/--
Specialization to `runSteps`: if the marker is exactly at the current
candidate, then after processing that candidate it is scheduled at the
next odd multiple `candidate + 2*p`.
-/
theorem runSteps_current_marker_advances
    {steps p : ℕ}
    (hmem :
      ((runSteps steps).candidate, p) ∈
        (runSteps steps).markers) :
    ((runSteps steps).candidate + 2 * p, p) ∈
      (runSteps (steps + 1)).markers := by

  rw [runSteps]

  exact
    step_moves_current_marker
      (runSteps steps)
      hmem

/-!
### Concrete checks of the scheduling mechanism
-/

/--
The initial marker `(9,3)` remains scheduled while candidates `5` and `7`
are processed.
-/
example :
    (9, 3) ∈
      (runSteps 2).markers := by
  native_decide

/--
When candidate `9` is processed, the marker for `3` advances to `15`.
-/
example :
    (15, 3) ∈
      (runSteps 3).markers := by
  native_decide

/--
The marker for `5` starts at its square `25`.
-/
example :
    (25, 5) ∈
      (runSteps 2).markers := by
  native_decide


/-!
## 8. Infinite additive progression of each marker

The paper states that once a prime marker `p` is active, its composite
keys form the additive progression

`p², p² + 2p, p² + 4p, ...`.

We now formalize this progression and prove that the operational dictionary
really follows it.  This is stronger than checking isolated examples: the
result below is quantified over an arbitrary number of future marker moves.
-/

/--
The `k`-th composite key scheduled by prime marker `p`, beginning at `p²`.
-/
def markerProgression
    (p k : ℕ) : ℕ :=
  p * p + 2 * p * k

theorem markerProgression_zero
    (p : ℕ) :
    markerProgression p 0 =
      p * p := by

  simp [markerProgression]

/--
Successive marker keys differ by exactly `2p`.
-/
theorem markerProgression_succ
    (p k : ℕ) :
    markerProgression p (k + 1) =
      markerProgression p k + 2 * p := by

  unfold markerProgression

  ring

/--
A future marker persists through any prescribed number of candidate steps,
provided the candidate has still not passed the marker key.

Because each iteration increases the candidate by exactly two, the condition

`currentCandidate + 2 * wait ≤ m`

means precisely that `m` is still a current-or-future key throughout those
`wait` iterations.
-/
theorem runSteps_marker_persists_until
    {steps wait m p : ℕ}
    (hmem :
      (m, p) ∈
        (runSteps steps).markers)
    (hbound :
      (runSteps steps).candidate +
          2 * wait ≤
        m) :
    (m, p) ∈
      (runSteps (steps + wait)).markers := by

  revert hbound

  induction wait with

  | zero =>
      intro hbound

      simpa using hmem

  | succ wait ih =>
      intro hbound

      have hboundPrev :
          (runSteps steps).candidate +
              2 * wait ≤
            m := by

        omega

      have hmemPrev :
          (m, p) ∈
            (runSteps
              (steps + wait)).markers := by

        exact
          ih hboundPrev

      have hCandidate :
          (runSteps
              (steps + wait)).candidate =
            (runSteps steps).candidate +
              2 * wait := by

        rw [
          runSteps_candidate,
          runSteps_candidate
        ]

        omega

      have hFuture :
          (runSteps
              (steps + wait)).candidate <
            m := by

        rw [hCandidate]

        omega

      have hNext :
          (m, p) ∈
            (runSteps
              ((steps + wait) + 1)).markers := by

        exact
          runSteps_future_marker_persists
            hmemPrev
            hFuture

      simpa [Nat.add_assoc] using hNext

/--
One complete marker cycle.

If the current candidate is exactly the `k`-th key of the progression
for `p`, and that marker is present, then after exactly `p` candidate
iterations:

* the candidate has reached the next progression key;
* the marker is present at that next key.

This packages together one move by `2p` and the intervening `p-1`
candidate iterations during which the marker waits unchanged.
-/
theorem runSteps_marker_progression_hop
    {steps p k : ℕ}
    (hpPos :
      0 < p)
    (hCandidate :
      (runSteps steps).candidate =
        markerProgression p k)
    (hmem :
      (markerProgression p k, p) ∈
        (runSteps steps).markers) :
    (runSteps (steps + p)).candidate =
        markerProgression p (k + 1)
      ∧
    (markerProgression p (k + 1), p) ∈
        (runSteps (steps + p)).markers := by

  have hCurrentMarker :
      ((runSteps steps).candidate, p) ∈
        (runSteps steps).markers := by

    rw [hCandidate]

    exact hmem

  have hMovedRaw :
      ((runSteps steps).candidate + 2 * p, p) ∈
        (runSteps (steps + 1)).markers := by

    exact
      runSteps_current_marker_advances
        hCurrentMarker

  have hMoved :
      (markerProgression p (k + 1), p) ∈
        (runSteps (steps + 1)).markers := by

    rw [
      markerProgression_succ,
      ← hCandidate
    ]

    exact hMovedRaw

  have hCandidateNat :
      5 + 2 * steps =
        markerProgression p k := by

    simpa [runSteps_candidate] using hCandidate

  have hWaitBound :
      (runSteps
          (steps + 1)).candidate +
          2 * (p - 1) ≤
        markerProgression p (k + 1) := by

    rw [
      runSteps_candidate,
      markerProgression_succ
    ]

    omega

  have hPersist :
      (markerProgression p (k + 1), p) ∈
        (runSteps
          ((steps + 1) + (p - 1))).markers := by

    exact
      runSteps_marker_persists_until
        hMoved
        hWaitBound

  have hIndex :
      (steps + 1) + (p - 1) =
        steps + p := by

    omega

  have hCandidateNext :
      (runSteps (steps + p)).candidate =
        markerProgression p (k + 1) := by

    rw [
      runSteps_candidate,
      markerProgression_succ
    ]

    omega

  constructor

  · exact hCandidateNext

  · rw [hIndex] at hPersist

    exact hPersist

/--
Full propagation theorem.

Once a marker `p` is present exactly when the candidate is at one point
of its additive progression, the same statement holds for every later
point of that progression.

After `t` marker cycles, the algorithm is at

`p² + 2p(k+t)`

and the marker `p` is present there.
-/
theorem runSteps_marker_progression_iterate
    {steps p k : ℕ}
    (hpPos :
      0 < p)
    (hCandidate :
      (runSteps steps).candidate =
        markerProgression p k)
    (hmem :
      (markerProgression p k, p) ∈
        (runSteps steps).markers)
    (t : ℕ) :
    (runSteps
        (steps + t * p)).candidate =
      markerProgression p (k + t)
      ∧
    (markerProgression p (k + t), p) ∈
      (runSteps
        (steps + t * p)).markers := by

  induction t with

  | zero =>
      constructor

      · simpa using hCandidate

      · simpa using hmem

  | succ t ih =>
      have hHop :
          (runSteps
              ((steps + t * p) + p)).candidate =
            markerProgression
              p
              ((k + t) + 1)
            ∧
          (markerProgression
              p
              ((k + t) + 1),
           p) ∈
            (runSteps
              ((steps + t * p) + p)).markers := by

        exact
          runSteps_marker_progression_hop
            hpPos
            ih.1
            ih.2

      simpa [
        Nat.succ_mul,
        Nat.add_assoc
      ] using hHop

/-!
### The initial marker `3` as an infinite theorem

The initial state has marker `(9,3)`.  Candidate `9` is reached after
processing `5` and `7`, i.e. at `runSteps 2`.

The following theorem therefore proves, for every natural `t`, that the
marker for `3` is present exactly at

`9 + 6t`.
-/

theorem marker_three_progresses_forever
    (t : ℕ) :
    (runSteps
        (2 + t * 3)).candidate =
      markerProgression 3 t
      ∧
    (markerProgression 3 t, 3) ∈
      (runSteps
        (2 + t * 3)).markers := by

  have hCandidate :
      (runSteps 2).candidate =
        markerProgression 3 0 := by

    norm_num [
      runSteps_candidate,
      markerProgression
    ]

  have hmem :
      (markerProgression 3 0, 3) ∈
        (runSteps 2).markers := by

    native_decide

  simpa using
    (runSteps_marker_progression_iterate
      (steps := 2)
      (p := 3)
      (k := 0)
      (hpPos := by norm_num)
      hCandidate
      hmem
      t)


/-!
## 9. Global scheduling invariant

To make the scheduling invariant compatible with newly discovered primes,
the lower edge of the scheduling window must take the square `p²` into
account.

A prime `p` is first scheduled at `p²`.  Before the running candidate has
reached `p²`, that marker must remain at or beyond `p²`; after the candidate
has reached `p²`, the next marker must lie in the ordinary width-`2p`
window beginning at the current candidate.

Accordingly we use the floor

`max c p²`.

For every already discovered odd prime `p < c`, the dictionary contains
one scheduled multiple `m` of `p` satisfying

`max c p² ≤ m < max c p² + 2p`.

When additionally `p² ≤ c` and `p ∣ c`, the floor becomes exactly `c`.
Parity then forces the scheduled multiple to be `c` itself.  This supplies
the candidate coverage needed for a correct primality decision.
-/

/-- Lower edge of the scheduling window for marker `p` at candidate `c`. -/
def scheduleFloor
    (c p : ℕ) : ℕ :=
  max c (p * p)

/--
Global scheduling invariant at candidate `c`.

For every earlier odd prime `p`, some marker for `p` is scheduled in the
half-open interval

`[max c p², max c p² + 2p)`.
-/
def PrimeScheduleAt
    (c : ℕ)
    (M : MarkerMap) : Prop :=
  ∀ p,
    Nat.Prime p →
    p ≠ 2 →
    p < c →
    ∃ m,
      (m, p) ∈ M ∧
      scheduleFloor c p ≤ m ∧
      m < scheduleFloor c p + 2 * p ∧
      p ∣ m

/-- State-level form of the global scheduling invariant. -/
def PrimeSchedule
    (s : SieveState) : Prop :=
  PrimeScheduleAt
    s.candidate
    s.markers

/--
Two odd multiples of the same positive odd number cannot occupy different
positions inside an interval of width `2p`.

If `c` and `m` are odd multiples of `p` and

`c ≤ m < c + 2p`,

then necessarily `m = c`.
-/
theorem odd_multiple_unique_in_two_p_window
    {c m p : ℕ}
    (hpPos : 0 < p)
    (hpOdd : Odd p)
    (hcOdd : Odd c)
    (hmOdd : Odd m)
    (hpDivC : p ∣ c)
    (hpDivM : p ∣ m)
    (hLower : c ≤ m)
    (hUpper : m < c + 2 * p) :
    m = c := by

  rcases hpDivC with
    ⟨a, ha⟩

  rcases hpDivM with
    ⟨b, hb⟩

  have hab :
      a ≤ b := by

    nlinarith

  have hbaUpper :
      b < a + 2 := by

    nlinarith

  have hCases :
      b = a ∨
      b = a + 1 := by

    omega

  rcases hCases with
    hEq | hSucc

  · rw [hEq] at hb

    omega

  · have hmc :
        m = c + p := by

      rw [ha, hb, hSucc]

      ring

    rcases hpOdd with
      ⟨u, hu⟩

    rcases hcOdd with
      ⟨v, hv⟩

    rcases hmOdd with
      ⟨w, hw⟩

    omega

/--
The global scheduling invariant implies the candidate-coverage property.

If `p² ≤ c`, then `scheduleFloor c p = c`; therefore the scheduled marker
lies in `[c,c+2p)`.  If `p ∣ c`, parity and divisibility force that marker
to be exactly at `c`.
-/
theorem primeSchedule_implies_candidateCoverageAt
    {c : ℕ}
    {M : MarkerMap}
    (hInv :
      MarkerInvariantAt c M)
    (hSchedule :
      PrimeScheduleAt c M) :
    CandidateCoverageAt c M := by

  intro p hpPrime hpNeTwo hpSq hpDiv

  rcases hInv with
    ⟨hc5, hcOdd, hMarkers⟩

  have hpLt :
      p < c := by

    have hpTwoLe :
        2 ≤ p :=
      hpPrime.two_le

    nlinarith

  obtain
    ⟨m,
     hmem,
     hLower,
     hUpper,
     hpDivM⟩ :=
    hSchedule
      p
      hpPrime
      hpNeTwo
      hpLt

  have hFloor :
      scheduleFloor c p = c := by

    unfold scheduleFloor

    exact
      max_eq_left
        hpSq

  rw [hFloor] at hLower hUpper

  have hFacts :
      MarkerFacts c m p :=
    hMarkers
      m
      p
      hmem

  have hpOdd :
      Odd p :=
    hpPrime.odd_of_ne_two
      hpNeTwo

  have hmEq :
      m = c := by

    exact
      odd_multiple_unique_in_two_p_window
        hpPrime.pos
        hpOdd
        hcOdd
        hFacts.oddKey
        hpDiv
        hpDivM
        hLower
        hUpper

  subst m

  exact hmem

/--
State-level form: the global schedule automatically supplies the local
coverage needed for the current primality decision.
-/
theorem primeSchedule_implies_candidateCoverage
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hSchedule :
      PrimeSchedule s) :
    CandidateCoverage s := by

  unfold MarkerInvariant at hInv
  unfold PrimeSchedule at hSchedule
  unfold CandidateCoverage

  exact
    primeSchedule_implies_candidateCoverageAt
      hInv
      hSchedule

/--
With marker soundness and the global schedule, the algorithm's actual
branch condition is equivalent to primality.
-/
theorem current_unmarked_iff_prime_of_schedule
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hSchedule :
      PrimeSchedule s) :
    factorsAt
        s.markers
        s.candidate = ∅
    ↔
    Nat.Prime s.candidate := by

  have hCoverage :
      CandidateCoverage s :=
    primeSchedule_implies_candidateCoverage
      s
      hInv
      hSchedule

  exact
    current_unmarked_iff_prime
      s
      hInv
      hCoverage

/-!
### Initial global schedule
-/

/--
The initial state satisfies the global scheduling invariant.

The only odd prime below candidate `5` is `3`; its marker is at `9 = 3²`,
which is exactly the scheduling floor `max 5 9`.
-/
theorem initial_primeSchedule :
    PrimeSchedule initialState := by

  unfold PrimeSchedule
  unfold PrimeScheduleAt

  intro p hpPrime hpNeTwo hpLt

  have hpTwoLe :
      2 ≤ p :=
    hpPrime.two_le

  have hpEqThree :
      p = 3 := by

    norm_num [initialState] at hpLt

    have hpCases :
        p = 2 ∨
        p = 3 ∨
        p = 4 := by

      omega

    rcases hpCases with
      hpEqTwo | hpRest

    · exact
        (hpNeTwo hpEqTwo).elim

    · rcases hpRest with
        hpEqThree | hpEqFour

      · exact hpEqThree

      · subst p

        norm_num at hpPrime

  subst p

  refine
    ⟨9, ?_, ?_, ?_, ?_⟩

  · exact
      initial_three_marker

  · norm_num [
      initialState,
      scheduleFloor
    ]

  · norm_num [
      initialState,
      scheduleFloor
    ]

  · norm_num

/--
The initial state therefore satisfies candidate coverage as a consequence
of the stronger global schedule.
-/
theorem initial_candidateCoverage_from_schedule :
    CandidateCoverage initialState := by

  exact
    primeSchedule_implies_candidateCoverage
      initialState
      initial_markerInvariant
      initial_primeSchedule

/-!
## 10. Preservation of the global schedule by one algorithm step
-/

/--
The square of an odd number is odd.
-/
theorem odd_mul_self
    {p : ℕ}
    (hpOdd : Odd p) :
    Odd (p * p) := by

  rcases hpOdd with
    ⟨k, hk⟩

  refine
    ⟨2 * k * k + 2 * k, ?_⟩

  rw [hk]

  ring

/--
If `p` and `c` are odd and `p < c+2`, then `p ≤ c`.

This excludes the only intervening integer `c+1`, which is even.
-/
theorem odd_le_current_of_lt_next
    {p c : ℕ}
    (hpOdd : Odd p)
    (hcOdd : Odd c)
    (hLt : p < c + 2) :
    p ≤ c := by

  rcases hpOdd with
    ⟨a, ha⟩

  rcases hcOdd with
    ⟨b, hb⟩

  omega

/--
The global prime schedule is preserved by one exact execution step.
-/
theorem primeSchedule_step
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hSchedule :
      PrimeSchedule s) :
    PrimeSchedule (step s) := by

  have hInvAt :
      MarkerInvariantAt
        s.candidate
        s.markers := by

    exact hInv

  rcases hInvAt with
    ⟨hc5, hcOdd, hMarkerFacts⟩

  unfold PrimeSchedule
  unfold PrimeScheduleAt

  rw [step_candidate]

  intro p hpPrime hpNeTwo hpLtNext

  have hpOdd :
      Odd p :=
    hpPrime.odd_of_ne_two
      hpNeTwo

  have hpLeCurrent :
      p ≤ s.candidate := by

    exact
      odd_le_current_of_lt_next
        hpOdd
        hcOdd
        hpLtNext

  by_cases hpEq :
      p = s.candidate

  · subst p

    have hEmpty :
        factorsAt
            s.markers
            s.candidate = ∅ := by

      exact
        (current_unmarked_iff_prime_of_schedule
          s
          hInv
          hSchedule).2
          hpPrime

    have hInserted :
        (s.candidate * s.candidate,
         s.candidate) ∈
          (step s).markers := by

      exact
        step_inserts_square_of_unmarked
          s
          hEmpty

    have hSqLower :
        s.candidate + 2 ≤
          s.candidate * s.candidate := by

      nlinarith

    have hFloor :
        scheduleFloor
            (s.candidate + 2)
            s.candidate =
          s.candidate * s.candidate := by

      unfold scheduleFloor

      exact
        max_eq_right
          hSqLower

    refine
      ⟨s.candidate * s.candidate,
       hInserted,
       ?_,
       ?_,
       ?_⟩

    · rw [hFloor]

    · rw [hFloor]

      have hcPos :
          0 < s.candidate := by
        omega

      nlinarith

    · exact
        ⟨s.candidate, by ring⟩

  · have hpLt :
        p < s.candidate := by
      omega

    obtain
      ⟨m,
       hmem,
       hLower,
       hUpper,
       hpDivM⟩ :=
      hSchedule
        p
        hpPrime
        hpNeTwo
        hpLt

    have hFacts :
        MarkerFacts
          s.candidate
          m
          p :=
      hMarkerFacts
        m
        p
        hmem

    by_cases hpSq :
        p * p ≤ s.candidate

    · have hFloorOld :
          scheduleFloor
              s.candidate
              p =
            s.candidate := by

        unfold scheduleFloor

        exact
          max_eq_left
            hpSq

      have hFloorNew :
          scheduleFloor
              (s.candidate + 2)
              p =
            s.candidate + 2 := by

        unfold scheduleFloor

        apply max_eq_left

        omega

      rw [hFloorOld] at hLower hUpper

      by_cases hmEq :
          m = s.candidate

      · subst m

        have hMoved :
            (s.candidate + 2 * p, p) ∈
              (step s).markers := by

          exact
            step_moves_current_marker
              s
              hmem

        have hpTwoLe :
            2 ≤ p :=
          hpPrime.two_le

        have hDivMoved :
            p ∣ s.candidate + 2 * p := by

          rcases hpDivM with
            ⟨q, hq⟩

          refine
            ⟨q + 2, ?_⟩

          rw [hq]

          ring

        refine
          ⟨s.candidate + 2 * p,
           hMoved,
           ?_,
           ?_,
           hDivMoved⟩

        · rw [hFloorNew]

          omega

        · rw [hFloorNew]

          omega

      · have hPersist :
            (m, p) ∈
              (step s).markers := by

          exact
            step_preserves_marker_of_key_ne
              s
              hmem
              hmEq

        have hNextLower :
            s.candidate + 2 ≤ m := by

          exact
            add_two_le_of_odd_le_ne
              hcOdd
              hFacts.oddKey
              hLower
              hmEq

        refine
          ⟨m,
           hPersist,
           ?_,
           ?_,
           hpDivM⟩

        · rw [hFloorNew]

          exact hNextLower

        · rw [hFloorNew]

          omega

    · have hpSqGt :
          s.candidate < p * p := by
        omega

      have hpSqOdd :
          Odd (p * p) :=
        odd_mul_self
          hpOdd

      have hNextLeSq :
          s.candidate + 2 ≤
            p * p := by

        exact
          add_two_le_of_odd_le_ne
            hcOdd
            hpSqOdd
            (Nat.le_of_lt hpSqGt)
            (ne_of_gt hpSqGt)

      have hFloorOld :
          scheduleFloor
              s.candidate
              p =
            p * p := by

        unfold scheduleFloor

        exact
          max_eq_right
            (Nat.le_of_lt hpSqGt)

      have hFloorNew :
          scheduleFloor
              (s.candidate + 2)
              p =
            p * p := by

        unfold scheduleFloor

        exact
          max_eq_right
            hNextLeSq

      have hmNe :
          m ≠ s.candidate := by

        intro hmEq

        subst m

        rw [hFloorOld] at hLower

        omega

      have hPersist :
          (m, p) ∈
            (step s).markers := by

        exact
          step_preserves_marker_of_key_ne
            s
            hmem
            hmNe

      rw [hFloorOld] at hLower hUpper

      refine
        ⟨m,
         hPersist,
         ?_,
         ?_,
         hpDivM⟩

      · rw [hFloorNew]

        exact hLower

      · rw [hFloorNew]

        exact hUpper

/--
The two global invariants are preserved simultaneously by one step.

The branch taken by the implementation is correct because
`current_unmarked_iff_prime_of_schedule` identifies the unmarked branch
exactly with primality.
-/
theorem global_invariants_step
    (s : SieveState)
    (hInv :
      MarkerInvariant s)
    (hSchedule :
      PrimeSchedule s) :
    MarkerInvariant (step s) ∧
    PrimeSchedule (step s) := by

  constructor

  · by_cases hEmpty :
        factorsAt
            s.markers
            s.candidate = ∅

    · have hPrime :
          Nat.Prime s.candidate := by

        exact
          (current_unmarked_iff_prime_of_schedule
            s
            hInv
            hSchedule).1
            hEmpty

      exact
        markerInvariant_step_of_unmarked_prime
          s
          hInv
          hEmpty
          hPrime

    · exact
        markerInvariant_step_of_marked
          s
          hInv
          hEmpty

  · exact
      primeSchedule_step
        s
        hInv
        hSchedule

/-!
## 11. Global induction over every execution step
-/

/--
For every finite number of iterations, both global invariants hold.
-/
theorem runSteps_global_invariants
    (steps : ℕ) :
    MarkerInvariant (runSteps steps) ∧
    PrimeSchedule (runSteps steps) := by

  induction steps with

  | zero =>
      exact
        ⟨initial_markerInvariant,
         initial_primeSchedule⟩

  | succ steps ih =>
      rw [runSteps]

      exact
        global_invariants_step
          (runSteps steps)
          ih.1
          ih.2

/--
At every iteration, the actual dictionary test performed by the algorithm
is equivalent to primality of the current candidate.
-/
theorem runSteps_unmarked_iff_prime
    (steps : ℕ) :
    factorsAt
        (runSteps steps).markers
        (runSteps steps).candidate = ∅
    ↔
    Nat.Prime
      (runSteps steps).candidate := by

  have hGlobal :=
    runSteps_global_invariants
      steps

  exact
    current_unmarked_iff_prime_of_schedule
      (runSteps steps)
      hGlobal.1
      hGlobal.2

/--
Equivalent form: at every iteration, a nonempty dictionary entry at the
current candidate is equivalent to that candidate being non-prime.
-/
theorem runSteps_marked_iff_not_prime
    (steps : ℕ) :
    factorsAt
        (runSteps steps).markers
        (runSteps steps).candidate ≠ ∅
    ↔
    ¬ Nat.Prime
      (runSteps steps).candidate := by

  constructor

  · intro hMarked hPrime

    have hEmpty :
        factorsAt
            (runSteps steps).markers
            (runSteps steps).candidate = ∅ := by

      exact
        (runSteps_unmarked_iff_prime
          steps).2
          hPrime

    exact
      hMarked
        hEmpty

  · intro hNotPrime hEmpty

    have hPrime :
        Nat.Prime
          (runSteps steps).candidate := by

      exact
        (runSteps_unmarked_iff_prime
          steps).1
          hEmpty

    exact
      hNotPrime
        hPrime

/--
Prime branch, now without any external invariant assumptions:
if the current candidate is prime, `step` appends it to the output list.
-/
theorem runSteps_prime_is_appended
    (steps : ℕ)
    (hPrime :
      Nat.Prime
        (runSteps steps).candidate) :
    (runSteps (steps + 1)).primes =
      (runSteps steps).primes ++
        [(runSteps steps).candidate] := by

  have hEmpty :
      factorsAt
          (runSteps steps).markers
          (runSteps steps).candidate = ∅ := by

    exact
      (runSteps_unmarked_iff_prime
        steps).2
        hPrime

  rw [runSteps]

  rw [
    step_of_unmarked
      (runSteps steps)
      hEmpty
  ]

/--
Composite branch, now without any external invariant assumptions:
if the current candidate is not prime, `step` leaves the output list
unchanged.
-/
theorem runSteps_nonprime_is_not_appended
    (steps : ℕ)
    (hNotPrime :
      ¬ Nat.Prime
        (runSteps steps).candidate) :
    (runSteps (steps + 1)).primes =
      (runSteps steps).primes := by

  have hMarked :
      factorsAt
          (runSteps steps).markers
          (runSteps steps).candidate ≠ ∅ := by

    exact
      (runSteps_marked_iff_not_prime
        steps).2
        hNotPrime

  rw [runSteps]

  rw [
    step_of_marked
      (runSteps steps)
      hMarked
  ]


/-!
## 12. Exact output sequence: all odd primes, once and in order

The operational correctness theorem above proves that every branch decision
is correct.  We now identify the complete output list.

`expectedPrimes steps` is an independent mathematical specification:
start with `3`, inspect the odd candidates `5,7,9,...` in increasing order,
and append a candidate exactly when it is prime.

The main theorem of this section proves that the executable sieve state
produces exactly this specification after every finite number of steps.
-/

/--
Independent specification of the prime sequence produced after `steps`
candidate inspections.
-/
def expectedPrimes : ℕ → List ℕ
  | 0 =>
      [3]
  | steps + 1 =>
      let c := 5 + 2 * steps
      if Nat.Prime c then
        expectedPrimes steps ++ [c]
      else
        expectedPrimes steps

/--
The operational algorithm and the independent mathematical specification
have exactly the same output list after every number of steps.
-/
theorem runSteps_primes_eq_expected
    (steps : ℕ) :
    (runSteps steps).primes =
      expectedPrimes steps := by

  induction steps with

  | zero =>
      rfl

  | succ steps ih =>
      by_cases hPrime :
          Nat.Prime
            (runSteps steps).candidate

      · have hPrimeNat :
            Nat.Prime
              (5 + 2 * steps) := by

          simpa [runSteps_candidate] using hPrime

        rw [
          runSteps_prime_is_appended
            steps
            hPrime,
          ih
        ]

        simp [
          expectedPrimes,
          hPrimeNat,
          runSteps_candidate
        ]

      · have hNotPrimeNat :
            ¬ Nat.Prime
              (5 + 2 * steps) := by

          simpa [runSteps_candidate] using hPrime

        rw [
          runSteps_nonprime_is_not_appended
            steps
            hPrime,
          ih
        ]

        simp [
          expectedPrimes,
          hNotPrimeNat
        ]

/--
Every number occurring in the mathematical specification is prime.
-/
theorem mem_expectedPrimes_prime
    {steps p : ℕ}
    (hmem :
      p ∈ expectedPrimes steps) :
    Nat.Prime p := by

  induction steps with

  | zero =>
      simp [expectedPrimes] at hmem

      subst p

      norm_num

  | succ steps ih =>
      by_cases hPrime :
          Nat.Prime
            (5 + 2 * steps)

      · simp [
          expectedPrimes,
          hPrime
        ] at hmem

        rcases hmem with
          hOld | hCurrent

        · exact
            ih hOld

        · subst p

          exact hPrime

      · simp [
          expectedPrimes,
          hPrime
        ] at hmem

        exact
          ih hmem

/--
The prime `2` never occurs in the odd-prime output specification.
-/
theorem mem_expectedPrimes_ne_two
    {steps p : ℕ}
    (hmem :
      p ∈ expectedPrimes steps) :
    p ≠ 2 := by

  induction steps with

  | zero =>
      simp [expectedPrimes] at hmem

      omega

  | succ steps ih =>
      by_cases hPrime :
          Nat.Prime
            (5 + 2 * steps)

      · simp [
          expectedPrimes,
          hPrime
        ] at hmem

        rcases hmem with
          hOld | hCurrent

        · exact
            ih hOld

        · omega

      · simp [
          expectedPrimes,
          hPrime
        ] at hmem

        exact
          ih hmem

/--
Every element already emitted after `steps` iterations is strictly below
the next candidate `5 + 2*steps`.
-/
theorem mem_expectedPrimes_lt_nextCandidate
    {steps p : ℕ}
    (hmem :
      p ∈ expectedPrimes steps) :
    p < 5 + 2 * steps := by

  induction steps with

  | zero =>
      simp [expectedPrimes] at hmem

      omega

  | succ steps ih =>
      by_cases hPrime :
          Nat.Prime
            (5 + 2 * steps)

      · simp [
          expectedPrimes,
          hPrime
        ] at hmem

        rcases hmem with
          hOld | hCurrent

        · have hOldBound :
              p < 5 + 2 * steps :=
            ih hOld

          omega

        · omega

      · simp [
          expectedPrimes,
          hPrime
        ] at hmem

        have hOldBound :
            p < 5 + 2 * steps :=
          ih hmem

        omega

/--
Every odd prime strictly below the next candidate is already present in
the mathematical specification.
-/
theorem prime_mem_expectedPrimes_of_lt
    (steps : ℕ)
    {p : ℕ}
    (hpPrime :
      Nat.Prime p)
    (hpNeTwo :
      p ≠ 2)
    (hpLt :
      p < 5 + 2 * steps) :
    p ∈ expectedPrimes steps := by

  induction steps with

  | zero =>
      have hpTwoLe :
          2 ≤ p :=
        hpPrime.two_le

      have hpNeFour :
          p ≠ 4 := by

        intro hpEqFour

        subst p

        norm_num at hpPrime

      have hpEq :
          p = 3 := by

        omega

      subst p

      simp [expectedPrimes]

  | succ steps ih =>
      have hpOdd :
          Odd p :=
        hpPrime.odd_of_ne_two
          hpNeTwo

      have hCurrentOdd :
          Odd (5 + 2 * steps) := by

        refine
          ⟨steps + 2, ?_⟩

        omega

      have hpLtNext :
          p <
            (5 + 2 * steps) + 2 := by
        omega

      have hpLeCurrent :
          p ≤
            5 + 2 * steps := by

        exact
          odd_le_current_of_lt_next
            hpOdd
            hCurrentOdd
            hpLtNext

      by_cases hpEq :
          p = 5 + 2 * steps

      · have hCurrentPrime :
            Nat.Prime
              (5 + 2 * steps) := by

          simpa [hpEq] using hpPrime

        simp [
          expectedPrimes,
          hCurrentPrime,
          hpEq
        ]

      · have hpLtCurrent :
            p <
              5 + 2 * steps := by
          omega

        have hOld :
            p ∈ expectedPrimes steps := by

          exact
            ih
              hpLtCurrent

        by_cases hCurrentPrime :
            Nat.Prime
              (5 + 2 * steps)

        · simp [
            expectedPrimes,
            hCurrentPrime,
            hOld
          ]

        · simp [
            expectedPrimes,
            hCurrentPrime,
            hOld
          ]

/--
Exact set-theoretic characterization of the output after every number of
steps.

A natural number occurs in the generated list iff it is a prime different
from `2` and it lies strictly below the next candidate.
-/
theorem mem_runSteps_primes_iff
    (steps p : ℕ) :
    p ∈ (runSteps steps).primes
    ↔
    Nat.Prime p ∧
    p ≠ 2 ∧
    p < (runSteps steps).candidate := by

  rw [
    runSteps_primes_eq_expected,
    runSteps_candidate
  ]

  constructor

  · intro hmem

    exact
      ⟨mem_expectedPrimes_prime hmem,
       mem_expectedPrimes_ne_two hmem,
       mem_expectedPrimes_lt_nextCandidate hmem⟩

  · rintro
      ⟨hpPrime,
       hpNeTwo,
       hpLt⟩

    exact
      prime_mem_expectedPrimes_of_lt
        steps
        hpPrime
        hpNeTwo
        hpLt

/-!
### Strict increasing order
-/

/--
A small self-contained definition of strict increase for lists.
Every later element of the tail must be larger than the head, recursively.
-/
def StrictlyIncreasing : List ℕ → Prop
  | [] =>
      True
  | x :: xs =>
      (∀ y, y ∈ xs → x < y) ∧
      StrictlyIncreasing xs

/--
Our self-contained definition is equivalent to Lean's standard
`List.Pairwise (<)` formulation.  We use the standard formulation for
large concrete computations because Mathlib provides a decidable instance
for it.
-/
theorem strictlyIncreasing_iff_pairwise
    (xs : List ℕ) :
    StrictlyIncreasing xs ↔
      List.Pairwise (fun a b : ℕ => a < b) xs := by

  induction xs with

  | nil =>
      simp [StrictlyIncreasing]

  | cons a xs ih =>
      simp [StrictlyIncreasing, ih]

/--
Appending one number larger than every existing entry preserves strict
increase.
-/
theorem strictlyIncreasing_append_singleton
    {xs : List ℕ}
    {c : ℕ}
    (hInc :
      StrictlyIncreasing xs)
    (hLt :
      ∀ x, x ∈ xs → x < c) :
    StrictlyIncreasing
      (xs ++ [c]) := by

  induction xs with

  | nil =>
      simp [StrictlyIncreasing]

  | cons a xs ih =>
      simp only [
        StrictlyIncreasing
      ] at hInc ⊢

      rcases hInc with
        ⟨hHead, hTail⟩

      constructor

      · intro y hy

        simp at hy

        rcases hy with
          hyOld | hyEq

        · exact
            hHead
              y
              hyOld

        · subst y

          exact
            hLt
              a
              (by simp)

      · apply ih

        · exact hTail

        · intro x hx

          exact
            hLt
              x
              (by
                simp [hx])

/--
The mathematical specification is strictly increasing.
-/
theorem expectedPrimes_strictlyIncreasing
    (steps : ℕ) :
    StrictlyIncreasing
      (expectedPrimes steps) := by

  induction steps with

  | zero =>
      simp [
        expectedPrimes,
        StrictlyIncreasing
      ]

  | succ steps ih =>
      by_cases hPrime :
          Nat.Prime
            (5 + 2 * steps)

      · simp only [
          expectedPrimes,
          hPrime,
          ite_true
        ]

        apply
          strictlyIncreasing_append_singleton
            ih

        intro x hx

        exact
          mem_expectedPrimes_lt_nextCandidate
            hx

      · simp [
          expectedPrimes,
          hPrime
        ]

        exact ih

/--
Therefore the actual output list of the executable sieve is strictly
increasing after every number of iterations.
-/
theorem runSteps_primes_strictlyIncreasing
    (steps : ℕ) :
    StrictlyIncreasing
      (runSteps steps).primes := by

  rw [
    runSteps_primes_eq_expected
  ]

  exact
    expectedPrimes_strictlyIncreasing
      steps

/-!
### End-to-end finite correctness theorem

This theorem packages the principal result reached so far:

after any finite number of iterations, the output is strictly increasing,
and its members are exactly all primes greater than `2` below the next
candidate.
-/
theorem additiveSieve_finite_correctness
    (steps : ℕ) :
    StrictlyIncreasing
        (runSteps steps).primes
    ∧
    (∀ p,
      p ∈ (runSteps steps).primes
      ↔
      Nat.Prime p ∧
      p ≠ 2 ∧
      p < (runSteps steps).candidate) := by

  constructor

  · exact
      runSteps_primes_strictlyIncreasing
        steps

  · intro p

    exact
      mem_runSteps_primes_iff
        steps
        p


/-!
## 13. Formal verification of the paper's printed first 1000 primes

Table 1 of the paper prints 1000 primes beginning with `3` and ending
with `7927`.  The list below is a literal transcription of that table.

The previous sections already prove the algorithm correct for every finite
number of steps.  Here we additionally verify the concrete published data:

* the table contains exactly 1000 entries;
* after processing all odd candidates through `7927`, the formal algorithm
  produces exactly this table;
* the next candidate is `7929`;
* the concrete table is strictly increasing;
* every table entry is prime and different from `2`.

Since the candidate processed at step `s` is `5 + 2*s`, candidate `7927`
is processed at step `3961`; therefore the state after that processing is
`runSteps 3962`.
-/

/-- Literal transcription of Table 1 in the paper. -/
def paperFirst1000Primes : List ℕ :=
  [
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
    43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157,
    163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227,
    229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
    293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367,
    373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439,
    443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509,
    521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599,
    601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661,
    673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
    757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829,
    839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
    929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009,
    1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087,
    1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171,
    1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259,
    1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327,
    1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447,
    1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523,
    1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607,
    1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697,
    1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787,
    1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879,
    1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993,
    1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081,
    2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153,
    2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269,
    2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351,
    2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437,
    2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549,
    2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659,
    2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719,
    2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803,
    2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909,
    2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019,
    3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121,
    3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229,
    3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329,
    3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433,
    3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529,
    3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613,
    3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701,
    3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803,
    3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911,
    3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007,
    4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099,
    4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217,
    4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289,
    4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421,
    4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517,
    4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637,
    4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723,
    4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817,
    4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943,
    4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021,
    5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119,
    5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237,
    5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381,
    5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449,
    5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557,
    5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657,
    5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749,
    5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851,
    5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953,
    5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079,
    6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197,
    6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277,
    6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361,
    6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481,
    6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599,
    6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703,
    6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823,
    6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911,
    6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001,
    7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127,
    7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237,
    7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351,
    7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489,
    7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573,
    7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673,
    7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759,
    7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883,
    7901, 7907, 7919, 7927
  ]

/-- The published table contains exactly 1000 numbers. -/
theorem paperFirst1000Primes_length :
    paperFirst1000Primes.length = 1000 := by
  native_decide

/-- The first entry of the published table is `3`. -/
theorem paperFirst1000Primes_head :
    paperFirst1000Primes.head? = some 3 := by
  native_decide

/-- The last entry of the published table is `7927`. -/
theorem paperFirst1000Primes_last :
    paperFirst1000Primes.getLast? = some 7927 := by
  native_decide

/--
Independent verification of the printed table against the mathematical
prime-list specification developed above.
-/
theorem paperFirst1000Primes_matches_spec :
    expectedPrimes 3962 =
      paperFirst1000Primes := by
  native_decide

/--
After the algorithm has processed every odd candidate from `5` through
`7927`, its output is exactly the 1000-entry table printed in the paper.
-/
theorem runSteps_3962_primes_eq_paper :
    (runSteps 3962).primes =
      paperFirst1000Primes := by

  calc
    (runSteps 3962).primes
        = expectedPrimes 3962 :=
      runSteps_primes_eq_expected 3962

    _ = paperFirst1000Primes :=
      paperFirst1000Primes_matches_spec

/--
After those 3962 iterations, the next candidate is `7929`.
-/
theorem runSteps_3962_candidate :
    (runSteps 3962).candidate = 7929 := by

  rw [runSteps_candidate]

/--
The concrete published table is strictly increasing.
-/
theorem paperFirst1000Primes_pairwise :
    List.Pairwise
      (fun a b : ℕ => a < b)
      paperFirst1000Primes := by

  native_decide

/--
The concrete published table is strictly increasing.

For this 1000-element concrete check we deliberately use Mathlib's
decidable `List.Pairwise (<)` representation and then transport the result
back to the paper's `StrictlyIncreasing` predicate.  This avoids unfolding
a proof recursively through 3962 sieve iterations.
-/
theorem paperFirst1000Primes_strictlyIncreasing :
    StrictlyIncreasing
      paperFirst1000Primes := by

  exact
    (strictlyIncreasing_iff_pairwise
      paperFirst1000Primes).2
      paperFirst1000Primes_pairwise

/--
Every number printed in Table 1 is prime and different from `2`.
-/
theorem mem_paperFirst1000Primes_iff
    (p : ℕ) :
    p ∈ paperFirst1000Primes
    ↔
    Nat.Prime p ∧
    p ≠ 2 ∧
    p < 7929 := by

  rw [← runSteps_3962_primes_eq_paper]

  have h :=
    mem_runSteps_primes_iff
      3962
      p

  rw [runSteps_3962_candidate] at h

  exact h

/--
Concrete end-to-end validation of the result table in the paper.
-/
theorem paperFirst1000Primes_validation :
    paperFirst1000Primes.length = 1000
    ∧
    StrictlyIncreasing paperFirst1000Primes
    ∧
    (∀ p,
      p ∈ paperFirst1000Primes
      ↔
      Nat.Prime p ∧
      p ≠ 2 ∧
      p < 7929) := by

  exact
    ⟨paperFirst1000Primes_length,
     paperFirst1000Primes_strictlyIncreasing,
     mem_paperFirst1000Primes_iff⟩


/-!
## 14. Final end-to-end correctness theorems

The formalization establishes all components needed for a complete
correctness statement for Algorithm 3.1:

* the current dictionary key is empty exactly when the current odd
  candidate is prime;
* a prime candidate is appended and a non-prime candidate is skipped;
* after every finite number of iterations, the output list contains
  exactly the odd primes below the next candidate;
* the output list is strictly increasing;
* every odd prime therefore appears after finitely many iterations;
* the concrete 1000-entry table printed in the paper is exactly the
  output after processing through `7927`.

The theorems below package these results into publication-level statements.
-/

/--
Every number ever emitted by the algorithm is an odd prime.
-/
theorem generated_number_is_odd_prime
    {steps p : ℕ}
    (hmem :
      p ∈ (runSteps steps).primes) :
    Nat.Prime p ∧ Odd p := by

  have hSpec :
      Nat.Prime p ∧
      p ≠ 2 ∧
      p < (runSteps steps).candidate :=

    (mem_runSteps_primes_iff
      steps
      p).1
      hmem

  exact
    ⟨hSpec.1,
     hSpec.1.odd_of_ne_two
       hSpec.2.1⟩

/--
Every prime different from `2` is eventually generated by the algorithm.
-/
theorem every_odd_prime_eventually_generated
    {p : ℕ}
    (hpPrime :
      Nat.Prime p)
    (hpNeTwo :
      p ≠ 2) :
    ∃ steps,
      p ∈ (runSteps steps).primes := by

  refine
    ⟨p, ?_⟩

  apply
    (mem_runSteps_primes_iff
      p
      p).2

  refine
    ⟨hpPrime,
     hpNeTwo,
     ?_⟩

  rw [runSteps_candidate]

  omega

/--
The implementation never appends a composite candidate.
-/
theorem composite_is_never_appended
    (steps : ℕ)
    {c : ℕ}
    (hCandidate :
      c =
        (runSteps steps).candidate)
    (hNotPrime :
      ¬ Nat.Prime c) :
    (runSteps (steps + 1)).primes =
      (runSteps steps).primes := by

  subst c

  exact
    runSteps_nonprime_is_not_appended
      steps
      hNotPrime

/--
Every prime candidate is appended at the iteration in which it is processed.
-/
theorem prime_is_appended_when_processed
    (steps : ℕ)
    {c : ℕ}
    (hCandidate :
      c =
        (runSteps steps).candidate)
    (hPrime :
      Nat.Prime c) :
    (runSteps (steps + 1)).primes =
      (runSteps steps).primes ++ [c] := by

  subst c

  exact
    runSteps_prime_is_appended
      steps
      hPrime

/--
Complete finite correctness of Algorithm 3.1 at every iteration.

After `steps` iterations:

1. the next candidate is exactly `5 + 2*steps`;
2. the dictionary is empty at that candidate iff it is prime;
3. the emitted list is strictly increasing;
4. its members are exactly the primes different from `2` below the
   next candidate.
-/
theorem additiveSieve_algorithm_correct_at_every_step
    (steps : ℕ) :
    (runSteps steps).candidate =
        5 + 2 * steps
    ∧
    (factorsAt
        (runSteps steps).markers
        (runSteps steps).candidate = ∅
      ↔
      Nat.Prime
        (runSteps steps).candidate)
    ∧
    StrictlyIncreasing
      (runSteps steps).primes
    ∧
    (∀ p,
      p ∈ (runSteps steps).primes
      ↔
      Nat.Prime p ∧
      p ≠ 2 ∧
      p < (runSteps steps).candidate) := by

  exact
    ⟨runSteps_candidate steps,
     runSteps_unmarked_iff_prime steps,
     runSteps_primes_strictlyIncreasing steps,
     fun p =>
       mem_runSteps_primes_iff
         steps
         p⟩

/--
Global correctness statement for the generated sequence.

The algorithm emits only odd primes, every odd prime is eventually emitted,
and every finite output prefix is strictly increasing.
-/
theorem additiveSieve_generates_exactly_odd_primes :
    (∀ steps p,
      p ∈ (runSteps steps).primes →
      Nat.Prime p ∧ Odd p)
    ∧
    (∀ p,
      Nat.Prime p →
      p ≠ 2 →
      ∃ steps,
        p ∈ (runSteps steps).primes)
    ∧
    (∀ steps,
      StrictlyIncreasing
        (runSteps steps).primes) := by

  refine
    ⟨?_, ?_, ?_⟩

  · intro steps p hmem

    exact
      generated_number_is_odd_prime
        hmem

  · intro p hpPrime hpNeTwo

    exact
      every_odd_prime_eventually_generated
        hpPrime
        hpNeTwo

  · intro steps

    exact
      runSteps_primes_strictlyIncreasing
        steps

/--
The exact concrete validation corresponding to Table 1 of the paper.

The formal execution through candidate `7927` produces the published list;
that list contains 1000 entries, begins with `3`, ends with `7927`, is
strictly increasing, and contains exactly the primes different from `2`
below the next candidate `7929`.
-/
theorem paper_table_end_to_end_validation :
    (runSteps 3962).primes =
        paperFirst1000Primes
    ∧
    paperFirst1000Primes.length = 1000
    ∧
    paperFirst1000Primes.head? = some 3
    ∧
    paperFirst1000Primes.getLast? = some 7927
    ∧
    (runSteps 3962).candidate = 7929
    ∧
    StrictlyIncreasing
      paperFirst1000Primes
    ∧
    (∀ p,
      p ∈ paperFirst1000Primes
      ↔
      Nat.Prime p ∧
      p ≠ 2 ∧
      p < 7929) := by

  exact
    ⟨runSteps_3962_primes_eq_paper,
     paperFirst1000Primes_length,
     paperFirst1000Primes_head,
     paperFirst1000Primes_last,
     runSteps_3962_candidate,
     paperFirst1000Primes_strictlyIncreasing,
     mem_paperFirst1000Primes_iff⟩

/--
Final validation bundle for the first paper.

This combines the general mathematical correctness theorem with the
specific verification of the 1000 values printed in the publication.
-/
theorem paper1_final_validation :
    ((∀ steps p,
        p ∈ (runSteps steps).primes →
        Nat.Prime p ∧ Odd p)
      ∧
      (∀ p,
        Nat.Prime p →
        p ≠ 2 →
        ∃ steps,
          p ∈ (runSteps steps).primes)
      ∧
      (∀ steps,
        StrictlyIncreasing
          (runSteps steps).primes))
    ∧
    ((runSteps 3962).primes =
        paperFirst1000Primes
      ∧
      paperFirst1000Primes.length = 1000
      ∧
      paperFirst1000Primes.head? = some 3
      ∧
      paperFirst1000Primes.getLast? = some 7927
      ∧
      (runSteps 3962).candidate = 7929
      ∧
      StrictlyIncreasing
        paperFirst1000Primes
      ∧
      (∀ p,
        p ∈ paperFirst1000Primes
        ↔
        Nat.Prime p ∧
        p ≠ 2 ∧
        p < 7929)) := by

  exact
    ⟨additiveSieve_generates_exactly_odd_primes,
     paper_table_end_to_end_validation⟩

end AdditiveSieveAlgorithm
