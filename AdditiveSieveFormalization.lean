import Mathlib

open scoped BigOperators

/-!
# Formal Verification of an Additive Sieve on an Arithmetic Progression

**Author:** Tomás Sánchez Expósito  
**System:** Lean 4 + Mathlib

This file formalizes the additive sieve based on the arithmetic progression

`C n = 3 + 2*n`

and develops the following chain of results:

* odd-prime membership and the index formula for `C`;
* additive composite marking and the square boundary;
* adjacent positions and the `6m ± 1` form for nontrivial twin primes;
* forbidden congruence classes for individual sieve primes;
* finite sieve sets, independent shards, and batch products;
* equivalence between sieve survival and a single batch `gcd` test;
* modular compression of a very large reference base;
* compressed coordinates `κ`, their explicit forbidden residue classes,
  and periodicity modulo each odd prime;
* correctness of a complete finite sieve up to the square-root boundary;
* specialization to
  `B = 2996863034895 * 2^1290000`;
* a final equivalence between twin-prime status and the residue-only
  compressed batch computation, under the stated completeness hypothesis.

## Scope

The final equivalence is conditional on `CompleteOddPrimeBatchUpTo`: the
finite batch must contain every relevant odd prime up to the square-root
boundary. The development therefore verifies the mathematical correctness
of the sieve and its modular compression. It does not, by itself, certify
a particular numerical candidate unless the completeness hypothesis is
instantiated for that candidate.

This source was checked in Lean Web with Lean `v4.35.0-rc1` and Mathlib,
with `All Messages (0)` on 2026-09-17.
-/

namespace AdditiveSieve

/-!
## Arithmetic progression and additive sieve
-/

def C (n : ℕ) : ℕ := 3 + 2 * n

theorem C_odd (n : ℕ) : Odd (C n) := by
  refine ⟨n + 1, ?_⟩
  simp [C]
  omega

theorem odd_prime_mem_C {p : ℕ}
    (hp : Nat.Prime p)
    (hp2 : p ≠ 2) :
    ∃ n : ℕ, C n = p := by

  have hodd : Odd p := hp.odd_of_ne_two hp2
  rcases hodd with ⟨k, hk⟩

  have hp3 : 3 ≤ p := by
    have hp2le : 2 ≤ p := hp.two_le
    omega

  have hk1 : 1 ≤ k := by
    omega

  refine ⟨k - 1, ?_⟩
  simp [C]
  omega

theorem index_formula {p s : ℕ}
    (hps : C s = p) :
    s = (p - 3) / 2 := by

  simp [C] at hps
  omega

theorem composite_index_identity {p s k : ℕ}
    (hps : C s = p) :
    C (s + k * p) = (2 * k + 1) * p := by

  rw [← hps]
  simp [C]
  ring

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

theorem square_at_index
    {p s : ℕ}
    (hps : C s = p) :
    C (s + (s + 1) * p) = p * p := by

  rw [composite_index_identity (k := s + 1) hps]

  have h : 2 * (s + 1) + 1 = p := by
    simp [C] at hps
    omega

  rw [h]

/-!
## Twin-prime geometry in the progression
-/

theorem C_succ (n : ℕ) :
    C (n + 1) = C n + 2 := by

  simp [C]
  omega

theorem adjacent_gap_two (n : ℕ) :
    C (n + 1) - C n = 2 := by

  rw [C_succ]
  omega

theorem adjacent_primes_are_twin
    {n : ℕ}
    (h1 : Nat.Prime (C n))
    (h2 : Nat.Prime (C (n + 1))) :
    Nat.Prime (C n) ∧
    Nat.Prime (C n + 2) := by

  constructor

  · exact h1

  · rw [← C_succ n]
    exact h2

theorem six_m_pair
    (m : ℕ)
    (hm : 1 ≤ m) :
    C (3 * m - 2) = 6 * m - 1 ∧
    C (3 * m - 2 + 1) = 6 * m + 1 := by

  constructor

  · simp [C]
    omega

  · simp [C]
    omega

theorem twin_primes_nontrivial_six_m_form
    {p : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime (p + 2))
    (hp3 : p ≠ 3) :
    ∃ m : ℕ,
      1 ≤ m ∧
      p = 6 * m - 1 ∧
      p + 2 = 6 * m + 1 := by

  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hq

  have hodd : Odd p := hp.odd_of_ne_two hp2

  rcases hodd with ⟨k, hk⟩

  have hmod0 : p % 3 ≠ 0 := by
    intro h0

    have hdvd : 3 ∣ p := by
      exact Nat.dvd_of_mod_eq_zero h0

    have heq : 3 = p := by
      exact (Nat.dvd_prime_two_le hp (by norm_num)).mp hdvd

    apply hp3
    omega

  have hmod1 : p % 3 ≠ 1 := by
    intro h1

    have hqmod : (p + 2) % 3 = 0 := by
      omega

    have hdvd : 3 ∣ (p + 2) := by
      exact Nat.dvd_of_mod_eq_zero hqmod

    have heq : 3 = p + 2 := by
      exact (Nat.dvd_prime_two_le hq (by norm_num)).mp hdvd

    have hpge2 : 2 ≤ p := hp.two_le
    omega

  have hmodlt : p % 3 < 3 := by
    exact Nat.mod_lt p (by norm_num)

  have hmod2 : p % 3 = 2 := by
    omega

  have hkmod2 : k % 3 = 2 := by
    omega

  have hkdiv :
      3 * (k / 3) + k % 3 = k := by
    exact Nat.div_add_mod k 3

  have hkform :
      3 * (k / 3) + 2 = k := by
    omega

  refine ⟨k / 3 + 1, ?_, ?_, ?_⟩

  · omega
  · omega
  · omega

theorem twin_primes_positions_in_C
    {p : ℕ}
    (hp : Nat.Prime p)
    (hq : Nat.Prime (p + 2))
    (hp3 : p ≠ 3) :
    ∃ m : ℕ,
      1 ≤ m ∧
      C (3 * m - 2) = p ∧
      C (3 * m - 1) = p + 2 := by

  obtain ⟨m, hm, hpform, hqform⟩ :=
    twin_primes_nontrivial_six_m_form hp hq hp3

  refine ⟨m, hm, ?_, ?_⟩

  · have hpair := six_m_pair m hm

    calc
      C (3 * m - 2) = 6 * m - 1 := hpair.1
      _ = p := hpform.symm

  · have hpair := six_m_pair m hm

    have hindex :
        3 * m - 1 = 3 * m - 2 + 1 := by
      omega

    rw [hindex]

    calc
      C (3 * m - 2 + 1) = 6 * m + 1 := hpair.2
      _ = p + 2 := hqform.symm

/-!
## Forbidden congruence classes in the original index
-/

theorem left_forbidden_value
    {q s k : ℕ}
    (hqs : C s = q) :
    C (s + k * q) = (2 * k + 1) * q := by

  exact composite_index_identity hqs

theorem left_member_divisible_by_q
    {q s k : ℕ}
    (hqs : C s = q) :
    q ∣ C (s + k * q) := by

  rw [left_forbidden_value hqs]

  refine ⟨2 * k + 1, ?_⟩

  simp [Nat.mul_comm]

theorem left_member_forbidden
    {q s k : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k)
    (hqs : C s = q) :
    ¬ Nat.Prime (C (s + k * q)) := by

  exact composite_at_marked_index hq hk hqs

theorem right_forbidden_value
    {q s k : ℕ}
    (hqs : C s = q)
    (hk : 1 ≤ k) :
    C ((s + k * q - 1) + 1) =
      (2 * k + 1) * q := by

  have hq3 : 3 ≤ q := by
    have h := hqs
    simp [C] at h
    omega

  have hkpos : 0 < k := by
    omega

  have hqpos : 0 < q := by
    omega

  have hkqpos : 0 < k * q := by
    exact Nat.mul_pos hkpos hqpos

  have hpos : 1 ≤ s + k * q := by
    omega

  have hindex :
      (s + k * q - 1) + 1 =
        s + k * q := by
    omega

  rw [hindex]

  exact composite_index_identity hqs

theorem right_member_divisible_by_q
    {q s k : ℕ}
    (hqs : C s = q)
    (hk : 1 ≤ k) :
    q ∣ C ((s + k * q - 1) + 1) := by

  rw [right_forbidden_value hqs hk]

  refine ⟨2 * k + 1, ?_⟩

  simp [Nat.mul_comm]

theorem right_member_forbidden
    {q s k : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hk : 1 ≤ k) :
    ¬ Nat.Prime
      (C ((s + k * q - 1) + 1)) := by

  rw [right_forbidden_value hqs hk]

  apply Nat.not_prime_mul

  · omega

  · have hq2 : 2 ≤ q := hq.two_le
    omega

theorem left_forbidden_period
    (s q k : ℕ) :
    s + (k + 1) * q =
      (s + k * q) + q := by

  ring

theorem left_forbidden_modEq
    (s q k : ℕ) :
    Nat.ModEq q (s + k * q) s := by

  have h :
      s + k * q = q * k + s := by
    ring

  rw [h]

  exact Nat.ModEq.modulus_mul_add

theorem right_forbidden_modEq
    {q s k : ℕ}
    (hqs : C s = q)
    (hk : 1 ≤ k) :
    Nat.ModEq q
      ((s + k * q - 1) + 1)
      s := by

  have hq3 : 3 ≤ q := by
    have h := hqs
    simp [C] at h
    omega

  have hkpos : 0 < k := by
    omega

  have hqpos : 0 < q := by
    omega

  have hkqpos : 0 < k * q := by
    exact Nat.mul_pos hkpos hqpos

  have hpos : 1 ≤ s + k * q := by
    omega

  have hindex :
      (s + k * q - 1) + 1 =
        s + k * q := by
    omega

  rw [hindex]

  exact left_forbidden_modEq s q k

theorem right_pair_position_modEq
    {q s k : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k) :
    Nat.ModEq q
      (s + k * q - 1)
      (s + q - 1) := by

  have hleft :
      Nat.ModEq q (s + k * q) s := by
    exact left_forbidden_modEq s q k

  have hshift :
      Nat.ModEq q s (s + q) := by

    have h :
        Nat.ModEq q (s + q) s := by
      exact Nat.add_modEq_right

    exact h.symm

  have hbase :
      Nat.ModEq q
        (s + k * q)
        (s + q) := by
    exact hleft.trans hshift

  have hkpos : 0 < k := by
    omega

  have hq2 : 2 ≤ q := hq.two_le

  have hqpos : 0 < q := by
    omega

  have hmulpos : 0 < k * q := by
    exact Nat.mul_pos hkpos hqpos

  have hleftpos :
      1 ≤ s + k * q := by
    omega

  have hrightpos :
      1 ≤ s + q := by
    omega

  have hone :
      Nat.ModEq q 1 1 := by
    exact Nat.ModEq.refl 1

  exact
    Nat.ModEq.sub
      hleftpos
      hrightpos
      hbase
      hone

theorem right_pair_position_modEq_nontrivial
    {q s k : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hq3 : q ≠ 3)
    (hk : 1 ≤ k) :
    Nat.ModEq q
      (s + k * q - 1)
      (s - 1) := by

  have hs1 : 1 ≤ s := by
    by_contra hnot

    have hs0 : s = 0 := by
      omega

    have hqeq : q = 3 := by
      rw [← hqs]
      rw [hs0]
      simp [C]

    exact hq3 hqeq

  have hleft :
      Nat.ModEq q
        (s + k * q)
        s := by
    exact left_forbidden_modEq s q k

  have hkpos : 0 < k := by
    omega

  have hq2 : 2 ≤ q := hq.two_le

  have hqpos : 0 < q := by
    omega

  have hmulpos :
      0 < k * q := by
    exact Nat.mul_pos hkpos hqpos

  have hpos :
      1 ≤ s + k * q := by
    omega

  have hone :
      Nat.ModEq q 1 1 := by
    exact Nat.ModEq.refl 1

  exact
    Nat.ModEq.sub
      hpos
      hs1
      hleft
      hone

theorem right_pair_q3_modEq
    (k : ℕ)
    (hk : 1 ≤ k) :
    Nat.ModEq 3
      (k * 3 - 1)
      2 := by

  have h :=
    right_pair_position_modEq
      (q := 3)
      (s := 0)
      (k := k)
      (by norm_num)
      hk

  simpa using h

def LeftForbiddenClass
    (q s n : ℕ) : Prop :=
  Nat.ModEq q n s

def RightForbiddenClass
    (q s n : ℕ) : Prop :=
  Nat.ModEq q n (s + q - 1)

theorem generated_pair_hits_forbidden_classes
    {q s k : ℕ}
    (hq : Nat.Prime q)
    (hk : 1 ≤ k) :
    LeftForbiddenClass q s
        (s + k * q) ∧
    RightForbiddenClass q s
        (s + k * q - 1) := by

  constructor

  · exact left_forbidden_modEq s q k

  · exact right_pair_position_modEq hq hk

theorem C_preserves_modEq
    {q a b : ℕ}
    (h : Nat.ModEq q a b) :
    Nat.ModEq q (C a) (C b) := by

  unfold C

  exact (h.mul_left 2).add_left 3

theorem left_class_implies_divisible
    {q s n : ℕ}
    (hqs : C s = q)
    (hn : LeftForbiddenClass q s n) :
    q ∣ C n := by

  unfold LeftForbiddenClass at hn

  have hC :
      Nat.ModEq q (C n) (C s) := by
    exact C_preserves_modEq hn

  have hdivCs : q ∣ C s := by
    rw [hqs]

  exact
    (hC.dvd_iff (Nat.dvd_refl q)).2
      hdivCs

theorem right_class_succ_modEq
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hn : RightForbiddenClass q s n) :
    Nat.ModEq q (n + 1) s := by

  unfold RightForbiddenClass at hn

  have h1 :
      Nat.ModEq q
        (n + 1)
        ((s + q - 1) + 1) := by
    exact hn.add_right 1

  have hq2 : 2 ≤ q := hq.two_le

  have hq1 : 1 ≤ q := by
    omega

  have hsq :
      (s + q - 1) + 1 =
        s + q := by
    omega

  rw [hsq] at h1

  have h2 :
      Nat.ModEq q
        (s + q)
        s := by
    exact Nat.add_modEq_right

  exact h1.trans h2

theorem right_class_implies_divisible
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hn : RightForbiddenClass q s n) :
    q ∣ C (n + 1) := by

  have hmod :
      Nat.ModEq q (n + 1) s := by
    exact right_class_succ_modEq hq hn

  have hleft :
      LeftForbiddenClass q s (n + 1) := by
    exact hmod

  exact left_class_implies_divisible hqs hleft

theorem forbidden_class_implies_one_member_divisible
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hforbidden :
      LeftForbiddenClass q s n ∨
      RightForbiddenClass q s n) :
    q ∣ C n ∨
    q ∣ C (n + 1) := by

  rcases hforbidden with hleft | hright

  · left
    exact left_class_implies_divisible hqs hleft

  · right
    exact right_class_implies_divisible
      hq hqs hright

theorem C_strict_mono
    {a b : ℕ}
    (h : a < b) :
    C a < C b := by

  simp [C]
  omega

theorem divisible_and_lt_implies_not_prime
    {q N : ℕ}
    (hq : Nat.Prime q)
    (hdiv : q ∣ N)
    (hlt : q < N) :
    ¬ Nat.Prime N := by

  intro hN

  have heq : q = N := by
    exact
      (Nat.dvd_prime_two_le
        hN
        hq.two_le).mp hdiv

  omega

theorem left_class_beyond_base_not_prime
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hn : LeftForbiddenClass q s n)
    (hsn : s < n) :
    ¬ Nat.Prime (C n) := by

  have hdiv : q ∣ C n := by
    exact left_class_implies_divisible hqs hn

  have hlt : q < C n := by
    rw [← hqs]
    exact C_strict_mono hsn

  exact divisible_and_lt_implies_not_prime
    hq hdiv hlt

theorem right_class_beyond_base_not_prime
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hn : RightForbiddenClass q s n)
    (hsn : s < n + 1) :
    ¬ Nat.Prime (C (n + 1)) := by

  have hdiv : q ∣ C (n + 1) := by
    exact right_class_implies_divisible hq hqs hn

  have hlt : q < C (n + 1) := by
    rw [← hqs]
    exact C_strict_mono hsn

  exact divisible_and_lt_implies_not_prime
    hq hdiv hlt

theorem left_divisible_implies_class
    {q s n : ℕ}
    (_hq : Nat.Prime q)
    (hqs : C s = q)
    (hdiv : q ∣ C n) :
    LeftForbiddenClass q s n := by

  have hdivs : q ∣ C s := by
    rw [hqs]

  have hn0 :
      Nat.ModEq q (C n) 0 := by
    exact (Nat.modEq_zero_iff_dvd).2 hdiv

  have hs0 :
      Nat.ModEq q (C s) 0 := by
    exact (Nat.modEq_zero_iff_dvd).2 hdivs

  have hC :
      Nat.ModEq q (C n) (C s) := by
    exact hn0.trans hs0.symm

  have htwo :
      Nat.ModEq q (2 * n) (2 * s) := by

    apply Nat.ModEq.add_left_cancel' 3

    simpa [C] using hC

  have hoddq : Odd q := by
    rw [← hqs]
    exact C_odd s

  have hcop :
      q.gcd 2 = 1 := by
    exact Nat.coprime_two_right.mpr hoddq

  unfold LeftForbiddenClass

  exact
    Nat.ModEq.cancel_left_of_coprime
      hcop
      htwo

theorem right_divisible_implies_class
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q)
    (hdiv : q ∣ C (n + 1)) :
    RightForbiddenClass q s n := by

  have hnext :
      LeftForbiddenClass q s (n + 1) := by
    exact
      left_divisible_implies_class
        hq hqs hdiv

  unfold LeftForbiddenClass at hnext
  unfold RightForbiddenClass

  have hshift :
      Nat.ModEq q
        s
        (s + q) := by

    have h :
        Nat.ModEq q
          (s + q)
          s := by
      exact Nat.add_modEq_right

    exact h.symm

  have hbase :
      Nat.ModEq q
        (n + 1)
        (s + q) := by

    exact hnext.trans hshift

  have hn1 :
      1 ≤ n + 1 := by
    omega

  have hq2 :
      2 ≤ q := hq.two_le

  have hsq1 :
      1 ≤ s + q := by
    omega

  have hone :
      Nat.ModEq q 1 1 := by
    exact Nat.ModEq.refl 1

  have hsub :
      Nat.ModEq q
        ((n + 1) - 1)
        ((s + q) - 1) := by

    exact
      Nat.ModEq.sub
        hn1
        hsq1
        hbase
        hone

  simpa using hsub

/-!
## Single-prime survival and divisibility
-/

def SurvivesPrime
    (q s n : ℕ) : Prop :=
  ¬ LeftForbiddenClass q s n ∧
  ¬ RightForbiddenClass q s n

theorem survives_prime_iff_no_divisibility
    {q s n : ℕ}
    (hq : Nat.Prime q)
    (hqs : C s = q) :
    SurvivesPrime q s n ↔
      (¬ q ∣ C n) ∧
      (¬ q ∣ C (n + 1)) := by

  constructor

  · intro hsurv

    constructor

    · intro hdiv

      have hclass :
          LeftForbiddenClass q s n := by

        exact
          left_divisible_implies_class
            hq hqs hdiv

      exact hsurv.1 hclass

    · intro hdiv

      have hclass :
          RightForbiddenClass q s n := by

        exact
          right_divisible_implies_class
            hq hqs hdiv

      exact hsurv.2 hclass

  · intro hnodiv

    constructor

    · intro hclass

      have hdiv :
          q ∣ C n := by

        exact
          left_class_implies_divisible
            hqs hclass

      exact hnodiv.1 hdiv

    · intro hclass

      have hdiv :
          q ∣ C (n + 1) := by

        exact
          right_class_implies_divisible
            hq hqs hclass

      exact hnodiv.2 hdiv

/-!
## Finite sieve sets and shard composition
-/

def primeIndex (q : ℕ) : ℕ :=
  (q - 3) / 2

theorem C_primeIndex
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2) :
    C (primeIndex q) = q := by

  obtain ⟨s, hs⟩ :=
    odd_prime_mem_C hq hq2

  have hi :
      s = primeIndex q := by

    unfold primeIndex

    exact index_formula hs

  rw [← hi]

  exact hs

def ValidSieveSet
    (Q : Finset ℕ) : Prop :=
  ∀ q ∈ Q,
    Nat.Prime q ∧ q ≠ 2

def SurvivesSet
    (Q : Finset ℕ)
    (n : ℕ) : Prop :=
  ∀ q ∈ Q,
    SurvivesPrime
      q
      (primeIndex q)
      n

theorem survives_set_iff_no_divisors
    (Q : Finset ℕ)
    (hQ : ValidSieveSet Q)
    (n : ℕ) :
    SurvivesSet Q n ↔
      ∀ q ∈ Q,
        (¬ q ∣ C n) ∧
        (¬ q ∣ C (n + 1)) := by

  unfold ValidSieveSet at hQ

  constructor

  · intro hsurv

    unfold SurvivesSet at hsurv

    intro q hqmem

    have hprops :
        Nat.Prime q ∧ q ≠ 2 :=
      hQ q hqmem

    have hqs :
        C (primeIndex q) = q := by

      exact
        C_primeIndex
          hprops.1
          hprops.2

    exact
      (survives_prime_iff_no_divisibility
        hprops.1
        hqs).mp
        (hsurv q hqmem)

  · intro hnodiv

    unfold SurvivesSet

    intro q hqmem

    have hprops :
        Nat.Prime q ∧ q ≠ 2 :=
      hQ q hqmem

    have hqs :
        C (primeIndex q) = q := by

      exact
        C_primeIndex
          hprops.1
          hprops.2

    exact
      (survives_prime_iff_no_divisibility
        hprops.1
        hqs).mpr
        (hnodiv q hqmem)

theorem survives_empty
    (n : ℕ) :
    SurvivesSet ∅ n := by

  simp [SurvivesSet]

theorem survives_insert_iff
    (q : ℕ)
    (Q : Finset ℕ)
    (n : ℕ) :
    SurvivesSet (insert q Q) n ↔
      SurvivesPrime
        q
        (primeIndex q)
        n ∧
      SurvivesSet Q n := by

  simp [SurvivesSet]

theorem survives_union_iff
    (A B : Finset ℕ)
    (n : ℕ) :
    SurvivesSet (A ∪ B) n ↔
      SurvivesSet A n ∧
      SurvivesSet B n := by

  unfold SurvivesSet

  constructor

  · intro hAB

    constructor

    · intro q hqA

      apply hAB q

      exact Finset.mem_union_left B hqA

    · intro q hqB

      apply hAB q

      exact Finset.mem_union_right A hqB

  · intro h q hqAB

    have hmem :
        q ∈ A ∨ q ∈ B := by
      exact Finset.mem_union.mp hqAB

    rcases hmem with hqA | hqB

    · exact h.1 q hqA

    · exact h.2 q hqB

theorem survives_three_shards_iff
    (A B D : Finset ℕ)
    (n : ℕ) :
    SurvivesSet (A ∪ B ∪ D) n ↔
      SurvivesSet A n ∧
      SurvivesSet B n ∧
      SurvivesSet D n := by

  constructor

  · intro hABD

    have h_outer :
        SurvivesSet (A ∪ B) n ∧
        SurvivesSet D n := by

      exact
        (survives_union_iff
          (A ∪ B)
          D
          n).mp hABD

    have h_inner :
        SurvivesSet A n ∧
        SurvivesSet B n := by

      exact
        (survives_union_iff
          A
          B
          n).mp h_outer.1

    exact
      ⟨h_inner.1,
       h_inner.2,
       h_outer.2⟩

  · intro h

    have hAB :
        SurvivesSet (A ∪ B) n := by

      exact
        (survives_union_iff
          A
          B
          n).mpr
          ⟨h.1, h.2.1⟩

    exact
      (survives_union_iff
        (A ∪ B)
        D
        n).mpr
        ⟨hAB, h.2.2⟩

/-!
## Batch products and GCD criteria
-/

/--
Product of all numbers in one finite sieve batch.
For a ValidSieveSet, these numbers are odd primes.
-/
def batchProduct
    (Q : Finset ℕ) : ℕ :=
  Finset.prod Q (fun q => q)

/--
Every member of the batch divides the batch product.
-/
theorem member_dvd_batchProduct
    {Q : Finset ℕ}
    {q : ℕ}
    (hqmem : q ∈ Q) :
    q ∣ batchProduct Q := by

  unfold batchProduct

  exact
    Finset.dvd_prod_of_mem
      (fun x : ℕ => x)
      hqmem

/--
If q divides N and q belongs to the batch, then q also divides
gcd(N, batchProduct Q).
-/
theorem member_common_divisor_dvd_gcd
    {Q : Finset ℕ}
    {q N : ℕ}
    (hqmem : q ∈ Q)
    (hdiv : q ∣ N) :
    q ∣ Nat.gcd N (batchProduct Q) := by

  exact
    Nat.dvd_gcd
      hdiv
      (member_dvd_batchProduct hqmem)

/--
If gcd(N, batchProduct Q)=1, no prime of the batch can divide N.
-/
theorem gcd_batch_eq_one_implies_no_member_divides
    (Q : Finset ℕ)
    (N : ℕ)
    (hQ : ValidSieveSet Q)
    (hgcd :
      Nat.gcd N (batchProduct Q) = 1) :
    ∀ q ∈ Q, ¬ q ∣ N := by

  intro q hqmem hdiv

  have hprime :
      Nat.Prime q :=
    (hQ q hqmem).1

  have hqdvdg :
      q ∣ Nat.gcd N (batchProduct Q) := by

    exact
      member_common_divisor_dvd_gcd
        hqmem
        hdiv

  rw [hgcd] at hqdvdg

  have hq1 : q = 1 := by
    simpa using hqdvdg

  have hq2 : 2 ≤ q := hprime.two_le

  omega

/--
If no prime in Q divides N, then N is coprime to the product
of all primes in Q, hence the gcd is 1.
-/
theorem no_member_divides_implies_gcd_batch_eq_one
    (Q : Finset ℕ)
    (N : ℕ)
    (hQ : ValidSieveSet Q)
    (hnodiv :
      ∀ q ∈ Q, ¬ q ∣ N) :
    Nat.gcd N (batchProduct Q) = 1 := by

  have hcop :
      N.Coprime (batchProduct Q) := by

    unfold batchProduct

    apply Nat.Coprime.prod_right

    intro q hqmem

    have hprime :
        Nat.Prime q :=
      (hQ q hqmem).1

    have hqcopN :
        q.Coprime N := by

      exact
        (hprime.coprime_iff_not_dvd).2
          (hnodiv q hqmem)

    exact hqcopN.symm

  exact hcop.gcd_eq_one

/--
Exact batch-GCD criterion:
gcd(N, product(Q)) = 1 iff none of the primes in Q divides N.
-/
theorem gcd_batch_eq_one_iff_no_member_divides
    (Q : Finset ℕ)
    (N : ℕ)
    (hQ : ValidSieveSet Q) :
    Nat.gcd N (batchProduct Q) = 1 ↔
      ∀ q ∈ Q, ¬ q ∣ N := by

  constructor

  · intro hgcd

    exact
      gcd_batch_eq_one_implies_no_member_divides
        Q N hQ hgcd

  · intro hnodiv

    exact
      no_member_divides_implies_gcd_batch_eq_one
        Q N hQ hnodiv

/--
A candidate pair survives the whole batch iff both members have
gcd 1 with the batch product.
-/
theorem survives_set_iff_two_batch_gcds_one
    (Q : Finset ℕ)
    (hQ : ValidSieveSet Q)
    (n : ℕ) :
    SurvivesSet Q n ↔
      Nat.gcd (C n) (batchProduct Q) = 1 ∧
      Nat.gcd (C (n + 1)) (batchProduct Q) = 1 := by

  constructor

  · intro hsurv

    have hnodiv :
        ∀ q ∈ Q,
          (¬ q ∣ C n) ∧
          (¬ q ∣ C (n + 1)) := by

      exact
        (survives_set_iff_no_divisors
          Q hQ n).mp hsurv

    constructor

    · apply
        no_member_divides_implies_gcd_batch_eq_one
          Q
          (C n)
          hQ

      intro q hqmem

      exact (hnodiv q hqmem).1

    · apply
        no_member_divides_implies_gcd_batch_eq_one
          Q
          (C (n + 1))
          hQ

      intro q hqmem

      exact (hnodiv q hqmem).2

  · intro hgcd

    apply
      (survives_set_iff_no_divisors
        Q hQ n).mpr

    intro q hqmem

    constructor

    · exact
        gcd_batch_eq_one_implies_no_member_divides
          Q
          (C n)
          hQ
          hgcd.1
          q
          hqmem

    · exact
        gcd_batch_eq_one_implies_no_member_divides
          Q
          (C (n + 1))
          hQ
          hgcd.2
          q
          hqmem

/--
Product of the two members of the candidate pair.
-/
def pairProduct
    (n : ℕ) : ℕ :=
  C n * C (n + 1)

/--
Compressed batch criterion:
one gcd against C(n)*C(n+1) is enough to test both members
against every prime in the batch.
-/
theorem survives_set_iff_batch_gcd_one
    (Q : Finset ℕ)
    (hQ : ValidSieveSet Q)
    (n : ℕ) :
    SurvivesSet Q n ↔
      Nat.gcd
        (pairProduct n)
        (batchProduct Q) = 1 := by

  constructor

  · intro hsurv

    have hnodiv :
        ∀ q ∈ Q,
          (¬ q ∣ C n) ∧
          (¬ q ∣ C (n + 1)) := by

      exact
        (survives_set_iff_no_divisors
          Q hQ n).mp hsurv

    apply
      no_member_divides_implies_gcd_batch_eq_one
        Q
        (pairProduct n)
        hQ

    intro q hqmem

    have hprime :
        Nat.Prime q :=
      (hQ q hqmem).1

    have hpair :
        (¬ q ∣ C n) ∧
        (¬ q ∣ C (n + 1)) :=
      hnodiv q hqmem

    intro hdivPair

    have hcases :
        q ∣ C n ∨ q ∣ C (n + 1) := by

      unfold pairProduct at hdivPair

      exact
        (hprime.dvd_mul).mp
          hdivPair

    rcases hcases with hleft | hright

    · exact hpair.1 hleft

    · exact hpair.2 hright

  · intro hgcd

    have hnoPair :
        ∀ q ∈ Q,
          ¬ q ∣ pairProduct n := by

      exact
        gcd_batch_eq_one_implies_no_member_divides
          Q
          (pairProduct n)
          hQ
          hgcd

    apply
      (survives_set_iff_no_divisors
        Q hQ n).mpr

    intro q hqmem

    have hprime :
        Nat.Prime q :=
      (hQ q hqmem).1

    have hnpair :
        ¬ q ∣ pairProduct n :=
      hnoPair q hqmem

    constructor

    · intro hdiv

      apply hnpair

      unfold pairProduct

      exact
        (hprime.dvd_mul).2
          (Or.inl hdiv)

    · intro hdiv

      apply hnpair

      unfold pairProduct

      exact
        (hprime.dvd_mul).2
          (Or.inr hdiv)


/-!
## Modular compression of the base
-/

/--
Residue of the giant base B modulo the product of one sieve batch.
-/
def batchResidue
    (B : ℕ)
    (Q : Finset ℕ) : ℕ :=
  B % batchProduct Q

/--
B and its compressed residue represent the same residue class
modulo the batch product.
-/
theorem base_modEq_batchResidue
    (B : ℕ)
    (Q : Finset ℕ) :
    Nat.ModEq
      (batchProduct Q)
      B
      (batchResidue B Q) := by

  unfold batchResidue

  exact
    (Nat.mod_modEq B (batchProduct Q)).symm

/--
Left member of the twin-candidate family B + 6m - 1.
-/
def shiftedMinus
    (B m : ℕ) : ℕ :=
  B + 6 * m - 1

/--
Right member of the twin-candidate family B + 6m + 1.
-/
def shiftedPlus
    (B m : ℕ) : ℕ :=
  B + 6 * m + 1

/--
Replacing B by B mod batchProduct(Q) preserves the right candidate
modulo the batch product.
-/
theorem shiftedPlus_modEq_residue
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ) :
    Nat.ModEq
      (batchProduct Q)
      (shiftedPlus B m)
      (shiftedPlus (batchResidue B Q) m) := by

  have hB :
      Nat.ModEq
        (batchProduct Q)
        B
        (batchResidue B Q) := by

    exact base_modEq_batchResidue B Q

  unfold shiftedPlus

  exact hB.add_right (6 * m + 1)

/--
For m ≥ 1, replacing B by its batch residue also preserves
the left candidate B + 6m - 1 modulo the batch product.
-/
theorem shiftedMinus_modEq_residue
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.ModEq
      (batchProduct Q)
      (shiftedMinus B m)
      (shiftedMinus (batchResidue B Q) m) := by

  have hB :
      Nat.ModEq
        (batchProduct Q)
        B
        (batchResidue B Q) := by

    exact base_modEq_batchResidue B Q

  have hsum :
      Nat.ModEq
        (batchProduct Q)
        (B + 6 * m)
        (batchResidue B Q + 6 * m) := by

    exact hB.add_right (6 * m)

  have hleft :
      1 ≤ B + 6 * m := by
    omega

  have hright :
      1 ≤ batchResidue B Q + 6 * m := by
    omega

  have hone :
      Nat.ModEq
        (batchProduct Q)
        1
        1 := by

    exact Nat.ModEq.refl 1

  unfold shiftedMinus

  exact
    Nat.ModEq.sub
      hleft
      hright
      hsum
      hone

/--
The product of the two original candidates is congruent modulo the
batch product to the product formed using only the compressed residue.
-/
theorem shiftedPairProduct_modEq_residue
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.ModEq
      (batchProduct Q)
      (shiftedMinus B m * shiftedPlus B m)
      (shiftedMinus (batchResidue B Q) m *
       shiftedPlus (batchResidue B Q) m) := by

  have hminus :
      Nat.ModEq
        (batchProduct Q)
        (shiftedMinus B m)
        (shiftedMinus (batchResidue B Q) m) := by

    exact
      shiftedMinus_modEq_residue
        B Q m hm

  have hplus :
      Nat.ModEq
        (batchProduct Q)
        (shiftedPlus B m)
        (shiftedPlus (batchResidue B Q) m) := by

    exact
      shiftedPlus_modEq_residue
        B Q m

  exact hminus.mul hplus

/--
The GCD used by the compressed sieve is unchanged when the huge B
is replaced by its residue modulo the batch product.
-/
theorem shiftedPair_gcd_eq_residue_gcd
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.gcd
      (shiftedMinus B m * shiftedPlus B m)
      (batchProduct Q)
    =
    Nat.gcd
      (shiftedMinus (batchResidue B Q) m *
       shiftedPlus (batchResidue B Q) m)
      (batchProduct Q) := by

  exact
    (shiftedPairProduct_modEq_residue
      B Q m hm).gcd_eq

/--
Therefore the original pair passes the batch GCD test exactly when
the residue-compressed pair passes it.
-/
theorem shiftedPair_gcd_one_iff_residue_gcd_one
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.gcd
      (shiftedMinus B m * shiftedPlus B m)
      (batchProduct Q) = 1
    ↔
    Nat.gcd
      (shiftedMinus (batchResidue B Q) m *
       shiftedPlus (batchResidue B Q) m)
      (batchProduct Q) = 1 := by

  rw [
    shiftedPair_gcd_eq_residue_gcd
      B Q m hm
  ]

/--
Equivalent statement in the explicit formulas used in the search:
(B + 6m - 1)(B + 6m + 1) may be replaced by
(R + 6m - 1)(R + 6m + 1), where R = B mod batchProduct(Q).
-/
theorem explicit_compressed_batch_test
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.gcd
      ((B + 6 * m - 1) *
       (B + 6 * m + 1))
      (batchProduct Q) = 1
    ↔
    Nat.gcd
      (((B % batchProduct Q) + 6 * m - 1) *
       ((B % batchProduct Q) + 6 * m + 1))
      (batchProduct Q) = 1 := by

  simpa [
    shiftedMinus,
    shiftedPlus,
    batchResidue
  ] using
    shiftedPair_gcd_one_iff_residue_gcd_one
      B Q m hm


/-!
## Structured base and reference constants
-/

/--
Structured giant base used in the search:
B = A * 2^E.
-/
def structuredBase
    (A E : ℕ) : ℕ :=
  A * 2 ^ E

/--
Compressed residue of B = A * 2^E modulo the product of one batch.

This is exactly:
((A mod Q) * (2^E mod Q)) mod Q,
where Q is represented by batchProduct S.
-/
def structuredBaseResidue
    (A E : ℕ)
    (S : Finset ℕ) : ℕ :=
  ((A % batchProduct S) *
    ((2 ^ E) % batchProduct S)) %
    batchProduct S

/--
Core compression identity:

(A * 2^E) mod Q
=
((A mod Q) * (2^E mod Q)) mod Q.
-/
theorem structuredBase_mod_eq_residue
    (A E : ℕ)
    (S : Finset ℕ) :
    structuredBase A E % batchProduct S =
      structuredBaseResidue A E S := by

  unfold structuredBase
  unfold structuredBaseResidue

  exact
    Nat.mul_mod
      A
      (2 ^ E)
      (batchProduct S)

/--
The power itself can also be computed after reducing the base:

2^E mod Q = (2 mod Q)^E mod Q.
-/
theorem two_pow_mod_reduced_base
    (E : ℕ)
    (S : Finset ℕ) :
    (2 ^ E) % batchProduct S =
      ((2 % batchProduct S) ^ E) %
        batchProduct S := by

  exact
    Nat.pow_mod
      2
      E
      (batchProduct S)

/--
Equivalent residue formula using a reduced base before exponentiation.
This mirrors modular exponentiation in an implementation.
-/
def structuredBaseResiduePowMod
    (A E : ℕ)
    (S : Finset ℕ) : ℕ :=
  ((A % batchProduct S) *
    (((2 % batchProduct S) ^ E) %
      batchProduct S)) %
    batchProduct S

theorem structuredBaseResidue_eq_powMod
    (A E : ℕ)
    (S : Finset ℕ) :
    structuredBaseResidue A E S =
      structuredBaseResiduePowMod A E S := by

  unfold structuredBaseResidue
  unfold structuredBaseResiduePowMod

  rw [
    two_pow_mod_reduced_base
      E S
  ]

/--
Therefore the huge integer B = A * 2^E never has to be expanded
in order to obtain B mod batchProduct(S).
-/
theorem structuredBase_mod_eq_powModResidue
    (A E : ℕ)
    (S : Finset ℕ) :
    structuredBase A E % batchProduct S =
      structuredBaseResiduePowMod A E S := by

  rw [
    structuredBase_mod_eq_residue
      A E S
  ]

  exact
    structuredBaseResidue_eq_powMod
      A E S

/--
The compressed twin-candidate test specialized to
B = A * 2^E.

The original enormous candidates and the candidates built from the
small batch residue give exactly the same batch-GCD result.
-/
theorem structuredBase_compressed_batch_test
    (A E : ℕ)
    (S : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.gcd
      (((structuredBase A E) + 6 * m - 1) *
       ((structuredBase A E) + 6 * m + 1))
      (batchProduct S) = 1
    ↔
    Nat.gcd
      ((structuredBaseResidue A E S + 6 * m - 1) *
       (structuredBaseResidue A E S + 6 * m + 1))
      (batchProduct S) = 1 := by

  have h :=
    explicit_compressed_batch_test
      (structuredBase A E)
      S
      m
      hm

  have hres :
      structuredBase A E % batchProduct S =
        structuredBaseResidue A E S := by

    exact
      structuredBase_mod_eq_residue
        A E S

  rw [hres] at h

  exact h

/--
The same compressed batch test, written using the modular-power
version of the residue.
-/
theorem structuredBase_powMod_compressed_batch_test
    (A E : ℕ)
    (S : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.gcd
      (((structuredBase A E) + 6 * m - 1) *
       ((structuredBase A E) + 6 * m + 1))
      (batchProduct S) = 1
    ↔
    Nat.gcd
      ((structuredBaseResiduePowMod A E S + 6 * m - 1) *
       (structuredBaseResiduePowMod A E S + 6 * m + 1))
      (batchProduct S) = 1 := by

  have h :=
    structuredBase_compressed_batch_test
      A E S m hm

  have hres :
      structuredBaseResidue A E S =
        structuredBaseResiduePowMod A E S := by

    exact
      structuredBaseResidue_eq_powMod
        A E S

  rw [hres] at h

  exact h

/-
The concrete constants from the large twin-prime reference pair
used in the project.
-/

def referenceA : ℕ :=
  2996863034895

def referenceE : ℕ :=
  1290000

def referenceB : ℕ :=
  structuredBase referenceA referenceE

def referenceBatchResidue
    (S : Finset ℕ) : ℕ :=
  structuredBaseResidue
    referenceA
    referenceE
    S

/--
For the concrete reference number
B = 2,996,863,034,895 * 2^1,290,000,
its residue modulo any batch product is obtained by the same
compressed formula.
-/
theorem referenceB_mod_eq_referenceBatchResidue
    (S : Finset ℕ) :
    referenceB % batchProduct S =
      referenceBatchResidue S := by

  unfold referenceB
  unfold referenceBatchResidue

  exact
    structuredBase_mod_eq_residue
      referenceA
      referenceE
      S


/-!
## Compressed coordinates
-/

/--
Origin used for the compressed post-reference coordinates:

O = B + 3.
-/
def origin
    (B : ℕ) : ℕ :=
  B + 3

/--
Compressed coordinate of N relative to the origin O = B + 3:

κ = (N - O) / 2.
-/
def compressedIndex
    (B N : ℕ) : ℕ :=
  (N - origin B) / 2

/--
The two compressed coordinates used for the twin-candidate pair.
-/
def kappaMinus
    (m : ℕ) : ℕ :=
  3 * m - 2

def kappaPlus
    (m : ℕ) : ℕ :=
  3 * m - 1

/--
For m ≥ 1, the left candidate B + 6m - 1 lies at or above
the compressed origin B + 3.
-/
theorem shiftedMinus_ge_origin
    (B m : ℕ)
    (hm : 1 ≤ m) :
    origin B ≤ shiftedMinus B m := by

  unfold origin
  unfold shiftedMinus

  omega

/--
For m ≥ 1, the right candidate B + 6m + 1 lies at or above
the compressed origin B + 3.
-/
theorem shiftedPlus_ge_origin
    (B m : ℕ)
    (hm : 1 ≤ m) :
    origin B ≤ shiftedPlus B m := by

  unfold origin
  unfold shiftedPlus

  omega

/--
Distance from the origin to the left member:

(B + 6m - 1) - (B + 3) = 2(3m - 2).
-/
theorem shiftedMinus_sub_origin
    (B m : ℕ)
    (hm : 1 ≤ m) :
    shiftedMinus B m - origin B =
      2 * kappaMinus m := by

  unfold shiftedMinus
  unfold origin
  unfold kappaMinus

  omega

/--
Distance from the origin to the right member:

(B + 6m + 1) - (B + 3) = 2(3m - 1).
-/
theorem shiftedPlus_sub_origin
    (B m : ℕ)
    (hm : 1 ≤ m) :
    shiftedPlus B m - origin B =
      2 * kappaPlus m := by

  unfold shiftedPlus
  unfold origin
  unfold kappaPlus

  omega

/--
The compressed coordinate of B + 6m - 1 is exactly

κ₁ = 3m - 2.
-/
theorem compressedIndex_shiftedMinus
    (B m : ℕ)
    (hm : 1 ≤ m) :
    compressedIndex B (shiftedMinus B m) =
      kappaMinus m := by

  unfold compressedIndex

  rw [
    shiftedMinus_sub_origin
      B m hm
  ]

  omega

/--
The compressed coordinate of B + 6m + 1 is exactly

κ₂ = 3m - 1.
-/
theorem compressedIndex_shiftedPlus
    (B m : ℕ)
    (hm : 1 ≤ m) :
    compressedIndex B (shiftedPlus B m) =
      kappaPlus m := by

  unfold compressedIndex

  rw [
    shiftedPlus_sub_origin
      B m hm
  ]

  omega

/--
The two compressed coordinates are consecutive:

κ₂ = κ₁ + 1.
-/
theorem kappaPlus_eq_succ_kappaMinus
    (m : ℕ)
    (hm : 1 ≤ m) :
    kappaPlus m =
      kappaMinus m + 1 := by

  unfold kappaPlus
  unfold kappaMinus

  omega

/--
Therefore the two original candidates become adjacent positions
in compressed coordinates.
-/
theorem compressed_twin_positions_adjacent
    (B m : ℕ)
    (hm : 1 ≤ m) :
    compressedIndex B (shiftedPlus B m) =
      compressedIndex B (shiftedMinus B m) + 1 := by

  rw [
    compressedIndex_shiftedPlus
      B m hm,
    compressedIndex_shiftedMinus
      B m hm
  ]

  exact
    kappaPlus_eq_succ_kappaMinus
      m hm

/--
Translation of the original arithmetic progression C(n)=3+2n
by the large base B.
-/
def translatedC
    (B n : ℕ) : ℕ :=
  B + C n

/--
The translated progression can equivalently be written from
the compressed origin:

B + C(n) = O + 2n.
-/
theorem translatedC_eq_origin_plus_twice
    (B n : ℕ) :
    translatedC B n =
      origin B + 2 * n := by

  unfold translatedC
  unfold origin
  unfold C

  omega

/--
The left post-reference candidate is exactly the translated
arithmetic-progression member at κ₁ = 3m - 2.
-/
theorem shiftedMinus_eq_translatedC
    (B m : ℕ)
    (hm : 1 ≤ m) :
    shiftedMinus B m =
      translatedC B (kappaMinus m) := by

  unfold shiftedMinus
  unfold translatedC
  unfold kappaMinus
  unfold C

  omega

/--
The right post-reference candidate is exactly the translated
arithmetic-progression member at κ₂ = 3m - 1.
-/
theorem shiftedPlus_eq_translatedC
    (B m : ℕ)
    (hm : 1 ≤ m) :
    shiftedPlus B m =
      translatedC B (kappaPlus m) := by

  unfold shiftedPlus
  unfold translatedC
  unfold kappaPlus
  unfold C

  omega

/--
The candidate pair B+6m-1, B+6m+1 is therefore represented by
two adjacent members of the translated C progression.
-/
theorem shifted_pair_as_adjacent_translatedC
    (B m : ℕ)
    (hm : 1 ≤ m) :
    shiftedMinus B m =
        translatedC B (kappaMinus m) ∧
    shiftedPlus B m =
        translatedC B (kappaMinus m + 1) := by

  constructor

  · exact
      shiftedMinus_eq_translatedC
        B m hm

  · have hk :
        kappaPlus m =
          kappaMinus m + 1 := by

      exact
        kappaPlus_eq_succ_kappaMinus
          m hm

    rw [← hk]

    exact
      shiftedPlus_eq_translatedC
        B m hm

/--
Residue of the compressed origin O=B+3 modulo one batch product.
-/
def originBatchResidue
    (B : ℕ)
    (S : Finset ℕ) : ℕ :=
  (batchResidue B S + 3) %
    batchProduct S

/--
The residue of O=B+3 can be computed from the already-compressed
residue R=B mod batchProduct(S).
-/
theorem origin_mod_eq_originBatchResidue
    (B : ℕ)
    (S : Finset ℕ) :
    origin B % batchProduct S =
      originBatchResidue B S := by

  have h :
      Nat.ModEq
        (batchProduct S)
        (B + 3)
        (batchResidue B S + 3) := by

    exact
      (base_modEq_batchResidue
        B S).add_right 3

  unfold origin
  unfold originBatchResidue

  exact h

/--
Concrete origin associated with the project's giant reference B.
-/
def referenceOrigin : ℕ :=
  origin referenceB

def referenceOriginBatchResidue
    (S : Finset ℕ) : ℕ :=
  originBatchResidue
    referenceB
    S

theorem referenceOrigin_mod_eq_referenceOriginBatchResidue
    (S : Finset ℕ) :
    referenceOrigin % batchProduct S =
      referenceOriginBatchResidue S := by

  unfold referenceOrigin
  unfold referenceOriginBatchResidue

  exact
    origin_mod_eq_originBatchResidue
      referenceB S

/--
For the concrete reference B, the two searched numbers have
compressed coordinates κ₁=3m-2 and κ₂=3m-1.
-/
theorem reference_compressed_coordinates
    (m : ℕ)
    (hm : 1 ≤ m) :
    compressedIndex
        referenceB
        (shiftedMinus referenceB m) =
      kappaMinus m
    ∧
    compressedIndex
        referenceB
        (shiftedPlus referenceB m) =
      kappaPlus m := by

  constructor

  · exact
      compressedIndex_shiftedMinus
        referenceB m hm

  · exact
      compressedIndex_shiftedPlus
        referenceB m hm


/-!
## Forbidden classes in κ-coordinates
-/

/--
A compressed coordinate κ is forbidden by q when q divides the
translated progression value B + C(κ) = O + 2κ.
-/
def KappaForbidden
    (B q kappa : ℕ) : Prop :=
  q ∣ translatedC B kappa

/--
Equivalent form of a forbidden compressed coordinate written
directly from the compressed origin O = B + 3.
-/
theorem kappaForbidden_iff_origin_plus_twice
    (B q kappa : ℕ) :
    KappaForbidden B q kappa ↔
      q ∣ origin B + 2 * kappa := by

  unfold KappaForbidden

  rw [
    translatedC_eq_origin_plus_twice
      B kappa
  ]

/--
Congruent compressed coordinates produce congruent translated
candidate values.
-/
theorem translatedC_preserves_modEq
    {B q a b : ℕ}
    (h : Nat.ModEq q a b) :
    Nat.ModEq q
      (translatedC B a)
      (translatedC B b) := by

  unfold translatedC

  exact
    (C_preserves_modEq h).add_left B

/--
Being forbidden by q depends only on the residue class of κ modulo q.
-/
theorem kappaForbidden_congruent_iff
    {B q a b : ℕ}
    (h : Nat.ModEq q a b) :
    KappaForbidden B q a ↔
      KappaForbidden B q b := by

  unfold KappaForbidden

  have htranslated :
      Nat.ModEq q
        (translatedC B a)
        (translatedC B b) := by

    exact
      translatedC_preserves_modEq h

  constructor

  · intro ha

    have ha0 :
        Nat.ModEq q
          (translatedC B a)
          0 := by

      exact
        (Nat.modEq_zero_iff_dvd).2 ha

    have hb0 :
        Nat.ModEq q
          (translatedC B b)
          0 := by

      exact
        htranslated.symm.trans ha0

    exact
      (Nat.modEq_zero_iff_dvd).1 hb0

  · intro hb

    have hb0 :
        Nat.ModEq q
          (translatedC B b)
          0 := by

      exact
        (Nat.modEq_zero_iff_dvd).2 hb

    have ha0 :
        Nat.ModEq q
          (translatedC B a)
          0 := by

      exact
        htranslated.trans hb0

    exact
      (Nat.modEq_zero_iff_dvd).1 ha0

/--
Forbidden compressed coordinates repeat with period q.
-/
theorem kappaForbidden_periodic
    (B q kappa t : ℕ) :
    KappaForbidden B q (kappa + t * q) ↔
      KappaForbidden B q kappa := by

  have hclass :
      Nat.ModEq q
        (kappa + t * q)
        kappa := by

    exact
      left_forbidden_modEq
        kappa q t

  exact
    kappaForbidden_congruent_iff
      hclass

/--
The left member B+6m-1 is divisible by q exactly when the compressed
coordinate κ₁ = 3m-2 is forbidden by q.
-/
theorem shiftedMinus_divisible_iff_kappaForbidden
    (B q m : ℕ)
    (hm : 1 ≤ m) :
    q ∣ shiftedMinus B m ↔
      KappaForbidden B q (kappaMinus m) := by

  unfold KappaForbidden

  rw [
    ← shiftedMinus_eq_translatedC
      B m hm
  ]

/--
The right member B+6m+1 is divisible by q exactly when the compressed
coordinate κ₂ = 3m-1 is forbidden by q.
-/
theorem shiftedPlus_divisible_iff_kappaForbidden
    (B q m : ℕ)
    (hm : 1 ≤ m) :
    q ∣ shiftedPlus B m ↔
      KappaForbidden B q (kappaPlus m) := by

  unfold KappaForbidden

  rw [
    ← shiftedPlus_eq_translatedC
      B m hm
  ]

/--
A twin candidate pair survives one divisor q exactly when neither
of its two adjacent compressed coordinates is forbidden by q.
-/
theorem shiftedPair_survives_q_iff_kappa
    (B q m : ℕ)
    (hm : 1 ≤ m) :
    (¬ q ∣ shiftedMinus B m) ∧
    (¬ q ∣ shiftedPlus B m)
    ↔
    (¬ KappaForbidden B q (kappaMinus m)) ∧
    (¬ KappaForbidden B q (kappaPlus m)) := by

  constructor

  · intro h

    constructor

    · intro hk

      have hdiv :
          q ∣ shiftedMinus B m := by

        exact
          (shiftedMinus_divisible_iff_kappaForbidden
            B q m hm).2 hk

      exact h.1 hdiv

    · intro hk

      have hdiv :
          q ∣ shiftedPlus B m := by

        exact
          (shiftedPlus_divisible_iff_kappaForbidden
            B q m hm).2 hk

      exact h.2 hdiv

  · intro h

    constructor

    · intro hdiv

      have hk :
          KappaForbidden B q (kappaMinus m) := by

        exact
          (shiftedMinus_divisible_iff_kappaForbidden
            B q m hm).1 hdiv

      exact h.1 hk

    · intro hdiv

      have hk :
          KappaForbidden B q (kappaPlus m) := by

        exact
          (shiftedPlus_divisible_iff_kappaForbidden
            B q m hm).1 hdiv

      exact h.2 hk

/--
Since κ₂ = κ₁+1, one can express the pair using a single starting
compressed coordinate and its successor.
-/
theorem shiftedPair_survives_q_iff_adjacent_kappa
    (B q m : ℕ)
    (hm : 1 ≤ m) :
    (¬ q ∣ shiftedMinus B m) ∧
    (¬ q ∣ shiftedPlus B m)
    ↔
    (¬ KappaForbidden B q (kappaMinus m)) ∧
    (¬ KappaForbidden B q (kappaMinus m + 1)) := by

  have hk :
      kappaPlus m =
        kappaMinus m + 1 := by

    exact
      kappaPlus_eq_succ_kappaMinus
        m hm

  rw [← hk]

  exact
    shiftedPair_survives_q_iff_kappa
      B q m hm

/--
For the concrete giant reference B, forbidden compressed coordinates
still repeat periodically modulo q.
-/
theorem reference_kappaForbidden_periodic
    (q kappa t : ℕ) :
    KappaForbidden
        referenceB
        q
        (kappa + t * q)
    ↔
    KappaForbidden
        referenceB
        q
        kappa := by

  exact
    kappaForbidden_periodic
      referenceB q kappa t

/--
For the concrete reference B, the searched pair survives q exactly
when its two consecutive compressed coordinates avoid q's forbidden
residue class.
-/
theorem reference_shiftedPair_survives_q_iff_adjacent_kappa
    (q m : ℕ)
    (hm : 1 ≤ m) :
    (¬ q ∣ shiftedMinus referenceB m) ∧
    (¬ q ∣ shiftedPlus referenceB m)
    ↔
    (¬ KappaForbidden
        referenceB q (kappaMinus m)) ∧
    (¬ KappaForbidden
        referenceB q (kappaMinus m + 1)) := by

  exact
    shiftedPair_survives_q_iff_adjacent_kappa
      referenceB q m hm


/-!
## Explicit forbidden residue class
-/

/--
r_q = O mod q, where O = B + 3 is the compressed origin.
-/
def originResidueModPrime
    (B q : ℕ) : ℕ :=
  origin B % q

/--
For an odd prime q, the inverse of 2 modulo q is represented by

(q + 1) / 2.

Indeed, 2 * ((q+1)/2) = q+1 ≡ 1 (mod q).
-/
def invTwo
    (q : ℕ) : ℕ :=
  (q + 1) / 2

/--
For every odd prime q,

2 * invTwo(q) = q + 1.
-/
theorem two_mul_invTwo_eq_q_add_one
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2) :
    2 * invTwo q = q + 1 := by

  have hodd :
      Odd q := by

    exact
      hq.odd_of_ne_two
        hq2

  rcases hodd with ⟨t, ht⟩

  unfold invTwo

  omega

/--
Therefore invTwo(q) really is a multiplicative inverse of 2
modulo every odd prime q.
-/
theorem two_mul_invTwo_modEq_one
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2) :
    Nat.ModEq q
      (2 * invTwo q)
      1 := by

  rw [
    two_mul_invTwo_eq_q_add_one
      hq hq2
  ]

  simp

/--
Explicit forbidden residue for the compressed coordinate κ:

κ_q = (-r_q) * 2⁻¹  (mod q),

represented in natural-number arithmetic as

((q - r_q) * invTwo(q)) mod q,

where r_q = O mod q.
-/
def forbiddenKappaResidue
    (B q : ℕ) : ℕ :=
  ((q - originResidueModPrime B q) *
    invTwo q) % q

/--
The definition written exactly in terms of O = B + 3.
-/
theorem forbiddenKappaResidue_formula
    (B q : ℕ) :
    forbiddenKappaResidue B q =
      ((q - (origin B % q)) *
        ((q + 1) / 2)) % q := by

  rfl

/--
For a prime q, r_q is a genuine residue: r_q < q.
-/
theorem originResidueModPrime_lt
    (B : ℕ)
    {q : ℕ}
    (hq : Nat.Prime q) :
    originResidueModPrime B q < q := by

  have hq2 :
      2 ≤ q := hq.two_le

  have hqpos :
      0 < q := by
    omega

  unfold originResidueModPrime

  exact
    Nat.mod_lt
      (origin B)
      hqpos

/--
The explicitly constructed residue κ_q really is forbidden:
q divides O + 2κ_q.
-/
theorem forbiddenKappaResidue_is_forbidden
    (B : ℕ)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2) :
    KappaForbidden
      B q
      (forbiddenKappaResidue B q) := by

  have hO :
      Nat.ModEq q
        (origin B)
        (originResidueModPrime B q) := by

    unfold originResidueModPrime

    exact
      (Nat.mod_modEq
        (origin B)
        q).symm

  have hF :
      Nat.ModEq q
        (forbiddenKappaResidue B q)
        ((q - originResidueModPrime B q) *
          invTwo q) := by

    unfold forbiddenKappaResidue

    exact
      Nat.mod_modEq
        ((q - originResidueModPrime B q) *
          invTwo q)
        q

  have h2F :
      Nat.ModEq q
        (2 * forbiddenKappaResidue B q)
        (2 *
          ((q - originResidueModPrime B q) *
            invTwo q)) := by

    exact hF.mul_left 2

  have hInv :
      Nat.ModEq q
        (2 * invTwo q)
        1 := by

    exact
      two_mul_invTwo_modEq_one
        hq hq2

  have hInvScaled :
      Nat.ModEq q
        ((q - originResidueModPrime B q) *
          (2 * invTwo q))
        ((q - originResidueModPrime B q) * 1) := by

    exact
      hInv.mul_left
        (q - originResidueModPrime B q)

  have hScaled :
      Nat.ModEq q
        (2 *
          ((q - originResidueModPrime B q) *
            invTwo q))
        (q - originResidueModPrime B q) := by

    simpa [
      Nat.mul_assoc,
      Nat.mul_comm,
      Nat.mul_left_comm
    ] using hInvScaled

  have h2Fneg :
      Nat.ModEq q
        (2 * forbiddenKappaResidue B q)
        (q - originResidueModPrime B q) := by

    exact
      h2F.trans hScaled

  have hsum :
      Nat.ModEq q
        (origin B +
          2 * forbiddenKappaResidue B q)
        (originResidueModPrime B q +
          (q - originResidueModPrime B q)) := by

    exact hO.add h2Fneg

  have hrlt :
      originResidueModPrime B q < q := by

    exact
      originResidueModPrime_lt
        B hq

  have hresidueSum :
      originResidueModPrime B q +
          (q - originResidueModPrime B q)
        = q := by

    omega

  rw [hresidueSum] at hsum

  have hq0 :
      Nat.ModEq q q 0 := by

    exact
      (Nat.modEq_zero_iff_dvd).2
        (Nat.dvd_refl q)

  have hzero :
      Nat.ModEq q
        (origin B +
          2 * forbiddenKappaResidue B q)
        0 := by

    exact hsum.trans hq0

  have hdiv :
      q ∣
        origin B +
          2 * forbiddenKappaResidue B q := by

    exact
      (Nat.modEq_zero_iff_dvd).1
        hzero

  exact
    (kappaForbidden_iff_origin_plus_twice
      B q (forbiddenKappaResidue B q)).2
      hdiv

/--
Main theorem for the explicit forbidden residue class.

For every odd prime q, a compressed coordinate κ is forbidden
if and only if it belongs to the single residue class

κ ≡ (-r_q) * 2⁻¹ (mod q),

where r_q = O mod q.
-/
theorem kappaForbidden_iff_modEq_forbiddenResidue
    (B : ℕ)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (kappa : ℕ) :
    KappaForbidden B q kappa
    ↔
    Nat.ModEq q
      kappa
      (forbiddenKappaResidue B q) := by

  constructor

  · intro hk

    have hkdiv :
        q ∣ origin B + 2 * kappa := by

      exact
        (kappaForbidden_iff_origin_plus_twice
          B q kappa).1 hk

    have hf :
        KappaForbidden
          B q
          (forbiddenKappaResidue B q) := by

      exact
        forbiddenKappaResidue_is_forbidden
          B hq hq2

    have hfdiv :
        q ∣
          origin B +
            2 * forbiddenKappaResidue B q := by

      exact
        (kappaForbidden_iff_origin_plus_twice
          B q (forbiddenKappaResidue B q)).1 hf

    have hk0 :
        Nat.ModEq q
          (origin B + 2 * kappa)
          0 := by

      exact
        (Nat.modEq_zero_iff_dvd).2
          hkdiv

    have hf0 :
        Nat.ModEq q
          (origin B +
            2 * forbiddenKappaResidue B q)
          0 := by

      exact
        (Nat.modEq_zero_iff_dvd).2
          hfdiv

    have heq :
        Nat.ModEq q
          (origin B + 2 * kappa)
          (origin B +
            2 * forbiddenKappaResidue B q) := by

      exact
        hk0.trans
          hf0.symm

    have htwo :
        Nat.ModEq q
          (2 * kappa)
          (2 * forbiddenKappaResidue B q) := by

      apply
        Nat.ModEq.add_left_cancel'
          (origin B)

      exact heq

    have hodd :
        Odd q := by

      exact
        hq.odd_of_ne_two
          hq2

    have hcop :
        q.gcd 2 = 1 := by

      exact
        Nat.coprime_two_right.mpr
          hodd

    exact
      Nat.ModEq.cancel_left_of_coprime
        hcop
        htwo

  · intro hmod

    have hf :
        KappaForbidden
          B q
          (forbiddenKappaResidue B q) := by

      exact
        forbiddenKappaResidue_is_forbidden
          B hq hq2

    exact
      (kappaForbidden_congruent_iff
        (B := B)
        hmod).2
        hf

/--
The explicit forbidden residue is itself the canonical representative
of its class: it is strictly smaller than q.
-/
theorem forbiddenKappaResidue_lt
    (B : ℕ)
    {q : ℕ}
    (hq : Nat.Prime q) :
    forbiddenKappaResidue B q < q := by

  have hq2 :
      2 ≤ q := hq.two_le

  have hqpos :
      0 < q := by
    omega

  unfold forbiddenKappaResidue

  exact
    Nat.mod_lt
      ((q - originResidueModPrime B q) *
        invTwo q)
      hqpos

/--
For an odd prime q, the candidate pair survives q exactly when
its two adjacent compressed coordinates avoid q's explicit
forbidden residue class.
-/
theorem shiftedPair_survives_q_iff_avoids_forbiddenResidue
    (B : ℕ)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (m : ℕ)
    (hm : 1 ≤ m) :
    (¬ q ∣ shiftedMinus B m) ∧
    (¬ q ∣ shiftedPlus B m)
    ↔
    (¬ Nat.ModEq q
        (kappaMinus m)
        (forbiddenKappaResidue B q)) ∧
    (¬ Nat.ModEq q
        (kappaMinus m + 1)
        (forbiddenKappaResidue B q)) := by

  have h :=
    shiftedPair_survives_q_iff_adjacent_kappa
      B q m hm

  rw [
    kappaForbidden_iff_modEq_forbiddenResidue
      B hq hq2 (kappaMinus m),
    kappaForbidden_iff_modEq_forbiddenResidue
      B hq hq2 (kappaMinus m + 1)
  ] at h

  exact h

/--
Explicit forbidden residue for the concrete giant reference B.
-/
def referenceForbiddenKappaResidue
    (q : ℕ) : ℕ :=
  forbiddenKappaResidue
    referenceB
    q

/--
For the concrete reference B, the same explicit formula applies:

κ ≡ -r_q * 2⁻¹ (mod q).
-/
theorem reference_kappaForbidden_iff_explicit_residue
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (kappa : ℕ) :
    KappaForbidden
      referenceB
      q
      kappa
    ↔
    Nat.ModEq q
      kappa
      (referenceForbiddenKappaResidue q) := by

  unfold referenceForbiddenKappaResidue

  exact
    kappaForbidden_iff_modEq_forbiddenResidue
      referenceB
      hq
      hq2
      kappa

/--
And the searched pair survives q precisely when neither of its
two consecutive κ-coordinates lies in that explicit residue class.
-/
theorem reference_shiftedPair_survives_q_iff_avoids_explicit_residue
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (m : ℕ)
    (hm : 1 ≤ m) :
    (¬ q ∣ shiftedMinus referenceB m) ∧
    (¬ q ∣ shiftedPlus referenceB m)
    ↔
    (¬ Nat.ModEq q
        (kappaMinus m)
        (referenceForbiddenKappaResidue q)) ∧
    (¬ Nat.ModEq q
        (kappaMinus m + 1)
        (referenceForbiddenKappaResidue q)) := by

  unfold referenceForbiddenKappaResidue

  exact
    shiftedPair_survives_q_iff_avoids_forbiddenResidue
      referenceB
      hq
      hq2
      m
      hm


/-!
## Batch sieve in κ-coordinates
-/

/--
A single odd prime q accepts a compressed coordinate kappa when
neither kappa nor kappa+1 belongs to q's explicit forbidden class.
-/
def KappaSurvivesPrime
    (B q kappa : ℕ) : Prop :=
  (¬ Nat.ModEq q
      kappa
      (forbiddenKappaResidue B q)) ∧
  (¬ Nat.ModEq q
      (kappa + 1)
      (forbiddenKappaResidue B q))

/--
A compressed coordinate survives a whole finite batch Q when it
survives every prime q in Q.
-/
def KappaSurvivesSet
    (B : ℕ)
    (Q : Finset ℕ)
    (kappa : ℕ) : Prop :=
  ∀ q ∈ Q,
    KappaSurvivesPrime
      B q kappa

/--
For a valid odd-prime q, survival of the compressed coordinate
kappaMinus(m) is exactly survival of the original pair
B+6m-1, B+6m+1 against q.
-/
theorem kappaSurvivesPrime_iff_shiftedPair_survives
    (B : ℕ)
    {q : ℕ}
    (hq : Nat.Prime q)
    (hq2 : q ≠ 2)
    (m : ℕ)
    (hm : 1 ≤ m) :
    KappaSurvivesPrime
      B q (kappaMinus m)
    ↔
    (¬ q ∣ shiftedMinus B m) ∧
    (¬ q ∣ shiftedPlus B m) := by

  unfold KappaSurvivesPrime

  exact
    (shiftedPair_survives_q_iff_avoids_forbiddenResidue
      B hq hq2 m hm).symm

/--
Batch version: the compressed coordinate survives Q exactly when
the original candidate pair avoids every q in Q.
-/
theorem kappaSurvivesSet_iff_shiftedPair_survives_all
    (B : ℕ)
    (Q : Finset ℕ)
    (hQ : ValidSieveSet Q)
    (m : ℕ)
    (hm : 1 ≤ m) :
    KappaSurvivesSet
      B Q (kappaMinus m)
    ↔
    ∀ q ∈ Q,
      (¬ q ∣ shiftedMinus B m) ∧
      (¬ q ∣ shiftedPlus B m) := by

  constructor

  · intro hsurv q hqmem

    have hprops :
        Nat.Prime q ∧ q ≠ 2 :=
      hQ q hqmem

    have hk :
        KappaSurvivesPrime
          B q (kappaMinus m) := by

      exact hsurv q hqmem

    exact
      (kappaSurvivesPrime_iff_shiftedPair_survives
        B
        hprops.1
        hprops.2
        m
        hm).mp
        hk

  · intro hall

    unfold KappaSurvivesSet

    intro q hqmem

    have hprops :
        Nat.Prime q ∧ q ≠ 2 :=
      hQ q hqmem

    exact
      (kappaSurvivesPrime_iff_shiftedPair_survives
        B
        hprops.1
        hprops.2
        m
        hm).mpr
        (hall q hqmem)

/--
Main theorem for the compressed batch sieve.

The purely compressed residue-class sieve is equivalent to the
single batch-GCD test on the original candidate pair.
-/
theorem kappaSurvivesSet_iff_batch_gcd_one
    (B : ℕ)
    (Q : Finset ℕ)
    (hQ : ValidSieveSet Q)
    (m : ℕ)
    (hm : 1 ≤ m) :
    KappaSurvivesSet
      B Q (kappaMinus m)
    ↔
    Nat.gcd
      (shiftedMinus B m *
       shiftedPlus B m)
      (batchProduct Q) = 1 := by

  constructor

  · intro hsurv

    have hall :
        ∀ q ∈ Q,
          (¬ q ∣ shiftedMinus B m) ∧
          (¬ q ∣ shiftedPlus B m) := by

      exact
        (kappaSurvivesSet_iff_shiftedPair_survives_all
          B Q hQ m hm).mp
          hsurv

    apply
      (gcd_batch_eq_one_iff_no_member_divides
        Q
        (shiftedMinus B m * shiftedPlus B m)
        hQ).2

    intro q hqmem hdiv

    have hprime :
        Nat.Prime q :=
      (hQ q hqmem).1

    have hpair :
        (¬ q ∣ shiftedMinus B m) ∧
        (¬ q ∣ shiftedPlus B m) :=
      hall q hqmem

    have hcases :
        q ∣ shiftedMinus B m ∨
        q ∣ shiftedPlus B m := by

      exact
        (hprime.dvd_mul).mp
          hdiv

    rcases hcases with hleft | hright

    · exact hpair.1 hleft

    · exact hpair.2 hright

  · intro hgcd

    have hnoProduct :
        ∀ q ∈ Q,
          ¬ q ∣
            (shiftedMinus B m *
             shiftedPlus B m) := by

      exact
        (gcd_batch_eq_one_iff_no_member_divides
          Q
          (shiftedMinus B m * shiftedPlus B m)
          hQ).1
          hgcd

    apply
      (kappaSurvivesSet_iff_shiftedPair_survives_all
        B Q hQ m hm).2

    intro q hqmem

    have hprime :
        Nat.Prime q :=
      (hQ q hqmem).1

    have hnp :
        ¬ q ∣
          (shiftedMinus B m *
           shiftedPlus B m) :=
      hnoProduct q hqmem

    constructor

    · intro hleft

      apply hnp

      exact
        (hprime.dvd_mul).2
          (Or.inl hleft)

    · intro hright

      apply hnp

      exact
        (hprime.dvd_mul).2
          (Or.inr hright)

/--
Compressed-coordinate survival distributes over the union of
two sieve shards.
-/
theorem kappaSurvives_union_iff
    (B : ℕ)
    (A D : Finset ℕ)
    (kappa : ℕ) :
    KappaSurvivesSet B (A ∪ D) kappa
    ↔
    KappaSurvivesSet B A kappa ∧
    KappaSurvivesSet B D kappa := by

  unfold KappaSurvivesSet

  constructor

  · intro hAD

    constructor

    · intro q hqA

      exact
        hAD q
          (Finset.mem_union_left D hqA)

    · intro q hqD

      exact
        hAD q
          (Finset.mem_union_right A hqD)

  · intro h q hqAD

    have hmem :
        q ∈ A ∨ q ∈ D := by

      exact
        Finset.mem_union.mp
          hqAD

    rcases hmem with hqA | hqD

    · exact h.1 q hqA

    · exact h.2 q hqD

/--
The same property for three independent compressed sieve shards.
-/
theorem kappaSurvives_three_shards_iff
    (B : ℕ)
    (A D E : Finset ℕ)
    (kappa : ℕ) :
    KappaSurvivesSet
        B (A ∪ D ∪ E) kappa
    ↔
    KappaSurvivesSet B A kappa ∧
    KappaSurvivesSet B D kappa ∧
    KappaSurvivesSet B E kappa := by

  constructor

  · intro hADE

    have hOuter :
        KappaSurvivesSet B (A ∪ D) kappa ∧
        KappaSurvivesSet B E kappa := by

      exact
        (kappaSurvives_union_iff
          B
          (A ∪ D)
          E
          kappa).mp
          hADE

    have hInner :
        KappaSurvivesSet B A kappa ∧
        KappaSurvivesSet B D kappa := by

      exact
        (kappaSurvives_union_iff
          B A D kappa).mp
          hOuter.1

    exact
      ⟨hInner.1,
       hInner.2,
       hOuter.2⟩

  · intro h

    have hAD :
        KappaSurvivesSet
          B (A ∪ D) kappa := by

      exact
        (kappaSurvives_union_iff
          B A D kappa).mpr
          ⟨h.1, h.2.1⟩

    exact
      (kappaSurvives_union_iff
        B
        (A ∪ D)
        E
        kappa).mpr
        ⟨hAD, h.2.2⟩

/--
Specialization to the concrete giant reference B.
-/
theorem reference_kappaSurvivesSet_iff_batch_gcd_one
    (Q : Finset ℕ)
    (hQ : ValidSieveSet Q)
    (m : ℕ)
    (hm : 1 ≤ m) :
    KappaSurvivesSet
      referenceB
      Q
      (kappaMinus m)
    ↔
    Nat.gcd
      (shiftedMinus referenceB m *
       shiftedPlus referenceB m)
      (batchProduct Q) = 1 := by

  exact
    kappaSurvivesSet_iff_batch_gcd_one
      referenceB
      Q
      hQ
      m
      hm


/-!
## Completeness and primality correctness
-/

/--
A finite batch Q is complete up to M for the odd-prime sieve when:

1. every member of Q is an odd prime;
2. every q in Q satisfies q*q ≤ M;
3. every odd prime p with p*p ≤ M belongs to Q.

Thus Q contains exactly the kind of prime divisors that can witness
compositeness below the square-root boundary.
-/
def CompleteOddPrimeBatchUpTo
    (Q : Finset ℕ)
    (M : ℕ) : Prop :=
  ValidSieveSet Q ∧
  (∀ q ∈ Q, q * q ≤ M) ∧
  (∀ p : ℕ,
    Nat.Prime p →
    p ≠ 2 →
    p * p ≤ M →
    p ∈ Q)

/--
If N is odd, 2 ≤ N ≤ M, Q is complete up to M, and no q in Q
divides N, then N is prime.

The proof uses the smallest prime factor. If N were composite,
minFac(N) would be an odd prime whose square is at most N, hence
at most M, so completeness would force it into Q, contradicting
the survival assumption.
-/
theorem prime_of_complete_odd_batch_no_divisor
    (Q : Finset ℕ)
    (M N : ℕ)
    (hComplete :
      CompleteOddPrimeBatchUpTo Q M)
    (hN2 : 2 ≤ N)
    (hOdd : Odd N)
    (hNM : N ≤ M)
    (hNoDiv :
      ∀ q ∈ Q, ¬ q ∣ N) :
    Nat.Prime N := by

  by_contra hNotPrime

  have hNpos :
      0 < N := by
    omega

  have hNne1 :
      N ≠ 1 := by
    omega

  have hMinPrime :
      Nat.Prime N.minFac := by

    exact
      Nat.minFac_prime
        hNne1

  have hMinDvd :
      N.minFac ∣ N := by

    exact
      Nat.minFac_dvd N

  have hMinNeTwo :
      N.minFac ≠ 2 := by

    intro hTwo

    have hTwoDvd :
        2 ∣ N := by

      rw [← hTwo]

      exact hMinDvd

    rcases hOdd with ⟨k, hk⟩
    rcases hTwoDvd with ⟨t, ht⟩

    omega

  have hMinSqN :
      N.minFac ^ 2 ≤ N := by

    exact
      Nat.minFac_sq_le_self
        hNpos
        hNotPrime

  have hMinSqM :
      N.minFac * N.minFac ≤ M := by

    have h :
        N.minFac ^ 2 ≤ M := by

      exact
        le_trans
          hMinSqN
          hNM

    simpa [pow_two] using h

  have hMinMem :
      N.minFac ∈ Q := by

    exact
      hComplete.2.2
        N.minFac
        hMinPrime
        hMinNeTwo
        hMinSqM

  exact
    (hNoDiv
      N.minFac
      hMinMem)
      hMinDvd

/--
For m ≥ 1, the two searched numbers differ by exactly 2.
-/
theorem shiftedPlus_eq_shiftedMinus_add_two
    (B m : ℕ)
    (hm : 1 ≤ m) :
    shiftedPlus B m =
      shiftedMinus B m + 2 := by

  unfold shiftedPlus
  unfold shiftedMinus

  omega

/--
For m ≥ 1, the left candidate is already at least 5.
-/
theorem five_le_shiftedMinus
    (B m : ℕ)
    (hm : 1 ≤ m) :
    5 ≤ shiftedMinus B m := by

  unfold shiftedMinus

  omega

/--
For m ≥ 1, the right candidate is already at least 7.
-/
theorem seven_le_shiftedPlus
    (B m : ℕ)
    (hm : 1 ≤ m) :
    7 ≤ shiftedPlus B m := by

  unfold shiftedPlus

  omega

/--
Global correctness of the finite sieve for one twin-candidate pair.

Assume both candidates are odd and Q is the complete odd-prime batch
up to the larger member B+6m+1. Then:

both candidates are prime

iff

no q in Q divides either candidate.
-/
theorem shifted_pair_primes_iff_complete_batch_no_divisors
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hOddMinus :
      Odd (shiftedMinus B m))
    (hOddPlus :
      Odd (shiftedPlus B m))
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus B m)) :
    (Nat.Prime (shiftedMinus B m) ∧
     Nat.Prime (shiftedPlus B m))
    ↔
    ∀ q ∈ Q,
      (¬ q ∣ shiftedMinus B m) ∧
      (¬ q ∣ shiftedPlus B m) := by

  constructor

  · intro hPrimePair q hqMem

    have hValid :
        ValidSieveSet Q :=
      hComplete.1

    have hqPrime :
        Nat.Prime q :=
      (hValid q hqMem).1

    have hqSq :
        q * q ≤ shiftedPlus B m :=
      hComplete.2.1 q hqMem

    constructor

    · intro hqDivMinus

      have hqEq :
          q = shiftedMinus B m := by

        exact
          (Nat.dvd_prime_two_le
            hPrimePair.1
            hqPrime.two_le).mp
            hqDivMinus

      have hGap :
          shiftedPlus B m =
            shiftedMinus B m + 2 := by

        exact
          shiftedPlus_eq_shiftedMinus_add_two
            B m hm

      have hMinus5 :
          5 ≤ shiftedMinus B m := by

        exact
          five_le_shiftedMinus
            B m hm

      rw [hqEq, hGap] at hqSq

      nlinarith

    · intro hqDivPlus

      have hqEq :
          q = shiftedPlus B m := by

        exact
          (Nat.dvd_prime_two_le
            hPrimePair.2
            hqPrime.two_le).mp
            hqDivPlus

      have hPlus7 :
          7 ≤ shiftedPlus B m := by

        exact
          seven_le_shiftedPlus
            B m hm

      rw [hqEq] at hqSq

      nlinarith

  · intro hSurvives

    have hMinusLePlus :
        shiftedMinus B m ≤
          shiftedPlus B m := by

      have hGap :
          shiftedPlus B m =
            shiftedMinus B m + 2 := by

        exact
          shiftedPlus_eq_shiftedMinus_add_two
            B m hm

      omega

    have hMinus2 :
        2 ≤ shiftedMinus B m := by

      have hMinus5 :
          5 ≤ shiftedMinus B m := by

        exact
          five_le_shiftedMinus
            B m hm

      omega

    have hPlus2 :
        2 ≤ shiftedPlus B m := by

      have hPlus7 :
          7 ≤ shiftedPlus B m := by

        exact
          seven_le_shiftedPlus
            B m hm

      omega

    constructor

    · apply
        prime_of_complete_odd_batch_no_divisor
          Q
          (shiftedPlus B m)
          (shiftedMinus B m)
          hComplete
          hMinus2
          hOddMinus
          hMinusLePlus

      intro q hqMem

      exact
        (hSurvives q hqMem).1

    · apply
        prime_of_complete_odd_batch_no_divisor
          Q
          (shiftedPlus B m)
          (shiftedPlus B m)
          hComplete
          hPlus2
          hOddPlus
          (le_refl _)

      intro q hqMem

      exact
        (hSurvives q hqMem).2

/--
The same global correctness theorem expressed entirely in the
compressed kappa-coordinate sieve.
-/
theorem shifted_pair_primes_iff_complete_kappa_sieve
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hOddMinus :
      Odd (shiftedMinus B m))
    (hOddPlus :
      Odd (shiftedPlus B m))
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus B m)) :
    (Nat.Prime (shiftedMinus B m) ∧
     Nat.Prime (shiftedPlus B m))
    ↔
    KappaSurvivesSet
      B
      Q
      (kappaMinus m) := by

  have hPair :
      (Nat.Prime (shiftedMinus B m) ∧
       Nat.Prime (shiftedPlus B m))
      ↔
      ∀ q ∈ Q,
        (¬ q ∣ shiftedMinus B m) ∧
        (¬ q ∣ shiftedPlus B m) := by

    exact
      shifted_pair_primes_iff_complete_batch_no_divisors
        B
        Q
        m
        hm
        hOddMinus
        hOddPlus
        hComplete

  have hKappa :
      KappaSurvivesSet
        B
        Q
        (kappaMinus m)
      ↔
      ∀ q ∈ Q,
        (¬ q ∣ shiftedMinus B m) ∧
        (¬ q ∣ shiftedPlus B m) := by

    exact
      kappaSurvivesSet_iff_shiftedPair_survives_all
        B
        Q
        hComplete.1
        m
        hm

  exact
    hPair.trans
      hKappa.symm

/--
Equivalent global correctness statement in the one-GCD batch form.

Under complete finite sieving up to the square-root boundary:

both candidate numbers are prime

iff

one GCD of their product against the batch product is 1.
-/
theorem shifted_pair_primes_iff_complete_batch_gcd_one
    (B : ℕ)
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hOddMinus :
      Odd (shiftedMinus B m))
    (hOddPlus :
      Odd (shiftedPlus B m))
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus B m)) :
    (Nat.Prime (shiftedMinus B m) ∧
     Nat.Prime (shiftedPlus B m))
    ↔
    Nat.gcd
      (shiftedMinus B m *
       shiftedPlus B m)
      (batchProduct Q) = 1 := by

  have hPrimeKappa :
      (Nat.Prime (shiftedMinus B m) ∧
       Nat.Prime (shiftedPlus B m))
      ↔
      KappaSurvivesSet
        B
        Q
        (kappaMinus m) := by

    exact
      shifted_pair_primes_iff_complete_kappa_sieve
        B
        Q
        m
        hm
        hOddMinus
        hOddPlus
        hComplete

  have hKappaGcd :
      KappaSurvivesSet
        B
        Q
        (kappaMinus m)
      ↔
      Nat.gcd
        (shiftedMinus B m *
         shiftedPlus B m)
        (batchProduct Q) = 1 := by

    exact
      kappaSurvivesSet_iff_batch_gcd_one
        B
        Q
        hComplete.1
        m
        hm

  exact
    hPrimeKappa.trans
      hKappaGcd


/-!
## Specialization to the concrete reference base
-/

/--
If the translation base B is even, then every left candidate
B + 6m - 1 is odd for m ≥ 1.
-/
theorem shiftedMinus_odd_of_even_base
    {B m : ℕ}
    (hB : Even B)
    (hm : 1 ≤ m) :
    Odd (shiftedMinus B m) := by

  rcases hB with ⟨t, ht⟩

  refine
    ⟨t + 3 * m - 1, ?_⟩

  unfold shiftedMinus

  omega

/--
If the translation base B is even, then every right candidate
B + 6m + 1 is odd.
-/
theorem shiftedPlus_odd_of_even_base
    {B m : ℕ}
    (hB : Even B) :
    Odd (shiftedPlus B m) := by

  rcases hB with ⟨t, ht⟩

  refine
    ⟨t + 3 * m, ?_⟩

  unfold shiftedPlus

  omega

/--
The concrete reference base

B = 2,996,863,034,895 * 2^1,290,000

is even.
-/
theorem referenceB_even :
    Even referenceB := by

  unfold referenceB
  unfold structuredBase

  have hE :
      referenceE ≠ 0 := by
    norm_num [referenceE]

  have hPow :
      Even (2 ^ referenceE) := by

    exact
      (Nat.even_pow' hE).2
        (by norm_num)

  exact
    (Nat.even_mul).2
      (Or.inr hPow)

/--
Hence every left candidate in the concrete post-reference search
is odd.
-/
theorem reference_shiftedMinus_odd
    (m : ℕ)
    (hm : 1 ≤ m) :
    Odd (shiftedMinus referenceB m) := by

  exact
    shiftedMinus_odd_of_even_base
      referenceB_even
      hm

/--
And every right candidate in the concrete post-reference search
is odd.
-/
theorem reference_shiftedPlus_odd
    (m : ℕ) :
    Odd (shiftedPlus referenceB m) := by

  exact
    shiftedPlus_odd_of_even_base
      referenceB_even

/--
Specialized finite-sieve correctness theorem for the concrete
reference B.

Once Q contains every odd prime required by the square-root
boundary, the concrete pair is prime exactly when no q in Q
divides either member.
-/
theorem reference_pair_primes_iff_complete_batch_no_divisors
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    (Nat.Prime (shiftedMinus referenceB m) ∧
     Nat.Prime (shiftedPlus referenceB m))
    ↔
    ∀ q ∈ Q,
      (¬ q ∣ shiftedMinus referenceB m) ∧
      (¬ q ∣ shiftedPlus referenceB m) := by

  exact
    shifted_pair_primes_iff_complete_batch_no_divisors
      referenceB
      Q
      m
      hm
      (reference_shiftedMinus_odd m hm)
      (reference_shiftedPlus_odd m)
      hComplete

/--
The same concrete correctness statement in compressed κ coordinates.
-/
theorem reference_pair_primes_iff_complete_kappa_sieve
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    (Nat.Prime (shiftedMinus referenceB m) ∧
     Nat.Prime (shiftedPlus referenceB m))
    ↔
    KappaSurvivesSet
      referenceB
      Q
      (kappaMinus m) := by

  exact
    shifted_pair_primes_iff_complete_kappa_sieve
      referenceB
      Q
      m
      hm
      (reference_shiftedMinus_odd m hm)
      (reference_shiftedPlus_odd m)
      hComplete

/--
Concrete correctness written directly with the explicit forbidden
residue class for every q in Q.
-/
theorem reference_pair_primes_iff_explicit_kappa_classes
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    (Nat.Prime (shiftedMinus referenceB m) ∧
     Nat.Prime (shiftedPlus referenceB m))
    ↔
    ∀ q ∈ Q,
      (¬ Nat.ModEq q
        (kappaMinus m)
        (referenceForbiddenKappaResidue q)) ∧
      (¬ Nat.ModEq q
        (kappaMinus m + 1)
        (referenceForbiddenKappaResidue q)) := by

  have h :=
    reference_pair_primes_iff_complete_kappa_sieve
      Q
      m
      hm
      hComplete

  simpa [
    KappaSurvivesSet,
    KappaSurvivesPrime,
    referenceForbiddenKappaResidue
  ] using h

/--
Concrete correctness in the one-GCD batch form.
-/
theorem reference_pair_primes_iff_complete_batch_gcd_one
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    (Nat.Prime (shiftedMinus referenceB m) ∧
     Nat.Prime (shiftedPlus referenceB m))
    ↔
    Nat.gcd
      (shiftedMinus referenceB m *
       shiftedPlus referenceB m)
      (batchProduct Q) = 1 := by

  exact
    shifted_pair_primes_iff_complete_batch_gcd_one
      referenceB
      Q
      m
      hm
      (reference_shiftedMinus_odd m hm)
      (reference_shiftedPlus_odd m)
      hComplete

/--
The original huge-number GCD test is equivalent to the GCD test
performed only with the batch residue of the concrete reference B.
-/
theorem reference_original_gcd_iff_compressed_residue_gcd
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m) :
    Nat.gcd
      (shiftedMinus referenceB m *
       shiftedPlus referenceB m)
      (batchProduct Q) = 1
    ↔
    Nat.gcd
      ((referenceBatchResidue Q + 6 * m - 1) *
       (referenceBatchResidue Q + 6 * m + 1))
      (batchProduct Q) = 1 := by

  have h :=
    structuredBase_compressed_batch_test
      referenceA
      referenceE
      Q
      m
      hm

  simpa [
    referenceB,
    referenceBatchResidue,
    shiftedMinus,
    shiftedPlus
  ] using h

/--
Main theorem specialized to the concrete reference base.

For the actual reference B and a complete finite sieve batch Q,
the two enormous integers are both prime iff the residue-only
batch computation returns gcd = 1.

Thus the primality decision is preserved all the way from the
original huge integers to the compressed modular computation.
-/
theorem reference_pair_primes_iff_compressed_residue_gcd_one
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    (Nat.Prime (shiftedMinus referenceB m) ∧
     Nat.Prime (shiftedPlus referenceB m))
    ↔
    Nat.gcd
      ((referenceBatchResidue Q + 6 * m - 1) *
       (referenceBatchResidue Q + 6 * m + 1))
      (batchProduct Q) = 1 := by

  have hPrimeGcd :=
    reference_pair_primes_iff_complete_batch_gcd_one
      Q
      m
      hm
      hComplete

  have hCompressed :=
    reference_original_gcd_iff_compressed_residue_gcd
      Q
      m
      hm

  exact
    hPrimeGcd.trans
      hCompressed


/-!
## Final synthesis
-/

/--
A pair (a,b) is a twin-prime pair when both numbers are prime
and their gap is exactly 2.
-/
def TwinPrimePair
    (a b : ℕ) : Prop :=
  Nat.Prime a ∧
  Nat.Prime b ∧
  b = a + 2

/--
When the gap is already known to be 2, proving that (a,b) is a
twin-prime pair is equivalent to proving primality of both members.
-/
theorem twinPrimePair_iff_prime_pair_of_gap_two
    {a b : ℕ}
    (hGap : b = a + 2) :
    TwinPrimePair a b
    ↔
    (Nat.Prime a ∧ Nat.Prime b) := by

  constructor

  · intro h

    exact
      ⟨h.1, h.2.1⟩

  · intro h

    exact
      ⟨h.1, h.2, hGap⟩

/--
For every m ≥ 1, the two concrete post-reference candidates
already have gap 2.
-/
theorem reference_candidate_gap_two
    (m : ℕ)
    (hm : 1 ≤ m) :
    shiftedPlus referenceB m =
      shiftedMinus referenceB m + 2 := by

  exact
    shiftedPlus_eq_shiftedMinus_add_two
      referenceB
      m
      hm

/--
Twin-prime status of the concrete candidate pair is equivalent to
survival of the complete compressed κ-sieve.
-/
theorem reference_twinPrimePair_iff_complete_kappa_sieve
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    TwinPrimePair
      (shiftedMinus referenceB m)
      (shiftedPlus referenceB m)
    ↔
    KappaSurvivesSet
      referenceB
      Q
      (kappaMinus m) := by

  have hTwin :
      TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      (Nat.Prime (shiftedMinus referenceB m) ∧
       Nat.Prime (shiftedPlus referenceB m)) := by

    exact
      twinPrimePair_iff_prime_pair_of_gap_two
        (reference_candidate_gap_two
          m hm)

  exact
    hTwin.trans
      (reference_pair_primes_iff_complete_kappa_sieve
        Q
        m
        hm
        hComplete)

/--
Twin-prime status is equivalent to avoiding, for every q in the
complete batch, the explicit forbidden residue class

κ ≡ -r_q * 2⁻¹ (mod q)

at both adjacent compressed positions κ and κ+1.
-/
theorem reference_twinPrimePair_iff_explicit_kappa_classes
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    TwinPrimePair
      (shiftedMinus referenceB m)
      (shiftedPlus referenceB m)
    ↔
    ∀ q ∈ Q,
      (¬ Nat.ModEq q
        (kappaMinus m)
        (referenceForbiddenKappaResidue q)) ∧
      (¬ Nat.ModEq q
        (kappaMinus m + 1)
        (referenceForbiddenKappaResidue q)) := by

  have hTwin :
      TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      (Nat.Prime (shiftedMinus referenceB m) ∧
       Nat.Prime (shiftedPlus referenceB m)) := by

    exact
      twinPrimePair_iff_prime_pair_of_gap_two
        (reference_candidate_gap_two
          m hm)

  exact
    hTwin.trans
      (reference_pair_primes_iff_explicit_kappa_classes
        Q
        m
        hm
        hComplete)

/--
Twin-prime status is equivalent to the one-GCD test performed on
the original enormous candidate pair.
-/
theorem reference_twinPrimePair_iff_complete_batch_gcd_one
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    TwinPrimePair
      (shiftedMinus referenceB m)
      (shiftedPlus referenceB m)
    ↔
    Nat.gcd
      (shiftedMinus referenceB m *
       shiftedPlus referenceB m)
      (batchProduct Q) = 1 := by

  have hTwin :
      TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      (Nat.Prime (shiftedMinus referenceB m) ∧
       Nat.Prime (shiftedPlus referenceB m)) := by

    exact
      twinPrimePair_iff_prime_pair_of_gap_two
        (reference_candidate_gap_two
          m hm)

  exact
    hTwin.trans
      (reference_pair_primes_iff_complete_batch_gcd_one
        Q
        m
        hm
        hComplete)

/--
FINAL THEOREM.

For the concrete reference

B = 2,996,863,034,895 * 2^1,290,000,

and any complete finite odd-prime sieve batch Q, the two numbers

B + 6m - 1
B + 6m + 1

form a twin-prime pair if and only if the entirely compressed,
residue-only computation

gcd(
  (R + 6m - 1)(R + 6m + 1),
  product(Q)
) = 1

succeeds, where R = B mod product(Q).

This closes the formal chain from the original huge integers to the
compressed modular sieve.
-/
theorem reference_twinPrimePair_iff_compressed_residue_gcd_one
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    TwinPrimePair
      (shiftedMinus referenceB m)
      (shiftedPlus referenceB m)
    ↔
    Nat.gcd
      ((referenceBatchResidue Q + 6 * m - 1) *
       (referenceBatchResidue Q + 6 * m + 1))
      (batchProduct Q) = 1 := by

  have hTwin :
      TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      (Nat.Prime (shiftedMinus referenceB m) ∧
       Nat.Prime (shiftedPlus referenceB m)) := by

    exact
      twinPrimePair_iff_prime_pair_of_gap_two
        (reference_candidate_gap_two
          m hm)

  exact
    hTwin.trans
      (reference_pair_primes_iff_compressed_residue_gcd_one
        Q
        m
        hm
        hComplete)

/--
Bundle of the four equivalent views certified by the development:

1. complete κ-sieve survival;
2. explicit forbidden residue classes;
3. original one-GCD batch test;
4. compressed residue-only one-GCD batch test.

Each is equivalent to the same twin-prime assertion.
-/
theorem reference_final_validation_bundle
    (Q : Finset ℕ)
    (m : ℕ)
    (hm : 1 ≤ m)
    (hComplete :
      CompleteOddPrimeBatchUpTo
        Q
        (shiftedPlus referenceB m)) :
    (TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      KappaSurvivesSet
        referenceB
        Q
        (kappaMinus m))
    ∧
    (TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      ∀ q ∈ Q,
        (¬ Nat.ModEq q
          (kappaMinus m)
          (referenceForbiddenKappaResidue q)) ∧
        (¬ Nat.ModEq q
          (kappaMinus m + 1)
          (referenceForbiddenKappaResidue q)))
    ∧
    (TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      Nat.gcd
        (shiftedMinus referenceB m *
         shiftedPlus referenceB m)
        (batchProduct Q) = 1)
    ∧
    (TwinPrimePair
        (shiftedMinus referenceB m)
        (shiftedPlus referenceB m)
      ↔
      Nat.gcd
        ((referenceBatchResidue Q + 6 * m - 1) *
         (referenceBatchResidue Q + 6 * m + 1))
        (batchProduct Q) = 1) := by

  constructor

  · exact
      reference_twinPrimePair_iff_complete_kappa_sieve
        Q
        m
        hm
        hComplete

  · constructor

    · exact
        reference_twinPrimePair_iff_explicit_kappa_classes
          Q
          m
          hm
          hComplete

    · constructor

      · exact
          reference_twinPrimePair_iff_complete_batch_gcd_one
            Q
            m
            hm
            hComplete

      · exact
          reference_twinPrimePair_iff_compressed_residue_gcd_one
            Q
            m
            hm
            hComplete

end AdditiveSieve
