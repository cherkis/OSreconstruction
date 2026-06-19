/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Jensen's Functional Equation implies Linearity

This file proves that a continuous function D : ℝ → ℝ satisfying Jensen's functional equation
D(s + t) + D(s - t) = 2 * D(s) with D(0) = 0 must be linear: D(t) = t * D(1).

This is a key step in the spectral theorem via RMK approach, needed to prove
that the "odd part" of the quadratic form Q(w + tv) is linear in t.

## Main results

- `jensen_implies_linear_on_rat`: D(q) = q * D(1) for all rationals q
- `jensen_implies_linear`: D(t) = t * D(1) for all reals t (if D is continuous)

## References

- Jordan-von Neumann theorem: Inner product spaces are characterized by parallelogram identity
- Mathlib's `Analysis.InnerProductSpace.OfNorm` for similar reasoning
-/

import Mathlib

open scoped Topology
open Filter

/-- Jensen's functional equation: D(s + t) + D(s - t) = 2 * D(s) -/
def SatisfiesJensen (D : ℝ → ℝ) : Prop :=
  ∀ s t : ℝ, D (s + t) + D (s - t) = 2 * D s

namespace JensenLinearity

/-- D is odd: D(-t) = -D(t) -/
theorem jensen_odd {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ t : ℝ, D (-t) = -D t := by
  intro t
  have h := hJ 0 t
  simp only [zero_add, zero_sub, hD0, mul_zero] at h
  linarith

/-- D(2t) = 2 * D(t) -/
theorem jensen_double {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ t : ℝ, D (2 * t) = 2 * D t := by
  intro t
  have h := hJ t t
  have hrr : t + t = 2 * t := by ring
  rw [hrr, sub_self, hD0, add_zero] at h
  exact h

/-- D(n) = n * D(1) for natural numbers, using strong induction -/
theorem jensen_nat {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ n : ℕ, D n = n * D 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp only [Nat.cast_zero, zero_mul, hD0]
    | 1 => simp only [Nat.cast_one, one_mul]
    | n + 2 =>
      -- Use Jensen with s = n+1, t = 1: D(n+2) + D(n) = 2*D(n+1)
      have h := hJ ((n : ℝ) + 1) 1
      have heq1 : (n : ℝ) + 1 + 1 = n + 2 := by ring
      have heq2 : (n : ℝ) + 1 - 1 = n := by ring
      rw [heq1, heq2] at h
      have ih1 : D ((n + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) * D 1 := ih (n + 1) (by omega)
      have ih0 : D ((n : ℕ) : ℝ) = ((n : ℕ) : ℝ) * D 1 := ih n (by omega)
      push_cast at h ih1 ih0 ⊢
      linarith

/-- D(n) = n * D(1) for all integers -/
theorem jensen_int {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ n : ℤ, D n = n * D 1 := by
  intro n
  cases n with
  | ofNat m => exact_mod_cast jensen_nat hJ hD0 m
  | negSucc m =>
    have h := jensen_nat hJ hD0 (m + 1)
    have hodd := jensen_odd hJ hD0 (m + 1)
    simp only [Int.negSucc_eq, Int.cast_neg]
    push_cast at h hodd ⊢
    linarith

/-- D(n * t) = n * D(t) for natural numbers n -/
theorem jensen_nat_scale {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ (n : ℕ) (t : ℝ), D (n * t) = n * D t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro t
    match n with
    | 0 => simp only [Nat.cast_zero, zero_mul, hD0]
    | 1 => simp only [Nat.cast_one, one_mul]
    | n + 2 =>
      have h := hJ (((n + 1 : ℕ) : ℝ) * t) t
      have heq1 : ((n + 1 : ℕ) : ℝ) * t + t = ((n + 2 : ℕ) : ℝ) * t := by push_cast; ring
      have heq2 : ((n + 1 : ℕ) : ℝ) * t - t = ((n : ℕ) : ℝ) * t := by push_cast; ring
      rw [heq1, heq2] at h
      have ih1 : D (((n + 1 : ℕ) : ℝ) * t) = ((n + 1 : ℕ) : ℝ) * D t := ih (n + 1) (by omega) t
      have ih0 : D (((n : ℕ) : ℝ) * t) = ((n : ℕ) : ℝ) * D t := ih n (by omega) t
      push_cast at h ih1 ih0 ⊢
      linarith

/-- D(n * t) = n * D(t) for integers n -/
theorem jensen_int_scale {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ (n : ℤ) (t : ℝ), D (n * t) = n * D t := by
  intro n t
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact jensen_nat_scale hJ hD0 m t
  | negSucc m =>
    have hpos : D (((m + 1 : ℕ) : ℝ) * t) = ((m + 1 : ℕ) : ℝ) * D t := jensen_nat_scale hJ hD0 (m + 1) t
    simp only [Int.negSucc_eq, Int.cast_neg, neg_mul]
    have hodd := jensen_odd hJ hD0 (((m + 1 : ℕ) : ℝ) * t)
    push_cast at hpos hodd ⊢
    linarith [hpos, hodd]

/-- D(q) = q * D(1) for all rationals q -/
theorem jensen_rat {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) :
    ∀ q : ℚ, D q = q * D 1 := by
  intro q
  have hden_pos : 0 < q.den := q.den_pos
  have hden_ne : (q.den : ℝ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hden_pos
  -- D(den * q) = D(num) = num * D(1)
  -- D(den * q) = den * D(q)
  have h1 : D (((q.den : ℕ) : ℝ) * (q : ℝ)) = ((q.den : ℕ) : ℝ) * D q := jensen_nat_scale hJ hD0 q.den q
  have h2 : ((q.den : ℕ) : ℝ) * (q : ℝ) = (q.num : ℝ) := by
    have hq := q.num_div_den
    have hq' : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      rw [← hq]
      simp only [Rat.cast_def]
    rw [hq']
    field_simp [hden_ne]
  rw [h2] at h1
  have h3 : D (q.num : ℝ) = (q.num : ℝ) * D 1 := jensen_int hJ hD0 q.num
  rw [h3] at h1
  -- h1 : q.num * D 1 = q.den * D q
  -- Solve for D q: D q = (q.num / q.den) * D 1 = q * D 1
  have hgoal : D q = q * D 1 := by
    have hden_pos' : (0 : ℝ) < q.den := by exact_mod_cast hden_pos
    have h1' : D q = (q.num : ℝ) * D 1 / (q.den : ℝ) := by
      field_simp [hden_ne] at h1 ⊢
      linarith [h1]
    rw [h1']
    have hq' : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      rw [← q.num_div_den]
      simp only [Rat.cast_def]
    rw [hq']
    ring
  exact hgoal

/-- Main theorem: If D is continuous and satisfies Jensen with D(0) = 0, then D(t) = t * D(1).
    Uses density of ℚ in ℝ. -/
theorem jensen_implies_linear {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0)
    (hCont : Continuous D) : ∀ t : ℝ, D t = t * D 1 := by
  -- Define f(t) = D(t) and g(t) = t * D(1)
  set f := D with hf_def
  set g := fun t : ℝ => t * D 1 with hg_def
  -- g is continuous
  have hg_cont : Continuous g := continuous_id.mul continuous_const
  -- f and g agree on rationals
  have heq_rat : ∀ q : ℚ, f (q : ℝ) = g (q : ℝ) := fun q => jensen_rat hJ hD0 q
  -- Two continuous functions agreeing on a dense set are equal
  intro t
  have hdense := Rat.isDenseEmbedding_coe_real.dense
  -- Use that continuous functions agreeing on dense set are equal
  have hext : f = g := by
    apply hdense.equalizer hCont hg_cont
    ext q
    exact heq_rat q
  calc f t = g t := congr_fun hext t

/-- Jensen function with D(0) = 0 and bounded on [0,1] is continuous at 0.
    Key insight: D(t) = D(2^n t)/2^n, and D(2^n t) is bounded when 2^n t ∈ [0,1]. -/
theorem jensen_bounded_continuous_at_zero {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0)
    (hBound : ∃ M : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, |D r| ≤ M) : ContinuousAt D 0 := by
  obtain ⟨M, hM⟩ := hBound
  have hM_pos : 0 ≤ M := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, zero_le_one⟩
    specialize hM 0 h0
    simp only [hD0, abs_zero] at hM
    exact hM
  -- D(2t) = 2D(t), so D(t/2^n) = D(t)/2^n
  have hD_double := jensen_double hJ hD0
  have hD_half : ∀ t : ℝ, D (t / 2) = D t / 2 := by
    intro t
    have h := hD_double (t / 2)
    have heq : 2 * (t / 2) = t := by ring
    rw [heq] at h
    linarith
  have hD_pow : ∀ (n : ℕ) (t : ℝ), D (t / 2^n) = D t / 2^n := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have h1 : t / 2^(n+1) = (t / 2^n) / 2 := by
        rw [pow_succ]; ring
      rw [h1, hD_half, ih]
      rw [pow_succ]; ring
  -- D is odd, so |D(-t)| = |D(t)|
  have hD_odd := jensen_odd hJ hD0
  -- For |t| ≤ 1/2^n, we have |D(t)| ≤ M/2^n
  have hsmall : ∀ (n : ℕ) (t : ℝ), |t| ≤ 1 / 2^n → |D t| ≤ M / 2^n := by
    intro n t ht
    have h2n_pos : (0 : ℝ) < 2^n := by positivity
    have h2n_nonneg : (0 : ℝ) ≤ 2^n := le_of_lt h2n_pos
    by_cases ht0 : 0 ≤ t
    · -- t ≥ 0: D(t) = D(2^n t)/2^n where 2^n t ∈ [0, 1]
      have ht_le : t ≤ 1 / 2^n := by rw [abs_of_nonneg ht0] at ht; exact ht
      have hprod_le : 2^n * t ≤ 1 := by
        calc 2^n * t ≤ 2^n * (1 / 2^n) := mul_le_mul_of_nonneg_left ht_le h2n_nonneg
          _ = 1 := by field_simp
      have hrange : 2^n * t ∈ Set.Icc (0 : ℝ) 1 := ⟨mul_nonneg h2n_nonneg ht0, hprod_le⟩
      have hD_bound := hM (2^n * t) hrange
      have ht' : t = (2^n * t) / 2^n := by field_simp
      rw [ht', hD_pow n (2^n * t), abs_div, abs_of_pos h2n_pos]
      exact div_le_div_of_nonneg_right hD_bound h2n_nonneg
    · -- t < 0: use D(-t) = -D(t)
      push Not at ht0
      have ht_neg : -t > 0 := by linarith
      have ht_neg_le : -t ≤ 1 / 2^n := by
        have h1 : |t| = -t := abs_of_neg ht0; linarith
      have hprod_le : 2^n * (-t) ≤ 1 := by
        calc 2^n * (-t) ≤ 2^n * (1 / 2^n) := mul_le_mul_of_nonneg_left ht_neg_le h2n_nonneg
          _ = 1 := by field_simp
      have hrange : 2^n * (-t) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨mul_nonneg h2n_nonneg (le_of_lt ht_neg), hprod_le⟩
      have hD_bound := hM (2^n * (-t)) hrange
      have h' : -t = (2^n * (-t)) / 2^n := by field_simp
      rw [← abs_neg, ← hD_odd, h', hD_pow n (2^n * (-t)), abs_div, abs_of_pos h2n_pos]
      exact div_le_div_of_nonneg_right hD_bound h2n_nonneg
  -- Continuity at 0: for any ε > 0, find δ > 0 such that |t| < δ implies |D(t)| < ε
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- Choose n such that M / 2^n < ε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M / 2^n < ε := by
    by_cases hM0 : M = 0
    · use 0; simp only [hM0, zero_div]; exact hε
    · have hM_pos' : 0 < M := lt_of_le_of_ne hM_pos (Ne.symm hM0)
      -- Since 2^n → ∞, we can find n with 2^n > M/ε, hence M/2^n < ε
      have h2_gt_1 : (2 : ℝ) > 1 := by norm_num
      have htend := tendsto_pow_atTop_atTop_of_one_lt h2_gt_1
      rw [tendsto_atTop_atTop] at htend
      obtain ⟨N, hN⟩ := htend (M / ε + 1)
      use N
      have h2N_pos : (0 : ℝ) < 2^N := by positivity
      have hN' : M / ε + 1 ≤ 2^N := hN N (le_refl N)
      have hkey : M / ε < 2^N := by linarith
      -- M / 2^N < ε ↔ M < ε * 2^N ↔ M / ε < 2^N
      have h2N_ne : (2 : ℝ)^N ≠ 0 := by positivity
      rw [show M / (2 : ℝ)^N < ε ↔ M < ε * 2^N from by
        constructor
        · intro h; calc M = M / 2^N * 2^N := by field_simp
            _ < ε * 2^N := by nlinarith
        · intro h; calc M / 2^N = M * (2^N)⁻¹ := by ring
            _ < ε * 2^N * (2^N)⁻¹ := by nlinarith [inv_pos.mpr h2N_pos]
            _ = ε := by field_simp]
      calc M = M / ε * ε := by field_simp
        _ < 2^N * ε := by nlinarith
        _ = ε * 2^N := by ring
  use 1 / 2^n
  refine ⟨by positivity, fun t ht => ?_⟩
  simp only [hD0, dist_zero_right] at ht ⊢
  exact lt_of_le_of_lt (hsmall n t (le_of_lt ht)) hn

/-- If D satisfies Jensen with D(0) = 0 and is bounded on [0,1], then D is continuous everywhere.
    The key is that the "increment function" f(h) = D(s+h) - D(s) also satisfies Jensen at 0. -/
theorem jensen_bounded_continuous {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0)
    (hBound : ∃ M : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, |D r| ≤ M) : Continuous D := by
  rw [continuous_iff_continuousAt]
  intro s
  -- Define f(h) = D(s + h) - D(s). This satisfies Jensen with f(0) = 0.
  set f : ℝ → ℝ := fun h => D (s + h) - D s with hf_def
  -- f satisfies Jensen: f(a + b) + f(a - b) = 2f(a)
  have hf_jensen : SatisfiesJensen f := by
    intro a b
    simp only [hf_def]
    -- We need: D(s + (a+b)) - D(s) + D(s + (a-b)) - D(s) = 2*(D(s+a) - D(s))
    -- i.e., D(s + (a+b)) + D(s + (a-b)) = 2*D(s+a)
    -- From Jensen at (s+a, b): D((s+a)+b) + D((s+a)-b) = 2*D(s+a)
    have h := hJ (s + a) b
    have heq1 : s + (a + b) = (s + a) + b := by ring
    have heq2 : s + (a - b) = (s + a) - b := by ring
    rw [heq1, heq2]
    linarith
  have hf_zero : f 0 = 0 := by simp [hf_def]
  -- f is bounded on [0, 1] (since D is bounded on bounded intervals)
  -- First show D is bounded on any bounded interval
  obtain ⟨M, hM⟩ := hBound
  have hD_double := jensen_double hJ hD0
  -- D is bounded on [0, 2^n] by 2^n * M
  have hD_bounded_nat : ∀ (n : ℕ), ∀ r ∈ Set.Icc (0 : ℝ) (2^n), |D r| ≤ 2^n * M := by
    intro n
    induction n with
    | zero =>
      intro r hr
      simp only [pow_zero, one_mul] at hr ⊢
      exact hM r hr
    | succ n ih =>
      intro r hr
      simp only [pow_succ] at hr ⊢
      by_cases hr1 : r ≤ 2^n
      · have hr' : r ∈ Set.Icc (0 : ℝ) (2^n) := ⟨hr.1, hr1⟩
        have hM_nn : 0 ≤ M := by
          have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_refl 0, zero_le_one⟩
          have := hM 0 h0; simp only [hD0, abs_zero] at this; exact this
        have h2n_nn : (0 : ℝ) ≤ 2^n := pow_nonneg (by norm_num) n
        calc |D r| ≤ 2^n * M := ih r hr'
          _ ≤ 2^n * 2 * M := by nlinarith
      · -- r ∈ (2^n, 2^{n+1}], so r/2 ∈ (2^{n-1}, 2^n]
        push Not at hr1
        have hr_half : r / 2 ∈ Set.Icc (0 : ℝ) (2^n) := by
          constructor
          · linarith [hr.1]
          · linarith [hr.2]
        have hD_r : D r = 2 * D (r / 2) := by
          have h := hD_double (r / 2)
          have heq : 2 * (r / 2) = r := by ring
          rw [heq] at h; exact h
        rw [hD_r, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        calc 2 * |D (r / 2)| ≤ 2 * (2^n * M) := by nlinarith [ih (r/2) hr_half]
          _ = 2^n * 2 * M := by ring
  -- D is bounded on [-2^n, 2^n] by 2^n * M (using oddness)
  have hD_odd := jensen_odd hJ hD0
  have hD_bounded_sym : ∀ (n : ℕ), ∀ r ∈ Set.Icc (-(2^n : ℝ)) (2^n), |D r| ≤ 2^n * M := by
    intro n r hr
    by_cases hr0 : 0 ≤ r
    · exact hD_bounded_nat n r ⟨hr0, hr.2⟩
    · push Not at hr0
      have hr1 : -(2^n : ℝ) ≤ r := hr.1
      have hr2 : r ≤ 2^n := hr.2
      have hr' : -r ∈ Set.Icc (0 : ℝ) (2^n) := ⟨by linarith, by linarith⟩
      rw [← abs_neg, ← hD_odd]
      exact hD_bounded_nat n (-r) hr'
  -- f is bounded on [0, 1]
  -- Need to find M' such that |f(h)| ≤ M' for h ∈ [0, 1]
  -- |f(h)| = |D(s+h) - D(s)| ≤ |D(s+h)| + |D(s)|
  -- Choose n large enough that |s| ≤ 2^n and |s| + 1 ≤ 2^n
  have hf_bound : ∃ M' : ℝ, ∀ h ∈ Set.Icc (0 : ℝ) 1, |f h| ≤ M' := by
    -- Find n with |s| + 1 ≤ 2^n
    obtain ⟨n, hn⟩ : ∃ n : ℕ, |s| + 1 ≤ 2^n := by
      have h : Tendsto (fun n : ℕ => (2 : ℝ)^n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      rw [Filter.tendsto_atTop_atTop] at h
      obtain ⟨N, hN⟩ := h (|s| + 1)
      exact ⟨N, hN N (le_refl N)⟩
    use 2 * (2^n * M)
    intro h hh
    simp only [hf_def]
    have hs_range : s ∈ Set.Icc (-(2^n : ℝ)) (2^n) := by
      constructor <;> linarith [abs_le.mp (le_of_lt (lt_of_lt_of_le (lt_add_one |s|) hn))]
    have hsh_range : s + h ∈ Set.Icc (-(2^n : ℝ)) (2^n) := by
      have hs1 : -(2^n : ℝ) ≤ s := hs_range.1
      have hh1 : 0 ≤ h := hh.1
      have hh2 : h ≤ 1 := hh.2
      have hs_le_abs : s ≤ |s| := le_abs_self s
      constructor
      · linarith
      · linarith
    calc |D (s + h) - D s| ≤ |D (s + h)| + |D s| := abs_sub _ _
      _ ≤ 2^n * M + 2^n * M := by
          have h1 := hD_bounded_sym n (s + h) hsh_range
          have h2 := hD_bounded_sym n s hs_range
          linarith [abs_nonneg (D (s + h)), abs_nonneg (D s)]
      _ = 2 * (2^n * M) := by ring
  -- Apply continuity at 0 to f
  have hf_cont_zero := jensen_bounded_continuous_at_zero hf_jensen hf_zero hf_bound
  -- Convert to continuity of D at s
  rw [Metric.continuousAt_iff] at hf_cont_zero ⊢
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hf_cont_zero ε hε
  use δ, hδ_pos
  intro t ht
  have heq : s + (t - s) = t := by ring
  have h : D t - D s = f (t - s) := by simp only [hf_def, heq]
  have hf0 : f 0 = 0 := hf_zero
  calc dist (D t) (D s) = |D t - D s| := Real.dist_eq (D t) (D s)
    _ = |f (t - s)| := by rw [h]
    _ = |f (t - s) - 0| := by rw [sub_zero]
    _ = |f (t - s) - f 0| := by rw [hf0]
    _ = dist (f (t - s)) (f 0) := (Real.dist_eq _ _).symm
    _ < ε := hδ (by simpa [Real.dist_eq, sub_zero] using ht)

/-- Main result: Jensen + bounded on interval + D(0) = 0 implies D(t) = t * D(1). -/
theorem jensen_bounded_implies_linear {D : ℝ → ℝ} (hJ : SatisfiesJensen D) (hD0 : D 0 = 0)
    (hBound : ∃ M : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, |D r| ≤ M) : ∀ t : ℝ, D t = t * D 1 := by
  have hCont := jensen_bounded_continuous hJ hD0 hBound
  exact jensen_implies_linear hJ hD0 hCont

end JensenLinearity

/-- Convenience wrapper: continuous Jensen function with D(0) = 0 is linear -/
theorem continuous_jensen_is_linear {D : ℝ → ℝ}
    (hJ : SatisfiesJensen D) (hD0 : D 0 = 0) (hCont : Continuous D) :
    ∀ t : ℝ, D t = t * D 1 :=
  JensenLinearity.jensen_implies_linear hJ hD0 hCont

/-- Convenience wrapper: bounded Jensen function with D(0) = 0 is linear -/
theorem bounded_jensen_is_linear {D : ℝ → ℝ}
    (hJ : SatisfiesJensen D) (hD0 : D 0 = 0)
    (hBound : ∃ M : ℝ, ∀ r ∈ Set.Icc (0 : ℝ) 1, |D r| ≤ M) :
    ∀ t : ℝ, D t = t * D 1 :=
  JensenLinearity.jensen_bounded_implies_linear hJ hD0 hBound
