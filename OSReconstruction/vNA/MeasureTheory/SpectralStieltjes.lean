/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# Spectral Measures via Stieltjes Functions

This file connects spectral measures to Mathlib's `StieltjesFunction` infrastructure.

For a self-adjoint operator T with spectral measure P:
- The function F_x(λ) = ⟨x, P((-∞, λ]) x⟩ is monotone non-decreasing and right-continuous
- This is exactly what `StieltjesFunction` captures
- The associated measure is the spectral measure μ_{x,x}

For the complex spectral measure μ_{x,y}(E) = ⟨x, P(E) y⟩, we use polarization:
  μ_{x,y} = (1/4)[μ_{x+y,x+y} - μ_{x-y,x-y} + i·μ_{x+iy,x+iy} - i·μ_{x-iy,x-iy}]

## Main Definitions

* `SpectralDistribution` - The distribution function F_x(λ) = ⟨x, P((-∞, λ]) x⟩
* `SpectralDistribution.toStieltjes` - Conversion to `StieltjesFunction`
* `SpectralDistribution.toMeasure` - The spectral measure μ_{x,x}

## Main Results

* `SpectralDistribution.measure_Ioc` - μ_{x,x}((a, b]) = F_x(b) - F_x(a)
* `SpectralDistribution.measure_Icc` - μ_{x,x}([a, b]) for closed intervals
* Polarization identity for complex spectral measures

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VII
* Mathlib's `MeasureTheory.Measure.Stieltjes`
-/

noncomputable section

open scoped ENNReal NNReal
open Set Filter Topology MeasureTheory

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Spectral Distribution Functions -/

/-- A spectral distribution function is a right-continuous, monotone non-decreasing function
    F : ℝ → ℝ with F(-∞) = 0 and F(+∞) = some bound.

    This arises from F(λ) = ⟨x, P((-∞, λ]) x⟩ for a spectral measure P and vector x. -/
structure SpectralDistribution where
  /-- The distribution function -/
  toFun : ℝ → ℝ
  /-- Monotone non-decreasing -/
  mono : Monotone toFun
  /-- Right-continuous -/
  right_continuous : ∀ x, ContinuousWithinAt toFun (Set.Ici x) x
  /-- Non-negative values -/
  nonneg : ∀ x, 0 ≤ toFun x
  /-- Bounded above -/
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  /-- F(x) ≤ bound for all x -/
  le_bound : ∀ x, toFun x ≤ bound
  /-- F(x) → 0 as x → -∞ -/
  tendsto_neg_infty : Tendsto toFun atBot (nhds 0)
  /-- F(x) → bound as x → +∞ -/
  tendsto_pos_infty : Tendsto toFun atTop (nhds bound)

namespace SpectralDistribution

variable (F : SpectralDistribution)

/-- Convert a spectral distribution to a Stieltjes function. -/
def toStieltjes : StieltjesFunction ℝ where
  toFun := F.toFun
  mono' := F.mono
  right_continuous' := F.right_continuous

/-- The measure associated to a spectral distribution function.
    This is the unique measure with μ((a, b]) = F(b) - F(a). -/
def toMeasure : Measure ℝ :=
  F.toStieltjes.measure

/-- The measure of a half-open interval (a, b]. -/
theorem measure_Ioc (a b : ℝ) :
    F.toMeasure (Set.Ioc a b) = ENNReal.ofReal (F.toFun b - F.toFun a) := by
  unfold toMeasure toStieltjes
  exact StieltjesFunction.measure_Ioc _ a b

/-- The measure of (a, b] is non-negative because F is monotone. -/
theorem measure_Ioc_nonneg (a b : ℝ) (hab : a ≤ b) :
    0 ≤ F.toFun b - F.toFun a :=
  sub_nonneg.mpr (F.mono hab)

/-- The measure of a closed interval [a, b]. -/
theorem measure_Icc (a b : ℝ) :
    F.toMeasure (Set.Icc a b) =
      ENNReal.ofReal (F.toFun b - Function.leftLim F.toFun a) := by
  unfold toMeasure toStieltjes
  exact StieltjesFunction.measure_Icc _ a b

/-- The measure of {a} (point mass). -/
theorem measure_singleton (a : ℝ) :
    F.toMeasure {a} = ENNReal.ofReal (F.toFun a - Function.leftLim F.toFun a) := by
  unfold toMeasure toStieltjes
  exact StieltjesFunction.measure_singleton _ a

/-- The measure is finite. -/
theorem measure_finite : F.toMeasure Set.univ < ⊤ := by
  have h := StieltjesFunction.measure_univ F.toStieltjes F.tendsto_neg_infty F.tendsto_pos_infty
  rw [toMeasure, h]
  exact ENNReal.ofReal_lt_top

/-- The measure is σ-finite (in fact finite). -/
instance : IsFiniteMeasure F.toMeasure where
  measure_univ_lt_top := F.measure_finite

end SpectralDistribution

/-! ### Construction from Projection-Valued Measures -/

/-- A projection-valued measure (PVM) on ℝ into B(H).

    For a self-adjoint operator T, the spectral theorem gives a unique PVM P with
    T = ∫ λ dP(λ). -/
structure ProjectionValuedMeasure (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection for each Borel set -/
  proj : Set ℝ → (H →L[ℂ] H)
  /-- P(∅) = 0 -/
  empty : proj ∅ = 0
  /-- P(ℝ) = I -/
  univ : proj Set.univ = ContinuousLinearMap.id ℂ H
  /-- P(E)² = P(E) (idempotent) -/
  idempotent : ∀ E, proj E ∘L proj E = proj E
  /-- P(E)* = P(E) (self-adjoint) -/
  selfAdjoint : ∀ E, (proj E).adjoint = proj E
  /-- P(E ∩ F) = P(E) ∘ P(F) (multiplicative) -/
  inter : ∀ E F, proj (E ∩ F) = proj E ∘L proj F
  /-- σ-additivity in the strong operator topology -/
  sigma_additive : ∀ (E : ℕ → Set ℝ), (∀ i j, i ≠ j → Disjoint (E i) (E j)) →
    ∀ x : H, Tendsto (fun n => ∑ i ∈ Finset.range n, proj (E i) x)
      atTop (nhds (proj (⋃ i, E i) x))

namespace ProjectionValuedMeasure

variable [CompleteSpace H] (P : ProjectionValuedMeasure H)

/-- P applied to disjoint sets gives orthogonal ranges: for disjoint E, F,
    ⟨P(E)x, P(F)x⟩ = 0. This follows from P(E ∩ F) = P(E) P(F) and E ∩ F = ∅. -/
theorem proj_orthogonal (x : H) (E F : Set ℝ) (hEF : Disjoint E F) :
    @inner ℂ H _ (P.proj E x) (P.proj F x) = 0 := by
  have h1 : P.proj (E ∩ F) = P.proj E ∘L P.proj F := P.inter E F
  have h2 : E ∩ F = ∅ := Set.disjoint_iff_inter_eq_empty.mp hEF
  rw [h2, P.empty] at h1
  -- P(E) P(F) = 0, so ⟨P(E)x, P(F)x⟩ = ⟨x, P(E)* P(F) x⟩ = ⟨x, P(E) P(F) x⟩ = 0
  -- Use adjoint_inner_right: ⟨x, A* y⟩ = ⟨A x, y⟩
  -- So ⟨P(E)x, P(F)x⟩ = ⟨x, P(E)* P(F)x⟩ (by adjoint_inner_right with A = P(E), y = P(F)x)
  have h3 : @inner ℂ H _ (P.proj E x) (P.proj F x) =
      @inner ℂ H _ x ((P.proj E).adjoint (P.proj F x)) :=
    (ContinuousLinearMap.adjoint_inner_right (P.proj E) x (P.proj F x)).symm
  rw [h3, P.selfAdjoint E]
  -- Now: ⟨x, P(E)(P(F)x)⟩ = ⟨x, (P(E) ∘ P(F)) x⟩ = ⟨x, 0⟩ = 0
  simp only [← ContinuousLinearMap.comp_apply, ← h1, ContinuousLinearMap.zero_apply,
    inner_zero_right]

/-- For a sequence of disjoint sets E_n, the partial sums ∑_{k<n} P(E_k) x form a Cauchy sequence. -/
theorem proj_disjoint_cauchy (x : H) (E : ℕ → Set ℝ) (hE : ∀ i j, i ≠ j → Disjoint (E i) (E j)) :
    CauchySeq (fun n => ∑ i ∈ Finset.range n, P.proj (E i) x) := by
  -- The sequence converges by σ-additivity, hence is Cauchy
  exact (P.sigma_additive E hE x).cauchySeq

/-- Finite additivity: P(A ∪ B) x = P(A) x + P(B) x for disjoint A, B.
    Derived from σ-additivity using the sequence A, B, ∅, ∅, ... -/
theorem proj_finite_additive (x : H) (A B : Set ℝ) (hAB : Disjoint A B) :
    P.proj (A ∪ B) x = P.proj A x + P.proj B x := by
  -- Define the sequence: A, B, ∅, ∅, ...
  set E : ℕ → Set ℝ := fun | 0 => A | 1 => B | (_ + 2) => ∅ with hE_def
  -- Pairwise disjoint
  have hE_disj : ∀ i j, i ≠ j → Disjoint (E i) (E j) := by
    intro i j hij
    match i, j with
    | 0, 0 => exact absurd rfl hij
    | 0, 1 => exact hAB
    | 1, 0 => exact hAB.symm
    | 0, _ + 2 | 1, _ + 2 | _ + 2, _ + 2 => exact disjoint_bot_right
    | _ + 2, 0 | _ + 2, 1 => exact disjoint_bot_left
    | 1, 1 => exact absurd rfl hij
  -- ⋃ E = A ∪ B
  have hE_union : ⋃ i, E i = A ∪ B := by
    ext z; simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      match i with
      | 0 => exact Or.inl hi
      | 1 => exact Or.inr hi
      | _ + 2 => simp [E] at hi
    · rintro (ha | hb)
      · exact ⟨0, ha⟩
      · exact ⟨1, hb⟩
  -- σ-additivity gives convergence
  have hσ := P.sigma_additive E hE_disj x
  rw [hE_union] at hσ
  -- Partial sums stabilize at P(A)x + P(B)x for n ≥ 2
  have h_tail : ∀ k, k ≥ 2 → P.proj (E k) x = 0 := by
    intro k hk
    have : E k = ∅ := by match k, hk with | _ + 2, _ => rfl
    rw [this, P.empty, ContinuousLinearMap.zero_apply]
  -- Prove stability by reducing to the case n = m + 2
  suffices hstab : ∀ m, ∑ i ∈ Finset.range (m + 2), P.proj (E i) x =
      P.proj A x + P.proj B x by
    -- Eventually constant → converges to constant
    have hevt : (fun n => ∑ i ∈ Finset.range n, P.proj (E i) x) =ᶠ[atTop]
        fun _ => P.proj A x + P.proj B x := by
      filter_upwards [Filter.eventually_ge_atTop 2] with n hn
      rw [show n = (n - 2) + 2 from by omega]
      exact hstab _
    exact tendsto_nhds_unique hσ (tendsto_const_nhds.congr' hevt.symm)
  -- Induction on m
  intro m
  induction m with
  | zero => simp [Finset.sum_range_succ, E]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 from by ring, Finset.sum_range_succ, ih,
        h_tail (k + 2) (by omega), add_zero]

/-- Helper: E is decreasing for any gap, not just consecutive indices. -/
theorem _root_.decreasing_chain_le {E : ℕ → Set ℝ} (hE_dec : ∀ n, E (n + 1) ⊆ E n)
    {i j : ℕ} (hij : i ≤ j) : E j ⊆ E i := by
  induction hij with
  | refl => exact Subset.rfl
  | step _ ih => exact (hE_dec _).trans ih

/-- For decreasing sets E_n with ⋂ E_n = S, P(E_n) x → P(S) x in the norm topology.

    This is the monotone convergence theorem for projection-valued measures.
    The proof uses σ-additivity on the "difference" sets F_k = E_k \ E_{k+1},
    telescoping sums, and finite additivity derived from σ-additivity. -/
theorem proj_decreasing_tendsto (x : H) (E : ℕ → Set ℝ) (S : Set ℝ)
    (hE_dec : ∀ n, E (n + 1) ⊆ E n)
    (hE_inter : ⋂ n, E n = S) :
    Tendsto (fun n => P.proj (E n) x) atTop (nhds (P.proj S x)) := by
  -- S ⊆ E_n for all n
  have hS_sub : ∀ n, S ⊆ E n := fun n => hE_inter ▸ Set.iInter_subset E n
  -- Define difference sets F_k = E_k \ E_{k+1}
  set F : ℕ → Set ℝ := fun k => E k \ E (k + 1) with hF_def
  -- F_k are pairwise disjoint
  have hF_disj : ∀ i j, i ≠ j → Disjoint (F i) (F j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hz hzj
    -- hz : z ∈ E i \ E (i+1), hzj : z ∈ E j \ E (j+1)
    rcases lt_or_gt_of_ne hij with h | h
    · -- i < j: E j ⊆ E (i+1), so z ∈ E (i+1), contradicts hz.2
      exact hz.2 (decreasing_chain_le hE_dec (show i + 1 ≤ j by omega) hzj.1)
    · -- j < i: E i ⊆ E (j+1), so z ∈ E (j+1), contradicts hzj.2
      exact hzj.2 (decreasing_chain_le hE_dec (show j + 1 ≤ i by omega) hz.1)
  -- Finite additivity: P(E_k)x = P(E_{k+1})x + P(F_k)x
  have htelesc : ∀ k, P.proj (E k) x = P.proj (E (k + 1)) x + P.proj (F k) x := by
    intro k
    rw [show E k = E (k + 1) ∪ (E k \ E (k + 1)) from (Set.union_diff_cancel (hE_dec k)).symm]
    exact P.proj_finite_additive x _ _ (Set.disjoint_left.mpr fun _ hz hzd => hzd.2 hz)
  -- Telescoping: ∑_{k<n} P(F_k)x = P(E_0)x - P(E_n)x
  have htelesc_sum : ∀ n, ∑ k ∈ Finset.range n, P.proj (F k) x =
      P.proj (E 0) x - P.proj (E n) x := by
    intro n; induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, (sub_eq_of_eq_add (htelesc m)).symm]
      abel
  -- P(E_n)x = P(E_0)x - ∑_{k<n} P(F_k)x
  have hEn_eq : ∀ n, P.proj (E n) x =
      P.proj (E 0) x - ∑ k ∈ Finset.range n, P.proj (F k) x := by
    intro n; rw [htelesc_sum n]; abel
  -- ⋃_k F_k = E_0 \ S
  have hF_union : ⋃ k, F k = E 0 \ S := by
    ext z; simp only [Set.mem_iUnion, Set.mem_diff]
    constructor
    · rintro ⟨k, hzk, hzk'⟩
      exact ⟨decreasing_chain_le hE_dec (Nat.zero_le k) hzk,
             fun hzS => hzk' (hS_sub (k + 1) hzS)⟩
    · rintro ⟨hz0, hzS⟩
      rw [← hE_inter] at hzS
      simp only [Set.mem_iInter] at hzS
      push Not at hzS
      -- Find smallest k with z ∉ E k
      haveI : DecidablePred (fun m => z ∉ E m) := Classical.decPred _
      have hexists : ∃ m, z ∉ E m := hzS
      set k := Nat.find hexists
      have hk_spec : z ∉ E k := Nat.find_spec hexists
      have hk_pos : k ≠ 0 := by
        intro hk0; rw [hk0] at hk_spec; exact hk_spec hz0
      have hk_prev : z ∈ E (k - 1) := by
        by_contra hc; exact Nat.find_min hexists (by omega) hc
      exact ⟨k - 1, hk_prev, by rwa [show k - 1 + 1 = k from by omega]⟩
  -- E_0 = S ∪ (E_0 \ S), disjoint, so P(E_0\S)x = P(E_0)x - P(S)x
  have hE0_decomp : P.proj (E 0) x = P.proj S x + P.proj (E 0 \ S) x := by
    have := P.proj_finite_additive x S (E 0 \ S)
      (Set.disjoint_left.mpr (fun _ hzS hzd => hzd.2 hzS))
    rwa [Set.union_diff_cancel (hS_sub 0)] at this
  -- σ-additivity: ∑_{k<N} P(F_k)x → P(E_0 \ S)x
  have hF_sigma := P.sigma_additive F hF_disj x
  rw [hF_union] at hF_sigma
  -- P(E_n)x = P(E_0)x - ∑ P(F_k)x, and ∑ → P(E_0\S)x
  -- So P(E_0)x - ∑ → P(E_0)x - P(E_0\S)x = P(S)x
  have h_sub := tendsto_const_nhds (x := P.proj (E 0) x) |>.sub hF_sigma
  -- h_sub : P(E_0)x - ∑... → P(E_0)x - P(E_0\S)x
  -- P(E_0)x - P(E_0\S)x = P(S)x by hE0_decomp
  have h_eq : P.proj (E 0) x - P.proj (E 0 \ S) x = P.proj S x :=
    sub_eq_iff_eq_add.mpr hE0_decomp
  rw [h_eq] at h_sub
  exact h_sub.congr (fun n => (hEn_eq n).symm)

/-- ⟨x, P(E)x⟩ is real and non-negative for any projection P(E). -/
theorem inner_proj_nonneg (x : H) (E : Set ℝ) :
    0 ≤ (@inner ℂ H _ x (P.proj E x)).re := by
  -- P(E) is a self-adjoint idempotent, hence ⟨x, P(E)x⟩ = ‖P(E)x‖² ≥ 0
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  -- ⟨x, P(E)x⟩ = ⟨P(E)*x, P(E)x⟩ = ⟨P(E)x, P(E)x⟩ = ‖P(E)x‖²
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, inner_self_eq_norm_sq_to_K]
  norm_cast
  exact sq_nonneg _

/-- ⟨x, P(E)x⟩ is actually real (imaginary part is 0). -/
theorem inner_proj_real (x : H) (E : Set ℝ) :
    (@inner ℂ H _ x (P.proj E x)).im = 0 := by
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- ⟨x, P(E)x⟩.re = ‖P(E)x‖² for projections. -/
theorem inner_proj_eq_norm_sq (x : H) (E : Set ℝ) :
    (@inner ℂ H _ x (P.proj E x)).re = ‖P.proj E x‖^2 := by
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, sq]
  exact inner_self_eq_norm_mul_norm (𝕜 := ℂ) (P.proj E x)

/-- ⟨x, P(E)x⟩ ≤ ‖x‖² because P(E) ≤ I. -/
theorem inner_proj_le_norm_sq (x : H) (E : Set ℝ) :
    (@inner ℂ H _ x (P.proj E x)).re ≤ ‖x‖^2 := by
  have h1 : (P.proj E).adjoint = P.proj E := P.selfAdjoint E
  have h2 : P.proj E ∘L P.proj E = P.proj E := P.idempotent E
  have h3 : @inner ℂ H _ x (P.proj E x) = @inner ℂ H _ (P.proj E x) (P.proj E x) := by
    conv_lhs => rw [← h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left, h1]
  rw [h3, inner_self_eq_norm_sq_to_K]
  norm_cast
  -- ‖P(E)x‖² ≤ ‖x‖² because P(E) is a contraction (as a projection)
  have hP_contraction : ‖P.proj E x‖ ≤ ‖x‖ := by
    -- P(E) = P(E)² implies ‖P(E)x‖ ≤ ‖x‖
    by_cases hPx : P.proj E x = 0
    · rw [hPx, norm_zero]
      exact norm_nonneg x
    · have hPx_pos : 0 < ‖P.proj E x‖ := norm_pos_iff.mpr hPx
      have hcs : (@inner ℂ H _ x (P.proj E x)).re ≤ ‖x‖ * ‖P.proj E x‖ := by
        calc (@inner ℂ H _ x (P.proj E x)).re
            ≤ |(@inner ℂ H _ x (P.proj E x)).re| := le_abs_self _
          _ ≤ ‖@inner ℂ H _ x (P.proj E x)‖ := Complex.abs_re_le_norm _
          _ ≤ ‖x‖ * ‖P.proj E x‖ := norm_inner_le_norm x (P.proj E x)
      rw [h3] at hcs
      -- Now hcs : (@inner ℂ H _ (P.proj E x) (P.proj E x)).re ≤ ‖x‖ * ‖P.proj E x‖
      -- Use inner_self_eq_norm_mul_norm: re ⟪y, y⟫ = ‖y‖ * ‖y‖
      have h5 : (@inner ℂ H _ (P.proj E x) (P.proj E x)).re = ‖P.proj E x‖ * ‖P.proj E x‖ := by
        simp only [← RCLike.re_to_complex]
        exact inner_self_eq_norm_mul_norm (P.proj E x)
      rw [h5] at hcs
      -- hcs : ‖P.proj E x‖ * ‖P.proj E x‖ ≤ ‖x‖ * ‖P.proj E x‖
      calc ‖P.proj E x‖ = (‖P.proj E x‖ * ‖P.proj E x‖) / ‖P.proj E x‖ := by
            field_simp [hPx_pos.ne']
        _ ≤ (‖x‖ * ‖P.proj E x‖) / ‖P.proj E x‖ := by
            apply div_le_div_of_nonneg_right hcs hPx_pos.le
        _ = ‖x‖ := by field_simp [hPx_pos.ne']
  calc ‖P.proj E x‖^2 ≤ ‖x‖^2 := sq_le_sq' (by linarith [norm_nonneg (P.proj E x)])
                                            hP_contraction

/-- Projections are contractions: ‖P(E)y‖ ≤ ‖y‖. -/
theorem proj_contraction (y : H) (E : Set ℝ) : ‖P.proj E y‖ ≤ ‖y‖ := by
  have h := P.inner_proj_le_norm_sq y E
  rw [P.inner_proj_eq_norm_sq] at h
  -- h : ‖P.proj E y‖ ^ 2 ≤ ‖y‖ ^ 2, want ‖P.proj E y‖ ≤ ‖y‖
  by_contra h_neg
  push Not at h_neg
  -- h_neg : ‖y‖ < ‖P.proj E y‖, so |‖y‖| < |‖P.proj E y‖|, so ‖y‖² < ‖P.proj E y‖²
  have : ‖y‖ ^ 2 < ‖P.proj E y‖ ^ 2 := by
    rwa [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
  linarith

/-- For E ⊆ F, ‖P(E)x‖ ≤ ‖P(F)x‖ (monotonicity of projection norms). -/
theorem proj_norm_mono (x : H) (E F : Set ℝ) (hEF : E ⊆ F) :
    ‖P.proj E x‖ ≤ ‖P.proj F x‖ := by
  have h1 : P.proj E = P.proj E ∘L P.proj F := by
    rw [← P.inter, Set.inter_eq_left.mpr hEF]
  calc ‖P.proj E x‖ = ‖P.proj E (P.proj F x)‖ := by
        conv_lhs => rw [h1]; simp [ContinuousLinearMap.comp_apply]
    _ ≤ ‖P.proj F x‖ := P.proj_contraction _ _

/-- The spectral distribution function for a vector x:
    F_x(t) = ⟨x, P((-∞, t]) x⟩ -/
def distributionFunction (x : H) : SpectralDistribution where
  toFun := fun t => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
  mono := by
    intro a b hab
    -- Simplify the function application
    simp only
    -- Use inner_proj_eq_norm_sq: ⟨x, P(E) x⟩.re = ‖P(E) x‖²
    rw [P.inner_proj_eq_norm_sq, P.inner_proj_eq_norm_sq]
    -- Goal: ‖P(Iic a) x‖² ≤ ‖P(Iic b) x‖²
    have hsub : Set.Iic a ⊆ Set.Iic b := Set.Iic_subset_Iic.mpr hab
    -- P(Iic a) = P(Iic a ∩ Iic b) = P(Iic a) ∘ P(Iic b)
    have h1 : Set.Iic a ∩ Set.Iic b = Set.Iic a := Set.inter_eq_left.mpr hsub
    have h2 : P.proj (Set.Iic a) = P.proj (Set.Iic a) ∘L P.proj (Set.Iic b) := by
      rw [← P.inter, h1]
    -- P(Iic a) x = P(Iic a) (P(Iic b) x)
    have h3 : P.proj (Set.Iic a) x = P.proj (Set.Iic a) (P.proj (Set.Iic b) x) := by
      conv_lhs => rw [h2]
      simp only [ContinuousLinearMap.comp_apply]
    -- Projections are contractions: ‖P(E) y‖ ≤ ‖y‖
    have hcontract : ‖P.proj (Set.Iic a) (P.proj (Set.Iic b) x)‖ ≤ ‖P.proj (Set.Iic b) x‖ := by
      have hP := P.idempotent (Set.Iic a)
      have hPsa := P.selfAdjoint (Set.Iic a)
      set y := P.proj (Set.Iic b) x with hy_def
      by_cases hy : P.proj (Set.Iic a) y = 0
      · rw [hy_def, hy, norm_zero]
        exact norm_nonneg _
      · have hpos : 0 < ‖P.proj (Set.Iic a) y‖ := norm_pos_iff.mpr hy
        have hinner : (@inner ℂ H _ y (P.proj (Set.Iic a) y)).re = ‖P.proj (Set.Iic a) y‖^2 :=
          P.inner_proj_eq_norm_sq y (Set.Iic a)
        have hcs : (@inner ℂ H _ y (P.proj (Set.Iic a) y)).re ≤ ‖y‖ * ‖P.proj (Set.Iic a) y‖ := by
          calc (@inner ℂ H _ y (P.proj (Set.Iic a) y)).re
              ≤ |(@inner ℂ H _ y (P.proj (Set.Iic a) y)).re| := le_abs_self _
            _ ≤ ‖@inner ℂ H _ y (P.proj (Set.Iic a) y)‖ := Complex.abs_re_le_norm _
            _ ≤ ‖y‖ * ‖P.proj (Set.Iic a) y‖ := norm_inner_le_norm y (P.proj (Set.Iic a) y)
        rw [hinner] at hcs
        calc ‖P.proj (Set.Iic a) y‖
            = ‖P.proj (Set.Iic a) y‖^2 / ‖P.proj (Set.Iic a) y‖ := by field_simp [hpos.ne']
          _ ≤ (‖y‖ * ‖P.proj (Set.Iic a) y‖) / ‖P.proj (Set.Iic a) y‖ := by
              apply div_le_div_of_nonneg_right hcs hpos.le
          _ = ‖y‖ := by field_simp [hpos.ne']
    -- ‖P(Iic a) x‖² ≤ ‖P(Iic b) x‖²
    rw [h3]
    apply sq_le_sq' (by linarith [norm_nonneg (P.proj (Set.Iic a) (P.proj (Set.Iic b) x))])
    exact hcontract
  right_continuous := by
    intro t
    -- Step 1: Sequential convergence P(Iic(t + 1/(n+1)))x → P(Iic t)x
    set E := fun n : ℕ => Set.Iic (t + 1 / ((↑n : ℝ) + 1))
    have hE_dec : ∀ n, E (n + 1) ⊆ E n := by
      intro n; simp only [E]; apply Set.Iic_subset_Iic.mpr
      have h1 : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
      linarith [one_div_le_one_div_of_le h1 (by push_cast; linarith : (↑n : ℝ) + 1 ≤ ↑(n + 1) + 1)]
    have hE_inter : ⋂ n, E n = Set.Iic t := by
      ext s; simp only [Set.mem_iInter, Set.mem_Iic, E]
      refine ⟨fun h => ?_, fun hs n => le_add_of_le_of_nonneg hs (by positivity)⟩
      by_contra hst; push Not at hst
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (s - t))
      have hpos : (0 : ℝ) < s - t := sub_pos.mpr hst
      have h1 : 1 < (↑n : ℝ) * (s - t) := by rwa [div_lt_iff₀ hpos] at hn
      have h2 : (s - t) * ((↑n : ℝ) + 1) ≤ 1 :=
        (le_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1)).mp (by linarith [h n])
      nlinarith [mul_comm (s - t) (↑n : ℝ)]
    have hconv := P.proj_decreasing_tendsto x E (Set.Iic t) hE_dec hE_inter
    -- Compose with continuous map y ↦ ⟨x, y⟩.re
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => (@inner ℂ H _ x (P.proj (E n) x)).re)
        atTop (nhds ((@inner ℂ H _ x (P.proj (Set.Iic t) x)).re)) :=
      hcont.continuousAt.tendsto.comp hconv
    -- Step 2: ContinuousWithinAt from monotonicity + sequential convergence
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    rw [Metric.tendsto_atTop] at hseq
    obtain ⟨N, hN⟩ := hseq ε hε
    refine ⟨1 / ((↑N : ℝ) + 1), by positivity, fun s hs hds => ?_⟩
    have hst : t ≤ s := hs
    have hsd : s < t + 1 / ((↑N : ℝ) + 1) := by
      rw [Real.dist_eq, abs_lt] at hds; linarith [hds.2]
    -- f(t) ≤ f(s) ≤ f(t + 1/(N+1)) by proj_norm_mono + inner_proj_eq_norm_sq
    have h_lo : (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re ≤
        (@inner ℂ H _ x (P.proj (Set.Iic s) x)).re := by
      rw [P.inner_proj_eq_norm_sq, P.inner_proj_eq_norm_sq]
      have := P.proj_norm_mono x _ _ (Set.Iic_subset_Iic.mpr hst)
      nlinarith [norm_nonneg (P.proj (Set.Iic t) x)]
    have h_hi : (@inner ℂ H _ x (P.proj (Set.Iic s) x)).re ≤
        (@inner ℂ H _ x (P.proj (E N) x)).re := by
      rw [P.inner_proj_eq_norm_sq, P.inner_proj_eq_norm_sq]
      have := P.proj_norm_mono x _ _ (Set.Iic_subset_Iic.mpr hsd.le)
      nlinarith [norm_nonneg (P.proj (Set.Iic s) x)]
    -- |f(s) - f(t)| = f(s) - f(t) ≤ f(N) - f(t) = |f(N) - f(t)| < ε
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    have hNN := hN N le_rfl; rw [Real.dist_eq] at hNN
    have h_nn : 0 ≤ (@inner ℂ H _ x (P.proj (E N) x)).re -
        (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re := by linarith
    rw [abs_of_nonneg h_nn] at hNN
    linarith
  nonneg := fun t => P.inner_proj_nonneg x (Set.Iic t)
  bound := ‖x‖^2
  bound_nonneg := sq_nonneg _
  le_bound := fun t => P.inner_proj_le_norm_sq x (Set.Iic t)
  tendsto_neg_infty := by
    -- P(Iic(-n))x → P(∅)x = 0 via proj_decreasing_tendsto
    set f := fun t : ℝ => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
    -- f is monotone
    have f_mono : Monotone f := by
      intro a b hab; simp only [f]
      rw [P.inner_proj_eq_norm_sq, P.inner_proj_eq_norm_sq]
      have := P.proj_norm_mono x _ _ (Set.Iic_subset_Iic.mpr hab)
      nlinarith [norm_nonneg (P.proj (Set.Iic a) x)]
    -- Sequential convergence: f(-n) → 0
    set E := fun n : ℕ => Set.Iic (-(↑n : ℝ))
    have hE_dec : ∀ n, E (n + 1) ⊆ E n := by
      intro n; simp only [E]; apply Set.Iic_subset_Iic.mpr; push_cast; linarith
    have hE_inter : ⋂ n, E n = ∅ := by
      ext s; simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, E]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_gt (-s)
        linarith [h n]
      · intro h; exact h.elim
    have hconv := P.proj_decreasing_tendsto x E ∅ hE_dec hE_inter
    rw [P.empty, ContinuousLinearMap.zero_apply] at hconv
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => f (-(↑n : ℝ))) atTop (nhds 0) := by
      have := hcont.continuousAt.tendsto.comp hconv
      simp only [inner_zero_right, Complex.zero_re, Function.comp_def] at this
      exact this
    -- Use tendsto_order for atBot filter
    rw [tendsto_order]
    constructor
    · -- For a' < 0, eventually f(s) > a' (trivially since f ≥ 0)
      intro a' ha'
      rw [Filter.eventually_atBot]
      exact ⟨0, fun s _ => lt_of_lt_of_le ha' (P.inner_proj_nonneg x (Set.Iic s))⟩
    · -- For a' > 0, eventually f(s) < a' (since f(-n) → 0 and f monotone)
      intro a' ha'
      rw [Filter.eventually_atBot]
      have hexN : ∃ N : ℕ, f (-(↑N : ℝ)) < a' := by
        by_contra h; push Not at h
        exact absurd (ge_of_tendsto' hseq h) (not_le.mpr ha')
      obtain ⟨N, hN⟩ := hexN
      exact ⟨-(↑N : ℝ), fun s hs => lt_of_le_of_lt (f_mono hs) hN⟩
  tendsto_pos_infty := by
    -- P(Iic(n))x → P(ℝ)x = x via complement: P(Ioi(n))x → 0
    set f := fun t : ℝ => (@inner ℂ H _ x (P.proj (Set.Iic t) x)).re
    -- f is monotone
    have f_mono : Monotone f := by
      intro a b hab; simp only [f]
      rw [P.inner_proj_eq_norm_sq, P.inner_proj_eq_norm_sq]
      have := P.proj_norm_mono x _ _ (Set.Iic_subset_Iic.mpr hab)
      nlinarith [norm_nonneg (P.proj (Set.Iic a) x)]
    -- Complement sets Ioi(n) are decreasing with ⋂ = ∅
    set G := fun n : ℕ => Set.Ioi (↑n : ℝ)
    have hG_dec : ∀ n, G (n + 1) ⊆ G n := by
      intro n; simp only [G]; apply Set.Ioi_subset_Ioi; push_cast; linarith
    have hG_inter : ⋂ n, G n = ∅ := by
      ext s; simp only [Set.mem_iInter, Set.mem_Ioi, Set.mem_empty_iff_false, G]
      constructor
      · intro h; obtain ⟨n, hn⟩ := exists_nat_gt s; linarith [h n]
      · intro h; exact h.elim
    have hG_conv := P.proj_decreasing_tendsto x G ∅ hG_dec hG_inter
    rw [P.empty, ContinuousLinearMap.zero_apply] at hG_conv
    -- P(Iic n)x = x - P(Ioi n)x by finite additivity
    have h_decomp : ∀ n : ℕ, P.proj (Set.Iic (↑n : ℝ)) x + P.proj (Set.Ioi (↑n : ℝ)) x = x := by
      intro n
      have hunion : Set.Iic (↑n : ℝ) ∪ Set.Ioi (↑n : ℝ) = Set.univ := Set.Iic_union_Ioi
      have hdisj : Disjoint (Set.Iic (↑n : ℝ)) (Set.Ioi (↑n : ℝ)) :=
        Set.disjoint_left.mpr fun z hz hzoi =>
          not_lt.mpr (Set.mem_Iic.mp hz) (Set.mem_Ioi.mp hzoi)
      have := P.proj_finite_additive x _ _ hdisj
      rw [hunion, P.univ, ContinuousLinearMap.id_apply] at this
      exact this.symm
    -- P(Iic n)x → x (since P(Ioi n)x → 0)
    have hconv : Tendsto (fun n : ℕ => P.proj (Set.Iic (↑n : ℝ)) x) atTop (nhds x) := by
      have heq : (fun (n : ℕ) => P.proj (Set.Iic (↑n : ℝ)) x) = fun n => x - P.proj (G n) x := by
        ext n; simp only [G]; exact eq_sub_iff_add_eq.mpr (h_decomp n)
      rw [heq]; simpa [sub_zero] using tendsto_const_nhds (x := x) |>.sub hG_conv
    -- Compose with continuous inner product to get f(n) → ‖x‖²
    have hcont : Continuous (fun y : H => (@inner ℂ H _ x y).re) := by fun_prop
    have hseq : Tendsto (fun n : ℕ => f (↑n : ℝ)) atTop (nhds (‖x‖^2)) := by
      have h1 := hcont.continuousAt.tendsto.comp hconv
      simp only [Function.comp_def] at h1
      have hlim : (@inner ℂ H _ x x).re = ‖x‖ ^ 2 := by
        have h := P.inner_proj_eq_norm_sq x Set.univ
        rw [P.univ, ContinuousLinearMap.id_apply] at h
        exact h
      rwa [hlim] at h1
    -- Use tendsto_order: for monotone f bounded above by ‖x‖² with f(n) → ‖x‖²
    rw [tendsto_order]
    constructor
    · -- For a' < ‖x‖², eventually f(s) > a'
      intro a' ha'
      rw [Filter.eventually_atTop]
      have hexN : ∃ N : ℕ, a' < f ↑N := by
        by_contra h; push Not at h
        exact absurd (le_of_tendsto' hseq h) (not_le.mpr ha')
      obtain ⟨N, hN⟩ := hexN
      exact ⟨↑N, fun s hs => lt_of_lt_of_le hN (f_mono hs)⟩
    · -- For a' > ‖x‖², eventually f(s) < a' (since f ≤ ‖x‖² always)
      intro a' ha'
      rw [Filter.eventually_atTop]
      exact ⟨0, fun s _ => lt_of_le_of_lt (P.inner_proj_le_norm_sq x (Set.Iic s)) ha'⟩

/-- The spectral measure μ_{x,x} for a vector x. -/
def diagonalMeasure (x : H) : Measure ℝ :=
  (P.distributionFunction x).toMeasure

/-- The complex spectral measure μ_{x,y} defined via polarization. -/
def complexMeasure (x y : H) (E : Set ℝ) : ℂ :=
  -- Polarization identity:
  -- 4⟨x, Py⟩ = ⟨x+y, P(x+y)⟩ - ⟨x-y, P(x-y)⟩ - i⟨x+iy, P(x+iy)⟩ + i⟨x-iy, P(x-iy)⟩
  let μpp := (P.diagonalMeasure (x + y) E).toReal
  let μmm := (P.diagonalMeasure (x - y) E).toReal
  let μpi := (P.diagonalMeasure (x + Complex.I • y) E).toReal
  let μmi := (P.diagonalMeasure (x - Complex.I • y) E).toReal
  (1/4 : ℂ) * (μpp - μmm - Complex.I * μpi + Complex.I * μmi)

/-- The spectral inner product measure for a vector z:
    E ↦ ENNReal.ofReal(⟨z, P(E)z⟩.re).
    This is a σ-additive measure that equals the diagonal spectral measure. -/
noncomputable def spectralInnerMeasure (z : H) : Measure ℝ :=
  Measure.ofMeasurable
    (fun E _ => ENNReal.ofReal ((@inner ℂ H _ z (P.proj E z)).re))
    (by simp [P.empty])
    (fun E _hE_meas hE_disj => by
      show ENNReal.ofReal ((@inner ℂ H _ z (P.proj (⋃ n, E n) z)).re) =
        ∑' n, ENNReal.ofReal ((@inner ℂ H _ z (P.proj (E n) z)).re)
      have h_nonneg : ∀ n, 0 ≤ (@inner ℂ H _ z (P.proj (E n) z)).re :=
        fun n => P.inner_proj_nonneg z (E n)
      have h_sigma := P.sigma_additive E (fun i j hij => hE_disj hij) z
      have h_real : Tendsto (fun N => ∑ i ∈ Finset.range N,
            (@inner ℂ H _ z (P.proj (E i) z)).re)
          atTop (nhds ((@inner ℂ H _ z (P.proj (⋃ n, E n) z)).re)) := by
        have hcont : Continuous (fun y : H => (@inner ℂ H _ z y).re) := by fun_prop
        have h := hcont.continuousAt.tendsto.comp h_sigma
        simp only [Function.comp_def] at h
        exact h.congr (fun N => by
          rw [inner_sum]
          simp only [← Complex.coe_reAddGroupHom, map_sum])
      have h_ennreal : Tendsto (fun N => ∑ i ∈ Finset.range N,
            ENNReal.ofReal ((@inner ℂ H _ z (P.proj (E i) z)).re))
          atTop (nhds (ENNReal.ofReal ((@inner ℂ H _ z
            (P.proj (⋃ n, E n) z)).re))) := by
        have := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h_real
        simp only [Function.comp_def] at this
        exact this.congr (fun N => by
          exact ENNReal.ofReal_sum_of_nonneg (fun i _ => h_nonneg i))
      have h_mono : Monotone (fun N => ∑ i ∈ Finset.range N,
            ENNReal.ofReal ((@inner ℂ H _ z (P.proj (E i) z)).re)) :=
        fun _ _ hab => Finset.sum_le_sum_of_subset (Finset.range_mono hab)
      rw [ENNReal.tsum_eq_iSup_nat, iSup_eq_of_tendsto h_mono h_ennreal])

/-- The spectral inner measure applied to a measurable set. -/
theorem spectralInnerMeasure_apply (z : H) (E : Set ℝ) (hE : MeasurableSet E) :
    P.spectralInnerMeasure z E = ENNReal.ofReal ((@inner ℂ H _ z (P.proj E z)).re) :=
  Measure.ofMeasurable_apply E hE

/-- The spectral inner measure is a finite measure. -/
instance spectralInnerMeasure_isFiniteMeasure (z : H) :
    IsFiniteMeasure (P.spectralInnerMeasure z) := by
  constructor
  rw [P.spectralInnerMeasure_apply z Set.univ MeasurableSet.univ, P.univ,
    ContinuousLinearMap.id_apply]
  exact ENNReal.ofReal_lt_top

/-- The diagonal measure is a finite measure. -/
instance diagonalMeasure_isFiniteMeasure (z : H) :
    IsFiniteMeasure (P.diagonalMeasure z) where
  measure_univ_lt_top := (P.distributionFunction z).measure_finite

/-- The diagonal measure of Iic t equals the spectral inner measure of Iic t. -/
theorem diagonalMeasure_Iic_eq (z : H) (t : ℝ) :
    P.diagonalMeasure z (Set.Iic t) = P.spectralInnerMeasure z (Set.Iic t) := by
  rw [P.spectralInnerMeasure_apply z _ measurableSet_Iic]
  simp only [diagonalMeasure, SpectralDistribution.toMeasure]
  have h_tendsto : Tendsto (P.distributionFunction z).toStieltjes atBot (nhds (0 : ℝ)) :=
    (P.distributionFunction z).tendsto_neg_infty
  rw [(P.distributionFunction z).toStieltjes.measure_Iic h_tendsto t, sub_zero]
  simp only [SpectralDistribution.toStieltjes, distributionFunction]

/-- The diagonal measure equals the spectral inner product measure. -/
theorem diagonalMeasure_eq_spectralInnerMeasure (z : H) :
    P.diagonalMeasure z = P.spectralInnerMeasure z :=
  Measure.ext_of_Iic _ _ (P.diagonalMeasure_Iic_eq z)

/-- The core connection: μ_z(E).toReal = ⟨z, P(E)z⟩.re for measurable E. -/
theorem diagonalMeasure_apply (z : H) (E : Set ℝ) (hE : MeasurableSet E) :
    (P.diagonalMeasure z E).toReal = (@inner ℂ H _ z (P.proj E z)).re := by
  rw [P.diagonalMeasure_eq_spectralInnerMeasure z, P.spectralInnerMeasure_apply z E hE,
    ENNReal.toReal_ofReal (P.inner_proj_nonneg z E)]

/-- The complex measure agrees with the inner product on projections. -/
theorem complexMeasure_eq_inner (x y : H) (E : Set ℝ) (hE : MeasurableSet E) :
    P.complexMeasure x y E = @inner ℂ H _ x (P.proj E y) := by
  simp only [complexMeasure]
  -- Rewrite each diagonal measure using diagonalMeasure_apply
  rw [P.diagonalMeasure_apply (x + y) E hE,
      P.diagonalMeasure_apply (x - y) E hE,
      P.diagonalMeasure_apply (x + Complex.I • y) E hE,
      P.diagonalMeasure_apply (x - Complex.I • y) E hE]
  -- Now LHS has (1/4) * (re⟨x+y, P(E)(x+y)⟩ - re⟨x-y, P(E)(x-y)⟩ - I*re⟨x+iy, P(E)(x+iy)⟩ + I*re⟨x-iy, P(E)(x-iy)⟩)
  -- RHS is ⟨x, P(E) y⟩
  -- Use self-adjointness to get ⟨x, P(E) y⟩ = ⟨P(E) x, y⟩
  have h_adj : @inner ℂ H _ x (P.proj E y) =
      @inner ℂ H _ (P.proj E x) y := by
    rw [← ContinuousLinearMap.adjoint_inner_left, P.selfAdjoint]
  rw [h_adj]
  -- Apply the polarization identity for the operator P(E)
  have h_pol := inner_map_polarization' (P.proj E).toLinearMap x y
  simp only [ContinuousLinearMap.coe_coe] at h_pol
  rw [h_pol]
  -- Now both sides have the same structure. The RHS uses ⟨P(E) z, z⟩ while LHS uses (⟨z, P(E) z⟩.re : ℂ)
  -- For self-adjoint P(E): ⟨P(E) z, z⟩ = ⟨z, P(E) z⟩ and ⟨z, P(E) z⟩ is real
  -- So ⟨P(E) z, z⟩ = (⟨z, P(E) z⟩.re : ℂ)
  have h_diag : ∀ z : H, @inner ℂ H _ (P.proj E z) z =
      ((@inner ℂ H _ z (P.proj E z)).re : ℂ) := by
    intro z
    have h1 : @inner ℂ H _ (P.proj E z) z = @inner ℂ H _ z (P.proj E z) := by
      rw [← ContinuousLinearMap.adjoint_inner_left, P.selfAdjoint]
    rw [h1, Complex.ext_iff]
    exact ⟨by simp, by simp [P.inner_proj_real z E]⟩
  rw [h_diag (x + y), h_diag (x - y), h_diag (x + Complex.I • y), h_diag (x - Complex.I • y)]
  ring

end ProjectionValuedMeasure

end
