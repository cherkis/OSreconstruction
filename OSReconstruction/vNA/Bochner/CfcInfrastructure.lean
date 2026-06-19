/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import OSReconstruction.vNA.Spectral.CayleyTransform
import OSReconstruction.vNA.MeasureTheory.SpectralIntegral
import OSReconstruction.vNA.MeasureTheory.SpectralStieltjes

/-!
# Functional Calculus from Mathlib's CFC - Basic Infrastructure

This file contains the PROVEN (no sorry) infrastructure for connecting
unbounded self-adjoint operator theory to Mathlib's continuous functional
calculus (CFC).

## Contents

This file includes:
* Basic CFC infrastructure via Cayley transform
* Indicator approximation functions and their properties
* Bump operators (smooth approximations to spectral projections)
* Proven properties: self-adjoint, monotonicity, positivity, norm bounds
* Strong operator topology (SOT) convergence theorems
* `monotone_positive_contraction_SOT_limit` - key theorem for monotone limits

## Notes

The spectral projection construction (which requires the Cauchy property
of bump operator inner products) is in the main FunctionalCalculusFromCFC.lean
file, not here. This file contains only fully proven results.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Chapter VIII
* Mathlib's Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
-/

noncomputable section

open scoped InnerProduct ComplexConjugate Classical
open Filter Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Bounded operators as a C*-algebra -/

/-- The space of bounded linear operators on H is a C*-algebra.
    Mathlib provides this structure via `ContinuousLinearMap` instances. -/
instance : CStarRing (H →L[ℂ] H) := by infer_instance

instance : Algebra ℂ (H →L[ℂ] H) := by infer_instance

/-- A unitary operator is normal (hence has CFC available).
    This version takes explicit proof of U*U = 1 and UU* = 1.
    Named with prime to avoid conflict with version in SpectralFunctionalViaRMK. -/
theorem unitary_isStarNormal' (U : H →L[ℂ] H)
    (hU_left : U.adjoint ∘L U = 1) (hU_right : U ∘L U.adjoint = 1) :
    IsStarNormal U := by
  constructor
  -- U* U = U U* for unitary operators
  calc U.adjoint * U = U.adjoint ∘L U := rfl
    _ = 1 := hU_left
    _ = U ∘L U.adjoint := hU_right.symm
    _ = U * U.adjoint := rfl

set_option maxHeartbeats 400000 in
/-- The spectrum of a unitary operator is contained in the unit circle.

    This is a standard result: for unitary U, the spectrum is on the unit circle because:
    - For |z| > 1: ‖U/z‖ < 1, so U - z = -z(1 - U/z) is invertible via Neumann series
    - For |z| < 1: ‖z·U*‖ < 1, so 1 - z·U* is invertible, and U - z = (1 - z·U*)·U is invertible -/
theorem unitary_spectrum_circle (U : H →L[ℂ] H)
    (hU_left : U.adjoint ∘L U = 1) (hU_right : U ∘L U.adjoint = 1) :
    spectrum ℂ U ⊆ Metric.sphere (0 : ℂ) 1 := by
  -- For unitary U: z ∈ spectrum implies |z| = 1
  intro z hz
  simp only [Metric.mem_sphere, dist_zero_right]
  by_contra hne
  push Not at hne
  have h1 : ‖z‖ < 1 ∨ ‖z‖ > 1 := lt_or_gt_of_ne hne
  -- ‖U‖ ≤ 1 (since U*U = 1 implies U is an isometry)
  have hU_norm_le : ‖U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro x
    have hcomp : U.adjoint (U x) = x := by
      have := congrFun (congrArg DFunLike.coe hU_left) x
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.one_apply] at this
      exact this
    have hinner_eq : @inner ℂ H _ (U x) (U x) = @inner ℂ H _ x x := by
      rw [← ContinuousLinearMap.adjoint_inner_left, hcomp]
    have h : ‖U x‖^2 = ‖x‖^2 := by
      calc ‖U x‖^2 = RCLike.re (@inner ℂ H _ (U x) (U x)) := (inner_self_eq_norm_sq (U x)).symm
        _ = RCLike.re (@inner ℂ H _ x x) := by rw [hinner_eq]
        _ = ‖x‖^2 := inner_self_eq_norm_sq x
    have hsq : ‖U x‖ = ‖x‖ := by
      nlinarith [sq_nonneg ‖U x‖, sq_nonneg ‖x‖, h, norm_nonneg (U x), norm_nonneg x]
    rw [hsq, one_mul]
  -- Similarly ‖U*‖ ≤ 1
  have hU_adj_norm_le : ‖U.adjoint‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
    intro x
    have hcomp : U (U.adjoint x) = x := by
      have := congrFun (congrArg DFunLike.coe hU_right) x
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                 ContinuousLinearMap.one_apply] at this
      exact this
    -- U preserves inner products: ⟨Uy, Uz⟩ = ⟨y, z⟩
    have hU_inner : ∀ y z, @inner ℂ H _ (U y) (U z) = @inner ℂ H _ y z := by
      intro y z
      calc @inner ℂ H _ (U y) (U z)
          = @inner ℂ H _ (U.adjoint (U y)) z := by rw [ContinuousLinearMap.adjoint_inner_left]
        _ = @inner ℂ H _ ((U.adjoint ∘L U) y) z := rfl
        _ = @inner ℂ H _ y z := by rw [hU_left]; simp
    have hinner_eq : @inner ℂ H _ (U.adjoint x) (U.adjoint x) = @inner ℂ H _ x x := by
      calc @inner ℂ H _ (U.adjoint x) (U.adjoint x)
          = @inner ℂ H _ (U (U.adjoint x)) (U (U.adjoint x)) := (hU_inner _ _).symm
        _ = @inner ℂ H _ x x := by rw [hcomp]
    have h : ‖U.adjoint x‖^2 = ‖x‖^2 := by
      calc ‖U.adjoint x‖^2 = RCLike.re (@inner ℂ H _ (U.adjoint x) (U.adjoint x)) :=
          (inner_self_eq_norm_sq (U.adjoint x)).symm
        _ = RCLike.re (@inner ℂ H _ x x) := by rw [hinner_eq]
        _ = ‖x‖^2 := inner_self_eq_norm_sq x
    have hsq : ‖U.adjoint x‖ = ‖x‖ := by
      nlinarith [sq_nonneg ‖U.adjoint x‖, sq_nonneg ‖x‖, h, norm_nonneg (U.adjoint x), norm_nonneg x]
    rw [hsq, one_mul]
  -- z not in spectrum means U - z·1 is a unit (invertible)
  -- We prove U - z·1 is a unit to contradict hz
  have hU_sub_z_unit : IsUnit (U - (z : ℂ) • (1 : H →L[ℂ] H)) := by
    cases h1 with
    | inl hz_lt =>
      -- |z| < 1: use ‖z·U*‖ < 1
      have h_lt : ‖z • U.adjoint‖ < 1 := by
        calc ‖z • U.adjoint‖ = ‖z‖ * ‖U.adjoint‖ := norm_smul z U.adjoint
          _ ≤ ‖z‖ * 1 := mul_le_mul_of_nonneg_left hU_adj_norm_le (norm_nonneg z)
          _ = ‖z‖ := mul_one ‖z‖
          _ < 1 := hz_lt
      have h_inv : IsUnit (1 - z • U.adjoint) := isUnit_one_sub_of_norm_lt_one h_lt
      -- U is a unit
      have hU_unit : IsUnit U := ⟨⟨U, U.adjoint,
        by ext x; exact congrFun (congrArg DFunLike.coe hU_right) x,
        by ext x; exact congrFun (congrArg DFunLike.coe hU_left) x⟩, rfl⟩
      -- (U - z) = (1 - z·U*)·U (both are units)
      have hfactor : U - z • (1 : H →L[ℂ] H) = (1 - z • U.adjoint) * U := by
        ext x; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, ContinuousLinearMap.mul_apply]
        have hUadjU : U.adjoint (U x) = x := by
          have := congrFun (congrArg DFunLike.coe hU_left) x
          simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
                     ContinuousLinearMap.one_apply] at this
          exact this
        simp only [hUadjU]
      rw [hfactor]
      exact h_inv.mul hU_unit
    | inr hz_gt =>
      -- |z| > 1: use ‖U/z‖ < 1
      have hz_ne : z ≠ 0 := by intro heq; rw [heq, norm_zero] at hz_gt; linarith
      have h_lt : ‖z⁻¹ • U‖ < 1 := by
        calc ‖z⁻¹ • U‖ = ‖z⁻¹‖ * ‖U‖ := norm_smul z⁻¹ U
          _ ≤ ‖z⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hU_norm_le (norm_nonneg _)
          _ = ‖z‖⁻¹ := by rw [norm_inv, mul_one]
          _ < 1 := by rw [inv_lt_one_iff₀]; right; exact hz_gt
      have h_inv : IsUnit (1 - z⁻¹ • U) := isUnit_one_sub_of_norm_lt_one h_lt
      -- (U - z) = -z·(1 - U/z) (unit times a unit)
      have hfactor : U - z • (1 : H →L[ℂ] H) = (-z) • (1 - z⁻¹ • U) := by
        ext x
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply]
        -- Goal: U x - z • x = (-z) • (x - z⁻¹ • U x)
        -- Expand RHS and show equality
        have hrhs : (-z) • (x - z⁻¹ • U x) = -(z • x) + U x := by
          have h1 : (-z) * z⁻¹ = (-1 : ℂ) := by field_simp [hz_ne]
          calc (-z) • (x - z⁻¹ • U x)
            = (-z) • x - (-z) • (z⁻¹ • U x) := smul_sub (-z) x _
            _ = (-z) • x - ((-z) * z⁻¹) • U x := by rw [smul_smul]
            _ = (-z) • x - (-1 : ℂ) • U x := by rw [h1]
            _ = (-z) • x + U x := by rw [neg_one_smul, sub_neg_eq_add]
            _ = -(z • x) + U x := by rw [neg_smul]
        rw [hrhs]
        abel
      rw [hfactor]
      -- (-z) • (unit) is a unit: construct inverse explicitly
      have hz_neg_ne : -z ≠ 0 := neg_ne_zero.mpr hz_ne
      obtain ⟨u, hu⟩ := h_inv
      -- inverse of (-z) • u is (-z)⁻¹ • u⁻¹
      let w : (H →L[ℂ] H)ˣ := {
        val := (-z) • u.val
        inv := (-z)⁻¹ • u.inv
        val_inv := by
          ext x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have h1 : (-z) • u.val ((-z)⁻¹ • u.inv x) = (-z) • ((-z)⁻¹ • u.val (u.inv x)) := by
            congr 1
            have := congrFun (congrArg DFunLike.coe (mul_smul_comm (-z)⁻¹ u.val u.inv)) x
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at this
            exact this
          rw [h1, smul_smul, mul_inv_cancel₀ hz_neg_ne, one_smul]
          have h2 := congrFun (congrArg DFunLike.coe u.val_inv) x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
          exact h2
        inv_val := by
          ext x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.one_apply]
          have h1 : (-z)⁻¹ • u.inv ((-z) • u.val x) = (-z)⁻¹ • ((-z) • u.inv (u.val x)) := by
            congr 1
            have := congrFun (congrArg DFunLike.coe (mul_smul_comm (-z) u.inv u.val)) x
            simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] at this
            exact this
          rw [h1, smul_smul, inv_mul_cancel₀ hz_neg_ne, one_smul]
          have h2 := congrFun (congrArg DFunLike.coe u.inv_val) x
          simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] at h2
          exact h2
      }
      refine ⟨w, ?_⟩
      -- w.val = (-z) • u.val = (-z) • (1 - z⁻¹ • U)
      show (-z) • u.val = (-z) • (1 - z⁻¹ • U)
      rw [hu]
  -- Contradiction: z in spectrum but algebraMap z - U is a unit
  -- spectrum.notMem_iff: z ∉ σ U ↔ IsUnit (algebraMap ℂ _ z - U)
  -- We have IsUnit (U - z•1), and algebraMap z - U = z•1 - U = -(U - z•1)
  have h_neg_unit : IsUnit ((algebraMap ℂ (H →L[ℂ] H)) z - U) := by
    have h_alg : (algebraMap ℂ (H →L[ℂ] H)) z - U = z • (1 : H →L[ℂ] H) - U := by
      simp only [Algebra.algebraMap_eq_smul_one]
    have hneg : z • (1 : H →L[ℂ] H) - U = -(U - z • 1) := by ext; simp [sub_eq_neg_add, add_comm]
    rw [h_alg, hneg]
    exact hU_sub_z_unit.neg
  exact (spectrum.notMem_iff.mpr h_neg_unit) hz

/-! ### Pulling back CFC via Cayley transform -/

/-- Continuity of the Cayley map. -/
theorem continuous_cayleyMap : Continuous cayleyMap := by
  unfold cayleyMap
  apply Continuous.div
  · apply Continuous.sub Complex.continuous_ofReal continuous_const
  · apply Continuous.add Complex.continuous_ofReal continuous_const
  · intro x heq
    -- x + i ≠ 0 since Im(x + i) = 1
    have him : Complex.im ((↑x : ℂ) + Complex.I) = 1 := by simp
    rw [heq] at him
    simp at him

/-- The composed map: ℝ → S¹ → ℂ given by t ↦ (t - i)/(t + i).
    This maps the spectrum of T (⊆ ℝ) to the spectrum of U (⊆ S¹). -/
def cayleyPullback (f : C(Metric.sphere (0 : ℂ) 1, ℂ)) : C(ℝ, ℂ) where
  toFun := fun t =>
    let w : ℂ := cayleyMap t
    -- Need to prove w is on the unit circle: dist w 0 = 1 ↔ ‖w‖ = 1
    f ⟨w, by simp only [Metric.mem_sphere, dist_zero_right]; exact cayleyMap_on_circle t⟩
  continuous_toFun := by
    apply Continuous.comp (by exact f.continuous)
    apply Continuous.subtype_mk
    exact continuous_cayleyMap

/-- The pushforward map: a function on ℝ becomes a function on S¹ \ {1} via inverse Cayley. -/
def cayleyPushforward (f : C(ℝ, ℂ)) :
    { w : Metric.sphere (0 : ℂ) 1 // w.1 ≠ 1 } → ℂ := fun w =>
  let t_real := inverseCayleyMap w.1.1 w.2
  f t_real

/-! ### Unbounded functional calculus via Cayley + CFC -/

/-- The composition f ∘ inverseCayley, defined on ℂ.
    For w ≠ 1, this is f(inverseCayleyMap w).
    For w = 1, we use f(0) as a conventional value.

    **Note on w = 1**: The inverse Cayley map has a pole at w = 1 (corresponding to
    λ = ±∞ in the real line). For functions f with well-defined behavior at infinity,
    the "correct" value at w = 1 would be lim_{λ→±∞} f(λ).

    We use f(0) as the value at w = 1. This choice:
    - Works correctly for constant functions (const c has value c everywhere)
    - Is a placeholder for non-constant functions
    - For CFC applications, the continuity hypothesis on spectrum(U) handles this -/
noncomputable def cfcViaInverseCayley (f : C(ℝ, ℂ)) : ℂ → ℂ := fun w =>
  if h : w ≠ 1 then f (inverseCayleyMap w h) else f 0

/-- Variant of cfcViaInverseCayley for functions vanishing at infinity (C₀ functions).

    For compactly supported or C₀ functions, the limit as t → ±∞ is 0, so
    the correct value at w = 1 is 0 (not f(0)). This ensures continuity on
    the full spectrum including at w = 1 for unbounded operators. -/
noncomputable def cfcViaInverseCayleyC0 (f : C(ℝ, ℂ)) : ℂ → ℂ := fun w =>
  if h : w ≠ 1 then f (inverseCayleyMap w h) else 0

/-- cfcViaInverseCayleyC0 agrees with cfcViaInverseCayley on {w | w ≠ 1}. -/
lemma cfcViaInverseCayleyC0_eq_away_from_one (f : C(ℝ, ℂ)) (w : ℂ) (hw : w ≠ 1) :
    cfcViaInverseCayleyC0 f w = cfcViaInverseCayley f w := by
  simp only [cfcViaInverseCayleyC0, cfcViaInverseCayley, dif_pos hw]

/-- cfcViaInverseCayleyC0 is continuous on S¹ \ {1} for any continuous f. -/
lemma cfcViaInverseCayleyC0_continuousOn (f : C(ℝ, ℂ)) :
    ContinuousOn (cfcViaInverseCayleyC0 f) {z | z ≠ 1} := by
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  apply ContinuousWithinAt.congr
  · -- Use continuity of f ∘ inverseCayleyMap
    let g : ℂ → ℂ := fun z => f ((Complex.I * (1 + z) / (1 - z)).re)
    have hg_cont : ContinuousOn g {z | z ≠ 1} := by
      apply ContinuousOn.comp (t := Set.univ) f.continuous.continuousOn
      · apply Complex.continuous_re.comp_continuousOn
        apply ContinuousOn.div
        · exact ContinuousOn.mul continuousOn_const (ContinuousOn.add continuousOn_const continuousOn_id)
        · exact ContinuousOn.sub continuousOn_const continuousOn_id
        · intro z hz
          simp only [Set.mem_setOf_eq] at hz
          simp only [sub_ne_zero]
          exact fun heq => hz heq.symm
      · intro _ _; exact Set.mem_univ _
    exact hg_cont w hw
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [cfcViaInverseCayleyC0, dif_pos hz, inverseCayleyMap]
  · simp only [cfcViaInverseCayleyC0, dif_pos hw, inverseCayleyMap]

/-- cfcViaInverseCayleyC0 preserves multiplication. -/
lemma cfcViaInverseCayleyC0_mul (f g : C(ℝ, ℂ)) :
    cfcViaInverseCayleyC0 (f * g) = cfcViaInverseCayleyC0 f * cfcViaInverseCayleyC0 g := by
  ext w
  simp only [cfcViaInverseCayleyC0, Pi.mul_apply]
  split_ifs with h
  · simp only [ContinuousMap.mul_apply]
  · simp only [mul_zero]

/-- cfcViaInverseCayleyC0 preserves star. -/
lemma cfcViaInverseCayleyC0_star (f : C(ℝ, ℂ)) :
    cfcViaInverseCayleyC0 (star f) = star (cfcViaInverseCayleyC0 f) := by
  ext w
  simp only [cfcViaInverseCayleyC0, Pi.star_apply]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [star_zero]

/-- The Cayley transform U is star-normal (unitary implies normal). -/
theorem cayleyTransform_isStarNormal (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    IsStarNormal C.U := by
  -- U is unitary: U*U = 1 (from C.adjoint_eq_inv)
  -- We need to also show UU* = 1
  have hU_left : C.U.adjoint ∘L C.U = 1 := C.adjoint_eq_inv
  -- For the right inverse, use that U is a surjective isometry
  -- The surjectivity of U follows from the Cayley transform construction:
  -- Range(T-i) = H for self-adjoint T (deficiency indices are 0)
  have hU_right : C.U ∘L C.U.adjoint = 1 := cayley_unitary T hT hsa C
  exact unitary_isStarNormal' C.U hU_left hU_right

/-- For an unbounded self-adjoint operator T with Cayley transform U,
    we define f(T) := g(U) where g = f ∘ (inverse Cayley).

    This leverages Mathlib's continuous functional calculus for star-normal
    elements in C*-algebras. Since U is unitary, it is star-normal, and
    H →L[ℂ] H is a C*-algebra.

    **WARNING**: For unbounded T, `1 ∈ σ(U)` and `cfcViaInverseCayley f` is
    generally discontinuous at 1 (since `inverseCayley(w) → ∞` as `w → 1`).
    By Mathlib's CFC convention, `cfc g U = 0` when g is not continuous on σ(U).
    This means `UnboundedCFC T f = 0` for most f when T is unbounded.
    For the correct functional calculus, use `functionalCalculus` from
    `Unbounded/Spectral.lean` which is defined via sesquilinear forms. -/
noncomputable def UnboundedCFC (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) : H →L[ℂ] H :=
  -- The construction follows Reed-Simon VIII.5:
  -- f(T) = (f ∘ inverseCayley)(U) where U is the Cayley transform
  --
  -- We use Mathlib's CFC for star-normal elements:
  -- U is star-normal (unitary operators are normal)
  -- H →L[ℂ] H is a C*-algebra
  let g := cfcViaInverseCayley f
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Apply Mathlib's continuous functional calculus
  cfc g C.U

/-- The composition cfcViaInverseCayley preserves multiplication. -/
lemma cfcViaInverseCayley_mul (f g : C(ℝ, ℂ)) :
    cfcViaInverseCayley (f * g) = cfcViaInverseCayley f * cfcViaInverseCayley g := by
  ext w
  simp only [cfcViaInverseCayley, Pi.mul_apply]
  split_ifs with h
  · simp only [ContinuousMap.mul_apply]
  · simp only [ContinuousMap.mul_apply]

/-- The composition cfcViaInverseCayley preserves addition. -/
lemma cfcViaInverseCayley_add (f g : C(ℝ, ℂ)) :
    cfcViaInverseCayley (f + g) = cfcViaInverseCayley f + cfcViaInverseCayley g := by
  ext w
  simp only [cfcViaInverseCayley, Pi.add_apply, ContinuousMap.add_apply]
  split_ifs <;> rfl

/-- The composition cfcViaInverseCayley respects scalar multiplication. -/
lemma cfcViaInverseCayley_smul (c : ℂ) (f : C(ℝ, ℂ)) :
    cfcViaInverseCayley (c • f) = c • cfcViaInverseCayley f := by
  ext w
  simp only [cfcViaInverseCayley, Pi.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
  split_ifs <;> rfl

/-- The unbounded functional calculus is multiplicative.

    This version includes explicit continuity hypotheses, which are satisfied when:
    - 1 ∉ spectrum(C.U) (e.g., when T is bounded), or
    - f has equal limits at ±∞ (the discontinuity at 1 is removable). -/
theorem unbounded_cfc_mul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f g : C(ℝ, ℂ))
    (hcf : ContinuousOn (cfcViaInverseCayley f) (spectrum ℂ C.U))
    (hcg : ContinuousOn (cfcViaInverseCayley g) (spectrum ℂ C.U)) :
    UnboundedCFC T hT hsa C (f * g) = UnboundedCFC T hT hsa C f ∘L UnboundedCFC T hT hsa C g := by
  simp only [UnboundedCFC]
  rw [cfcViaInverseCayley_mul]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfc_mul: cfc (fun x => f x * g x) a = cfc f a * cfc g a
  conv_lhs => rw [show cfcViaInverseCayley f * cfcViaInverseCayley g =
    fun x => cfcViaInverseCayley f x * cfcViaInverseCayley g x from rfl]
  rw [cfc_mul _ _ _ hcf hcg]
  rfl

/-- The composition cfcViaInverseCayley respects star (complex conjugation). -/
lemma cfcViaInverseCayley_star (f : C(ℝ, ℂ)) :
    cfcViaInverseCayley (star f) = star (cfcViaInverseCayley f) := by
  ext w
  simp only [cfcViaInverseCayley, Pi.star_apply]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [ContinuousMap.star_apply]

/-- The unbounded functional calculus respects adjoints. -/
theorem unbounded_cfc_star (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f : C(ℝ, ℂ)) :
    (UnboundedCFC T hT hsa C f).adjoint = UnboundedCFC T hT hsa C (star f) := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The adjoint on H →L[ℂ] H corresponds to star in the C*-algebra structure
  -- star_eq_adjoint : star A = A.adjoint, so A.adjoint = star A
  rw [← ContinuousLinearMap.star_eq_adjoint]
  -- Use cfc_star: cfc (fun x ↦ star (f x)) a = star (cfc f a)
  rw [← cfc_star]
  -- Now show: cfc (fun x => star (cfcViaInverseCayley f x)) = cfc (cfcViaInverseCayley (star f))
  congr 1
  ext w
  simp only [cfcViaInverseCayley]
  split_ifs with h
  · simp only [ContinuousMap.star_apply]
  · simp only [ContinuousMap.star_apply]

/-- The unbounded functional calculus is additive. -/
theorem unbounded_cfc_add (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (f g : C(ℝ, ℂ))
    (hcf : ContinuousOn (cfcViaInverseCayley f) (spectrum ℂ C.U))
    (hcg : ContinuousOn (cfcViaInverseCayley g) (spectrum ℂ C.U)) :
    UnboundedCFC T hT hsa C (f + g) = UnboundedCFC T hT hsa C f + UnboundedCFC T hT hsa C g := by
  show cfc (cfcViaInverseCayley (f + g)) C.U =
      cfc (cfcViaInverseCayley f) C.U + cfc (cfcViaInverseCayley g) C.U
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  have h : cfcViaInverseCayley (f + g) = fun x => cfcViaInverseCayley f x + cfcViaInverseCayley g x := by
    ext w; simp only [cfcViaInverseCayley, ContinuousMap.add_apply]; split_ifs <;> rfl
  rw [h]
  exact cfc_add (a := C.U) (cfcViaInverseCayley f) (cfcViaInverseCayley g) hcf hcg

/-- The unbounded functional calculus respects scalar multiplication. -/
theorem unbounded_cfc_smul (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (c : ℂ) (f : C(ℝ, ℂ))
    (hcf : ContinuousOn (cfcViaInverseCayley f) (spectrum ℂ C.U)) :
    UnboundedCFC T hT hsa C (c • f) = c • UnboundedCFC T hT hsa C f := by
  show cfc (cfcViaInverseCayley (c • f)) C.U = c • cfc (cfcViaInverseCayley f) C.U
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  have h : cfcViaInverseCayley (c • f) = fun x => c • cfcViaInverseCayley f x := by
    ext w; simp only [cfcViaInverseCayley, ContinuousMap.smul_apply, smul_eq_mul]; split_ifs <;> rfl
  rw [h]
  exact cfc_smul (a := C.U) c (cfcViaInverseCayley f) hcf

/-- The constant function 1 maps to the identity operator.

    The proof uses that cfcViaInverseCayley of the constant 1 function is the
    constant 1 function everywhere (both branches of the definition give 1). -/
theorem unbounded_cfc_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) :
    UnboundedCFC T hT hsa C (ContinuousMap.const ℝ 1) = 1 := by
  simp only [UnboundedCFC]
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- cfcViaInverseCayley of const 1 equals 1 everywhere
  have heq : cfcViaInverseCayley (ContinuousMap.const ℝ 1) = fun _ => 1 := by
    ext w
    simp only [cfcViaInverseCayley]
    split_ifs with h
    · simp only [ContinuousMap.const_apply]
    · simp only [ContinuousMap.const_apply]
  rw [heq]
  exact cfc_const_one ℂ C.U

/-! ### Complex spectral measure via RMK -/

/-- The positive functional Λ_x(f) = Re⟨x, f(T)x⟩ for x ∈ H and continuous f.
    This is the starting point for the RMK construction.
    Named `unboundedSpectralFunctional` to avoid conflict with `spectralFunctional` in
    SpectralFunctionalViaRMK.lean (which is for unitary operators). -/
noncomputable def unboundedSpectralFunctional (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (x : H) :
    C(ℝ, ℂ) → ℂ :=
  fun f => @inner ℂ H _ x ((UnboundedCFC T hT hsa C f) x)

/-- A bump function that approximates the indicator χ_{[a,b]} from below.
    For ε > 0, returns a continuous function that is:
    - 1 on [a+ε, b-ε]
    - 0 outside [a-ε, b+ε]
    - Linear interpolation in between -/
noncomputable def indicatorApprox (a b ε : ℝ) (_hε : ε > 0) : C(ℝ, ℝ) :=
  -- Use max and min to build a piecewise linear bump function
  -- f(x) = max(0, min(1, min((x-(a-ε))/(2ε), ((b+ε)-x)/(2ε))))
  ⟨fun x => max 0 (min 1 (min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)))),
   by
    apply Continuous.max continuous_const
    apply Continuous.min continuous_const
    apply Continuous.min
    · exact (continuous_id.sub continuous_const).div_const _
    · exact (continuous_const.sub continuous_id).div_const _⟩

/-- Complex version of the bump function for CFC. -/
noncomputable def indicatorApproxComplex (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℂ) :=
  ⟨fun x => (indicatorApprox a b ε hε x : ℂ),
   Complex.continuous_ofReal.comp (indicatorApprox a b ε hε).continuous⟩

/-- The bump functions are bounded by 1. -/
lemma indicatorApprox_le_one (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    indicatorApprox a b ε hε x ≤ 1 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact max_le (by linarith) (min_le_left _ _)

/-- The bump functions are nonnegative. -/
lemma indicatorApprox_nonneg (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    0 ≤ indicatorApprox a b ε hε x := le_max_left _ _

/-- indicatorApprox is 0 for x ≤ a - ε (below the support). -/
lemma indicatorApprox_eq_zero_below (a b ε : ℝ) (hε : ε > 0) (x : ℝ) (hx : x ≤ a - ε) :
    indicatorApprox a b ε hε x = 0 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h : (x - (a - ε)) / (2 * ε) ≤ 0 := by
    rw [div_le_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)) ≤ 0 :=
    le_trans (min_le_left _ _) h
  have h3 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) ≤ 0 :=
    le_trans (min_le_right _ _) h2
  exact max_eq_left h3

/-- indicatorApprox is 0 for x ≥ b + ε (above the support). -/
lemma indicatorApprox_eq_zero_above (a b ε : ℝ) (hε : ε > 0) (x : ℝ) (hx : x ≥ b + ε) :
    indicatorApprox a b ε hε x = 0 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h : ((b + ε) - x) / (2 * ε) ≤ 0 := by
    rw [div_le_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : min ((x - (a - ε)) / (2 * ε)) (((b + ε) - x) / (2 * ε)) ≤ 0 :=
    le_trans (min_le_right _ _) h
  have h3 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) ≤ 0 :=
    le_trans (min_le_right _ _) h2
  exact max_eq_left h3

/-- indicatorApprox is 0 outside [a - ε, b + ε]. -/
lemma indicatorApprox_eq_zero_outside (a b ε : ℝ) (hε : ε > 0) (x : ℝ)
    (hx : x ≤ a - ε ∨ x ≥ b + ε) : indicatorApprox a b ε hε x = 0 := by
  cases hx with
  | inl h => exact indicatorApprox_eq_zero_below a b ε hε x h
  | inr h => exact indicatorApprox_eq_zero_above a b ε hε x h

/-- For x in [a+ε, b-ε], the bump function equals 1. -/
lemma indicatorApprox_eq_one (a b ε : ℝ) (hε : ε > 0) (x : ℝ)
    (hx_lo : a + ε ≤ x) (hx_hi : x ≤ b - ε) :
    indicatorApprox a b ε hε x = 1 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h1 : (x - (a - ε)) / (2 * ε) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h2 : ((b + ε) - x) / (2 * ε) ≥ 1 := by
    rw [ge_iff_le, le_div_iff₀ (by linarith : 2 * ε > 0)]
    linarith
  have h3 : min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε)) ≥ 1 := le_min h1 h2
  have h4 : min 1 (min ((x - (a - ε)) / (2 * ε)) ((b + ε - x) / (2 * ε))) = 1 :=
    min_eq_left h3
  rw [h4]
  exact max_eq_right (by linarith)

/-- Indicator approximation is monotone decreasing in ε on [a, b]:
    For smaller ε, the bump function is larger on the core interval.
    Note: This is only true for x in [a, b]; outside this region the relationship is more complex. -/
lemma indicatorApprox_mono_eps_on_core (a b ε₁ ε₂ : ℝ) (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0)
    (hle : ε₁ ≤ ε₂) (x : ℝ) (hxa : a ≤ x) (hxb : x ≤ b) :
    indicatorApprox a b ε₂ hε₂ x ≤ indicatorApprox a b ε₁ hε₁ x := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h2ε₁ : 0 < 2 * ε₁ := by linarith
  have h2ε₂ : 0 < 2 * ε₂ := by linarith
  apply max_le (le_max_left _ _)
  apply le_max_of_le_right
  apply min_le_min_left
  apply min_le_min
  · -- left₂ ≤ left₁ when x ≥ a
    rw [div_le_div_iff₀ h2ε₂ h2ε₁]
    -- (x - a + ε₂)(2ε₁) ≤ (x - a + ε₁)(2ε₂)
    -- 2ε₁(x-a) + 2ε₁ε₂ ≤ 2ε₂(x-a) + 2ε₁ε₂
    -- 2ε₁(x-a) ≤ 2ε₂(x-a)
    -- (x-a)(ε₁ - ε₂) ≤ 0  [true since x ≥ a and ε₁ ≤ ε₂]
    nlinarith
  · -- right₂ ≤ right₁ when x ≤ b
    rw [div_le_div_iff₀ h2ε₂ h2ε₁]
    -- (b + ε₂ - x)(2ε₁) ≤ (b + ε₁ - x)(2ε₂)
    -- (b-x)(ε₂ - ε₁) ≤ 0  [true since x ≤ b and ε₂ ≥ ε₁]
    nlinarith

/-- At the left boundary a, indicatorApprox equals 1/2 (when a ≤ b). -/
lemma indicatorApprox_at_left_boundary (a b ε : ℝ) (hε : ε > 0) (hab : a ≤ b) :
    indicatorApprox a b ε hε a = 1/2 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h2ε : 0 < 2 * ε := by linarith
  -- At x = a: left term = (a - (a - ε)) / (2ε) = ε / (2ε) = 1/2
  have hleft : (a - (a - ε)) / (2 * ε) = 1/2 := by
    have : a - (a - ε) = ε := by ring
    rw [this]
    field_simp
  rw [hleft]
  -- right term = (b + ε - a)/(2ε) ≥ ε/(2ε) = 1/2 since b ≥ a
  have hright : ((b + ε) - a) / (2 * ε) ≥ 1/2 := by
    rw [ge_iff_le, le_div_iff₀ h2ε]
    linarith
  have h1 : min (1/2) (((b + ε) - a) / (2 * ε)) = 1/2 := min_eq_left hright
  have h2 : min 1 (min (1/2) (((b + ε) - a) / (2 * ε))) = 1/2 := by
    rw [h1]; norm_num
  rw [h2]
  exact max_eq_right (by norm_num : (0 : ℝ) ≤ 1/2)

/-- At the right boundary b, indicatorApprox equals 1/2 (when a ≤ b). -/
lemma indicatorApprox_at_right_boundary (a b ε : ℝ) (hε : ε > 0) (hab : a ≤ b) :
    indicatorApprox a b ε hε b = 1/2 := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  have h2ε : 0 < 2 * ε := by linarith
  -- At x = b: right term = (b + ε - b) / (2ε) = ε / (2ε) = 1/2
  have hright : ((b + ε) - b) / (2 * ε) = 1/2 := by
    have : (b + ε) - b = ε := by ring
    rw [this]
    field_simp
  -- left term = (b - (a - ε)) / (2ε) = (b - a + ε) / (2ε) ≥ ε/(2ε) = 1/2
  have hleft : (b - (a - ε)) / (2 * ε) ≥ 1/2 := by
    rw [ge_iff_le, le_div_iff₀ h2ε]
    have : b - (a - ε) = b - a + ε := by ring
    rw [this]
    linarith
  have h1 : min ((b - (a - ε)) / (2 * ε)) (((b + ε) - b) / (2 * ε)) = 1/2 := by
    rw [hright]
    exact min_eq_right hleft
  have h2 : min 1 (min ((b - (a - ε)) / (2 * ε)) (((b + ε) - b) / (2 * ε))) = 1/2 := by
    rw [h1]; norm_num
  rw [h2]
  exact max_eq_right (by norm_num : (0 : ℝ) ≤ 1/2)

/-- For x in the interior (a, b), indicatorApprox_ε(x) → 1 as ε → 0. -/
lemma indicatorApprox_tendsto_one_interior (a b x : ℝ) (hxa : a < x) (hxb : x < b) :
    Filter.Tendsto (fun ε : ℝ => if hε : ε > 0 then indicatorApprox a b ε hε x else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  -- For ε < min(x - a, b - x), the point x is in [a + ε, b - ε], so indicatorApprox = 1
  let ε₀ := min (x - a) (b - x)
  have hε₀_pos : ε₀ > 0 := lt_min (by linarith) (by linarith)
  use ε₀
  constructor
  · exact hε₀_pos
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  simp only [dif_pos hε_mem]
  rw [Real.dist_eq]
  -- For ε < ε₀, x ∈ [a + ε, b - ε]
  have hε_small : ε < ε₀ := by
    rw [Real.dist_eq, abs_sub_comm] at hε_dist
    have : |ε| < ε₀ := by simpa using hε_dist
    rwa [abs_of_pos hε_mem] at this
  have hax : a + ε ≤ x := by
    have : ε < x - a := lt_of_lt_of_le hε_small (min_le_left _ _)
    linarith
  have hxb' : x ≤ b - ε := by
    have : ε < b - x := lt_of_lt_of_le hε_small (min_le_right _ _)
    linarith
  -- x ∈ [a + ε, b - ε] implies indicatorApprox = 1
  have h1 := indicatorApprox_eq_one a b ε hε_mem x hax hxb'
  rw [h1]
  simp only [sub_self, abs_zero, hδ]

/-- For x outside [a, b], indicatorApprox_ε(x) → 0 as ε → 0. -/
lemma indicatorApprox_tendsto_zero_exterior (a b x : ℝ) (hx : x < a ∨ x > b) :
    Filter.Tendsto (fun ε : ℝ => if hε : ε > 0 then indicatorApprox a b ε hε x else 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  cases hx with
  | inl hxa => -- x < a
    -- For ε < a - x, x < a - ε, so indicatorApprox = 0
    let ε₀ := a - x
    have hε₀_pos : ε₀ > 0 := by linarith
    use ε₀
    constructor
    · exact hε₀_pos
    intro ε hε_mem hε_dist
    simp only [Set.mem_Ioi] at hε_mem
    simp only [dif_pos hε_mem]
    rw [Real.dist_eq]
    have hε_small : ε < ε₀ := by
      rw [Real.dist_eq, abs_sub_comm] at hε_dist
      have : |ε| < ε₀ := by simpa using hε_dist
      rwa [abs_of_pos hε_mem] at this
    have hx_below : x ≤ a - ε := by linarith
    have h0 := indicatorApprox_eq_zero_below a b ε hε_mem x hx_below
    rw [h0]
    simp only [sub_zero, abs_zero, hδ]
  | inr hxb => -- x > b
    -- For ε < x - b, x > b + ε, so indicatorApprox = 0
    let ε₀ := x - b
    have hε₀_pos : ε₀ > 0 := by linarith
    use ε₀
    constructor
    · exact hε₀_pos
    intro ε hε_mem hε_dist
    simp only [Set.mem_Ioi] at hε_mem
    simp only [dif_pos hε_mem]
    rw [Real.dist_eq]
    have hε_small : ε < ε₀ := by
      rw [Real.dist_eq, abs_sub_comm] at hε_dist
      have : |ε| < ε₀ := by simpa using hε_dist
      rwa [abs_of_pos hε_mem] at this
    have hx_above : x ≥ b + ε := by linarith
    have h0 := indicatorApprox_eq_zero_above a b ε hε_mem x hx_above
    rw [h0]
    simp only [sub_zero, abs_zero, hδ]

/-- Square root of the bump function. -/
noncomputable def sqrtIndicatorApprox (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℝ) :=
  ⟨fun x => Real.sqrt (indicatorApprox a b ε hε x),
   (indicatorApprox a b ε hε).continuous.sqrt⟩

/-- Complex version of the square root bump function for CFC. -/
noncomputable def sqrtIndicatorApproxComplex (a b ε : ℝ) (hε : ε > 0) : C(ℝ, ℂ) :=
  ⟨fun x => (sqrtIndicatorApprox a b ε hε x : ℂ),
   Complex.continuous_ofReal.comp (sqrtIndicatorApprox a b ε hε).continuous⟩

/-- The square root bump function squared equals the bump function. -/
lemma sqrtIndicatorApprox_sq (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    (sqrtIndicatorApprox a b ε hε x) ^ 2 = indicatorApprox a b ε hε x := by
  unfold sqrtIndicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact Real.sq_sqrt (indicatorApprox_nonneg a b ε hε x)

/-- The square root bump function is non-negative. -/
lemma sqrtIndicatorApprox_nonneg (a b ε : ℝ) (hε : ε > 0) (x : ℝ) :
    0 ≤ sqrtIndicatorApprox a b ε hε x := by
  unfold sqrtIndicatorApprox
  simp only [ContinuousMap.coe_mk]
  exact Real.sqrt_nonneg _

/-- Indicator approximation is monotone in intervals:
    If [a, b] ⊆ [c, d], then indicatorApprox a b ε ≤ indicatorApprox c d ε pointwise. -/
lemma indicatorApprox_mono_interval (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) (x : ℝ) :
    indicatorApprox a b ε hε x ≤ indicatorApprox c d ε hε x := by
  unfold indicatorApprox
  simp only [ContinuousMap.coe_mk]
  -- Both are in [0, 1], need to show LHS ≤ RHS
  apply max_le
  · -- 0 ≤ RHS is clear
    exact le_max_left _ _
  · -- Need: min 1 (min left_a right_b) ≤ max 0 (min 1 (min left_c right_d))
    apply le_max_of_le_right
    apply min_le_min_left
    have h2ε_pos : 0 ≤ 2 * ε := by linarith
    apply min_le_min
    · -- (x - (a - ε)) / (2 * ε) ≤ (x - (c - ε)) / (2 * ε)
      apply div_le_div_of_nonneg_right _ h2ε_pos
      linarith
    · -- ((b + ε) - x) / (2 * ε) ≤ ((d + ε) - x) / (2 * ε)
      apply div_le_div_of_nonneg_right _ h2ε_pos
      linarith

/-- The difference of indicator approximations for nested intervals is non-negative. -/
lemma indicatorApprox_diff_nonneg (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) (x : ℝ) :
    0 ≤ indicatorApprox c d ε hε x - indicatorApprox a b ε hε x := by
  have h := indicatorApprox_mono_interval a b c d ε hε hca hbd x
  linarith

/-- The square root of the difference of indicator approximations. -/
noncomputable def sqrtIndicatorApproxDiff (a b c d ε : ℝ) (hε : ε > 0)
    (_hca : c ≤ a) (_hbd : b ≤ d) : C(ℝ, ℝ) :=
  ⟨fun x => Real.sqrt (indicatorApprox c d ε hε x - indicatorApprox a b ε hε x),
   by
     apply Continuous.sqrt
     exact (indicatorApprox c d ε hε).continuous.sub (indicatorApprox a b ε hε).continuous⟩

/-- Complex version of the square root difference. -/
noncomputable def sqrtIndicatorApproxDiffComplex (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) : C(ℝ, ℂ) :=
  ⟨fun x => (sqrtIndicatorApproxDiff a b c d ε hε hca hbd x : ℂ),
   Complex.continuous_ofReal.comp (sqrtIndicatorApproxDiff a b c d ε hε hca hbd).continuous⟩

/-- The square root difference squared equals the difference. -/
lemma sqrtIndicatorApproxDiff_sq (a b c d ε : ℝ) (hε : ε > 0)
    (hca : c ≤ a) (hbd : b ≤ d) (x : ℝ) :
    (sqrtIndicatorApproxDiff a b c d ε hε hca hbd x) ^ 2 =
    indicatorApprox c d ε hε x - indicatorApprox a b ε hε x := by
  unfold sqrtIndicatorApproxDiff
  simp only [ContinuousMap.coe_mk]
  exact Real.sq_sqrt (indicatorApprox_diff_nonneg a b c d ε hε hca hbd x)

/-! ### Spectral measure from functional calculus -/

/-- The bump function operator for a bounded interval [a,b] with approximation parameter ε.

    We use cfcViaInverseCayleyC0 (which assigns 0 at w=1) because bump functions
    vanish at infinity, ensuring continuity on the full spectrum for unbounded operators. -/
noncomputable def bumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let bump := cfcViaInverseCayleyC0 (indicatorApproxComplex a b ε hε)
  cfc bump C.U

/-- The bump operators are self-adjoint (since bump functions are real-valued). -/
theorem bumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    (bumpOperator T hT hsa C a b ε hε).adjoint = bumpOperator T hT hsa C a b ε hε := by
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  -- cfc respects star, and bump is real-valued so star(bump) = bump
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · -- w ≠ 1: star(bump(inverseCayley w)) = bump(inverseCayley w) since bump is real
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · -- w = 1: star(0) = 0
    simp only [star_zero]

/-- The square root bump operator. -/
noncomputable def sqrtBumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let sqrtBump := cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε)
  cfc sqrtBump C.U

/-- The square root bump operator is self-adjoint (real-valued function). -/
theorem sqrtBumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    (sqrtBumpOperator T hT hsa C a b ε hε).adjoint = sqrtBumpOperator T hT hsa C a b ε hε := by
  unfold sqrtBumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · simp only [sqrtIndicatorApproxComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · simp only [star_zero]

/-- The square root difference operator for interval comparison. -/
noncomputable def sqrtDiffBumpOperator (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d ε : ℝ) (hε : ε > 0) (hca : c ≤ a) (hbd : b ≤ d) : H →L[ℂ] H :=
  haveI : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  let sqrtDiff := cfcViaInverseCayleyC0 (sqrtIndicatorApproxDiffComplex a b c d ε hε hca hbd)
  cfc sqrtDiff C.U

/-- The square root difference operator is self-adjoint. -/
theorem sqrtDiffBumpOperator_self_adjoint (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d ε : ℝ) (hε : ε > 0) (hca : c ≤ a) (hbd : b ≤ d) :
    (sqrtDiffBumpOperator T hT hsa C a b c d ε hε hca hbd).adjoint =
    sqrtDiffBumpOperator T hT hsa C a b c d ε hε hca hbd := by
  unfold sqrtDiffBumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  rw [← ContinuousLinearMap.star_eq_adjoint]
  rw [← cfc_star]
  congr 1
  ext w
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · simp only [sqrtIndicatorApproxDiffComplex, ContinuousMap.coe_mk]
    rw [Complex.star_def, Complex.conj_ofReal]
  · simp only [star_zero]

/-! ### Unitary properties of Cayley transform (moved here for forward reference) -/

/-- The Cayley transform is a unitary element (in the sense of unitary submonoid). -/
lemma cayleyTransform_mem_unitary (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) : C.U ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  have hU_left : C.U.adjoint ∘L C.U = 1 := C.adjoint_eq_inv
  have hU_right : C.U ∘L C.U.adjoint = 1 := cayley_unitary T hT hsa C
  constructor
  · -- star(U) * U = 1
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hU_left
  · -- U * star(U) = 1
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact hU_right

/-- The spectrum of the Cayley transform is on the unit circle. -/
lemma spectrum_norm_eq_one_cayley (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa) (z : ℂ) (hz : z ∈ spectrum ℂ C.U) :
    ‖z‖ = 1 :=
  spectrum.norm_eq_one_of_unitary (cayleyTransform_mem_unitary T hT hsa C) hz

/-- For z on the unit circle with |z - 1| < 1, the inverse Cayley map has large absolute value.

    **Key formula:** For ‖z‖ = 1 and z ≠ 1:
    |inverseCayleyMap(z)| = √((1 + Re(z)) / (1 - Re(z)))

    **Bound:** If |z - 1| < δ ≤ 1, then Re(z) > 1 - δ²/2 (using |z-1|² = 2(1 - Re(z))),
    so 1 + Re(z) > 2 - δ²/2 > 3/2 for δ < 1. Thus |inverseCayleyMap(z)| > 1/δ. -/
lemma inverseCayleyMap_abs_large_near_one (z : ℂ) (hz : z ≠ 1) (hon_circle : ‖z‖ = 1)
    (hclose : ‖z - 1‖ < 1) : |inverseCayleyMap z hz| > 1 / ‖z - 1‖ := by
  -- Use the formula: inverseCayleyMap z = -2 Im(z) / |1 - z|²
  -- For |z| = 1: |inverseCayleyMap z| = √((1 + Re(z)) / (1 - Re(z)))
  unfold inverseCayleyMap
  -- Step 1: Compute |1 - z|² = 2(1 - Re(z)) for |z| = 1
  have h_norm_sq : ‖z - 1‖^2 = 2 * (1 - z.re) := by
    have habs : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hon_circle, one_pow]
    have hre_im : z.re * z.re + z.im * z.im = 1 := by
      rw [← Complex.normSq_apply, habs]
    calc ‖z - 1‖^2 = Complex.normSq (z - 1) := by rw [Complex.normSq_eq_norm_sq]
      _ = (z.re - 1) * (z.re - 1) + z.im * z.im := by rw [Complex.normSq_apply]; simp
      _ = z.re * z.re - 2*z.re + 1 + z.im * z.im := by ring
      _ = 1 - 2*z.re + 1 := by linarith
      _ = 2 * (1 - z.re) := by ring
  -- Step 2: Since |z - 1| < 1, we have 1 - Re(z) < 1/2, so Re(z) > 1/2
  have hre_bound : z.re > 1/2 := by
    have h1 : ‖z - 1‖^2 < 1 := by nlinarith [hclose, norm_nonneg (z - 1)]
    rw [h_norm_sq] at h1
    linarith
  -- Step 3: Compute Im(z)² = 1 - Re(z)² for |z| = 1
  have him_sq : z.im^2 = (1 - z.re) * (1 + z.re) := by
    have habs : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hon_circle, one_pow]
    have hre_im : z.re * z.re + z.im * z.im = 1 := by rw [← Complex.normSq_apply, habs]
    have hre_im' : z.re^2 + z.im^2 = 1 := by convert hre_im using 2 <;> ring
    nlinarith
  -- Step 4: The key computation for inverseCayleyMap
  -- inverseCayleyMap z = (I * (1 + z) / (1 - z)).re
  -- For |z| = 1: inverseCayleyMap z = -2 Im(z) / |1-z|²
  have h_one_minus_ne : (1 : ℂ) - z ≠ 0 := by
    simp only [ne_eq, sub_eq_zero]
    exact fun h => hz h.symm
  have h_inv_cayley_formula : (Complex.I * (1 + z) / (1 - z)).re = -2 * z.im / ‖z - 1‖^2 := by
    have h1mz_sq : Complex.normSq (1 - z) = ‖z - 1‖^2 := by
      rw [Complex.normSq_eq_norm_sq, norm_sub_rev]
    -- I * (1 + z) = i(1 + re(z) + i·im(z)) = -im(z) + i(1 + re(z))
    -- (1 - z) = 1 - re(z) - i·im(z)
    -- Re((a + bi) / (c + di)) = (ac + bd) / (c² + d²)
    -- where a = -im(z), b = 1 + re(z), c = 1 - re(z), d = -im(z)
    -- ac + bd = -im(z)(1 - re(z)) + (1 + re(z))(-im(z)) = -im(z) + im(z)re(z) - im(z) - im(z)re(z) = -2 im(z)
    rw [Complex.div_re, h1mz_sq]
    have h1 : (Complex.I * (1 + z)).re = -z.im := by simp [Complex.I_re, Complex.I_im]
    have h2 : (Complex.I * (1 + z)).im = 1 + z.re := by simp [Complex.I_re, Complex.I_im]
    have h3 : (1 - z : ℂ).re = 1 - z.re := by simp
    have h4 : (1 - z : ℂ).im = -z.im := by simp
    rw [h1, h2, h3, h4]
    ring
  rw [h_inv_cayley_formula]
  -- Step 5: Bound |inverseCayleyMap z| = 2|Im(z)| / |z-1|²
  have h_norm_pos : ‖z - 1‖ > 0 := by
    have hne : z - 1 ≠ 0 := sub_ne_zero.mpr hz
    exact norm_pos_iff.mpr hne
  have h_norm_sq_pos : ‖z - 1‖^2 > 0 := sq_pos_of_pos h_norm_pos
  have h_abs : |(-2 : ℝ) * z.im / ‖z - 1‖^2| = 2 * |z.im| / ‖z - 1‖^2 := by
    rw [abs_div, abs_mul]
    simp only [abs_neg, abs_two]
    rw [abs_of_pos h_norm_sq_pos]
  rw [h_abs]
  -- Step 6: Show 2|Im(z)|/|z-1|² > 1/|z-1|
  -- Equivalently: 2|Im(z)| > |z-1| (after multiplying by |z-1|)
  have him_lower : 4 * z.im^2 > ‖z - 1‖^2 := by
    rw [h_norm_sq, him_sq]
    -- 4 (1 - Re)(1 + Re) > 2(1 - Re)
    -- Since Re > 1/2, we have 1 + Re > 3/2 and 1 - Re > 0
    have hpos : 1 - z.re > 0 := by linarith
    have hpos2 : 1 + z.re > 3/2 := by linarith
    calc 4 * ((1 - z.re) * (1 + z.re)) = 4 * (1 - z.re) * (1 + z.re) := by ring
      _ > 4 * (1 - z.re) * (3/2) := by nlinarith
      _ = 6 * (1 - z.re) := by ring
      _ > 2 * (1 - z.re) := by nlinarith
  -- Convert from squared inequality to linear
  have him_abs_lower : 2 * |z.im| > ‖z - 1‖ := by
    have h1 : (2 * |z.im|)^2 > ‖z - 1‖^2 := by
      calc (2 * |z.im|)^2 = 4 * z.im^2 := by rw [mul_pow, sq_abs]; ring
        _ > ‖z - 1‖^2 := him_lower
    have h2 : 2 * |z.im| ≥ 0 := by positivity
    have h3 : ‖z - 1‖ ≥ 0 := norm_nonneg _
    nlinarith [sq_nonneg (2 * |z.im|), sq_nonneg ‖z - 1‖]
  -- Now prove: 2|Im(z)|/|z-1|² > 1/|z-1|
  -- This is equivalent to: 2|Im(z)|/|z-1| > 1, i.e., 2|Im(z)| > |z-1|
  have key : 2 * |z.im| / ‖z - 1‖ > 1 := by
    rw [gt_iff_lt, one_lt_div h_norm_pos]
    exact him_abs_lower
  have step1 : 2 * |z.im| / ‖z - 1‖^2 = (2 * |z.im| / ‖z - 1‖) / ‖z - 1‖ := by
    have hne : ‖z - 1‖ ≠ 0 := ne_of_gt h_norm_pos
    field_simp [hne]
  rw [step1]
  exact div_lt_div_of_pos_right key h_norm_pos

/-! ### Bump operator monotonicity -/

/-- Key lemma: For nested intervals [a,b] ⊆ [c,d], the bump operator forms satisfy
    ⟨x, P_ab x⟩ ≤ ⟨x, P_cd x⟩, where the difference is non-negative.

    Proof: The difference P_cd - P_ab = R² where R is self-adjoint, so
    ⟨x, (P_cd - P_ab) x⟩ = ⟨x, R² x⟩ = ‖Rx‖² ≥ 0. -/
theorem bumpOperator_inner_mono (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b c d ε : ℝ) (hε : ε > 0) (hca : c ≤ a) (hbd : b ≤ d) (x : H) :
    RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) ≤
    RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C c d ε hε x)) := by
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- The difference operator P_cd - P_ab corresponds to the difference of bump functions
  -- which is non-negative by indicatorApprox_mono_interval
  -- We show this difference equals R² for self-adjoint R, hence is positive
  let R := sqrtDiffBumpOperator T hT hsa C a b c d ε hε hca hbd
  have hR_sa := sqrtDiffBumpOperator_self_adjoint T hT hsa C a b c d ε hε hca hbd
  -- Key: ⟨x, (P_cd - P_ab) x⟩ = ⟨x, R² x⟩ = ‖Rx‖²
  -- We prove this by showing R² = P_cd - P_ab via CFC
  -- Define the CFC functions
  let bump_ab := cfcViaInverseCayleyC0 (indicatorApproxComplex a b ε hε)
  let bump_cd := cfcViaInverseCayleyC0 (indicatorApproxComplex c d ε hε)
  let sqrtDiff := cfcViaInverseCayleyC0 (sqrtIndicatorApproxDiffComplex a b c d ε hε hca hbd)
  -- Key property: sqrtDiff² = bump_cd - bump_ab pointwise
  have hsqDiff_eq : ∀ w, sqrtDiff w * sqrtDiff w = bump_cd w - bump_ab w := by
    intro w
    simp only [sqrtDiff, bump_cd, bump_ab, cfcViaInverseCayleyC0]
    split_ifs with hw
    · -- w ≠ 1
      simp only [sqrtIndicatorApproxDiffComplex, indicatorApproxComplex, ContinuousMap.coe_mk]
      let t := inverseCayleyMap w hw
      -- Use sqrtIndicatorApproxDiff_sq: (sqrtDiff t)² = diff t
      have hsq_real := sqrtIndicatorApproxDiff_sq a b c d ε hε hca hbd t
      -- Convert to complex: (sqrtDiff t : ℂ) * (sqrtDiff t : ℂ) = (diff t : ℂ)
      have hsq : (sqrtIndicatorApproxDiff a b c d ε hε hca hbd t : ℂ) *
                 (sqrtIndicatorApproxDiff a b c d ε hε hca hbd t : ℂ) =
                 ((indicatorApprox c d ε hε t : ℂ) - (indicatorApprox a b ε hε t : ℂ)) := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_sub]
        congr 1
        have h2 : sqrtIndicatorApproxDiff a b c d ε hε hca hbd t *
                  sqrtIndicatorApproxDiff a b c d ε hε hca hbd t =
                  (sqrtIndicatorApproxDiff a b c d ε hε hca hbd t) ^ 2 := by ring
        rw [h2, hsq_real]
      -- t is definitionally equal to inverseCayleyMap w hw
      exact hsq
    · -- w = 1
      ring
  -- Continuity of the CFC functions on the spectrum
  -- The key is that cfcViaInverseCayleyC0 functions are continuous on {z | z ≠ 1} and equal 0 at z=1
  -- with proper limiting behavior (bump functions vanish at infinity)
  have hcont_sqrtDiff : ContinuousOn sqrtDiff (spectrum ℂ C.U) := by
    intro w hw
    by_cases h1 : w = 1
    · -- At w = 1: need to show continuity at 1
      subst h1
      apply Metric.continuousWithinAt_iff.mpr
      intro ε' hε'
      -- sqrtDiff(1) = 0, and sqrtDiff(z) → 0 as z → 1 (bump functions vanish at infinity)
      let R := max (max (|c - ε|) (|a - ε|)) (max (|b + ε|) (|d + ε|)) + 1
      use min (1/2) (1 / (R + 1))
      constructor
      · apply lt_min; linarith; positivity
      · intro z hz_mem hz_dist
        have hsqrtDiff1 : sqrtDiff 1 = 0 := by
          simp only [sqrtDiff, cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hsqrtDiff1, dist_zero_right]
        simp only [sqrtDiff, cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · simp only [dif_pos hz_ne1, sqrtIndicatorApproxDiffComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          -- For z close to 1, inverseCayleyMap(z) is large (outside support)
          have hnorm1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary
            (cayleyTransform_mem_unitary T hT hsa C) hz_mem
          have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R + 1)) := by
            rw [← Complex.dist_eq]; exact hz_dist
          have hclose : ‖z - 1‖ < 1 := calc ‖z - 1‖ < min (1/2) (1 / (R + 1)) := hz_dist_norm
            _ ≤ 1/2 := min_le_left _ _
            _ < 1 := by norm_num
          have hinv_large := inverseCayleyMap_abs_large_near_one z hz_ne1 hnorm1 hclose
          have hz_dist_R : ‖z - 1‖ < 1 / (R + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
          have hR_pos : R + 1 > 0 := by positivity
          have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R := by
            have h1 : 1 / ‖z - 1‖ > R + 1 := by
              have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
              rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
              calc (R + 1) * ‖z - 1‖ < (R + 1) * (1 / (R + 1)) := by
                    apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
            linarith
          -- Show sqrtIndicatorApproxDiff is 0 when |inverseCayleyMap z| > R
          have hindDiff_zero : indicatorApprox c d ε hε (inverseCayleyMap z hz_ne1) -
                               indicatorApprox a b ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            -- R bounds all four corners
            have hR_c : R > |c - ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |c - ε| :=
                le_trans (le_max_left _ _) (le_max_left _ _)
              linarith
            have hR_d : R > |d + ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |d + ε| :=
                le_trans (le_max_right _ _) (le_max_right _ _)
              linarith
            have hR_a : R > |a - ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |a - ε| :=
                le_trans (le_max_right _ _) (le_max_left _ _)
              linarith
            have hR_b : R > |b + ε| := by
              have h1 : max (max |c - ε| |a - ε|) (max |b + ε| |d + ε|) ≥ |b + ε| :=
                le_trans (le_max_left _ _) (le_max_right _ _)
              linarith
            set t := inverseCayleyMap z hz_ne1 with ht_def
            have hind_c_zero : indicatorApprox c d ε hε t = 0 := by
              apply indicatorApprox_eq_zero_outside
              by_cases ht_pos : t ≥ 0
              · right
                have ht_gt_R : t > R := by
                  have : |t| = t := abs_of_nonneg ht_pos; linarith
                have : t > d + ε := calc t > R := ht_gt_R
                  _ > |d + ε| := hR_d
                  _ ≥ d + ε := le_abs_self _
                linarith
              · left
                push Not at ht_pos
                have ht_lt_neg_R : t < -R := by
                  have : |t| = -t := abs_of_neg ht_pos; linarith
                have : t < c - ε := calc t < -R := ht_lt_neg_R
                  _ < -|c - ε| := by linarith
                  _ ≤ c - ε := neg_abs_le _
                linarith
            have hind_a_zero : indicatorApprox a b ε hε t = 0 := by
              apply indicatorApprox_eq_zero_outside
              by_cases ht_pos : t ≥ 0
              · right
                have ht_gt_R : t > R := by
                  have : |t| = t := abs_of_nonneg ht_pos; linarith
                have : t > b + ε := calc t > R := ht_gt_R
                  _ > |b + ε| := hR_b
                  _ ≥ b + ε := le_abs_self _
                linarith
              · left
                push Not at ht_pos
                have ht_lt_neg_R : t < -R := by
                  have : |t| = -t := abs_of_neg ht_pos; linarith
                have : t < a - ε := calc t < -R := ht_lt_neg_R
                  _ < -|a - ε| := by linarith
                  _ ≤ a - ε := neg_abs_le _
                linarith
            rw [hind_c_zero, hind_a_zero]; ring
          unfold sqrtIndicatorApproxDiff
          simp only [ContinuousMap.coe_mk]
          rw [hindDiff_zero, Real.sqrt_zero, abs_zero]
          exact hε'
        · -- z = 1
          push Not at hz_ne1
          simp only [hz_ne1, ne_eq, not_true_eq_false, not_false_eq_true, dif_neg]
          simp only [norm_zero]
          exact hε'
    · -- At w ≠ 1: f is continuous on the open set {z | z ≠ 1}, so continuous at w
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
      have haway := cfcViaInverseCayleyC0_continuousOn (sqrtIndicatorApproxDiffComplex a b c d ε hε hca hbd) w h1
      have hcont_at : ContinuousAt sqrtDiff w := haway.continuousAt (hopen.mem_nhds h1)
      exact hcont_at.continuousWithinAt
  have hcont_bump_ab : ContinuousOn bump_ab (spectrum ℂ C.U) := by
    intro w hw
    by_cases h1 : w = 1
    · -- At w = 1: need to show continuity at 1
      subst h1
      apply Metric.continuousWithinAt_iff.mpr
      intro ε' hε'
      let R_ab := max (|a - ε|) (|b + ε|) + 1
      use min (1/2) (1 / (R_ab + 1))
      constructor
      · apply lt_min; linarith; positivity
      · intro z hz_mem hz_dist
        have hbump_ab_1 : bump_ab 1 = 0 := by
          simp only [bump_ab, cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hbump_ab_1, dist_zero_right]
        simp only [bump_ab, cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · simp only [dif_pos hz_ne1, indicatorApproxComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hnorm1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary
            (cayleyTransform_mem_unitary T hT hsa C) hz_mem
          have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R_ab + 1)) := by
            rw [← Complex.dist_eq]; exact hz_dist
          have hclose : ‖z - 1‖ < 1 := calc ‖z - 1‖ < min (1/2) (1 / (R_ab + 1)) := hz_dist_norm
            _ ≤ 1/2 := min_le_left _ _
            _ < 1 := by norm_num
          have hinv_large := inverseCayleyMap_abs_large_near_one z hz_ne1 hnorm1 hclose
          have hz_dist_R : ‖z - 1‖ < 1 / (R_ab + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
          have hR_pos : R_ab + 1 > 0 := by positivity
          have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R_ab := by
            have h1' : 1 / ‖z - 1‖ > R_ab + 1 := by
              have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
              rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
              calc (R_ab + 1) * ‖z - 1‖ < (R_ab + 1) * (1 / (R_ab + 1)) := by
                    apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
            linarith
          -- indicatorApprox is 0 outside [-R_ab, R_ab]
          have hind_zero : indicatorApprox a b ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            apply indicatorApprox_eq_zero_outside
            have hR_a : R_ab > |a - ε| := by
              have h1' : max |a - ε| |b + ε| ≥ |a - ε| := le_max_left _ _; linarith
            have hR_b : R_ab > |b + ε| := by
              have h1' : max |a - ε| |b + ε| ≥ |b + ε| := le_max_right _ _; linarith
            set t := inverseCayleyMap z hz_ne1 with ht_def
            by_cases ht_pos : t ≥ 0
            · right
              have ht_gt_R : t > R_ab := by
                have : |t| = t := abs_of_nonneg ht_pos; linarith
              have : t > b + ε := calc t > R_ab := ht_gt_R
                _ > |b + ε| := hR_b
                _ ≥ b + ε := le_abs_self _
              linarith
            · left
              push Not at ht_pos
              have ht_lt_neg_R : t < -R_ab := by
                have : |t| = -t := abs_of_neg ht_pos; linarith
              have : t < a - ε := calc t < -R_ab := ht_lt_neg_R
                _ < -|a - ε| := by linarith
                _ ≤ a - ε := neg_abs_le _
              linarith
          rw [hind_zero, abs_zero]
          exact hε'
        · push Not at hz_ne1
          simp only [hz_ne1, ne_eq, not_true_eq_false, ↓reduceDIte, norm_zero]
          exact hε'
    · -- w ≠ 1: f is continuous on the open set {z | z ≠ 1}, so continuous at w
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
      have haway := cfcViaInverseCayleyC0_continuousOn (indicatorApproxComplex a b ε hε) w h1
      have hcont_at : ContinuousAt bump_ab w := haway.continuousAt (hopen.mem_nhds h1)
      exact hcont_at.continuousWithinAt
  have hcont_bump_cd : ContinuousOn bump_cd (spectrum ℂ C.U) := by
    intro w hw
    by_cases h1 : w = 1
    · -- At w = 1: need to show continuity at 1
      subst h1
      apply Metric.continuousWithinAt_iff.mpr
      intro ε' hε'
      let R_cd := max (|c - ε|) (|d + ε|) + 1
      use min (1/2) (1 / (R_cd + 1))
      constructor
      · apply lt_min; linarith; positivity
      · intro z hz_mem hz_dist
        have hbump_cd_1 : bump_cd 1 = 0 := by
          simp only [bump_cd, cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hbump_cd_1, dist_zero_right]
        simp only [bump_cd, cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · simp only [dif_pos hz_ne1, indicatorApproxComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hnorm1 : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary
            (cayleyTransform_mem_unitary T hT hsa C) hz_mem
          have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R_cd + 1)) := by
            rw [← Complex.dist_eq]; exact hz_dist
          have hclose : ‖z - 1‖ < 1 := calc ‖z - 1‖ < min (1/2) (1 / (R_cd + 1)) := hz_dist_norm
            _ ≤ 1/2 := min_le_left _ _
            _ < 1 := by norm_num
          have hinv_large := inverseCayleyMap_abs_large_near_one z hz_ne1 hnorm1 hclose
          have hz_dist_R : ‖z - 1‖ < 1 / (R_cd + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
          have hR_pos : R_cd + 1 > 0 := by positivity
          have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R_cd := by
            have h1' : 1 / ‖z - 1‖ > R_cd + 1 := by
              have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
              rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
              calc (R_cd + 1) * ‖z - 1‖ < (R_cd + 1) * (1 / (R_cd + 1)) := by
                    apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
            linarith
          -- indicatorApprox is 0 outside [-R_cd, R_cd]
          have hind_zero : indicatorApprox c d ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            apply indicatorApprox_eq_zero_outside
            have hR_c : R_cd > |c - ε| := by
              have h1' : max |c - ε| |d + ε| ≥ |c - ε| := le_max_left _ _; linarith
            have hR_d : R_cd > |d + ε| := by
              have h1' : max |c - ε| |d + ε| ≥ |d + ε| := le_max_right _ _; linarith
            set t := inverseCayleyMap z hz_ne1 with ht_def
            by_cases ht_pos : t ≥ 0
            · right
              have ht_gt_R : t > R_cd := by
                have : |t| = t := abs_of_nonneg ht_pos; linarith
              have : t > d + ε := calc t > R_cd := ht_gt_R
                _ > |d + ε| := hR_d
                _ ≥ d + ε := le_abs_self _
              linarith
            · left
              push Not at ht_pos
              have ht_lt_neg_R : t < -R_cd := by
                have : |t| = -t := abs_of_neg ht_pos; linarith
              have : t < c - ε := calc t < -R_cd := ht_lt_neg_R
                _ < -|c - ε| := by linarith
                _ ≤ c - ε := neg_abs_le _
              linarith
          rw [hind_zero, abs_zero]
          exact hε'
        · push Not at hz_ne1
          simp only [hz_ne1, ne_eq, not_true_eq_false, ↓reduceDIte, norm_zero]
          exact hε'
    · -- w ≠ 1: f is continuous on the open set {z | z ≠ 1}, so continuous at w
      have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
      have haway := cfcViaInverseCayleyC0_continuousOn (indicatorApproxComplex c d ε hε) w h1
      have hcont_at : ContinuousAt bump_cd w := haway.continuousAt (hopen.mem_nhds h1)
      exact hcont_at.continuousWithinAt
  -- Show that cfc(sqrtDiff)² = cfc(bump_cd) - cfc(bump_ab)
  have hdiff_eq_sq : bumpOperator T hT hsa C c d ε hε - bumpOperator T hT hsa C a b ε hε = R * R := by
    simp only [bumpOperator, sqrtDiffBumpOperator, R]
    -- cfc(bump_cd) - cfc(bump_ab) = cfc(sqrtDiff) * cfc(sqrtDiff)
    rw [← cfc_mul sqrtDiff sqrtDiff C.U hcont_sqrtDiff hcont_sqrtDiff]
    rw [← cfc_sub bump_cd bump_ab C.U hcont_bump_cd hcont_bump_ab]
    congr 1
    ext w
    exact (hsqDiff_eq w).symm
  -- Now use hdiff_eq_sq to show the inner product inequality
  have hdiff_inner : @inner ℂ H _ x ((bumpOperator T hT hsa C c d ε hε -
      bumpOperator T hT hsa C a b ε hε) x) = @inner ℂ H _ x ((R * R) x) := by
    congr 1
    rw [hdiff_eq_sq]
  rw [ContinuousLinearMap.sub_apply, inner_sub_right] at hdiff_inner
  -- ⟨x, R * R x⟩ = ⟨x, R(Rx)⟩ = ⟨R*x, Rx⟩ = ⟨Rx, Rx⟩ = ‖Rx‖² (using R self-adjoint)
  have hRsq_inner : @inner ℂ H _ x ((R * R) x) = @inner ℂ H _ (R x) (R x) := by
    simp only [ContinuousLinearMap.mul_apply]
    -- ⟨x, R(Rx)⟩ = ⟨R.adjoint x, Rx⟩ = ⟨Rx, Rx⟩ (since R.adjoint = R)
    have h1 : @inner ℂ H _ (R.adjoint x) (R x) = @inner ℂ H _ x (R (R x)) :=
      ContinuousLinearMap.adjoint_inner_left R (R x) x
    rw [hR_sa] at h1
    exact h1.symm
  rw [hRsq_inner] at hdiff_inner
  -- ⟨Rx, Rx⟩ = ‖Rx‖² which has non-negative real part
  have hRx_nonneg : 0 ≤ RCLike.re (@inner ℂ H _ (R x) (R x)) := by
    rw [inner_self_eq_norm_sq (R x)]
    exact sq_nonneg _
  -- From hdiff_inner: ⟨x, P_cd x⟩ - ⟨x, P_ab x⟩ = ‖Rx‖²
  -- Taking real parts: re⟨x, P_cd x⟩ - re⟨x, P_ab x⟩ = ‖Rx‖² ≥ 0
  have hre_diff : RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C c d ε hε x)) -
      RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) =
      RCLike.re (@inner ℂ H _ (R x) (R x)) := by
    have h := congrArg RCLike.re hdiff_inner
    simp only [map_sub] at h
    exact h
  linarith [hRx_nonneg]

/- **Note on monotonicity:** Bump operators are NOT globally monotone in ε.

   While `indicatorApprox_mono_eps_on_core` shows that smaller ε gives larger values on [a,b],
   in the transition regions [a-ε, a] and [b, b+ε], the relationship is **reversed**:
   larger ε means wider support, so points outside [a,b] have positive value for large ε
   but value 0 for small ε.

   **Counterexample:** Take x with spectral measure concentrated near a - ε₁.
   Then for ε₂ > ε₁: bump_{ε₂}(a - ε₁) > 0 but bump_{ε₁}(a - ε₁) = 0.

   The Cauchy sequence proof for `bumpOperator_inner_cauchy` therefore uses **dominated
   convergence** for spectral measures instead of monotone convergence:
   - The bump functions bump_ε converge pointwise to χ_{(a,b)} ∪ {1/2 at boundaries}
   - All bump functions satisfy |bump_ε| ≤ 1
   - The spectral measure ⟨x, E(·) x⟩ is finite
   - By dominated convergence: ⟨x, P_ε x⟩ = ∫ bump_ε dμ_x converges -/

/-- The bump operators are positive contractions (0 ≤ bump ≤ 1 implies 0 ≤ P ≤ 1). -/
theorem bumpOperator_nonneg (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) (x : H) :
    0 ≤ RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) := by
  -- STRATEGY: Show P = Q² where Q = sqrtBumpOperator is self-adjoint, then ⟨x, Px⟩ = ‖Qx‖² ≥ 0
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Q = sqrt(bump) operator is self-adjoint
  have hQ_sa := sqrtBumpOperator_self_adjoint T hT hsa C a b ε hε
  let Q := sqrtBumpOperator T hT hsa C a b ε hε
  -- For self-adjoint Q: ⟨x, Q²x⟩ = ⟨Qx, Qx⟩ = ‖Qx‖²
  have hinner_sq : @inner ℂ H _ x (Q (Q x)) = @inner ℂ H _ (Q x) (Q x) := by
    have h1 : @inner ℂ H _ (Q.adjoint x) (Q x) = @inner ℂ H _ x (Q (Q x)) :=
      ContinuousLinearMap.adjoint_inner_left Q (Q x) x
    rw [hQ_sa] at h1
    exact h1.symm
  -- ⟨Qx, Qx⟩ = ‖Qx‖² which has re ≥ 0
  have hQx_norm : RCLike.re (@inner ℂ H _ (Q x) (Q x)) = ‖Q x‖^2 := inner_self_eq_norm_sq (Q x)
  -- Now we need: P = Q² (bump = sqrt(bump)²)
  have hP_eq_Q2 : bumpOperator T hT hsa C a b ε hε = Q * Q := by
    simp only [bumpOperator]
    -- bump = sqrt(bump) * sqrt(bump) pointwise, then use cfc_mul
    have hbump_eq : cfcViaInverseCayleyC0 (indicatorApproxComplex a b ε hε) =
        fun w => cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) w *
                 cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) w := by
      ext w
      simp only [cfcViaInverseCayleyC0]
      split_ifs with h
      · -- w ≠ 1: show bump(t) = sqrt(bump(t))² at t = inverseCayleyMap w h
        simp only [indicatorApproxComplex, sqrtIndicatorApproxComplex, ContinuousMap.coe_mk]
        let t := inverseCayleyMap w h
        have hsq : (sqrtIndicatorApprox a b ε hε t : ℂ) *
                   (sqrtIndicatorApprox a b ε hε t : ℂ) =
                   (indicatorApprox a b ε hε t : ℂ) := by
          rw [← Complex.ofReal_mul]
          congr 1
          have h1 := sqrtIndicatorApprox_sq a b ε hε t
          have : sqrtIndicatorApprox a b ε hε t * sqrtIndicatorApprox a b ε hε t =
                 (sqrtIndicatorApprox a b ε hε t) ^ 2 := by ring
          rw [this, h1]
        exact hsq.symm
      · -- w = 1: show 0 = 0 * 0
        ring
    rw [hbump_eq]
    -- cfc (f * f) = cfc f * cfc f by cfc_mul, which requires continuity on spectrum
    let f := cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε)
    show cfc (fun w => f w * f w) C.U = cfc f C.U * cfc f C.U
    -- Prove continuity of f on spectrum
    have hf_cont : ContinuousOn f (spectrum ℂ C.U) := by
      have hf_cont_away : ContinuousOn f {z | z ≠ 1} :=
        cfcViaInverseCayleyC0_continuousOn (sqrtIndicatorApproxComplex a b ε hε)
      intro w hw
      by_cases h1 : w = 1
      · -- At w = 1: f(1) = 0 and f(z) → 0 as z → 1 (bump functions vanish at infinity)
        subst h1
        rw [Metric.continuousWithinAt_iff]
        intro ε' hε'
        -- For z close to 1, inverseCayleyMap(z) is outside the support of the bump function
        -- Support of sqrtIndicatorApprox is [a-ε, b+ε]
        let R := max (|a - ε|) (|b + ε|) + 1
        -- For |inverseCayleyMap(z)| > R, sqrtIndicatorApprox = 0
        -- inverseCayleyMap(e^{iθ}) = -cot(θ/2) which → ±∞ as θ → 0
        -- We need δ such that |z - 1| < δ implies |inverseCayleyMap(z)| > R
        -- Use δ = 2/(R + 1) (heuristic: small angle θ gives large cot)
        use min (1/2) (1 / (R + 1))
        constructor
        · apply lt_min
          · norm_num
          · positivity
        intro z hz_mem hz_dist
        -- f(1) = 0
        have hf1 : f 1 = 0 := by
          show cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) 1 = 0
          simp only [cfcViaInverseCayleyC0, ne_eq, not_true_eq_false, ↓reduceDIte]
        rw [hf1, dist_zero_right]
        -- Show ‖f z‖ < ε'
        show ‖cfcViaInverseCayleyC0 (sqrtIndicatorApproxComplex a b ε hε) z‖ < ε'
        simp only [cfcViaInverseCayleyC0]
        by_cases hz_ne1 : z ≠ 1
        · -- z ≠ 1: show sqrtIndicatorApprox(inverseCayleyMap z) is small
          rw [dif_pos hz_ne1]
          simp only [sqrtIndicatorApproxComplex, ContinuousMap.coe_mk]
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hnonneg := sqrtIndicatorApprox_nonneg a b ε hε (inverseCayleyMap z hz_ne1)
          rw [abs_of_nonneg hnonneg]
          -- Key insight: for z close to 1, inverseCayleyMap(z) is outside the support
          -- of the bump function, so sqrtIndicatorApprox = sqrt(0) = 0 < ε'
          -- We show indicatorApprox(inverseCayleyMap z) = 0 using that:
          -- 1. |inverseCayleyMap(z)| > R for |z - 1| < 1/(R+1)
          -- 2. This puts inverseCayleyMap(z) outside [a-ε, b+ε]
          simp only [sqrtIndicatorApprox, ContinuousMap.coe_mk]
          -- Show indicatorApprox(inverseCayleyMap z) = 0
          have hind_zero : indicatorApprox a b ε hε (inverseCayleyMap z hz_ne1) = 0 := by
            -- Key: for z close to 1, |inverseCayleyMap z| is large
            -- inverseCayleyMap z = Re(i(1+z)/(1-z))
            -- For |z - 1| < 1/(R+1) ≤ 1/2, we have |inverseCayleyMap z| > R
            -- This means inverseCayleyMap z ∉ [a-ε, b+ε] ⊆ [-R+1, R-1]
            -- The detailed analysis uses properties of the inverse Cayley transform
            -- For a complete proof, we'd need to show:
            -- - For spectrum of unitary U, z is on the unit circle
            -- - inverseCayleyMap(e^{iθ}) = -cot(θ/2) for z = e^{iθ}
            -- - |cot(θ/2)| ≥ 1/|z-1| for |z-1| ≤ 1
            -- - So |inverseCayleyMap z| > 1/(1/(R+1)) = R+1 > R
            -- Using indicatorApprox_eq_zero_outside:
            apply indicatorApprox_eq_zero_outside
            -- Need: inverseCayleyMap z ≤ a - ε OR inverseCayleyMap z ≥ b + ε
            -- Step 1: z is on the unit circle (spectrum of unitary)
            have hon_circle : ‖z‖ = 1 := spectrum_norm_eq_one_cayley T hT hsa C z hz_mem
            -- Step 2: |z - 1| < 1/2 < 1
            have hz_dist_norm : ‖z - 1‖ < min (1/2) (1 / (R + 1)) := by
              rw [← Complex.dist_eq]; exact hz_dist
            have hclose : ‖z - 1‖ < 1 := by
              calc ‖z - 1‖ < min (1/2) (1 / (R + 1)) := hz_dist_norm
                _ ≤ 1/2 := min_le_left _ _
                _ < 1 := by norm_num
            -- Step 3: Use inverseCayleyMap_abs_large_near_one
            have hinv_large : |inverseCayleyMap z hz_ne1| > 1 / ‖z - 1‖ :=
              inverseCayleyMap_abs_large_near_one z hz_ne1 hon_circle hclose
            -- Step 4: Since |z - 1| < 1/(R+1), we have |inverseCayleyMap z| > R + 1
            have hz_dist_R : ‖z - 1‖ < 1 / (R + 1) := lt_of_lt_of_le hz_dist_norm (min_le_right _ _)
            have hR_pos : R + 1 > 0 := by
              have : R = max (|a - ε|) (|b + ε|) + 1 := rfl
              have h1 : max (|a - ε|) (|b + ε|) ≥ 0 := le_max_of_le_left (abs_nonneg _)
              linarith
            have hinv_gt_R : |inverseCayleyMap z hz_ne1| > R := by
              have h1 : 1 / ‖z - 1‖ > R + 1 := by
                have hnorm_pos : ‖z - 1‖ > 0 := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne1)
                rw [gt_iff_lt, lt_div_iff₀ hnorm_pos]
                calc (R + 1) * ‖z - 1‖ < (R + 1) * (1 / (R + 1)) := by
                      apply mul_lt_mul_of_pos_left hz_dist_R hR_pos
                  _ = 1 := mul_one_div_cancel (ne_of_gt hR_pos)
              calc |inverseCayleyMap z hz_ne1| > 1 / ‖z - 1‖ := hinv_large
                _ > R + 1 := h1
                _ > R := by linarith
            -- Step 5: |x| > R implies x ≤ a - ε or x ≥ b + ε
            -- where R = max(|a-ε|, |b+ε|) + 1
            have hR_bound : R > max (|a - ε|) (|b + ε|) := by
              have : R = max (|a - ε|) (|b + ε|) + 1 := rfl
              linarith
            -- |inverseCayleyMap z| > R means inverseCayleyMap z > R or inverseCayleyMap z < -R
            set t := inverseCayleyMap z hz_ne1 with ht_def
            by_cases ht_pos : t ≥ 0
            · -- t ≥ 0 and |t| > R means t > R
              right
              have ht_gt_R : t > R := by
                have : |t| = t := abs_of_nonneg ht_pos
                linarith
              have hmax : R > |b + ε| := lt_of_le_of_lt (le_max_right _ _) hR_bound
              have h1 : t > b + ε := calc t > R := ht_gt_R
                  _ > |b + ε| := hmax
                  _ ≥ b + ε := le_abs_self _
              exact le_of_lt h1
            · -- t < 0 and |t| > R means t < -R
              left
              push Not at ht_pos
              have ht_lt_neg_R : t < -R := by
                have : |t| = -t := abs_of_neg ht_pos
                linarith
              have hmax : R > |a - ε| := lt_of_le_of_lt (le_max_left _ _) hR_bound
              have h1 : t < a - ε := calc t < -R := ht_lt_neg_R
                  _ < -|a - ε| := by linarith
                  _ ≤ a - ε := neg_abs_le _
              exact le_of_lt h1
          rw [hind_zero, Real.sqrt_zero]
          exact hε'
        · -- z = 1: ‖0‖ < ε'
          push Not at hz_ne1
          rw [dif_neg (not_ne_iff.mpr hz_ne1)]
          simp only [norm_zero, hε']
      · -- At w ≠ 1: use continuity away from 1
        have hmem : w ∈ {z : ℂ | z ≠ 1} := h1
        have hcont_at_w := hf_cont_away w hmem
        rw [Metric.continuousWithinAt_iff] at hcont_at_w ⊢
        intro ε' hε'
        obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := hcont_at_w ε' hε'
        have hw_dist : 0 < dist w 1 := by rw [dist_pos]; exact h1
        use min δ₁ (dist w 1 / 2)
        constructor
        · exact lt_min hδ₁_pos (half_pos hw_dist)
        intro z hz_mem hz_dist
        apply hδ₁
        · simp only [Set.mem_setOf_eq]
          intro hz_eq_1
          rw [hz_eq_1] at hz_dist
          have h1 : dist w 1 / 2 < dist w 1 := half_lt_self hw_dist
          rw [dist_comm] at hz_dist
          have h2 : dist w 1 < min δ₁ (dist w 1 / 2) := hz_dist
          linarith [min_le_right δ₁ (dist w 1 / 2)]
        · exact lt_of_lt_of_le hz_dist (min_le_left δ₁ _)
    exact cfc_mul f f C.U hf_cont hf_cont
  -- Now combine: ⟨x, Px⟩ = ⟨x, Q²x⟩ = ⟨Qx, Qx⟩ and re(⟨Qx, Qx⟩) = ‖Qx‖² ≥ 0
  have hcalc : RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x)) = ‖Q x‖^2 := by
    calc RCLike.re (@inner ℂ H _ x (bumpOperator T hT hsa C a b ε hε x))
        = RCLike.re (@inner ℂ H _ x ((Q * Q) x)) := by rw [hP_eq_Q2]
      _ = RCLike.re (@inner ℂ H _ x (Q (Q x))) := rfl
      _ = RCLike.re (@inner ℂ H _ (Q x) (Q x)) := by rw [hinner_sq]
      _ = ‖Q x‖^2 := hQx_norm
  rw [hcalc]
  exact sq_nonneg ‖Q x‖

/-- Bump function difference is bounded by 1. -/
lemma indicatorApprox_diff_le (a b ε₁ ε₂ : ℝ) (hε₁ : ε₁ > 0) (hε₂ : ε₂ > 0) (x : ℝ) :
    |indicatorApprox a b ε₁ hε₁ x - indicatorApprox a b ε₂ hε₂ x| ≤ 1 := by
  have h1 := indicatorApprox_le_one a b ε₁ hε₁ x
  have h2 := indicatorApprox_nonneg a b ε₁ hε₁ x
  have h3 := indicatorApprox_le_one a b ε₂ hε₂ x
  have h4 := indicatorApprox_nonneg a b ε₂ hε₂ x
  rw [abs_le]
  constructor <;> linarith

/-- The bump operators are uniformly bounded by 1. -/
theorem bumpOperator_norm_le_one (T : UnboundedOperator H) (hT : T.IsDenselyDefined)
    (hsa : T.IsSelfAdjoint hT) (C : CayleyTransform T hT hsa)
    (a b ε : ℝ) (hε : ε > 0) :
    ‖bumpOperator T hT hsa C a b ε hε‖ ≤ 1 := by
  unfold bumpOperator
  haveI hNormal : IsStarNormal C.U := cayleyTransform_isStarNormal T hT hsa C
  -- Use norm_cfc_le: if ‖f(x)‖ ≤ c for x ∈ spectrum, then ‖cfc(f)‖ ≤ c
  apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
  intro w _
  simp only [cfcViaInverseCayleyC0]
  split_ifs with h
  · -- w ≠ 1
    simp only [indicatorApproxComplex, ContinuousMap.coe_mk]
    have h1 := indicatorApprox_nonneg a b ε hε (inverseCayleyMap w h)
    have h2 := indicatorApprox_le_one a b ε hε (inverseCayleyMap w h)
    calc ‖(↑((indicatorApprox a b ε hε) (inverseCayleyMap w h)) : ℂ)‖
        = |(indicatorApprox a b ε hε) (inverseCayleyMap w h)| := by
          simp only [Complex.norm_real, Real.norm_eq_abs]
      _ = (indicatorApprox a b ε hε) (inverseCayleyMap w h) := abs_of_nonneg h1
      _ ≤ 1 := h2
  · -- w = 1: f(1) = 0, so ‖0‖ ≤ 1
    simp only [norm_zero]
    norm_num



/-! ### Strong operator topology limits -/

/-- A sequence of operators A_n converges in the strong operator topology (SOT)
    to A if A_n x → A x for all x ∈ H. -/
def SOTConverges (A : ℕ → H →L[ℂ] H) (L : H →L[ℂ] H) : Prop :=
  ∀ x : H, Tendsto (fun n => A n x) atTop (nhds (L x))

/-- For a self-adjoint positive contraction B (0 ≤ B ≤ I in Loewner order), we have ‖Bx‖² ≤ re⟨x, Bx⟩.

    **Proof:** For self-adjoint B, ‖Bx‖² = ⟨Bx, Bx⟩ = ⟨x, B²x⟩. Since 0 ≤ B ≤ I implies
    B² ≤ B (because B(I-B) ≥ 0 for commuting positive operators), we get
    ⟨x, B²x⟩ ≤ ⟨x, Bx⟩.

    The condition 0 ≤ B ≤ I in Loewner order means:
    - ⟨x, Bx⟩ ≥ 0 for all x (positivity)
    - ⟨x, Bx⟩ ≤ ‖x‖² for all x (bounded by identity) -/
lemma norm_sq_le_inner_of_positive_contraction (B : H →L[ℂ] H)
    (hSA : B.adjoint = B)
    (hPos : ∀ x, 0 ≤ RCLike.re (@inner ℂ H _ x (B x)))
    (hLeI : ∀ x, RCLike.re (@inner ℂ H _ x (B x)) ≤ ‖x‖^2)
    (x : H) :
    ‖B x‖^2 ≤ RCLike.re (@inner ℂ H _ x (B x)) := by
  -- Step 1: ‖Bx‖² = re⟨Bx, Bx⟩ (inner product with itself equals norm squared)
  have h1 : (‖B x‖ : ℝ)^2 = RCLike.re (@inner ℂ H _ (B x) (B x)) := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (B x)
    simp only [RCLike.re_to_complex] at this ⊢
    exact this.symm
  -- Step 2: ⟨Bx, Bx⟩ = ⟨x, B²x⟩ using adjoint property and B = B*
  -- adjoint_inner_right A x y : ⟨x, A* y⟩ = ⟨A x, y⟩
  -- With A = B, x = x, y = Bx: ⟨x, B*(Bx)⟩ = ⟨Bx, Bx⟩
  -- Since B* = B: ⟨x, B(Bx)⟩ = ⟨Bx, Bx⟩
  have h2 : @inner ℂ H _ (B x) (B x) = @inner ℂ H _ x ((B * B) x) := by
    have hadj := ContinuousLinearMap.adjoint_inner_right B x (B x)
    -- hadj : ⟨x, B*(Bx)⟩ = ⟨Bx, Bx⟩
    rw [hSA] at hadj
    -- hadj : ⟨x, B(Bx)⟩ = ⟨Bx, Bx⟩
    exact hadj.symm
  -- Step 3: We need B² ≤ B in Loewner order, i.e., re⟨x, B²x⟩ ≤ re⟨x, Bx⟩
  -- This follows from t² ≤ t for t ∈ [0,1], applied via functional calculus
  -- For 0 ≤ B ≤ I, the spectrum of B is in [0,1], and f(t) = t - t² ≥ 0 on [0,1]
  -- Hence B - B² ≥ 0, so B² ≤ B
  -- This is a non-trivial spectral theory result
  have h3 : RCLike.re (@inner ℂ H _ x ((B * B) x)) ≤ RCLike.re (@inner ℂ H _ x (B x)) := by
    -- The key estimate: B² ≤ B for 0 ≤ B ≤ I (Loewner order)
    -- **Proof using spectral square root:**
    -- For 0 ≤ B ≤ I self-adjoint, let C = √B (positive square root via spectral theorem).
    -- Then C² = B and 0 ≤ C ≤ I (since √· is operator monotone on [0,∞)).
    -- Apply hLeI to vector Cx: ⟨Cx, B(Cx)⟩ ≤ ‖Cx‖²
    -- LHS = ⟨x, C·B·C x⟩ = ⟨x, C·C²·C x⟩ = ⟨x, C⁴x⟩ = ⟨x, B²x⟩
    -- RHS = ‖Cx‖² = ⟨Cx, Cx⟩ = ⟨x, C²x⟩ = ⟨x, Bx⟩
    -- Hence ⟨x, B²x⟩ ≤ ⟨x, Bx⟩, i.e., B² ≤ B.
    --
    -- **Alternative proof using CFC:**
    -- For t ∈ [0,1]: t - t² = t(1-t) ≥ 0
    -- By CFC positivity: cfc(t - t², B) = B - B² ≥ 0
    --
    -- Both proofs require spectral theory infrastructure.
    -- Suffices to show: ⟨x, Bx⟩ - ⟨x, B²x⟩ ≥ 0
    have hdiff : RCLike.re (@inner ℂ H _ x (B x)) - RCLike.re (@inner ℂ H _ x ((B * B) x)) =
        RCLike.re (@inner ℂ H _ x ((B - B * B) x)) := by
      rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
    suffices hkey : 0 ≤ RCLike.re (@inner ℂ H _ x ((B - B * B) x)) by linarith
    -- B - B² = B(I - B), and for commuting positive operators, the product is positive
    -- Strategy: Prove 0 ≤ B and B ≤ 1 in Loewner order, then use CFC
    -- The key estimate: for 0 ≤ B ≤ I self-adjoint, we have B² ≤ B
    -- Equivalently: ⟨x, Bx⟩ ≥ ⟨x, B²x⟩ = ‖Bx‖² for all x
    --
    -- **Proof strategy using CFC:**
    -- 1. B is self-adjoint with spectrum in [0,1] (from 0 ≤ B ≤ I)
    -- 2. The function f(t) = t - t² = t(1-t) is nonneg on [0,1]
    -- 3. By CFC: cfc(f, B) = B - B² ≥ 0
    -- 4. Hence ⟨x, (B - B²)x⟩ ≥ 0, i.e., ⟨x, Bx⟩ ≥ ⟨x, B²x⟩
    --
    -- **Alternative direct proof:**
    -- For self-adjoint B: ⟨x, B²x⟩ = ⟨Bx, Bx⟩ = ‖Bx‖²
    -- So we need ⟨x, Bx⟩.re ≥ ‖Bx‖²
    -- This follows from: for 0 ≤ B ≤ I, the spectrum is in [0,1], so B² ≤ B
    --
    -- **Proof using CFC.sqrt:**
    -- Step 1: Show B is positive in Loewner order (0 ≤ B)
    have hB_isPos : B.IsPositive := by
      rw [ContinuousLinearMap.isPositive_def']
      constructor
      · exact hSA
      · intro y
        rw [ContinuousLinearMap.reApplyInnerSelf]
        -- re⟪B y, y⟫ = re⟪y, B y⟫ by inner_re_symm
        rw [inner_re_symm]
        exact hPos y
    have hB_nonneg : (0 : H →L[ℂ] H) ≤ B := by
      rw [ContinuousLinearMap.nonneg_iff_isPositive]
      exact hB_isPos
    -- Step 2: Let C = √B (exists since B ≥ 0)
    let C := CFC.sqrt B
    -- C is nonnegative and self-adjoint
    have hC_nonneg : (0 : H →L[ℂ] H) ≤ C := CFC.sqrt_nonneg B
    have hC_isPos : C.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive C).mp hC_nonneg
    have hC_sa : C.adjoint = C := hC_isPos.isSelfAdjoint
    -- C² = B
    have hC_sq : C * C = B := CFC.sqrt_mul_sqrt_self B hB_nonneg
    -- Step 3: Apply hLeI to (C x)
    -- We need: re⟪C x, B (C x)⟫ ≤ ‖C x‖²
    -- hLeI gives: re⟪y, B y⟫ ≤ ‖y‖² for all y
    -- Applying to y = C x: re⟪C x, B (C x)⟫ ≤ ‖C x‖²
    have hLeI_Cx : RCLike.re (@inner ℂ H _ (C x) (B (C x))) ≤ ‖C x‖^2 := hLeI (C x)
    -- Step 4: Transform LHS: ⟨C x, B (C x)⟩ = ⟨x, C⁴ x⟩ = ⟨x, B² x⟩
    -- Using adjoint_inner_right: ⟪x, C† y⟫ = ⟪C x, y⟫
    -- With C† = C: ⟪x, C y⟫ = ⟪C x, y⟫, equivalently ⟪C x, y⟫ = ⟪x, C y⟫
    have hLHS : @inner ℂ H _ (C x) (B (C x)) = @inner ℂ H _ x ((B * B) x) := by
      -- ⟨Cx, B(Cx)⟩ = ⟨Cx, C²(Cx)⟩
      rw [← hC_sq]
      -- Unfold to ⟨Cx, C(C(Cx))⟩
      simp only [ContinuousLinearMap.mul_apply]
      -- adjoint_inner_right C x z : ⟪x, C† z⟫ = ⟪C x, z⟫
      -- With C† = C and z = C(C(Cx)): ⟪x, C(C(C(Cx)))⟫ = ⟪Cx, C(C(Cx))⟫
      -- Taking symm: ⟪Cx, C(C(Cx))⟫ = ⟪x, C(C(C(Cx)))⟫
      -- adjoint_inner_right C x z : ⟪x, C z⟫ = ⟪C x, z⟫ (since C† = C)
      -- We need: ⟪Cx, C(C(Cx))⟫ = ⟪x, C(C(C(Cx)))⟫
      -- From adjoint_inner_right with z = C(C(Cx)): ⟪x, C(C(C(Cx)))⟫ = ⟪Cx, C(C(Cx))⟫
      -- So the symm gives us our goal!
      have step := ContinuousLinearMap.adjoint_inner_right C x (C (C (C x)))
      rw [hC_sa] at step
      -- After simp, goal is: ⟨Cx, C(C(Cx))⟩ = ⟨x, C(C(C(Cx)))⟩
      -- step.symm provides exactly: ⟨Cx, C(C(Cx))⟩ = ⟨x, C(C(C(Cx)))⟩
      exact step.symm
    -- Step 5: Transform RHS: ‖Cx‖² = ⟨Cx, Cx⟩ = ⟨x, C² x⟩ = re⟨x, B x⟩
    have hRHS : (‖C x‖ : ℝ)^2 = RCLike.re (@inner ℂ H _ x (B x)) := by
      -- ‖Cx‖² = re⟨Cx, Cx⟩ (inner product with itself equals norm squared)
      have h_norm_sq := inner_self_eq_norm_sq (𝕜 := ℂ) (C x)
      simp only [RCLike.re_to_complex] at h_norm_sq
      -- Using adjoint_inner_right: ⟪x, C y⟫ = ⟪C x, y⟫
      -- With y = Cx: ⟪x, C(Cx)⟫ = ⟪Cx, Cx⟫
      -- Taking symm: ⟪Cx, Cx⟫ = ⟪x, C(Cx)⟫ = ⟪x, Bx⟫
      have step := ContinuousLinearMap.adjoint_inner_right C x (C x)
      rw [hC_sa] at step
      have hinner_eq : @inner ℂ H _ (C x) (C x) = @inner ℂ H _ x (B x) := by
        rw [step.symm]
        simp only [← ContinuousLinearMap.mul_apply, hC_sq]
      -- h_norm_sq : (inner (C x) (C x)).re = ‖C x‖²
      -- Goal: ‖C x‖² = re(inner x (B x))
      calc (‖C x‖ : ℝ)^2 = (@inner ℂ H _ (C x) (C x)).re := h_norm_sq.symm
        _ = (@inner ℂ H _ x (B x)).re := by rw [hinner_eq]
        _ = RCLike.re (@inner ℂ H _ x (B x)) := rfl
    -- Step 6: Combine: re⟨x, B²x⟩ ≤ re⟨x, Bx⟩, hence 0 ≤ re⟨x, (B - B²)x⟩
    have hLHS_re : RCLike.re (@inner ℂ H _ x ((B * B) x)) =
        RCLike.re (@inner ℂ H _ (C x) (B (C x))) := by
      rw [← hLHS]
    -- First show re⟨x, B²x⟩ ≤ re⟨x, Bx⟩
    have hB2_le_B : RCLike.re (@inner ℂ H _ x ((B * B) x)) ≤ RCLike.re (@inner ℂ H _ x (B x)) :=
      calc RCLike.re (@inner ℂ H _ x ((B * B) x))
          = RCLike.re (@inner ℂ H _ (C x) (B (C x))) := hLHS_re
        _ ≤ ‖C x‖^2 := hLeI_Cx
        _ = RCLike.re (@inner ℂ H _ x (B x)) := hRHS
    -- Now use hdiff: re⟨x, Bx⟩ - re⟨x, B²x⟩ = re⟨x, (B - B²)x⟩
    -- We have re⟨x, B²x⟩ ≤ re⟨x, Bx⟩, i.e., 0 ≤ re⟨x, Bx⟩ - re⟨x, B²x⟩
    linarith
  calc (‖B x‖ : ℝ)^2 = RCLike.re (@inner ℂ H _ (B x) (B x)) := h1
    _ = RCLike.re (@inner ℂ H _ x ((B * B) x)) := by rw [h2]
    _ ≤ RCLike.re (@inner ℂ H _ x (B x)) := h3

/-- For monotone increasing sequences of positive contractions, the SOT limit exists.

    **Proof outline:**
    1. For each x, the sequence ⟨x, A_n x⟩ is monotone increasing (from hMono) and bounded by ‖x‖²
    2. Hence ⟨x, A_n x⟩ converges for each x (monotone bounded real sequences converge)
    3. By polarization, ⟨x, A_n y⟩ converges for all x, y
    4. This defines a bounded sesquilinear form B(x,y) = lim_n ⟨x, A_n y⟩
    5. Apply sesquilinearToOperator to get L with ⟨x, Ly⟩ = B(x,y)
    6. Show A_n x → L x using: for n > m, (A_n - A_m)² ≤ A_n - A_m when 0 ≤ A_m ≤ A_n ≤ I
       So ‖A_n x - A_m x‖² = ⟨x, (A_n-A_m)² x⟩ ≤ ⟨x, (A_n-A_m) x⟩ → 0, showing A_n x is Cauchy. -/
theorem monotone_positive_contraction_SOT_limit
    (A : ℕ → H →L[ℂ] H)
    (hSA : ∀ n, (A n).adjoint = A n)  -- self-adjoint
    (hPos : ∀ n x, 0 ≤ RCLike.re (@inner ℂ H _ x (A n x)))  -- positive
    (hBound : ∀ n, ‖A n‖ ≤ 1)  -- contraction
    (hMono : ∀ n x, RCLike.re (@inner ℂ H _ x (A n x)) ≤ RCLike.re (@inner ℂ H _ x (A (n+1) x))) :
    ∃ L : H →L[ℂ] H, SOTConverges A L := by
  -- Step 1: For each x, A_n x is a Cauchy sequence in H
  have hCauchy : ∀ x : H, CauchySeq (fun n => A n x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    -- The diagonal inner products ⟨x, A_n x⟩ form a monotone bounded sequence
    -- Use that ⟨x, A_n x⟩ converges (monotone + bounded ⟹ Cauchy)
    have hdiag_mono : Monotone (fun n => RCLike.re (@inner ℂ H _ x (A n x))) := by
      intro n m hnm
      induction hnm with
      | refl => rfl
      | step _ ih => exact le_trans ih (hMono _ x)
    have hdiag_bound : ∀ n, RCLike.re (@inner ℂ H _ x (A n x)) ≤ ‖x‖^2 := by
      intro n
      have h1 : ‖@inner ℂ H _ x (A n x)‖ ≤ ‖x‖ * ‖A n x‖ := norm_inner_le_norm x (A n x)
      have h2 : ‖A n x‖ ≤ ‖A n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      have h3 : ‖A n‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _)
      have h4 : ‖A n x‖ ≤ ‖x‖ := by linarith
      have h5 : ‖@inner ℂ H _ x (A n x)‖ ≤ ‖x‖^2 := by
        calc ‖@inner ℂ H _ x (A n x)‖ ≤ ‖x‖ * ‖A n x‖ := h1
          _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
          _ = ‖x‖^2 := by ring
      -- |re z| ≤ |z| for complex z, and |z| = ‖z‖
      have h6 : |RCLike.re (@inner ℂ H _ x (A n x))| ≤ ‖@inner ℂ H _ x (A n x)‖ :=
        RCLike.abs_re_le_norm _
      have h7 : RCLike.re (@inner ℂ H _ x (A n x)) ≤ |RCLike.re (@inner ℂ H _ x (A n x))| :=
        le_abs_self _
      linarith
    -- The monotone bounded sequence converges, hence is Cauchy
    -- In ℝ, monotone bounded sequences converge (and hence are Cauchy)
    have hdiag_bddAbove : BddAbove (Set.range (fun n => RCLike.re (@inner ℂ H _ x (A n x)))) :=
      ⟨‖x‖^2, fun _ ⟨n, hn⟩ => hn ▸ hdiag_bound n⟩
    have hdiag_tendsto : ∃ L, Tendsto (fun n => RCLike.re (@inner ℂ H _ x (A n x))) atTop (nhds L) :=
      ⟨_, tendsto_atTop_ciSup hdiag_mono hdiag_bddAbove⟩
    have hdiag_cauchy : CauchySeq (fun n => RCLike.re (@inner ℂ H _ x (A n x))) :=
      hdiag_tendsto.choose_spec.cauchySeq
    rw [Metric.cauchySeq_iff] at hdiag_cauchy
    -- For the vector sequence, use ‖A_n x - A_m x‖² ≤ ⟨x, (A_n - A_m) x⟩ for n > m
    -- This follows from (A_n - A_m)² ≤ A_n - A_m when 0 ≤ A_m ≤ A_n ≤ I
    obtain ⟨N, hN⟩ := hdiag_cauchy (ε^2) (sq_pos_of_pos hε)
    use N
    intro n hn m hm
    -- Without loss of generality, assume n ≥ m (the distance is symmetric)
    wlog hnm : m ≤ n generalizing n m with hsymm
    · rw [dist_comm]
      exact hsymm m hm n hn (le_of_lt (not_le.mp hnm))
    -- Now n ≥ m, so A_n - A_m ≥ 0
    -- The key estimate: ‖A_n x - A_m x‖² ≤ ⟨x, A_n x⟩ - ⟨x, A_m x⟩
    -- This follows from the spectral theorem or direct computation using (A_n - A_m)² ≤ A_n - A_m
    have hdiff_pos : 0 ≤ RCLike.re (@inner ℂ H _ x ((A n - A m) x)) := by
      simp only [ContinuousLinearMap.sub_apply, inner_sub_right]
      have h := hdiag_mono hnm
      simp only [RCLike.re_to_complex, Complex.sub_re] at h ⊢
      linarith
    -- For the norm bound, we use that for 0 ≤ B ≤ I, ⟨Bx, Bx⟩ ≤ ⟨x, Bx⟩
    -- This follows from B² ≤ B (a consequence of B(I-B) ≥ 0 and B = B*)
    -- For now, bound directly: ‖(A_n - A_m) x‖² ≤ ‖A_n - A_m‖² ‖x‖² ≤ 4‖x‖²
    -- But this doesn't give us Cauchy. We need the finer estimate.
    -- The finer estimate uses: for self-adjoint B with 0 ≤ B ≤ I, ‖Bx‖² ≤ ⟨x, Bx⟩
    -- Proof: ⟨Bx, Bx⟩ = ⟨x, B²x⟩ ≤ ⟨x, Bx⟩ (since B² ≤ B for 0 ≤ B ≤ I)
    -- The condition B² ≤ B follows from B(I-B) ≥ 0, which holds when 0 ≤ B ≤ I
    -- For the formal proof, we apply this with B = A_n - A_m
    have hB_bound : dist (A n x) (A m x) < ε := by
      rw [dist_eq_norm]
      -- Use that ⟨x, A_n x⟩ - ⟨x, A_m x⟩ < ε² for large n, m
      have hdist_re : |RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x))| < ε^2 := by
        have h1 := hN n hn m hm
        rw [Real.dist_eq] at h1
        exact h1
      -- The real part difference bounds the norm squared (by the estimate above)
      -- ‖A_n x - A_m x‖² ≤ ⟨x, (A_n - A_m) x⟩.re = ⟨x, A_n x⟩.re - ⟨x, A_m x⟩.re < ε²
      -- Hence ‖A_n x - A_m x‖ < ε
      -- For a complete proof, we need the estimate ‖Bx‖² ≤ ⟨x, Bx⟩.re for 0 ≤ B ≤ I
      -- This is a standard result that requires the spectral theorem or direct verification
      -- For now, we use that the difference of diagonal inner products controls the distance
      by_cases hx : x = 0
      · simp [hx, hε]
      · -- Use the bound ‖A_n x - A_m x‖² ≤ (⟨x, A_n x⟩ - ⟨x, A_m x⟩).re via the auxiliary lemma
        -- Let B = A n - A m. We verify the hypotheses of norm_sq_le_inner_of_positive_contraction:
        let B := A n - A m
        -- B is self-adjoint
        have hB_sa : B.adjoint = B := by
          have h1 : (A n).adjoint = A n := hSA n
          have h2 : (A m).adjoint = A m := hSA m
          calc B.adjoint = (A n - A m).adjoint := rfl
            _ = (A n).adjoint - (A m).adjoint := map_sub _ _ _
            _ = A n - A m := by rw [h1, h2]
        -- B ≥ 0 (positivity) - prove for all y
        have hB_pos : ∀ y, 0 ≤ RCLike.re (@inner ℂ H _ y (B y)) := by
          intro y
          have hBy : B y = A n y - A m y := ContinuousLinearMap.sub_apply _ _ _
          rw [hBy, inner_sub_right]
          -- For y, we need the monotonicity of ⟨y, A_k y⟩
          have hdiag_mono_y : RCLike.re (@inner ℂ H _ y (A m y)) ≤ RCLike.re (@inner ℂ H _ y (A n y)) := by
            have hmono : Monotone (fun k => RCLike.re (@inner ℂ H _ y (A k y))) := by
              intro i j hij
              induction hij with
              | refl => rfl
              | step _ ih => exact le_trans ih (hMono _ y)
            exact hmono hnm
          -- RCLike.re (a - b) = RCLike.re a - RCLike.re b
          rw [map_sub]
          linarith
        -- B ≤ I (bounded by identity): ⟨y, By⟩ ≤ ‖y‖² for all y
        have hB_leI : ∀ y, RCLike.re (@inner ℂ H _ y (B y)) ≤ ‖y‖^2 := by
          intro y
          have hBy : B y = A n y - A m y := ContinuousLinearMap.sub_apply _ _ _
          rw [hBy, inner_sub_right]
          -- Need ⟨y, A_n y⟩ ≤ ‖y‖² for all y and A_m ≥ 0
          have hdiag_bound_y : ∀ k, RCLike.re (@inner ℂ H _ y (A k y)) ≤ ‖y‖^2 := by
            intro k
            have h1 : ‖@inner ℂ H _ y (A k y)‖ ≤ ‖y‖ * ‖A k y‖ := norm_inner_le_norm y (A k y)
            have h2 : ‖A k y‖ ≤ ‖A k‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
            have h3 : ‖A k‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hBound k) (norm_nonneg _)
            have h4 : ‖A k y‖ ≤ ‖y‖ := by linarith
            have h5 : ‖@inner ℂ H _ y (A k y)‖ ≤ ‖y‖^2 := by
              calc ‖@inner ℂ H _ y (A k y)‖ ≤ ‖y‖ * ‖A k y‖ := h1
                _ ≤ ‖y‖ * ‖y‖ := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
                _ = ‖y‖^2 := by ring
            have h6 : |RCLike.re (@inner ℂ H _ y (A k y))| ≤ ‖@inner ℂ H _ y (A k y)‖ :=
              RCLike.abs_re_le_norm _
            have h7 : RCLike.re (@inner ℂ H _ y (A k y)) ≤ |RCLike.re (@inner ℂ H _ y (A k y))| :=
              le_abs_self _
            linarith
          rw [map_sub]
          linarith [hdiag_bound_y n, hPos m y]
        -- Apply the auxiliary lemma
        have hkey : ‖B x‖^2 ≤ RCLike.re (@inner ℂ H _ x (B x)) :=
          norm_sq_le_inner_of_positive_contraction B hB_sa hB_pos hB_leI x
        -- Now connect to the original goal
        have hBx : B x = A n x - A m x := ContinuousLinearMap.sub_apply _ _ _
        have hB_inner_eq : RCLike.re (@inner ℂ H _ x (B x)) =
            RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x)) := by
          rw [hBx, inner_sub_right, map_sub]
        rw [hB_inner_eq] at hkey
        -- Since n ≥ m, the difference is positive, so |diff| = diff < ε²
        have hdiff_nonneg : 0 ≤ RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x)) := by
          have h := hdiag_mono hnm
          linarith
        have hdiff_lt : RCLike.re (@inner ℂ H _ x (A n x)) - RCLike.re (@inner ℂ H _ x (A m x)) < ε^2 := by
          rw [abs_of_nonneg hdiff_nonneg] at hdist_re
          exact hdist_re
        -- ‖(A n - A m) x‖² < ε², so ‖(A n - A m) x‖ < ε
        have hnorm_sq_lt : ‖B x‖^2 < ε^2 := lt_of_le_of_lt hkey hdiff_lt
        have hnorm_nonneg : 0 ≤ ‖B x‖ := norm_nonneg _
        have hε_pos : 0 < ε := hε
        have hnorm_lt : ‖B x‖ < ε := by
          nlinarith [sq_nonneg ‖B x‖, sq_nonneg ε]
        exact hnorm_lt
    exact hB_bound
  -- Step 2: Extract the limit for each x
  -- Since H is complete and A_n x is Cauchy, it converges
  have hlim : ∀ x, ∃ y, Tendsto (fun n => A n x) atTop (nhds y) := by
    intro x
    exact cauchySeq_tendsto_of_complete (hCauchy x)
  -- Define L x as the limit of A_n x
  let L_fun : H → H := fun x => Classical.choose (hlim x)
  have hL_spec : ∀ x, Tendsto (fun n => A n x) atTop (nhds (L_fun x)) :=
    fun x => Classical.choose_spec (hlim x)
  -- Step 3: Show L_fun is linear
  have hL_add : ∀ x y, L_fun (x + y) = L_fun x + L_fun y := by
    intro x y
    have h1 : Tendsto (fun n => A n (x + y)) atTop (nhds (L_fun (x + y))) := hL_spec (x + y)
    have h2 : Tendsto (fun n => A n x + A n y) atTop (nhds (L_fun x + L_fun y)) :=
      (hL_spec x).add (hL_spec y)
    have h3 : (fun n => A n (x + y)) = (fun n => A n x + A n y) := by
      ext n; exact (A n).map_add x y
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  have hL_smul : ∀ (c : ℂ) x, L_fun (c • x) = c • L_fun x := by
    intro c x
    have h1 : Tendsto (fun n => A n (c • x)) atTop (nhds (L_fun (c • x))) := hL_spec (c • x)
    have h2 : Tendsto (fun n => c • A n x) atTop (nhds (c • L_fun x)) :=
      (hL_spec x).const_smul c
    have h3 : (fun n => A n (c • x)) = (fun n => c • A n x) := by
      ext n; exact (A n).map_smul c x
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  -- Step 4: Show L_fun is bounded
  have hL_bound : ∃ C : ℝ, ∀ x, ‖L_fun x‖ ≤ C * ‖x‖ := by
    use 1
    intro x
    -- ‖L_fun x‖ = lim ‖A_n x‖ ≤ lim (‖A_n‖ * ‖x‖) ≤ 1 * ‖x‖
    have htend : Tendsto (fun n => ‖A n x‖) atTop (nhds ‖L_fun x‖) :=
      (continuous_norm.tendsto _).comp (hL_spec x)
    have hbound_seq : ∀ n, ‖A n x‖ ≤ 1 * ‖x‖ := by
      intro n
      calc ‖A n x‖ ≤ ‖A n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (hBound n) (norm_nonneg _)
    exact le_of_tendsto htend (Filter.Eventually.of_forall hbound_seq)
  -- Construct L as a continuous linear map
  let L_lin : H →ₗ[ℂ] H := {
    toFun := L_fun
    map_add' := hL_add
    map_smul' := hL_smul
  }
  obtain ⟨C, hC⟩ := hL_bound
  let L : H →L[ℂ] H := ⟨L_lin, AddMonoidHomClass.continuous_of_bound L_lin C hC⟩
  use L
  -- L satisfies SOTConverges
  intro x
  exact hL_spec x

