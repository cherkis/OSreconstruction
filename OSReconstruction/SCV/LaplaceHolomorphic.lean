import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Probability.Moments.ComplexMGF
import OSReconstruction.SCV.Osgood

/-
Copyright (c) 2026 ModularPhysics Contributors.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/

/-!
# Holomorphic Laplace Transforms

This file packages the one-variable half-plane holomorphicity statement needed
in the OS II reconstruction route: the Laplace transform of a finite measure
supported in `[0, ∞)` is holomorphic on the right half-plane.

The main theorem is:

* `SCV.laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport`
* `SCV.multivariateLaplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport`

The scalar theorem is proved by reducing to Mathlib's `ProbabilityTheory.complexMGF`
theory. The multivariate theorem is then obtained by combining a genuine
one-coordinate differentiation-under-the-integral argument with `SCV.osgood_lemma`.
-/

open MeasureTheory Filter Set Complex Real
open scoped Topology ProbabilityTheory

noncomputable section

namespace SCV

/-- The change-of-variable map `s ↦ -log s` used to pass from spectral variables
in `(0,1]` to Laplace variables in `[0,∞)`. -/
def negLogMap : ℝ → ℝ := fun s => -Real.log s

/-- Measurability of `s ↦ -log s`. -/
theorem negLogMap_measurable : Measurable negLogMap := by
  exact Real.measurable_log.neg

/-- Pushforward of a measure under `s ↦ -log s`, the basic spectral-to-Laplace
change of variables. -/
def laplaceMeasure (μ : Measure ℝ) : Measure ℝ := μ.map negLogMap

instance laplaceMeasure_isFinite (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (laplaceMeasure μ) := by
  unfold laplaceMeasure
  exact ⟨by
    rw [Measure.map_apply negLogMap_measurable MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top μ Set.univ⟩

/-- Rewrite a positive real power as an exponential of a logarithm. -/
theorem rpow_eq_exp_log (s : ℝ) (hs : 0 < s) (t : ℝ) :
    s ^ t = Real.exp (t * Real.log s) := by
  rw [Real.rpow_def_of_pos hs]
  ring_nf

/-- Rewrite `s^t` for `s > 0` in the Laplace form `exp (-t * (-log s))`. -/
theorem rpow_eq_exp_neg_neglog (s : ℝ) (hs : 0 < s) (t : ℝ) :
    s ^ t = Real.exp (-t * negLogMap s) := by
  unfold negLogMap
  rw [rpow_eq_exp_log s hs t]
  congr 1
  ring

/-- For a finite measure supported in `(0,∞)`, the `s^t` integral equals the
Laplace integral after the change of variables `u = -log s`. -/
theorem spectral_integral_eq_laplace
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iic 0) = 0)
    (t : ℝ) (_ht : 0 ≤ t)
    (_hint : Integrable (fun s => (s : ℝ) ^ t) μ) :
    ∫ s, (s : ℝ) ^ t ∂μ =
    ∫ u, Real.exp (-t * u) ∂(laplaceMeasure μ) := by
  unfold laplaceMeasure
  have hmeas : AEStronglyMeasurable (fun u => Real.exp (-t * u))
      (Measure.map negLogMap μ) := by
    have hcont : Continuous (fun u : ℝ => Real.exp (-(t * u))) := by
      exact Real.continuous_exp.comp (continuous_const.mul continuous_id).neg
    simpa [neg_mul] using hcont.aestronglyMeasurable
  rw [MeasureTheory.integral_map negLogMap_measurable.aemeasurable hmeas]
  apply integral_congr_ae
  have hae : ∀ᵐ s ∂μ, 0 < s := by
    rw [ae_iff]
    simp only [not_lt]
    exact hsupp
  filter_upwards [hae] with s hs
  exact rpow_eq_exp_neg_neglog s hs t

/-- If a finite measure is supported in `(0,1]`, then its `-log` pushforward is
supported in `[0,∞)`. -/
theorem laplaceMeasure_nonneg_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (_hsupp_pos : μ (Set.Iic 0) = 0)
    (hsupp_le1 : μ (Set.Ioi 1) = 0) :
    (laplaceMeasure μ) (Set.Iio 0) = 0 := by
  unfold laplaceMeasure
  rw [Measure.map_apply negLogMap_measurable measurableSet_Iio]
  have hsub : negLogMap ⁻¹' Set.Iio 0 ⊆ Set.Ioi 1 ∪ Set.Iic 0 := by
    intro s hs
    simp only [Set.mem_preimage, Set.mem_Iio, negLogMap, neg_lt, neg_zero] at hs
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic]
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have : Real.log s ≤ 0 := Real.log_nonpos h2.le h1
    linarith
  have hle : μ (negLogMap ⁻¹' Set.Iio 0) ≤ 0 := by
    calc
      μ (negLogMap ⁻¹' Set.Iio 0) ≤ μ (Set.Ioi 1 ∪ Set.Iic 0) := measure_mono hsub
      _ ≤ μ (Set.Ioi 1) + μ (Set.Iic 0) := measure_union_le _ _
      _ = 0 := by rw [hsupp_le1, _hsupp_pos, add_zero]
  exact le_antisymm hle (zero_le _)

/-- For `t ≥ 0` and `Re(z) > 0`, the Laplace kernel has norm at most `1`. -/
theorem exp_neg_mul_norm_le (z : ℂ) (hz : 0 < z.re) (t : ℝ) (ht : 0 ≤ t) :
    ‖Complex.exp (-z * (t : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  show (-z * (t : ℂ)).re ≤ 0
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im]
  nlinarith [mul_nonneg (le_of_lt hz) ht]

/-- For fixed `t`, the Laplace kernel is entire in the complex variable. -/
theorem exp_neg_mul_differentiable (t : ℝ) :
    Differentiable ℂ (fun z : ℂ => Complex.exp (-z * (t : ℂ))) :=
  ((differentiable_neg).mul (differentiable_const _)).cexp

/-- Explicit complex derivative of the Laplace kernel. -/
theorem exp_neg_mul_hasDerivAt (t : ℝ) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (-z * (t : ℂ)))
      (Complex.exp (-z₀ * (t : ℂ)) * (-(t : ℂ))) z₀ :=
  ((hasDerivAt_neg z₀).mul_const (t : ℂ) |>.congr_deriv (by ring)).cexp

/-- Derivative domination for the Laplace kernel on the half-plane `Re(z) ≥ δ > 0`. -/
theorem exp_neg_mul_deriv_bound (z : ℂ) (δ : ℝ) (_hδ : 0 < δ) (hz : δ ≤ z.re)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖Complex.exp (-z * (t : ℂ)) * (-(t : ℂ))‖ ≤ t * Real.exp (-δ * t) := by
  rw [norm_mul, Complex.norm_exp, norm_neg, Complex.norm_of_nonneg ht]
  have hre : (-z * (t : ℂ)).re ≤ -δ * t := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    nlinarith
  linarith [mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) ht]

/-- A finite measure supported in `[0, ∞)` sees the Laplace kernel bounded by `1`
    almost everywhere on the right half-plane. -/
theorem exp_neg_mul_ae_dominated (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iio 0) = 0) (z : ℂ) (hz : 0 < z.re) :
    ∀ᵐ (t : ℝ) ∂μ, ‖Complex.exp (-z * (t : ℂ))‖ ≤ 1 := by
  have hae : ∀ᵐ (t : ℝ) ∂μ, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hsupp
  filter_upwards [hae] with t ht
  exact exp_neg_mul_norm_le z hz t ht

private theorem integrable_exp_mul_of_lt_zero_of_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iio 0) = 0) {x : ℝ} (hx : x < 0) :
    Integrable (fun t : ℝ => Real.exp (x * t)) μ := by
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (x * t)) μ := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    simp
  refine hconst.mono' hmeas ?_
  have hae : ∀ᵐ (t : ℝ) ∂μ, 0 ≤ t := by
    rw [ae_iff]
    simp only [not_le]
    exact hsupp
  filter_upwards [hae] with t ht
  have hxt : x * t ≤ 0 := by nlinarith
  have hexp : Real.exp (x * t) ≤ 1 := Real.exp_le_one_iff.mpr hxt
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using hexp

private theorem neg_mem_interior_integrableExpSet_id_of_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : μ (Set.Iio 0) = 0) {x : ℝ} (hx : x < 0) :
    x ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (isOpen_Iio.mem_nhds hx) ?_
  intro y hy
  change Integrable (fun t : ℝ => Real.exp (y * t)) μ
  exact integrable_exp_mul_of_lt_zero_of_nonnegSupport μ hsupp hy

/-- The scalar Laplace transform of a finite measure supported in `[0,∞)` is
    holomorphic on the right half-plane. -/
theorem laplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hsupp : μ (Set.Iio 0) = 0) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∫ t : ℝ, Complex.exp (-z * (t : ℂ)) ∂μ)
      {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hz' : (-z).re ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
    have hzneg : (-z).re < 0 := by
      simp only [Complex.neg_re]
      linarith
    exact neg_mem_interior_integrableExpSet_id_of_nonnegSupport μ hsupp hzneg
  have hbase :
      HasDerivAt (ProbabilityTheory.complexMGF id μ)
        (μ[fun t ↦ t * Complex.exp ((-z) * (t : ℂ))]) (-z) :=
    ProbabilityTheory.hasDerivAt_complexMGF (X := id) (μ := μ) hz'
  have hcomp :
      HasDerivAt (fun w : ℂ => ProbabilityTheory.complexMGF id μ (-w))
        (μ[fun t ↦ t * Complex.exp ((-z) * (t : ℂ))] * (-1)) z := by
    simpa using hbase.comp z (hasDerivAt_neg z)
  simpa [ProbabilityTheory.complexMGF, mul_assoc]
    using hcomp.differentiableAt.differentiableWithinAt

/-- On the multivariate right half-plane and the nonnegative orthant,
the Laplace kernel has norm at most `1`. -/
theorem exp_neg_sum_mul_norm_le_one {m : ℕ}
    (z : Fin m → ℂ) (hz : ∀ i, 0 < (z i).re)
    (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ‖Complex.exp (-∑ i, z i * (t i : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hre :
      (-∑ i, z i * (t i : ℂ)).re = -∑ i, (z i).re * t i := by
    calc
      (-∑ i, z i * (t i : ℂ)).re = -(∑ i : Fin m, (z i * (t i : ℂ)).re) := by
        simp
      _ = -(∑ i : Fin m, (z i).re * t i) := by
        congr
        funext i
        simp [Complex.mul_re]
  rw [hre]
  have hsum_nonneg :
      0 ≤ ∑ i : Fin m, (z i).re * t i := by
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hz i)) (ht i))
  linarith

/-- The multivariate Laplace transform of a finite measure supported in the
nonnegative orthant is continuous on the product right half-plane. -/
theorem multivariateLaplaceTransform_continuousOn_rightHalfPlane_of_nonnegSupport
    {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hsupp : μ {t : Fin m → ℝ | ∃ i, t i < 0} = 0) :
    ContinuousOn
      (fun z : Fin m → ℂ =>
        ∫ t : Fin m → ℝ, Complex.exp (-∑ i, z i * (t i : ℂ)) ∂μ)
      {z : Fin m → ℂ | ∀ i, 0 < (z i).re} := by
  refine MeasureTheory.continuousOn_of_dominated (bound := fun _ => (1 : ℝ)) ?_ ?_ ?_ ?_
  · intro z _
    have hcont :
        Continuous (fun t : Fin m → ℝ => Complex.exp (-∑ i, z i * (t i : ℂ))) := by
      apply Continuous.cexp
      exact (continuous_finset_sum Finset.univ fun i _ =>
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))).neg
    exact hcont.aestronglyMeasurable
  · intro z hz
    have hnonneg : ∀ᵐ (t : Fin m → ℝ) ∂μ, ∀ i, 0 ≤ t i := by
      rw [ae_iff]
      have hset :
          {t : Fin m → ℝ | ¬ ∀ i, 0 ≤ t i} =
            {t : Fin m → ℝ | ∃ i, t i < 0} := by
        ext t
        simp [Set.mem_setOf_eq]
      rw [hset]
      exact hsupp
    filter_upwards [hnonneg] with t ht
    exact exp_neg_sum_mul_norm_le_one z hz t ht
  · simp
  · refine Filter.Eventually.of_forall ?_
    intro t
    have hcont :
        Continuous (fun z : Fin m → ℂ => Complex.exp (-∑ i, z i * (t i : ℂ))) := by
      apply Continuous.cexp
      exact (continuous_finset_sum Finset.univ fun i _ =>
        (continuous_apply i).mul continuous_const).neg
    exact hcont.continuousOn

private theorem ae_nonneg_of_nonnegOrthantSupport {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hsupp : μ {t : Fin m → ℝ | ∃ i, t i < 0} = 0) :
    ∀ᵐ (t : Fin m → ℝ) ∂μ, ∀ i, 0 ≤ t i := by
  rw [ae_iff]
  have hset :
      {t : Fin m → ℝ | ¬ ∀ i, 0 ≤ t i} =
        {t : Fin m → ℝ | ∃ i, t i < 0} := by
    ext t
    simp [Set.mem_setOf_eq]
  rw [hset]
  exact hsupp

private theorem integrable_exp_neg_sum_of_nonnegSupport {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hsupp : μ {t : Fin m → ℝ | ∃ i, t i < 0} = 0)
    (z : Fin m → ℂ) (hz : ∀ i, 0 < (z i).re) :
    Integrable (fun t : Fin m → ℝ => Complex.exp (-∑ i, z i * (t i : ℂ))) μ := by
  have hmeas :
      AEStronglyMeasurable (fun t : Fin m → ℝ => Complex.exp (-∑ i, z i * (t i : ℂ))) μ := by
    have hcont :
        Continuous (fun t : Fin m → ℝ => Complex.exp (-∑ i, z i * (t i : ℂ))) := by
      apply Continuous.cexp
      exact (continuous_finset_sum Finset.univ fun i _ =>
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i)))).neg
    exact hcont.aestronglyMeasurable
  refine (integrable_const (1 : ℝ)).mono' hmeas ?_
  filter_upwards [ae_nonneg_of_nonnegOrthantSupport μ hsupp] with t ht
  exact exp_neg_sum_mul_norm_le_one z hz t ht

private theorem integrable_coord_mul_exp_neg_of_nonnegOrthantSupport {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hsupp : μ {t : Fin m → ℝ | ∃ i, t i < 0} = 0)
    (i : Fin m) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun t : Fin m → ℝ => t i * Real.exp (-δ * t i)) μ := by
  have hmeas :
      AEStronglyMeasurable (fun t : Fin m → ℝ => t i * Real.exp (-δ * t i)) μ := by
    have hcont : Continuous (fun t : Fin m → ℝ => t i * Real.exp (-δ * t i)) := by
      simpa [mul_comm] using
        (continuous_apply i).mul
          (Real.continuous_exp.comp ((continuous_const.mul (continuous_apply i)).neg))
    exact hcont.aestronglyMeasurable
  refine (integrable_const (Real.exp (-1) / δ)).mono' hmeas ?_
  filter_upwards [ae_nonneg_of_nonnegOrthantSupport μ hsupp] with t ht
  have hti : 0 ≤ t i := ht i
  have hmain : t i * Real.exp (-δ * t i) ≤ Real.exp (-1) / δ := by
    have hscaled : (t i * Real.exp (-δ * t i)) * δ ≤ Real.exp (-1) := by
      have := Real.mul_exp_neg_le_exp_neg_one (δ * t i)
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    exact (le_div_iff₀ hδ).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hnonneg : 0 ≤ t i * Real.exp (-δ * t i) := by
    exact mul_nonneg hti (Real.exp_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hmain

private theorem sum_update_mul_eq {m : ℕ}
    (z : Fin m → ℂ) (i : Fin m) (w : ℂ) (t : Fin m → ℝ) :
    (∑ j : Fin m, Function.update z i w j * (t j : ℂ)) =
      w * (t i : ℂ) +
        Finset.sum (Finset.univ.erase i) (fun j => z j * (t j : ℂ)) := by
  calc
    (∑ j : Fin m, Function.update z i w j * (t j : ℂ)) =
        Function.update z i w i * (t i : ℂ) +
          Finset.sum (Finset.univ.erase i) (fun j => Function.update z i w j * (t j : ℂ)) := by
      symm
      rw [add_comm]
      rw [Finset.sum_erase_add (s := Finset.univ)
        (f := fun j : Fin m => Function.update z i w j * (t j : ℂ))
        (a := i) (by simp)]
    _ = w * (t i : ℂ) +
          Finset.sum (Finset.univ.erase i) (fun j => z j * (t j : ℂ)) := by
      rw [Function.update_self]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem sum_erase_mul_eq_sub {m : ℕ}
    (z : Fin m → ℂ) (i : Fin m) (t : Fin m → ℝ) :
    Finset.sum (Finset.univ.erase i) (fun j => z j * (t j : ℂ)) =
      (∑ j : Fin m, z j * (t j : ℂ)) - z i * (t i : ℂ) := by
  rw [eq_sub_iff_add_eq]
  rw [Finset.sum_erase_add (s := Finset.univ)
    (f := fun j : Fin m => z j * (t j : ℂ))
    (a := i) (by simp)]

private theorem exp_neg_sum_update_hasDerivAt {m : ℕ}
    (z : Fin m → ℂ) (i : Fin m) (t : Fin m → ℝ) (w₀ : ℂ) :
    HasDerivAt
      (fun w : ℂ => Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)))
      (Complex.exp (-∑ j, Function.update z i w₀ j * (t j : ℂ)) * (-(t i : ℂ))) w₀ := by
  let c : ℂ := (∑ j : Fin m, z j * (t j : ℂ)) - z i * (t i : ℂ)
  let g : ℂ → ℂ := fun w => -(w * (t i : ℂ)) - c
  have hlin : HasDerivAt g (-(t i : ℂ)) w₀ := by
    dsimp [g]
    simpa [one_mul] using (((hasDerivAt_id w₀).mul_const (t i : ℂ)).neg.sub_const c)
  have hmain :
      HasDerivAt (fun w : ℂ => Complex.exp (g w))
        (Complex.exp (g w₀) * (-(t i : ℂ))) w₀ :=
    hlin.cexp
  have hfun :
      (fun w : ℂ => Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ))) =
        fun w : ℂ => Complex.exp (g w) := by
    funext w
    rw [sum_update_mul_eq z i w t]
    rw [sum_erase_mul_eq_sub z i t]
    simp [g, c, sub_eq_add_neg, add_comm, add_left_comm]
  rw [hfun]
  rw [sum_update_mul_eq z i w₀ t, sum_erase_mul_eq_sub z i t]
  simpa [g, c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain

private theorem exp_neg_sum_update_deriv_bound {m : ℕ}
    (z : Fin m → ℂ) (hz : ∀ j, 0 < (z j).re)
    (i : Fin m) (δ : ℝ) (_hδ : 0 < δ) {w : ℂ} (hw : δ ≤ w.re)
    (t : Fin m → ℝ) (ht : ∀ j, 0 ≤ t j) :
    ‖Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)) * (-(t i : ℂ))‖ ≤
      t i * Real.exp (-δ * t i) := by
  let c : ℂ := Finset.sum (Finset.univ.erase i) (fun j => z j * (t j : ℂ))
  rw [sum_update_mul_eq z i w t]
  rw [norm_mul, Complex.norm_exp, norm_neg, Complex.norm_of_nonneg (ht i)]
  have hc_nonneg : 0 ≤ c.re := by
    have hcre :
        c.re = Finset.sum (Finset.univ.erase i) (fun j => (z j).re * t j) := by
      simp [c, Complex.mul_re]
    rw [hcre]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (le_of_lt (hz j)) (ht j))
  have hre : (-(w * (t i : ℂ) + c)).re ≤ -δ * t i := by
    have hti : 0 ≤ t i := ht i
    have hδw : δ * t i ≤ w.re * t i := mul_le_mul_of_nonneg_right hw hti
    have hreal : (-(w * (t i : ℂ) + c)).re = -(w.re * t i + c.re) := by
      simp [c, Complex.mul_re]
    rw [hreal]
    nlinarith
  rw [mul_comm (_ : ℝ) (t i)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (ht i)

private theorem multivariateLaplace_slice_differentiableAt_of_nonnegSupport
    {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hsupp : μ {t : Fin m → ℝ | ∃ i, t i < 0} = 0)
    (z : Fin m → ℂ) (hz : ∀ j, 0 < (z j).re) (i : Fin m) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        ∫ t : Fin m → ℝ, Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)) ∂μ)
      (z i) := by
  let s : Set ℂ := {w : ℂ | (z i).re / 2 < w.re}
  have hδ : 0 < (z i).re / 2 := by nlinarith [hz i]
  have hs : s ∈ 𝓝 (z i) := by
    have hzmem : (z i).re / 2 < (z i).re := by nlinarith [hz i]
    exact IsOpen.mem_nhds
      (isOpen_lt continuous_const Complex.continuous_re) hzmem
  have hF_meas : ∀ᶠ w in 𝓝 (z i),
      AEStronglyMeasurable
        (fun t : Fin m → ℝ => Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ))) μ := by
    refine Filter.Eventually.of_forall ?_
    intro w
    have hcont :
        Continuous (fun t : Fin m → ℝ =>
          Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ))) := by
      apply Continuous.cexp
      exact (continuous_finset_sum Finset.univ fun j _ =>
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j)))).neg
    exact hcont.aestronglyMeasurable
  have hF_int :
      Integrable
        (fun t : Fin m → ℝ => Complex.exp (-∑ j, Function.update z i (z i) j * (t j : ℂ))) μ := by
    simpa using integrable_exp_neg_sum_of_nonnegSupport μ hsupp z hz
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : Fin m → ℝ =>
          Complex.exp (-∑ j, Function.update z i (z i) j * (t j : ℂ)) * (-(t i : ℂ))) μ := by
    have hcont :
        Continuous (fun t : Fin m → ℝ =>
          Complex.exp (-∑ j, Function.update z i (z i) j * (t j : ℂ)) * (-(t i : ℂ))) := by
      apply Continuous.mul
      · apply Continuous.cexp
        exact (continuous_finset_sum Finset.univ fun j _ =>
          (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j)))).neg
      · exact (Complex.continuous_ofReal.comp (continuous_apply i)).neg
    exact hcont.aestronglyMeasurable
  have h_bound :
      ∀ᵐ t : Fin m → ℝ ∂μ,
        ∀ w ∈ s,
          ‖Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)) * (-(t i : ℂ))‖ ≤
            t i * Real.exp (-((z i).re / 2) * t i) := by
    filter_upwards [ae_nonneg_of_nonnegOrthantSupport μ hsupp] with t ht w hw
    exact exp_neg_sum_update_deriv_bound z hz i ((z i).re / 2) hδ (le_of_lt hw) t ht
  have bound_integrable :
      Integrable (fun t : Fin m → ℝ => t i * Real.exp (-((z i).re / 2) * t i)) μ := by
    simpa using
      integrable_coord_mul_exp_neg_of_nonnegOrthantSupport μ hsupp i ((z i).re / 2) hδ
  have h_diff :
      ∀ᵐ t : Fin m → ℝ ∂μ,
        ∀ w ∈ s,
          HasDerivAt
            (fun w : ℂ => Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)))
            (Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)) * (-(t i : ℂ))) w := by
    exact Filter.Eventually.of_forall (fun t w _ => exp_neg_sum_update_hasDerivAt z i t w)
  obtain ⟨_, hderiv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (x₀ := z i) (s := s)
      (bound := fun t : Fin m → ℝ => t i * Real.exp (-((z i).re / 2) * t i))
      hs hF_meas hF_int hF'_meas h_bound bound_integrable h_diff
  exact hderiv.differentiableAt

/-- The multivariate Laplace transform of a finite measure supported in the
nonnegative orthant is holomorphic on the product right half-plane. -/
theorem multivariateLaplaceTransform_differentiableOn_rightHalfPlane_of_nonnegSupport
    {m : ℕ} (μ : Measure (Fin m → ℝ)) [IsFiniteMeasure μ]
    (hsupp : μ {t : Fin m → ℝ | ∃ i, t i < 0} = 0) :
    DifferentiableOn ℂ
      (fun z : Fin m → ℂ =>
        ∫ t : Fin m → ℝ, Complex.exp (-∑ i, z i * (t i : ℂ)) ∂μ)
      {z : Fin m → ℂ | ∀ i, 0 < (z i).re} := by
  let U : Set (Fin m → ℂ) := {z : Fin m → ℂ | ∀ i, 0 < (z i).re}
  have hU : IsOpen U := by
    classical
    have hUeq : U = ⋂ i : Fin m, {z : Fin m → ℂ | 0 < (z i).re} := by
      ext z
      simp [U]
    rw [hUeq]
    exact isOpen_iInter_of_finite (fun i : Fin m =>
      isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply i)))
  have hcont :
      ContinuousOn
        (fun z : Fin m → ℂ =>
          ∫ t : Fin m → ℝ, Complex.exp (-∑ i, z i * (t i : ℂ)) ∂μ) U := by
    simpa [U] using
      multivariateLaplaceTransform_continuousOn_rightHalfPlane_of_nonnegSupport μ hsupp
  have hsep : ∀ z ∈ U, ∀ i : Fin m,
      DifferentiableAt ℂ
        (fun w => ∫ t : Fin m → ℝ,
          Complex.exp (-∑ j, Function.update z i w j * (t j : ℂ)) ∂μ) (z i) := by
    intro z hz i
    exact multivariateLaplace_slice_differentiableAt_of_nonnegSupport μ hsupp z hz i
  simpa [U] using osgood_lemma hU
    (fun z : Fin m → ℂ => ∫ t : Fin m → ℝ, Complex.exp (-∑ i, z i * (t i : ℂ)) ∂μ)
    hcont hsep

end SCV
