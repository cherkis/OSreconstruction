/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import OSReconstruction.Wightman.NuclearSpaces.NuclearSpace
import OSReconstruction.Wightman.NuclearSpaces.GaussianFieldBridge

/-!
# Schwartz Space is Nuclear

This file proves that the Schwartz space S(ℝⁿ) is a nuclear space, using two
complementary characterizations:

1. **Pietsch (OSReconstruction.NuclearSpace)**: nuclear dominance by seminorms.
   The `NuclearFrechet` presentation and `SchwartzMap.instNuclearSpace` use this.

2. **Dynin-Mityagin (GaussianField.DyninMityaginSpace)**: Schauder basis with rapid decay.
   This is imported from the `gaussian-field` library via `GaussianFieldBridge`.
   The sorry-free Hermite function infrastructure lives there.

## Main Results

* `schwartz_nuclearSpace_fin0` - S(ℝ⁰, ℝ) is nuclear (direct proof via evaluation)
* `SchwartzMap.instNuclearSpace` - S(ℝⁿ, ℝ) is nuclear (combines n=0 and n>0 cases)
* `GaussianField.DyninMityaginSpace (SchwartzMap D ℝ)` - S(D, ℝ) is nuclear (Dynin-Mityagin,
  sorry-free from gaussian-field, available via GaussianFieldBridge import)

## Hermite Function Infrastructure

The Hermite function definitions and theorems in this file are **superseded** by the
sorry-free versions from gaussian-field. Use the `gf`-prefixed re-exports from
`GaussianFieldBridge`:

* `gfHermiteFunction` — Hermite function definition
* `gfHermiteFunction_schwartz` — Schwartz membership (sorry-free)
* `gfHermiteFunction_orthonormal` — L² orthonormality (sorry-free)
* `gfHermiteFunction_seminorm_bound` — seminorm growth bounds (sorry-free)
* `gfHermiteFunction_complete` — completeness in L² (sorry-free)

## References

* Gel'fand-Vilenkin, "Generalized Functions IV" (1964), Ch. I, §3
* Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13
* Trèves, "Topological Vector Spaces" (1967), Ch. 51
-/

noncomputable section

open scoped SchwartzMap NNReal
open MeasureTheory

/-! ### Schwartz Space Seminorms -/

/-- The standard Schwartz seminorm indexed by (k, l) ∈ ℕ × ℕ:
    p_{k,l}(f) = sup_x ‖x‖^k · ‖iteratedFDeriv ℝ l f x‖

    This is a continuous seminorm on S(ℝⁿ, F). -/
def SchwartzMap.schwartzSeminorm (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k l : ℕ) :
    Seminorm ℝ (𝓢(E, F)) :=
  SchwartzMap.seminorm ℝ k l

/-! ### Combined Schwartz Seminorm for Fréchet Presentation -/

private abbrev schwartzPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (N + 1) ×ˢ Finset.range (N + 1)

/-- The combined Schwartz seminorm: sum of all individual seminorms p_{k,l} for k,l ≤ N.
    This family is monotone in N (adding more non-negative terms) and generates the
    same topology as the full family {p_{k,l}}_{k,l ∈ ℕ}.

    Note: Mathlib's individual Schwartz seminorms p_{k,l}(f) = sup_x ‖x‖^k · ‖D^l f(x)‖
    are NOT monotone in k (since ‖x‖^k is not monotone for ‖x‖ < 1), so diagonal
    seminorms p_{n,n} don't form an increasing family. Using sums over all pairs
    up to (N,N) gives a genuinely increasing family that generates the same topology. -/
private def schwartzCombinedSeminorm (n : ℕ) (N : ℕ) :
    Seminorm ℝ (𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :=
  (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2)

/-- Evaluating a combined seminorm at a point equals the real number sum. -/
private theorem schwartzCombinedSeminorm_apply (n N : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :
    schwartzCombinedSeminorm n N f =
    (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 f) := by
  unfold schwartzCombinedSeminorm
  -- Prove by induction on the finset using the AddMonoidHom property
  have key : ∀ (S : Finset (ℕ × ℕ)),
      (S.sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2)) f =
      S.sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 f) := by
    intro S
    induction S using Finset.cons_induction with
    | empty => simp [Seminorm.zero_apply]
    | cons a s has ih =>
      rw [Finset.sum_cons, Finset.sum_cons, Seminorm.add_apply, ih]
  exact key _

/-- An individual seminorm p_{k,l} is bounded by the combined seminorm for N ≥ max(k,l). -/
private theorem le_schwartzCombinedSeminorm (n : ℕ) {k l N : ℕ}
    (hk : k ≤ N) (hl : l ≤ N) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) :
    SchwartzMap.seminorm ℝ k l f ≤ schwartzCombinedSeminorm n N f := by
  rw [schwartzCombinedSeminorm_apply]
  have hmem : (k, l) ∈ schwartzPairs N :=
    Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
      (Finset.mem_range.mpr (by omega))
  calc SchwartzMap.seminorm ℝ k l f
      = (fun kl : ℕ × ℕ => SchwartzMap.seminorm ℝ kl.1 kl.2 f) (k, l) := rfl
    _ ≤ (schwartzPairs N).sum (fun kl => SchwartzMap.seminorm ℝ kl.1 kl.2 f) :=
        Finset.single_le_sum
          (fun (kl : ℕ × ℕ) _ => apply_nonneg (SchwartzMap.seminorm ℝ kl.1 kl.2) f) hmem

/-! ### Nuclearity for n = 0

When the domain is `EuclideanSpace ℝ (Fin 0)` (a single point), every Schwartz
function is determined by its value at `default`. All Schwartz seminorms except
`seminorm ℝ 0 0` vanish, so the nuclear dominance condition is trivial: use the
evaluation functional as the single nuclear component. -/

/-- On a zero-dimensional domain, Schwartz seminorms with `a ≥ 1` or `b ≥ 1` vanish.
    When `a ≥ 1`: the norm `‖x‖^a = 0` since the unique point has norm 0.
    When `b ≥ 1`: `iteratedFDeriv` is a multilinear map on a zero-dim space, hence 0. -/
private lemma seminorm_eq_zero_of_fin0 {a b : ℕ} (hab : (a, b) ≠ (0, 0))
    (f : 𝓢(EuclideanSpace ℝ (Fin 0), ℝ)) :
    SchwartzMap.seminorm ℝ a b f = 0 := by
  apply le_antisymm _ (apply_nonneg _ _)
  apply SchwartzMap.seminorm_le_bound ℝ a b f (le_refl 0)
  intro x; have hx : x = default := Subsingleton.elim x default; subst hx
  by_cases ha : a ≠ 0
  · rw [show ‖(default : EuclideanSpace ℝ (Fin 0))‖ = 0 from by
      simp [EuclideanSpace.norm_eq, Finset.univ_eq_empty], zero_pow ha, zero_mul]
  · push Not at ha; subst ha; simp only [pow_zero, one_mul]
    have hb : b ≠ 0 := by intro hb; exact hab (by ext <;> simp [*])
    rw [show iteratedFDeriv ℝ b (⇑f) default = 0 from by
      ext m; exact (iteratedFDeriv ℝ b (⇑f) default).map_coord_zero ⟨0, by omega⟩
        (Subsingleton.elim _ _), norm_zero]

/-- On a zero-dimensional domain, any individual Schwartz seminorm is bounded
    by `seminorm ℝ 0 0` (the sup-norm). -/
private lemma schwartz_seminorm_le_00 (i : ℕ × ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin 0), ℝ)) :
    (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 0)) ℝ i) f ≤
    (SchwartzMap.seminorm ℝ 0 0) f := by
  show (SchwartzMap.seminorm ℝ i.1 i.2) f ≤ _
  by_cases hab : (i.1, i.2) = (0, 0)
  · simp [Prod.ext_iff] at hab; rw [hab.1, hab.2]
  · rw [seminorm_eq_zero_of_fin0 hab]; exact apply_nonneg _ _

/-- On a zero-dimensional domain, any finite sup of Schwartz seminorms is bounded
    by `seminorm ℝ 0 0`. -/
private lemma sup_schwartz_le_00 (s : Finset (ℕ × ℕ))
    (f : 𝓢(EuclideanSpace ℝ (Fin 0), ℝ)) :
    (s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 0)) ℝ)) f ≤
    (SchwartzMap.seminorm ℝ 0 0) f := by
  induction s using Finset.cons_induction with
  | empty => simp [Seminorm.bot_eq_zero, Seminorm.zero_apply, apply_nonneg]
  | cons a s has ih =>
    rw [Finset.sup_cons, Seminorm.sup_apply]
    exact max_le (schwartz_seminorm_le_00 a f) ih

/-- Evaluation at the unique point of `EuclideanSpace ℝ (Fin 0)`, as a linear map
    from the Schwartz space to ℝ. -/
private def evalLM₀ :
    (SchwartzMap (EuclideanSpace ℝ (Fin 0)) ℝ) →ₗ[ℝ] ℝ where
  toFun f := f default
  map_add' f g := by simp [SchwartzMap.add_apply]
  map_smul' r f := by simp [SchwartzMap.smul_apply]

/-- The evaluation linear map is continuous in the Schwartz topology: it is
    bounded by `seminorm ℝ 0 0`, which is continuous. -/
private lemma evalLM₀_continuous : Continuous evalLM₀ := by
  apply WithSeminorms.continuous_of_isBounded
    (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin 0)) ℝ)
    (norm_withSeminorms ℝ ℝ)
  intro i; refine ⟨{⟨0, 0⟩}, 1, ?_⟩
  rw [Seminorm.le_def]; intro f
  simp only [Seminorm.comp_apply, Seminorm.smul_apply, Finset.sup_singleton,
    schwartzSeminormFamily, evalLM₀]
  change ‖f default‖ ≤ 1 • (SchwartzMap.seminorm ℝ 0 0) f
  rw [one_smul]; exact SchwartzMap.norm_le_seminorm ℝ f default

/-- Evaluation at the unique point, as a continuous linear map. -/
private def evalCLM₀ :
    (SchwartzMap (EuclideanSpace ℝ (Fin 0)) ℝ) →L[ℝ] ℝ :=
  ⟨evalLM₀, evalLM₀_continuous⟩

/-- On a zero-dimensional domain, `seminorm ℝ 0 0 f = ‖f default‖`. -/
private lemma seminorm_00_eq (f : 𝓢(EuclideanSpace ℝ (Fin 0), ℝ)) :
    (SchwartzMap.seminorm ℝ 0 0) f = ‖f default‖ := by
  apply le_antisymm
  · apply SchwartzMap.seminorm_le_bound ℝ 0 0 f (norm_nonneg _)
    intro x; have : x = default := Subsingleton.elim x default; rw [this]; simp
  · exact SchwartzMap.norm_le_seminorm ℝ f default

private lemma evalCLM₀_apply (f : 𝓢(EuclideanSpace ℝ (Fin 0), ℝ)) :
    evalCLM₀ f = f default := rfl

/-- **The Schwartz space S(ℝ⁰, ℝ) is nuclear.** The domain is a single point, so the
    space is one-dimensional and nuclear dominance holds with the evaluation functional. -/
theorem schwartz_nuclearSpace_fin0 :
    NuclearSpace (𝓢(EuclideanSpace ℝ (Fin 0), ℝ)) where
  nuclear_dominance := by
    intro p hp
    obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin 0)) ℝ) p hp
    set Cv := (C : ℝ) + 1
    have hCv_pos : 0 < Cv := by positivity
    have hCv_ge_one : 1 ≤ Cv := by linarith [NNReal.coe_nonneg C]
    have hCv_ge_C : (C : ℝ) ≤ Cv := by linarith
    let Cv_nn : ℝ≥0 := ⟨Cv, le_of_lt hCv_pos⟩
    have hp_bound : ∀ f, p f ≤ (C : ℝ) * ‖f default‖ := fun f => by
      calc p f ≤ (C • s.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin 0)) ℝ)) f := hle f
        _ ≤ (C : ℝ) * (SchwartzMap.seminorm ℝ 0 0) f := by
            simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
            exact mul_le_mul_of_nonneg_left (sup_schwartz_le_00 s f) (NNReal.coe_nonneg C)
        _ = (C : ℝ) * ‖f default‖ := by rw [seminorm_00_eq]
    refine ⟨Cv_nn • SchwartzMap.seminorm ℝ 0 0, ?_, ?_, ?_⟩
    · show Continuous fun x => (Cv_nn • SchwartzMap.seminorm ℝ 0 0) x
      simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Cv_nn]
      exact continuous_const.mul
        ((schwartz_withSeminorms ℝ (EuclideanSpace ℝ (Fin 0)) ℝ).continuous_seminorm ⟨0, 0⟩)
    · intro f
      simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Cv_nn]
      calc p f ≤ (C : ℝ) * ‖f default‖ := hp_bound f
        _ ≤ Cv * ‖f default‖ := mul_le_mul_of_nonneg_right hCv_ge_C (norm_nonneg _)
        _ = Cv * (SchwartzMap.seminorm ℝ 0 0) f := by rw [seminorm_00_eq]
    · refine ⟨fun i => if i = 0 then evalCLM₀ else 0,
              fun i => if i = 0 then Cv else 0, ?_, ?_, ?_, ?_⟩
      · intro i; by_cases hi : i = 0 <;> simp [hi, le_of_lt hCv_pos]
      · exact summable_of_ne_finset_zero (s := {0}) (fun k hk => by
          simp [Finset.mem_singleton] at hk; simp [hk])
      · intro i f; by_cases hi : i = 0
        · simp only [hi, ↓reduceIte, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Cv_nn]
          rw [evalCLM₀_apply, seminorm_00_eq]
          exact le_mul_of_one_le_left (norm_nonneg _) hCv_ge_one
        · simp [hi]; exact apply_nonneg (Cv_nn • SchwartzMap.seminorm ℝ 0 0) f
      · intro f
        rw [show ∑' i, ‖(if i = 0 then evalCLM₀ else 0) f‖ * (if i = 0 then Cv else 0) =
            ‖evalCLM₀ f‖ * Cv from by
          rw [tsum_eq_single 0 (fun i hi => by simp [hi])]; simp]
        rw [evalCLM₀_apply]
        nlinarith [hp_bound f, norm_nonneg (f default), NNReal.coe_nonneg C]

/-! ### Schwartz Space is Nuclear -/

/-- **The Schwartz space S(ℝⁿ, ℝ) is a nuclear space (Pietsch characterization).**

    * For **n > 0**: follows from the Dynin-Mityagin characterization via the
      Hermite function Schauder basis. The bridge
      `GaussianField.DyninMityaginSpace.toOSNuclearSpace` converts the
      gaussian-field `GaussianField.DyninMityaginSpace` instance to Pietsch form.

    * For **n = 0**: the domain `EuclideanSpace ℝ (Fin 0)` is a single point, so
      the Schwartz space is one-dimensional. Nuclear dominance is proved directly
      using the evaluation functional at the unique point. -/
theorem SchwartzMap.instNuclearSpace (n : ℕ) :
    NuclearSpace (𝓢(EuclideanSpace ℝ (Fin n), ℝ)) := by
  by_cases hn : n = 0
  · -- n = 0: domain is a single point, Schwartz space ≅ ℝ.
    subst hn
    exact schwartz_nuclearSpace_fin0
  · -- n > 0: EuclideanSpace ℝ (Fin n) is nontrivial, use the GF bridge
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := inferInstance
    exact GaussianField.DyninMityaginSpace.toOSNuclearSpace _

end
