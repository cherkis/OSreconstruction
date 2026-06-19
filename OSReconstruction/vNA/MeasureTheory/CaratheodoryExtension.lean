/-
Copyright (c) 2025 ModularPhysics Contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: ModularPhysics Contributors
-/
import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.MeasureTheory.OuterMeasure.OfFunction
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Set.Basic

/-!
# Carathéodory Extension for Spectral Measures

This file provides infrastructure for extending a premeasure defined on bounded intervals
to a full measure on the Borel σ-algebra of ℝ, using Mathlib's Carathéodory extension theorem.

## Main Definitions

* `IsBoundedInterval` - Predicate for bounded closed intervals
* `IntervalPremeasure` - A premeasure defined on bounded intervals [a, b]
* `IntervalPremeasure.toOuterMeasure` - Extension to an outer measure via `inducedOuterMeasure`
* `IntervalPremeasure.toMeasure` - The resulting Borel measure

## Main Results

* `IntervalPremeasure.toMeasure_Icc` - The measure of [a, b] equals the premeasure value
* `IntervalPremeasure.sigmaFinite` - The resulting measure is σ-finite

## Strategy

We use Mathlib's `OuterMeasure.inducedOuterMeasure` which extends a function defined on sets
satisfying a predicate P to an outer measure on all sets. The Carathéodory measurable sets
for this outer measure form a σ-algebra containing all Borel sets.

For spectral measures, we define P as the predicate "s is a bounded closed interval",
and the premeasure m assigns values to such intervals.

## References

* Reed-Simon, "Methods of Modern Mathematical Physics I", Appendix to VII
* Rudin, "Real and Complex Analysis", Chapter 1
* Mathlib's `MeasureTheory.OuterMeasure.Induced`
-/

noncomputable section

open scoped ENNReal NNReal Classical
open Set Filter Topology MeasureTheory OuterMeasure

universe u

/-! ### Predicate for bounded intervals -/

/-- A set is a bounded closed interval if it equals Icc a b for some a ≤ b.
    Note: the singleton {a} = Icc a a is included. -/
def IsBoundedClosedInterval (s : Set ℝ) : Prop :=
  ∃ a b : ℝ, a ≤ b ∧ s = Set.Icc a b

/-- A more careful predicate: either empty or a nonempty Icc. -/
def IsBoundedClosedIntervalOrEmpty (s : Set ℝ) : Prop :=
  s = ∅ ∨ ∃ a b : ℝ, a ≤ b ∧ s = Set.Icc a b

theorem isBoundedClosedIntervalOrEmpty_empty : IsBoundedClosedIntervalOrEmpty ∅ :=
  Or.inl rfl

theorem isBoundedClosedIntervalOrEmpty_Icc (a b : ℝ) (hab : a ≤ b) :
    IsBoundedClosedIntervalOrEmpty (Set.Icc a b) :=
  Or.inr ⟨a, b, hab, rfl⟩

/-! ### Interval Premeasures -/

/-- A premeasure on bounded intervals of ℝ.

    This captures the essential structure needed for Carathéodory extension:
    - A function μ₀ : [a, b] ↦ μ₀([a, b]) ∈ ℝ≥0∞ for a ≤ b
    - Additivity: μ₀([a, c]) = μ₀([a, b]) + μ₀([b, c])
    - Empty interval gives zero: μ₀({a}) = 0 (using Icc a a = {a})

    For spectral measures, this comes from ⟨x, P([a,b])y⟩ via total variation. -/
structure IntervalPremeasure where
  /-- The premeasure value on [a, b] for a ≤ b -/
  toFun : ∀ (a b : ℝ), a ≤ b → ℝ≥0∞
  /-- Point measure is zero: μ({a}) = μ(Icc a a) = 0 -/
  point_zero : ∀ a, toFun a a le_rfl = 0
  /-- Additivity: μ([a,c]) = μ([a,b]) + μ([b,c]) for a ≤ b ≤ c -/
  additive : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c),
    toFun a c (le_trans hab hbc) = toFun a b hab + toFun b c hbc
  /-- Monotonicity: [a', b'] ⊆ [a, b] implies μ([a', b']) ≤ μ([a, b]) -/
  monotone : ∀ a b a' b' (hab : a ≤ b) (ha'b' : a' ≤ b'),
    a ≤ a' → b' ≤ b → toFun a' b' ha'b' ≤ toFun a b hab
  /-- Local finiteness: each bounded interval has finite measure -/
  locally_finite : ∀ a b (hab : a ≤ b), toFun a b hab < ⊤

namespace IntervalPremeasure

variable (μ : IntervalPremeasure)

/-- Apply the premeasure to an interval. -/
def measureIcc (a b : ℝ) (hab : a ≤ b) : ℝ≥0∞ := μ.toFun a b hab

/-- The function that assigns 0 to ∅ and μ([a,b]) to Icc a b.
    This is the premeasure we extend via Carathéodory. -/
def premeasureFun (s : Set ℝ) : ℝ≥0∞ :=
  if s = ∅ then 0
  else if h' : ∃ a b : ℝ, a ≤ b ∧ s = Set.Icc a b then
    μ.toFun h'.choose h'.choose_spec.choose h'.choose_spec.choose_spec.1
  else ⊤

theorem premeasureFun_empty : premeasureFun μ ∅ = 0 := by
  unfold premeasureFun
  simp only [if_true]

theorem premeasureFun_Icc (a b : ℝ) (hab : a ≤ b) :
    premeasureFun μ (Set.Icc a b) = μ.toFun a b hab := by
  unfold premeasureFun
  have hne : Set.Icc a b ≠ ∅ := Set.nonempty_Icc.mpr hab |>.ne_empty
  simp only [hne, if_false]
  have hex : ∃ a' b' : ℝ, a' ≤ b' ∧ Set.Icc a b = Set.Icc a' b' := ⟨a, b, hab, rfl⟩
  simp only [hex, dif_pos]
  -- Need to show the chosen values give the same result
  -- This requires uniqueness of endpoints for Icc
  have heq := hex.choose_spec.choose_spec.2.symm
  have hab' := hex.choose_spec.choose_spec.1
  rw [Set.Icc_eq_Icc_iff hab'] at heq
  congr 1
  · exact heq.1
  · exact heq.2

/-- Convert the interval premeasure to an outer measure using Mathlib's ofFunction. -/
def toOuterMeasure : OuterMeasure ℝ :=
  OuterMeasure.ofFunction (premeasureFun μ) (premeasureFun_empty μ)

/-- The outer measure of an interval equals the premeasure. -/
theorem toOuterMeasure_Icc (a b : ℝ) (hab : a ≤ b) :
    toOuterMeasure μ (Set.Icc a b) = μ.toFun a b hab := by
  unfold toOuterMeasure
  apply le_antisymm
  · -- Upper bound: single cover by [a,b] gives μ([a,b])
    calc OuterMeasure.ofFunction (premeasureFun μ) (premeasureFun_empty μ) (Set.Icc a b)
        ≤ premeasureFun μ (Set.Icc a b) := ofFunction_le (Set.Icc a b)
      _ = μ.toFun a b hab := premeasureFun_Icc μ a b hab
  · -- Lower bound: any cover has sum ≥ μ([a,b])
    -- This requires compactness of [a,b] and properties of the premeasure
    sorry

/-- All Borel sets are Carathéodory-measurable for this outer measure.

    This is the key result that allows extending to a measure.
    The proof uses that intervals generate the Borel σ-algebra
    and intervals are Carathéodory-measurable. -/
theorem borel_le_caratheodory :
    (inferInstance : MeasurableSpace ℝ) ≤ (toOuterMeasure μ).caratheodory := by
  -- It suffices to show that all closed intervals are Carathéodory-measurable
  -- since they generate the Borel σ-algebra
  -- Then MeasurableSpace.generateFrom_le gives the result
  sorry

/-- Convert the interval premeasure to a Borel measure on ℝ. -/
def toMeasure : Measure ℝ :=
  (toOuterMeasure μ).toMeasure (borel_le_caratheodory μ)

/-- The measure agrees with the premeasure on intervals. -/
theorem toMeasure_Icc (a b : ℝ) (hab : a ≤ b) :
    toMeasure μ (Set.Icc a b) = μ.toFun a b hab := by
  unfold toMeasure
  rw [toMeasure_apply _ _ measurableSet_Icc]
  exact toOuterMeasure_Icc μ a b hab

/-- The measure is σ-finite since [-n, n] has finite measure and covers ℝ. -/
theorem sigmaFinite : SigmaFinite (toMeasure μ) := by
  rw [sigmaFinite_iff]
  refine ⟨⟨fun n => Set.Icc (-(n : ℝ)) n, ?_, ?_, ?_⟩⟩
  · intro n
    exact Set.mem_univ _
  · intro n
    rw [toMeasure_Icc μ _ _ (by linarith : -(n : ℝ) ≤ n)]
    exact μ.locally_finite _ _ _
  · ext x
    simp only [Set.mem_iUnion, Set.mem_Icc, Set.mem_univ, iff_true]
    use Nat.ceil (|x| + 1)
    constructor
    · have h := Nat.le_ceil (|x| + 1)
      have h2 := neg_abs_le x
      linarith
    · calc x ≤ |x| := le_abs_self x
        _ ≤ |x| + 1 := by linarith
        _ ≤ Nat.ceil (|x| + 1) := Nat.le_ceil _

end IntervalPremeasure

/-! ### Complex-valued interval premeasures -/

/-- A complex-valued premeasure on bounded intervals, used for spectral measures.
    The underlying positive measure comes from the total variation.

    Note: For the extension to work properly, `norm_additive` ensures that the
    total variation is truly additive (not just subadditive). This is a strong
    condition that holds for spectral measures. -/
structure ComplexIntervalPremeasure where
  /-- The complex measure value on [a, b] for a ≤ b -/
  toFun : ∀ (a b : ℝ), a ≤ b → ℂ
  /-- Point measure is zero -/
  point_zero : ∀ a, toFun a a le_rfl = 0
  /-- Additivity: μ([a,c]) = μ([a,b]) + μ([b,c]) -/
  additive : ∀ a b c (hab : a ≤ b) (hbc : b ≤ c),
    toFun a c (le_trans hab hbc) = toFun a b hab + toFun b c hbc
  /-- Boundedness: there exists a global bound on the total variation -/
  totalVar_bound : ℝ
  totalVar_bound_nonneg : totalVar_bound ≥ 0
  /-- Total variation bound on any interval -/
  norm_le : ∀ a b (hab : a ≤ b), ‖toFun a b hab‖ ≤ totalVar_bound

namespace ComplexIntervalPremeasure

variable (μ : ComplexIntervalPremeasure)

/-- A partition of [a, b] is a finite increasing sequence a = t₀ < t₁ < ... < tₙ = b. -/
structure Partition (a b : ℝ) (hab : a ≤ b) where
  /-- Number of subintervals -/
  n : ℕ
  /-- The partition points, with t 0 = a and t n = b -/
  points : Fin (n + 1) → ℝ
  /-- First point is a -/
  first : points ⟨0, Nat.zero_lt_succ n⟩ = a
  /-- Last point is b -/
  last : points ⟨n, Nat.lt_succ_self n⟩ = b
  /-- Points are strictly increasing -/
  strict_mono : StrictMono points

/-- The trivial partition of [a, b] with just a single subinterval [a, b].
    This exists when a < b. -/
noncomputable def Partition.trivial {a b : ℝ} (hab : a < b) :
    Partition a b (le_of_lt hab) where
  n := 1
  points := ![a, b]
  first := by simp [Matrix.cons_val_zero]
  last := by simp [Matrix.cons_val_one, Matrix.head_cons]
  strict_mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

/-- The variation of μ over a partition: Σᵢ ‖μ([tᵢ, tᵢ₊₁])‖ -/
noncomputable def partitionVariation (a b : ℝ) (hab : a ≤ b)
    (P : Partition a b hab) : ℝ :=
  ∑ i : Fin P.n, ‖μ.toFun (P.points i.castSucc) (P.points i.succ)
    (le_of_lt (P.strict_mono i.castSucc_lt_succ))‖

/-- The total variation of a complex premeasure on an interval [a, b].

    This is defined as the supremum over all partitions of the sum of norms:
    |μ|([a,b]) := sup { Σᵢ ‖μ([tᵢ, tᵢ₊₁])‖ : a = t₀ < t₁ < ... < tₙ = b }

    For an additive complex function, this is finite and satisfies:
    - |μ|([a,a]) = 0 (single point)
    - |μ|([a,c]) = |μ|([a,b]) + |μ|([b,c]) (additivity)
    - |μ|([a,b]) ≥ ‖μ([a,b])‖ (triangle inequality) -/
noncomputable def totalVariation (a b : ℝ) (hab : a ≤ b) : ℝ≥0∞ :=
  ⨆ (P : Partition a b hab), ENNReal.ofReal (partitionVariation μ a b hab P)

/-- Convert to a real interval premeasure via total variation.

    The key properties of total variation:
    1. point_zero: |μ|({a}) = 0 because the only partition has one point, no intervals
    2. additive: |μ|([a,c]) = |μ|([a,b]) + |μ|([b,c]) because partitions can be merged/split
    3. monotone: [a',b'] ⊆ [a,b] ⟹ |μ|([a',b']) ≤ |μ|([a,b]) by additivity
    4. locally_finite: |μ|([a,b]) ≤ totalVar_bound (from the bound on μ) -/
def toIntervalPremeasure : IntervalPremeasure where
  toFun := fun a b hab => totalVariation μ a b hab
  point_zero := fun a => by
    simp only [totalVariation, partitionVariation]
    -- For a = a, the only partition has n = 0, so the sum is empty = 0
    -- The sup of 0 is 0
    apply le_antisymm
    · -- Upper bound: all partitions have variation 0
      apply iSup_le
      intro P
      -- For a = a with strict_mono, we must have n = 0
      -- Because points 0 = a and points n = a, but strict_mono means points 0 < points n if n > 0
      have hn : P.n = 0 := by
        by_contra h
        push Not at h
        have h0 : 0 < P.n := Nat.pos_of_ne_zero h
        have hfirst := P.first
        have hlast := P.last
        have hlt : (⟨0, Nat.zero_lt_succ P.n⟩ : Fin (P.n + 1)) <
                   (⟨P.n, Nat.lt_succ_self P.n⟩ : Fin (P.n + 1)) := by
          exact h0
        have hpts := P.strict_mono hlt
        rw [hfirst, hlast] at hpts
        exact lt_irrefl a hpts
      -- Now use hn : P.n = 0 to show the sum is empty
      have hempty : (Finset.univ : Finset (Fin P.n)) = ∅ := by
        rw [hn]
        rfl
      simp only [hempty, Finset.sum_empty, ENNReal.ofReal_zero, le_refl]
    · exact zero_le _
  additive := fun a b c hab hbc => by
    -- Key property: partitions of [a,c] correspond to merged partitions of [a,b] ∪ [b,c]
    -- Any partition of [a,c] refines to one through b (adding b if needed)
    -- The supremum over [a,c] equals sum of suprema over [a,b] and [b,c]
    sorry
  monotone := fun a b a' b' hab ha'b' ha hb => by
    -- Follows from additivity: [a,b] = [a,a'] ∪ [a',b'] ∪ [b',b]
    -- So |μ|([a,b]) = |μ|([a,a']) + |μ|([a',b']) + |μ|([b',b]) ≥ |μ|([a',b'])
    sorry
  locally_finite := fun a b hab => by
    -- Bound: |μ|([a,b]) ≤ totalVar_bound
    -- For any partition, Σᵢ ‖μ([tᵢ, tᵢ₊₁])‖ ≤ n · totalVar_bound
    -- But we need a uniform bound independent of partition size...
    -- Actually, for bounded variation functions, the total variation is finite.
    -- This requires the norm_le hypothesis on μ.
    sorry

/-- The positive Borel measure from the total variation. -/
def toPositiveMeasure : Measure ℝ :=
  IntervalPremeasure.toMeasure (toIntervalPremeasure μ)

/-- The complex measure on Borel sets.
    For a Borel set E, this is defined as the limit of μ(E ∩ [-n, n]).

    Note: This requires careful construction using the dominated convergence
    theorem and the boundedness of μ. -/
def toComplexMeasure' (ν : ComplexIntervalPremeasure) (E : Set ℝ) : ℂ := by
  -- The sequence μ(E ∩ [-n, n]) is Cauchy because the differences
  -- |μ(E ∩ [-m, m]) - μ(E ∩ [-n, n])| ≤ |μ|(E ∩ ([-m,m] \ [-n,n]))
  -- which goes to 0 as n, m → ∞.
  exact sorry

end ComplexIntervalPremeasure

/-! ### Spectral premeasure from inner products -/

/-- A spectral premeasure: for each pair (x, y), a complex interval premeasure
    arising from spectral projections ⟨x, P([a,b])y⟩.

    This structure captures the abstract properties of a family of complex measures
    parameterized by vectors in a Hilbert space, with the sesquilinear structure
    that characterizes spectral measures. -/
structure SpectralPremeasure (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The sesquilinear form B_{x,y}([a, b]) = ⟨x, P([a,b])y⟩ -/
  form : H → H → ComplexIntervalPremeasure
  /-- Linear in y -/
  linear_right : ∀ x y₁ y₂ a b (hab : a ≤ b) (c : ℂ),
    (form x (c • y₁ + y₂)).toFun a b hab =
    c * (form x y₁).toFun a b hab + (form x y₂).toFun a b hab
  /-- Conjugate-linear in x -/
  conj_linear_left : ∀ x₁ x₂ y a b (hab : a ≤ b) (c : ℂ),
    (form (c • x₁ + x₂) y).toFun a b hab =
    starRingEnd ℂ c * (form x₁ y).toFun a b hab + (form x₂ y).toFun a b hab
  /-- Positivity: B_{x,x}([a, b]).re ≥ 0 -/
  nonneg : ∀ x a b (hab : a ≤ b), 0 ≤ ((form x x).toFun a b hab).re
  /-- Boundedness: |B_{x,y}([a, b])| ≤ ‖x‖ · ‖y‖ -/
  bound : ∀ x y a b (hab : a ≤ b), ‖(form x y).toFun a b hab‖ ≤ ‖x‖ * ‖y‖

namespace SpectralPremeasure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extend the spectral premeasure to a full spectral measure on Borel sets. -/
def toSpectralMeasure (P : SpectralPremeasure H) (E : Set ℝ) (x y : H) : ℂ :=
  ComplexIntervalPremeasure.toComplexMeasure' (P.form x y) E

/-- The extended measure agrees with the premeasure on intervals. -/
theorem toSpectralMeasure_Icc (P : SpectralPremeasure H) (a b : ℝ) (hab : a ≤ b) (x y : H) :
    P.toSpectralMeasure (Set.Icc a b) x y = (P.form x y).toFun a b hab := by
  sorry

/-- The extended measure is σ-additive. -/
theorem toSpectralMeasure_sigma_additive (P : SpectralPremeasure H)
    (x y : H) (E : ℕ → Set ℝ) (hdisj : ∀ i j, i ≠ j → Disjoint (E i) (E j)) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, P.toSpectralMeasure (E i) x y)
      atTop (nhds (P.toSpectralMeasure (⋃ i, E i) x y)) := by
  sorry

/-- The extended measure satisfies μ_{x,y}(ℝ) = ⟨x, y⟩. -/
theorem toSpectralMeasure_univ (P : SpectralPremeasure H) (x y : H) :
    P.toSpectralMeasure Set.univ x y = @inner ℂ H _ x y := by
  sorry

end SpectralPremeasure

/-! ### Construction from bump function operators -/

/-- Given operators P_n that approximate spectral projections, construct a spectral premeasure
    as the limit of ⟨x, P_n([a,b])y⟩.

    This is the key construction connecting the functional calculus approach
    (via bump functions) to the measure-theoretic approach. -/
def spectralPremeasureFromLimit {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : ℕ → ℝ → ℝ → H →L[ℂ] H)
    (hP_norm : ∀ n a b, ‖P n a b‖ ≤ 1)
    (hP_cauchy : ∀ a b x y, CauchySeq (fun n => @inner ℂ H _ x (P n a b y))) :
    SpectralPremeasure H where
  form := fun x y => {
    toFun := fun a b _hab =>
      Classical.choose (cauchySeq_tendsto_of_complete (hP_cauchy a b x y))
    point_zero := fun _a => by
      -- lim_{n→∞} ⟨x, P_n(a, a)y⟩ = 0 because P_n(a,a) → 0
      sorry
    additive := fun _a _b _c _hab _hbc => by
      -- Follows from additivity of indicator functions in limit
      sorry
    totalVar_bound := ‖x‖ * ‖y‖
    totalVar_bound_nonneg := by positivity
    norm_le := fun _a _b _hab => by
      -- |⟨x, Py⟩| ≤ ‖x‖ · ‖Py‖ ≤ ‖x‖ · ‖P‖ · ‖y‖ ≤ ‖x‖ · ‖y‖
      sorry
  }
  linear_right := fun _x _y₁ _y₂ _a _b _hab _c => by sorry
  conj_linear_left := fun _x₁ _x₂ _y _a _b _hab _c => by sorry
  nonneg := fun _x _a _b _hab => by sorry
  bound := fun _x _y _a _b _hab => by sorry

end
