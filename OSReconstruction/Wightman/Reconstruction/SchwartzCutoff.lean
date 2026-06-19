import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Schwartz Tail Decay

Small Schwartz-space estimates used in cutoff and density arguments.
-/

noncomputable section

open SchwartzMap

namespace OSReconstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- For a Schwartz function `f`, the weighted derivative norm
`‖x‖^k * ‖D^p f(x)‖` is uniformly small outside a large ball. -/
theorem schwartz_tail_decay (f : SchwartzMap (Fin n → ℝ) ℂ) (k p : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (x : Fin n → ℝ), R₀ < ‖x‖ →
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ < ε := by
  obtain ⟨C, hC⟩ := f.decay' (k + 2) p
  refine ⟨max 1 (Real.sqrt (|C| / ε) + 1), by positivity, fun x hR₀ => ?_⟩
  have hx2_pos : 0 < ‖x‖ ^ 2 := by
    have hx_pos : 0 < ‖x‖ := lt_of_lt_of_le (by positivity) (le_of_lt hR₀)
    positivity
  have key : ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ ≤ |C| / ‖x‖ ^ 2 := by
    have hbound := hC x
    have hpow : ‖x‖ ^ (k + 2) = ‖x‖ ^ k * ‖x‖ ^ 2 := by ring
    rw [hpow] at hbound
    rw [le_div_iff₀ hx2_pos]
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ * ‖x‖ ^ 2
          = ‖x‖ ^ k * ‖x‖ ^ 2 * ‖iteratedFDeriv ℝ p (⇑f) x‖ := by ring
      _ ≤ C := hbound
      _ ≤ |C| := le_abs_self C
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (⇑f) x‖ ≤ |C| / ‖x‖ ^ 2 := key
    _ < ε := by
      rw [div_lt_iff₀ hx2_pos]
      have hR_bound : Real.sqrt (|C| / ε) + 1 < ‖x‖ :=
        lt_of_le_of_lt (le_max_right _ _) hR₀
      have hsqrt_lt : Real.sqrt (|C| / ε) < ‖x‖ := by
        linarith
      have hCε : |C| / ε < ‖x‖ ^ 2 := by
        have h1 :=
          Real.sq_sqrt (show 0 ≤ |C| / ε from div_nonneg (abs_nonneg _) (le_of_lt hε))
        have hsqrt_nonneg : 0 ≤ Real.sqrt (|C| / ε) := Real.sqrt_nonneg _
        have hnorm_nonneg : 0 ≤ ‖x‖ := norm_nonneg x
        have hsq : (Real.sqrt (|C| / ε)) ^ 2 < ‖x‖ ^ 2 := by
          nlinarith
        calc
          |C| / ε = (Real.sqrt (|C| / ε)) ^ 2 := h1.symm
          _ < ‖x‖ ^ 2 := hsq
      have := (div_lt_iff₀ hε).mp hCε
      linarith

/-- If a sequence of Schwartz functions vanishes on the growing ball
`‖x‖ ≤ n + 1` at derivative order `l`, and their `(k + 2, l)` seminorms are
uniformly bounded, then the `(k,l)` seminorms tend to `0`. -/
theorem schwartz_seminorm_tendsto_zero_of_vanish_on_ball_uniform
    (h : ℕ → SchwartzMap E ℂ) (k l : ℕ)
    (hvanish : ∀ (n : ℕ) (x : E), ‖x‖ ≤ (n : ℝ) + 1 →
      iteratedFDeriv ℝ l (⇑(h n)) x = 0)
    (M : ℝ) (hM_pos : 0 ≤ M) (hM : ∀ n, (SchwartzMap.seminorm ℝ (k + 2) l) (h n) ≤ M) :
    Filter.Tendsto (fun n => (SchwartzMap.seminorm ℝ k l) (h n))
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨Nat.ceil (Real.sqrt (M / ε)) + 1, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  apply lt_of_le_of_lt
  · apply SchwartzMap.seminorm_le_bound ℝ k l (h n) (M := M / ((n : ℝ) + 1) ^ 2)
    · exact div_nonneg hM_pos (sq_nonneg _)
    · intro x
      by_cases hx : ‖x‖ ≤ (n : ℝ) + 1
      · simp [hvanish n x hx]
        exact div_nonneg hM_pos (sq_nonneg _)
      · push Not at hx
        have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hx_pos : 0 < ‖x‖ := lt_trans hn1_pos hx
        calc
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(h n)) x‖
              = (‖x‖ ^ (k + 2) * ‖iteratedFDeriv ℝ l (⇑(h n)) x‖) / ‖x‖ ^ 2 := by
                  field_simp [ne_of_gt (pow_pos hx_pos 2)]
                  ring
          _ ≤ (SchwartzMap.seminorm ℝ (k + 2) l) (h n) / ‖x‖ ^ 2 := by
                apply div_le_div_of_nonneg_right _ (sq_nonneg _)
                exact SchwartzMap.le_seminorm ℝ (k + 2) l (h n) x
          _ ≤ M / ‖x‖ ^ 2 := by
                apply div_le_div_of_nonneg_right (hM n) (sq_nonneg _)
          _ ≤ M / ((n : ℝ) + 1) ^ 2 := by
                apply div_le_div_of_nonneg_left hM_pos (pow_pos hn1_pos 2)
                exact sq_le_sq' (by linarith) hx.le
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((n : ℝ) + 1) ^ 2)]
    have hn1 : (n : ℝ) + 1 ≥ Real.sqrt (M / ε) + 1 := by
      have h1 : (⌈Real.sqrt (M / ε)⌉₊ : ℝ) ≥ Real.sqrt (M / ε) :=
        Nat.le_ceil (Real.sqrt (M / ε))
      have h2 : (n : ℝ) ≥ (⌈Real.sqrt (M / ε)⌉₊ : ℝ) + 1 := by
        exact_mod_cast hn
      linarith
    have hsq : M / ε < ((n : ℝ) + 1) ^ 2 := by
      calc
        M / ε ≤ (Real.sqrt (M / ε)) ^ 2 :=
          le_of_eq (Real.sq_sqrt (div_nonneg hM_pos hε.le)).symm
        _ < ((n : ℝ) + 1) ^ 2 := by
          nlinarith [Real.sqrt_nonneg (M / ε)]
    linarith [div_lt_iff₀ hε |>.mp hsq]

end OSReconstruction
