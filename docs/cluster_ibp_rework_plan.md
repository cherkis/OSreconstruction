# IBP / Schwartz-pairing rework plan for the cluster-proof dominator step

**Branch**: `r2e/ruelle-poly-bound-chain` (will likely fork into `r2e/cluster-ibp-rework` for the actual implementation).
**Target**: close the production `sorry` at `OSReconstruction/Wightman/Reconstruction/WickRotation/RuelleClusterBound.lean:718` in the body of `W_analytic_cluster_integral_via_ruelle`.
**Vetting status**: DRAFT. **Original Tflat-based plan ruled out** by Gemini-deep-think vetting (2026-05-10). Probing the alternatives.
**Author**: Michael Douglas (Claude Code), 2026-05-10.

---

## What's being closed

`W_analytic_cluster_integral_via_ruelle` (henceforth WCIVR) is the OS-side cluster theorem for the Wick-rotated boundary integral. Statement (paraphrased):

> For OPTR-supported `f : SchwartzNPoint d n` and `g : SchwartzNPoint d m`, given `RuelleAnalyticClusterHypotheses Wfn n m`, the joint Wick-rotated integral
> ```
> J(a) := ∫ F_ext_on_translatedPET_total Wfn (wick(x_n, x_m + (0,a))) · (f ⊗ g_a)(x) dx
> ```
> converges to the product of single-block integrals `L_n · L_m` as `|⃗a| → ∞`.

The current `sorry` is at the dominator-integrability step. The reason: post-vacuity-fix `RACH.bound` carries a `(1 + Δ⁻¹)^M` boundary regulator (Streater-Wightman 3.1.1 shape). After Wick rotation this becomes `1/Δ_time^M` — codimension-1 diagonal singularity, **not locally integrable for `M ≥ 1`**. So a pointwise dominator + dominated convergence cannot work.

The textbook resolution (Streater-Wightman §3.4 / Ruelle 1962 / AHR 1962) routes through a **Schwartz dual pairing** with a tempered distribution `Tflat`, not pointwise dominators.

---

## ⚠️ The FL trap that rules out the original Tflat-based plan

**Vetting by Gemini (2026-05-10)** identified a fatal flaw in the original Schwartz-pairing plan that uses a single Tflat:

For Wick-rotated points `z_k = wick(x_k) = (i τ_k, x_k)`, the FL kernel is
```
exp(i ξ_k · z_k) = exp(- E_k · Δτ_k - i p_k · Δx_k)
```
where Δτ_k are imaginary-time differences. Tflat's support in the dual cone (E_k ≥ 0) means the kernel is bounded **only when all Δτ_k > 0**.

For OPTR-supported `f, g` independently, the within-block time differences are positive. But the **junction** Δτ_{n+1, n} = τ_{n+1} − τ_n (last time of f vs first time of g) is **unconstrained** — `f` and `g` are independent Schwartz tests on independent OPTR domains. Junction inversion (`τ_{n+1} < τ_n`) is generic.

For junction-inverted z, the kernel `exp(i ξ · z)` has a factor `exp(+E · |Δτ_junction|)` that blows up exponentially as `E → ∞` in the Tflat support. So `ψ_z(ξ) := exp(i ξ · z)` **fails to be Schwartz**. Any application of `schwartz_clm_fubini_exchange` (which requires polynomial seminorm growth of the Schwartz-valued family) crashes here.

**Conclusion**: a single Tflat representation `W_analytic_BHW(z) = Tflat(ψ_z)` does NOT extend to all of PET — it works only on configurations whose imaginary differences are all positive (= the unpermuted ForwardTube subset of PET). Joint configs with junction inversion lie outside the FL representation's natural domain.

This rules out the original 6-sub-lemma plan.

---

## Three viable alternatives

### Alternative A — Per-permutation Tflat, glued by BHW symmetry

**Math**: PET is the permutation closure of ForwardTube. For each permutation σ ∈ S_{n+m}, `σ⁻¹(ForwardTube)` ⊂ PET admits a single Tflat representation. By BHW (`W_analytic_BHW` is permutation-invariant on PET), the Tflat's for different σ are related by permutation symmetry on the dual side.

For OPTR f, g with junction inversion, the natural permutation σ swaps the offending indices to put the joint config in ForwardTube under σ⁻¹. Apply Tflat_σ. Sum over the appropriate covering permutations.

**Lean status**:
- Requires a **family of Tflat distributions indexed by permutation**, with explicit symmetry relations.
- Need to prove the family is consistent (uniqueness of W_analytic on overlapping pieces).
- The Schwartz-Fubini exchange now has to be done per-Tflat_σ, then summed.

**Estimated effort**: 3–5 weeks. Mathematical complexity dominates; Lean engineering is roughly proportional.

**Risk**: high — the per-σ FL machinery is a new layer, and the permutation symmetry relations on the dual side are not in the project today.

### Alternative B — GNS-Bochner shortcut (Gemini's first recommendation)

**Math** (per Gemini): use the Wightman reconstruction identity directly. Define analytic Hilbert states `Φ(z) ∈ GNSHilbertSpace Wfn` for tube z via
```
Φ(z₁,...,z_n) := exp(-Im(z_n)·P) φ̂(x_n) ... exp(-Im(z₁ - z₂)·P) φ̂(x_1) Ω
```
(or some such formulation; spectrum_condition gives `e^{-yP}` bounded for `y ∈ V+`). Then:
- `u := (z̄_n, ..., z̄_1)` for OPTR f-block: in ForwardTube (positive successive Im differences). ✓
- `v := (z_{n+1}, ..., z_{n+m})` for OPTR g-block: in ForwardTube. ✓
- **No junction constraint needed at the Hilbert level**: Φ(u) and Φ(v) are independently well-defined finite-norm vectors. Their inner product `⟨Φ(u), Φ(v)⟩` equals `W_analytic(joint)` regardless of junction ordering.
- Bochner-integrate against f, g: `Ψ_f := ∫ Φ(u(x)) f(x) dx`, `Ψ_g := ∫ Φ(v(x)) g(x) dx`.
- Joint integral `J(a) = ⟨Ψ_f, U(a) Ψ_g⟩`.
- Apply existing `gns_orthogonal_spatial_cobounded_decay_of` (PR #86) to derive `J(a) → ⟨Ψ_f, Ω⟩ ⟨Ω, Ψ_g⟩ = L_n · L_m`.

**Lean status (probed 2026-05-10)**:
- ✅ GNS Hilbert space exists (`GNSHilbertSpace Wfn`, `gnsVacuum`).
- ✅ `WightmanInnerProduct d Wfn.W F G` for Borchers sequences `F, G`.
- ✅ `gns_cluster_completion`, `gns_orthogonal_spatial_cobounded_decay_of` (PR #86).
- ✅ `poincareActGNS` (Poincaré rep on GNS, used as `U(a)`).
- ❌ **No analytic Hilbert states `Φ(z)` for tube `z` defined.** This is the missing infrastructure.
- ❌ No `e^{-yP}` bounded-operator infrastructure for forward-cone `y`.
- ❌ No identity linking `⟨Φ(u), Φ(v)⟩` to `W_analytic(joint)` exposed as a lemma.

**Estimated effort to ship analytic-state machinery + glue**:
- `e^{-yP}` semigroup as bounded operators on GNS (via spectral functional calculus on the joint translation rep): **1–2 weeks**.
- Analytic-state construction `Φ(z)` for `z ∈ ForwardTube`: **1 week**, requires careful adjoint conventions and BHW-ordering analysis.
- `⟨Φ(u), Φ(v)⟩ = W_analytic(joint)` identity: **3–5 days** if analytic-state machinery is clean; could be longer if Lean type-class issues bite.
- Bochner integration of Schwartz-tame Hilbert-valued families: **2–3 days** (Mathlib has `MeasureTheory.Bochner` infrastructure, application is mechanical).
- Glue with cluster-decay: **3 days**.
- **Total: 3–5 weeks**.

**Risk**: medium. The analytic-Hilbert-state machinery is well-understood mathematically (Reed-Simon II §IX.8) but new to this project. Could compound with subtle technical obstacles around the spectral calculus and translation-by-imaginary-vector conventions.

**Plus**: aligns with the project's existing GNS direction; the analytic-state machinery would also unlock other cluster / decay arguments for free.

### Alternative C — Axiomatize the joint-integral cluster (Gemini's fallback)

**Math**: rather than going through any spectral or Hilbert-side machinery, introduce a `ClusterSpectralData` hypothesis that directly asserts `J(a) → L_n · L_m` for the joint integral itself, with appropriate hypotheses (OPTR support, etc.).

```lean
structure JointIntegralClusterData (Wfn : WightmanFunctions d) (n m : ℕ) : Prop where
  decay :
    ∀ (f : SchwartzNPoint d n) (g : SchwartzNPoint d m),
      OPTR_supp f → OPTR_supp g → ∀ ε > 0,
        ∃ R > 0, ∀ a, a 0 = 0, |⃗a| > R, ∀ g_a equiv to g(·−a),
          ‖J(a) − L_n · L_m‖ < ε
```

This is essentially the cluster-theorem statement promoted to a hypothesis structure, conditional only on Wfn (not on RACH).

**Lean status**: trivial to write the structure. Discharge becomes its own future-work item.

**Estimated effort**: 3–5 days for the structure + glue at the cluster proof site.

**Risk**: low to ship; the discharge becomes another open item like RACH was (now partially closed). The new axiom (if shipped) sits at the QFT-trust-boundary — Xi's discipline applies, and we'd need vetting (Gemini chat + deep-think) and audit-table entry.

**Trade-off**: this *transports* the unsolved content rather than solving it. It moves the open work from "prove the cluster theorem from RACH" to "supply `JointIntegralClusterData` from Wfn". The latter is essentially the textbook content and would be vetted as such.

---

## Comparison and recommendation

| Alternative | Effort | Risk | New axioms | Project alignment |
|-------------|--------|------|------------|-------------------|
| A — Per-permutation Tflat | 3–5 wk | High | None | Stays in SCV/FL track |
| B — GNS-Bochner shortcut | 3–5 wk | Medium | None | Aligns with GNS / L2 work |
| C — Axiomatize joint cluster | 3–5 days | Low ship, deferred discharge | One new vetted hypothesis | Transports problem |

**Pre-final recommendation** (subject to user vetting):

**Pursue B (GNS-Bochner) as the primary path**, with **C as the explicit fallback** if the analytic-state infrastructure proves harder than estimated. Reasons:

1. B aligns with the GNS direction the L2/L4 work in PR #86 already pushed.
2. B's intermediate machinery (analytic-Hilbert states + bounded `e^{-yP}` semigroup) has independent value for future cluster / decay arguments.
3. C is a 3–5 day fallback. If B's infrastructure work hits a 3–4 week wall, drop to C.
4. A (per-permutation Tflat) is the highest-risk path with the least independent value; deprioritize.

**A is genuinely an option** if Xi's E→R checkpoint work happens to expose Tflat or BHW symmetry infrastructure that we don't have yet — worth checking with him before committing.

---

## Sub-lemma decomposition for Alternative B

Assuming we go with B:

### B.1 — Bounded `e^{-yP}` semigroup on GNS Hilbert space

For `y ∈ V̄+` (forward cone closure), `exp(-y·P)` is a bounded operator on `GNSHilbertSpace Wfn`, where `P` is the joint translation generator (4-momentum) from SNAG.

**Building blocks**:
- SNAG theorem axiom (existing) gives joint PVM `E` for the spacetime translation rep on GNS.
- `exp(-y·P) := ∫ exp(-y·p) dE(p)` is a positive operator (since `p ∈ V̄+` on the spectrum, `y·p ≥ 0`, so `exp(-y·p) ≤ 1`).
- Bounded with norm ≤ 1.

**Estimated effort**: 1–2 weeks. Spectral functional calculus on the SNAG-derived PVM.

### B.2 — Analytic Hilbert states `Φ(z)` for `z ∈ ForwardTube d n`

Define `Φ(z₁,...,z_n) ∈ GNSHilbertSpace Wfn` via the BHW-order convention:
```
Φ(z₁,...,z_n) := exp(-Im(z₁)·P) φ(Re(z₁)) ·
                 exp(-Im(z₂ − z₁)·P) φ(Re(z₂ − z₁)) ·
                 ... ·
                 exp(-Im(z_n − z_{n-1})·P) φ(Re(z_n − z_{n-1})) Ω
```
Each `exp(-(y_k − y_{k-1})·P)` is bounded (B.1) since successive Im differences are in V+. The field operators `φ(x)` need to be applied to vectors in their domain — for analytic states `Φ(z)` with positive Im differences, these are standard arguments.

**Estimated effort**: 1 week, including identification with existing project field-operator machinery.

### B.3 — `⟨Φ(u), Φ(v)⟩ = W_analytic(joint(u,v))` identity

Where `u := (z̄_n,...,z̄_1)` and `v := (z_{n+1},...,z_{n+m})` for `(z₁,...,z_{n+m}) ∈ PET`.

The identity holds by direct computation: expanding both sides via the field-operator definitions and the BHW analytic-continuation theorem.

**Estimated effort**: 3–5 days.

### B.4 — Bochner-integrated Hilbert states from Schwartz tests

For `f : SchwartzNPoint d n` (OPTR-supported), define
```
Ψ_f := ∫ Φ(wick(x)) f(x) dx ∈ GNSHilbertSpace Wfn
```

via Mathlib's `MeasureTheory.Bochner` infrastructure. Need:
- Strong measurability of `x ↦ Φ(wick(x))` as a Hilbert-valued map.
- Norm bound: `‖Φ(wick(x))‖ ≤ K(x)` with `K(x) · |f(x)|` integrable (from Schwartz fall-off).

**Estimated effort**: 2–3 days. Mathlib's Bochner infrastructure is ready.

### B.5 — Glue: joint integral = `⟨Ψ_f, U(a) Ψ_g⟩`

Combine B.3 (per-config inner product) with B.4 (Bochner integral) via Schwartz-Fubini for Hilbert-valued integrals.

**Estimated effort**: 3 days.

### B.6 — Apply cluster-decay and identify limit

With `J(a) = ⟨Ψ_f, U(a) Ψ_g⟩`:
- Split off `Ω`-projections: `Ψ_f = ⟨Ω, Ψ_f⟩·Ω + (Ψ_f^⊥)`, similarly for `Ψ_g`.
- Apply `gns_orthogonal_spatial_cobounded_decay_of` to the `(Ψ_f^⊥, Ψ_g^⊥)` part.
- Disconnected limit: `⟨Ψ_f, Ω⟩ ⟨Ω, Ψ_g⟩`.
- Identify these projections with `L_n` and `L_m` via boundary recovery.

**Estimated effort**: 3–5 days.

### B.7 — Wire into `W_analytic_cluster_integral_via_ruelle`

Replace the `sorry` body with the assembled argument. The cluster theorem then becomes unconditional given `Wfn`'s axioms (not even RACH needed if the argument routes through GNS directly, though RACH may still be needed for other purposes in the broader cluster theorem).

**Estimated effort**: 2–3 days.

### Sub-total for B

3–5 weeks, with B.1 (bounded `e^{-yP}`) being the largest piece.

---

## Ordering of work

If B is chosen:
1. **B.1 first** — bounded `e^{-yP}` semigroup. This is the foundational infrastructure; everything else depends on it.
2. **B.2 after B.1** — analytic Hilbert states.
3. **B.3, B.4, B.5 in parallel-ish** — they're each ~3 days, independent given B.2.
4. **B.6, B.7 last** — glue.

If C is chosen as fallback (after some progress on B reveals it's harder than estimated):
1. Define `JointIntegralClusterData` structure.
2. Wire into cluster proof.
3. Defer discharge as future work.

---

## Open questions for the user

1. **Path choice**: B (GNS-Bochner, full infrastructure) or C (axiomatize, defer)? Per-permutation Tflat (A) is deprioritized.
2. **Time budget**: 3–5 weeks for B is the realistic estimate. Acceptable, or push for C as a faster ship?
3. **Coordination with Xi**: do we ping him now (post-pivot) or wait until we have concrete progress on B (or commitment to C)? Per his `bv_implies_fourier_support`-shaped previous reviews, he'd appreciate the Gemini-vetted FL-trap diagnosis even before code lands.
4. **Branch**: fork `r2e/cluster-ibp-rework` from current `r2e/ruelle-poly-bound-chain` head? Or start a clean branch from main + cherry-pick the chain-repair commits?
5. **PR cadence**: ship the chain-repair (commits `ebd007f`, `050449b`, `973617a`) as a small PR now — yes/no?

---

## Pre-reqs already in place

- ✅ `Wfn.spectrum_condition_compact_subset` (`973617a`) — satisfiable form for new code paths.
- ✅ `bv_implies_fourier_support` relaxed (`ebd007f`) — though not used by Alternative B.
- ✅ `vladimirov_tillmann` consumer relaxed.
- ✅ `hasCompactSubsetGrowth_of_global_polyGrowth` helper.
- ✅ `gns_cluster_completion` (existing).
- ✅ `gns_orthogonal_spatial_cobounded_decay_of` (PR #86).
- ✅ SNAG axiom (existing) — basis for B.1.
- ✅ `WightmanInnerProduct` Borchers-sequence pairing (existing).
- ❌ Bounded `e^{-yP}` semigroup — needs B.1.
- ❌ Analytic Hilbert states `Φ(z)` for tube `z` — needs B.2.

---

## Status of the FL-side Tflat machinery

The chain-repair commits on this branch (`ebd007f`, `050449b`, `973617a`) **remain useful** independently of which alternative is chosen. They:
- Make `bv_implies_fourier_support` hypothesis legitimate (Vladimirov H(T^C) form).
- Add `Wfn.spectrum_condition_compact_subset` so new code doesn't perpetuate the unsatisfiable form.
- Wire helper conversions at 4 call sites.

These are project-trust-surface improvements regardless of the IBP rework path. Worth shipping as a small PR per Gemini's recommendation.
