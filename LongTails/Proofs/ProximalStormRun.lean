import LongTails.Proofs.ProximalStormInner
import LongTails.Proofs.HessianNcscProcess

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

noncomputable def innerRun (g : E → Ω → E) (lam eta a : ℝ) (xt : E) (ξ : ℕ → Ω) (n0 : ℕ) :
    ℕ → E × E
  | 0 => (xt, g xt (ξ n0))
  | t + 1 => innerStep g lam eta a xt (innerRun g lam eta a xt ξ n0 t) (ξ (n0 + t + 1))

omit [CompleteSpace E] in
lemma measurable_innerStep {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (lam eta a : ℝ) : Measurable (fun z : (E × (E × E)) × Ω => innerStep g lam eta a z.1.1 z.1.2 z.2) := by
  have hx : Measurable fun z : (E × (E × E)) × Ω => z.1.2.1 - eta • z.1.2.2 := by fun_prop
  have hxt : Measurable fun z : (E × (E × E)) × Ω => z.1.1 := by fun_prop
  have hg1 : Measurable fun z : (E × (E × E)) × Ω => g (z.1.2.1 - eta • z.1.2.2) z.2 :=
    hg.comp (hx.prodMk measurable_snd)
  have hg2 : Measurable fun z : (E × (E × E)) × Ω => g z.1.2.1 z.2 :=
    hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  unfold innerStep
  refine hx.prodMk ?_
  have h3 : Measurable fun z : (E × (E × E)) × Ω => z.1.2.2 := by fun_prop
  have h4 : Measurable fun z : (E × (E × E)) × Ω => z.1.2.1 := by fun_prop
  exact (hg1.add ((hx.sub hxt).const_smul _)).add
    ((h3.sub (hg2.add ((h4.sub hxt).const_smul _))).const_smul _)

omit [CompleteSpace E] in
lemma measurable_innerRun {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (lam eta a : ℝ) {X : (ℕ → Ω) → E} (hX : Measurable X) (n0 : ℕ) :
    ∀ t, Measurable fun ξ : ℕ → Ω => innerRun g lam eta a (X ξ) ξ n0 t
  | 0 => hX.prodMk (hg.comp (hX.prodMk (measurable_pi_apply n0)))
  | t + 1 => (measurable_innerStep hg lam eta a).comp
      ((hX.prodMk (measurable_innerRun hg lam eta a hX n0 t)).prodMk
        (measurable_pi_apply (n0 + t + 1)))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma innerRun_congr (g : E → Ω → E) (lam eta a : ℝ) {X : (ℕ → Ω) → E} {n0 : ℕ}
    (hX : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 → ξ i = ξ' i) → X ξ = X ξ') :
    ∀ t, ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 + t + 1 → ξ i = ξ' i) →
      innerRun g lam eta a (X ξ) ξ n0 t = innerRun g lam eta a (X ξ') ξ' n0 t
  | 0, ξ, ξ', h => by
      have hx := hX ξ ξ' fun i hi => h i (by omega)
      simp only [innerRun, hx, h n0 (by omega)]
  | t + 1, ξ, ξ', h => by
      have hp := innerRun_congr g lam eta a hX t ξ ξ' fun i hi => h i (by omega)
      have hx := hX ξ ξ' fun i hi => h i (by omega)
      simp only [innerRun]
      rw [hp, hx, h (n0 + t + 1) (by omega)]

section Tower

variable {St : Type*} [MeasurableSpace St]

lemma tower_le (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ) (S : (ℕ → Ω) → St)
    (hS : Measurable S) (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ')
    (h : St → Ω → ℝ) (hh : Measurable (Function.uncurry h)) (h0 : ∀ s ω, 0 ≤ h s ω)
    (hi : ∀ s, Integrable (h s) p) (r : St → ℝ≥0∞) (hr : ∀ s, ENNReal.ofReal (∫ ω, h s ω ∂p) ≤ r s) :
    ∫⁻ ξ, ENNReal.ofReal (h (S ξ) (ξ k)) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ∫⁻ ξ, r (S ξ) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  have hm : Measurable fun z : St × Ω => ENNReal.ofReal (h z.1 z.2) :=
    ENNReal.measurable_ofReal.comp hh
  rw [HessianNcsc.fresh_lintegral p k S hS hdep (fun z => ENNReal.ofReal (h z.1 z.2)) hm]
  refine lintegral_mono fun ξ => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal (hi (S ξ))
    (Filter.Eventually.of_forall fun ω => h0 (S ξ) ω)]
  exact hr (S ξ)

end Tower

section Sequence

lemma window_bound (u v : ℕ → ℝ≥0∞) (K c : ℝ≥0∞) (hc : c ≤ 1) (hc0 : c ≠ 0)
    (h1 : ∀ t, u (t + 1) + v t ≤ u t + K) (h2 : ∀ t, u (t + 1) ≤ (1 - c) * u t + K)
    (T0 W : ℕ) :
    ∑ j ∈ Finset.range W, v (T0 + j) ≤ (1 - c) ^ T0 * u 0 + K / c + W * K := by
  have hgeo : ∀ n, u n ≤ (1 - c) ^ n * u 0 + K / c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        refine (h2 n).trans ?_
        calc (1 - c) * u n + K ≤ (1 - c) * ((1 - c) ^ n * u 0 + K / c) + K := by gcongr
          _ = (1 - c) ^ (n + 1) * u 0 + ((1 - c) * (K / c) + K) := by
              rw [mul_add, pow_succ, ← mul_assoc, mul_comm ((1 - c) ^ n) (1 - c), add_assoc]
          _ ≤ (1 - c) ^ (n + 1) * u 0 + K / c := by
              gcongr
              have : (1 - c) * (K / c) + K = K / c := by
                rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ← one_mul K]
                nth_rewrite 2 [show K = 1 * K by rw [one_mul]]
                rw [← add_mul]
                · congr 1
                  have hcinv : c * c⁻¹ = 1 := ENNReal.mul_inv_cancel hc0 (ne_top_of_le_ne_top
                    ENNReal.one_ne_top hc)
                  calc (1 - c) * c⁻¹ + 1 = (1 - c) * c⁻¹ + c * c⁻¹ := by rw [hcinv]
                    _ = ((1 - c) + c) * c⁻¹ := by rw [add_mul]
                    _ = c⁻¹ := by rw [tsub_add_cancel_of_le hc, one_mul]
              rw [this]
  have htel : ∀ n, u (T0 + n) + ∑ j ∈ Finset.range n, v (T0 + j) ≤ u T0 + n * K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ← add_assoc]
        have hs := h1 (T0 + n)
        calc u (T0 + (n + 1)) + ∑ j ∈ Finset.range n, v (T0 + j) + v (T0 + n)
            = (u (T0 + n + 1) + v (T0 + n)) + ∑ j ∈ Finset.range n, v (T0 + j) := by
              rw [← add_assoc T0 n 1]; ring
          _ ≤ (u (T0 + n) + K) + ∑ j ∈ Finset.range n, v (T0 + j) := by gcongr
          _ = (u (T0 + n) + ∑ j ∈ Finset.range n, v (T0 + j)) + K := by ring
          _ ≤ (u T0 + n * K) + K := by gcongr
          _ = u T0 + ((n + 1 : ℕ) : ℝ≥0∞) * K := by push_cast; ring
  calc ∑ j ∈ Finset.range W, v (T0 + j) ≤ u (T0 + W) + ∑ j ∈ Finset.range W, v (T0 + j) :=
        le_add_self
    _ ≤ u T0 + W * K := htel W
    _ ≤ ((1 - c) ^ T0 * u 0 + K / c) + W * K := by gcongr; exact hgeo T0

end Sequence

end OracleTemplate.ProximalStorm
