import LongTails.Proofs.HessianAdaptiveCubicRate
import LongTails.Proofs.HessianAdaptiveCubicMartingale
import LongTails.Proofs.HessianAdaptiveCubicInverseWeights
import LongTails.Proofs.AdamHeavyTailedHistory

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HessianAdaptiveCubicAccuracy

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants
open LongTails.Proofs.HessianAdaptiveCubicStep
open LongTails.Proofs.HessianAdaptiveCubicExecution
open LongTails.Proofs.HessianAdaptiveCubicMoments
open LongTails.Proofs.HessianAdaptiveCubicMartingale

lemma energy_telescope (E κ noise : ℕ → ℝ) (D : ℝ) (hκ : 0 ≤ κ 0)
    (hinit : E 0 ≤ κ 0 / 2 * D ^ 2)
    (hstep : ∀ n, E (n + 1) ≤ E n + (7 / 2) * D ^ 2 * (κ (n + 1) - κ n) + noise n)
    (N : ℕ) : E N ≤ (7 / 2) * D ^ 2 * κ N + ∑ n ∈ Finset.range N, noise n := by
  have hb : ∀ N, E N ≤ E 0 + (7 / 2) * D ^ 2 * (κ N - κ 0) +
      ∑ n ∈ Finset.range N, noise n := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n]
  have hnonneg : 0 ≤ D ^ 2 * κ 0 := mul_nonneg (sq_nonneg D) hκ
  nlinarith [hb N]

lemma model_energy_upper_bound {Ω : Type*} (p : Public)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (ξ : ℕ → Ω) (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (N : ℕ) :
    energy p f xstar (roundState p g H ξ N) ≤
      (7 / 2) * p.D ^ 2 * (roundState p g H ξ N).scale + noiseSum p f xstar g H N ξ := by
  let E := fun n => energy p f xstar (roundState p g H ξ n)
  let κ := fun n => (roundState p g H ξ n).scale
  have hinv (n : ℕ) := roundState_invariant p g H ξ hD hρ hσ hx n
  have hκ : 0 < κ 0 := (hinv 0).scale
  have hinit : E 0 ≤ κ 0 / 2 * p.D ^ 2 := by
    have hd := hdiam p.x0 hx xstar hxstar
    have hsq : ‖p.x0 - xstar‖ ^ 2 ≤ p.D ^ 2 := by nlinarith [norm_nonneg (p.x0 - xstar)]
    have hb := mul_le_mul_of_nonneg_left hsq (show 0 ≤ κ 0 / 2 by positivity)
    simpa only [E, κ, energy, roundState, initial, zero_mul, zero_add] using hb
  apply energy_telescope E κ (fun n => roundNoise p f xstar g H n ξ) p.D hκ.le hinit _ N
  intro n
  have hs := modelAt_invariant p g H ξ hD hρ hσ hx n
  have hpsd : IsPSD (modelAt p g H ξ n).modelHessian := hPSD _ (center_mem p _ (hinv n)) _
  have hb := adaptive_step_energy p (modelAt p g H ξ n)
    (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) xstar f hf hgrad hD hs hxstar hpsd
    (modelAt_trial p g H ξ n) hdiam
  have hmove := (movement_bounds p (modelAt p g H ξ n) hD hs hdiam).1
  have hnonneg : 0 ≤ (modelAt p g H ξ n).scale / 2 * movement p (modelAt p g H ξ n) :=
    mul_nonneg (div_nonneg hs.scale.le (by norm_num)) hmove
  have hES : energy p f xstar (modelAt p g H ξ n) = E n := rfl
  have hKS : (modelAt p g H ξ n).scale = κ n := rfl
  have hnext : roundState p g H ξ (n + 1) = advance p (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) := roundState_succ_modelAt p g H ξ n
  have hraw : E (n + 1) + (modelAt p g H ξ n).scale / 2 * movement p (modelAt p g H ξ n) ≤
      E n + (7 / 2) * p.D ^ 2 * (κ (n + 1) - κ n) + roundNoise p f xstar g H n ξ := by
    simpa only [E, κ, hnext, hES, hKS, roundNoise, dualNoise, real_inner_comm, neg_mul, sub_eq_add_neg] using hb
  linarith

lemma energy_square_bound {E κ M D : ℝ} (hE : 0 ≤ E)
    (hbound : E ≤ (7 / 2) * D ^ 2 * κ + M) :
    E ^ 2 ≤ (49 / 2) * D ^ 4 * κ ^ 2 + 2 * M ^ 2 := by
  have hsq := mul_self_le_mul_self hE hbound
  have hc := sq_nonneg ((7 / 2) * D ^ 2 * κ - M)
  nlinarith

lemma floor_square_bound {σ D κ t : ℝ} (hσ : 0 ≤ σ) (hD : 0 < D) (ht : 0 ≤ t)
    (hfloor : σ * (t + 1) ^ 3 / D ^ 2 ≤ κ) : σ ^ 2 * t ^ 6 ≤ D ^ 4 * κ ^ 2 := by
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht (by linarith : t ≤ t + 1) 3) hσ
  have hf := (div_le_iff₀ (sq_pos_of_pos hD)).mp hfloor
  have hb : σ * t ^ 3 ≤ κ * D ^ 2 := hp.trans hf
  have hs := mul_self_le_mul_self (show 0 ≤ σ * t ^ 3 by positivity) hb
  nlinarith only [hs]

lemma energy_second_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (E K M : X → ℝ) (D σ : ℝ) (N : ℕ)
    (hD : 0 < D) (hσ : 0 ≤ σ) (hmE : Measurable E) (hE : ∀ x, 0 ≤ E x)
    (hiK : Integrable (fun x => K x ^ 2) μ) (hiM : Integrable (fun x => M x ^ 2) μ)
    (hM : (∫ x, M x ^ 2 ∂μ) ≤ σ ^ 2 * (N : ℝ) ^ 6)
    (hfloor : ∀ x, σ * ((N : ℝ) + 1) ^ 3 / D ^ 2 ≤ K x)
    (hbound : ∀ x, E x ≤ (7 / 2) * D ^ 2 * K x + M x) :
    Integrable (fun x => E x ^ 2) μ ∧
      (∫ x, E x ^ 2 ∂μ) ≤ 36 * D ^ 4 * (∫ x, K x ^ 2 ∂μ) := by
  have hp (x : X) : E x ^ 2 ≤ (49 / 2) * D ^ 4 * K x ^ 2 + 2 * M x ^ 2 :=
    energy_square_bound (hE x) (hbound x)
  have hiB := (hiK.const_mul ((49 / 2) * D ^ 4)).add (hiM.const_mul 2)
  have hiE := HessianAdaptiveCubicNormalization.integrable_square_of_bound μ E _ hmE hiB hp
  refine ⟨hiE, ?_⟩
  have hb := integral_mono hiE hiB hp
  change (∫ x, E x ^ 2 ∂μ) ≤ (∫ x, (49 / 2) * D ^ 4 * K x ^ 2 + 2 * M x ^ 2 ∂μ) at hb
  rw [integral_add (f := fun x => (49 / 2) * D ^ 4 * K x ^ 2) (g := fun x => 2 * M x ^ 2)
    (hiK.const_mul _) (hiM.const_mul _), integral_const_mul, integral_const_mul] at hb
  have hf (x : X) : σ ^ 2 * (N : ℝ) ^ 6 ≤ D ^ 4 * K x ^ 2 :=
    floor_square_bound hσ hD (Nat.cast_nonneg N) (hfloor x)
  have hfi := integral_mono (integrable_const (σ ^ 2 * (N : ℝ) ^ 6)) (hiK.const_mul (D ^ 4)) hf
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul] at hfi
  have hk : 0 ≤ ∫ x, K x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg (K x))
  have hnonneg : 0 ≤ D ^ 4 * (∫ x, K x ^ 2 ∂μ) := mul_nonneg (by positivity) hk
  nlinarith

lemma inverse_weight_second_moment {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A : X → ℝ) (V : ℕ → X → ℝ)
    (D C : ℝ) (N : ℕ) (hN : 1 ≤ N) (hC : 1 ≤ C)
    (hmA : Measurable A) (hA : ∀ x, 0 ≤ A x) (hV : ∀ n x, 0 ≤ V n x)
    (hiV : ∀ n < N, Integrable (V n) μ)
    (hpot : ∀ x, HessianAdaptiveCubicInverseWeights.weightPolynomial N * A x ≤
      128 * D * Real.sqrt N + 256 * ∑ n ∈ Finset.range N, Real.sqrt (V n x))
    (hmove : (∫ x, ∑ n ∈ Finset.range N, V n x ∂μ) ≤ 8 * D ^ 2 * C) :
    Integrable (fun x => A x ^ 2) μ ∧
      (∫ x, A x ^ 2 ∂μ) * (N : ℝ) ^ 7 ≤ 1100 ^ 2 * D ^ 2 * C := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hiSum : Integrable (fun x => ∑ n ∈ Finset.range N, V n x) μ :=
    integrable_finsetSum _ (fun n hn => hiV n (Finset.mem_range.mp hn))
  have hp (x : X) : A x ^ 2 * (N : ℝ) ^ 7 ≤
      32768 * D ^ 2 + 131072 * ∑ n ∈ Finset.range N, V n x :=
    HessianAdaptiveCubicInverseWeights.inverse_square_of_potential (fun n => V n x)
      (fun n => hV n x) N hN (hA x) (hpot x)
  have hiBound := ((integrable_const (32768 * D ^ 2)).add (hiSum.const_mul 131072)).div_const ((N : ℝ) ^ 7)
  have hiA := HessianAdaptiveCubicNormalization.integrable_square_of_bound μ A _ hmA hiBound
    (fun x => (le_div_iff₀ (pow_pos hNp 7)).2 (hp x))
  refine ⟨hiA, ?_⟩
  have hi := integral_mono (hiA.mul_const ((N : ℝ) ^ 7))
    ((integrable_const (32768 * D ^ 2)).add (hiSum.const_mul 131072)) hp
  change (∫ x, A x ^ 2 * (N : ℝ) ^ 7 ∂μ) ≤
    (∫ x, 32768 * D ^ 2 + 131072 * ∑ n ∈ Finset.range N, V n x ∂μ) at hi
  rw [integral_mul_const, integral_add (f := fun _ => 32768 * D ^ 2)
    (g := fun x => 131072 * ∑ n ∈ Finset.range N, V n x)
    (integrable_const _) (hiSum.const_mul _), integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul] at hi
  have hDC := mul_le_mul_of_nonneg_left hC (sq_nonneg D)
  nlinarith

lemma accuracy_squared {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (gap E A : X → ℝ) (D K C : ℝ) (N : ℕ) (hK : 0 ≤ K)
    (hmg : Measurable gap) (hmE : Measurable E) (hmA : Measurable A)
    (hg : ∀ x, 0 ≤ gap x) (hE : ∀ x, 0 ≤ E x) (hA : ∀ x, 0 ≤ A x)
    (hiE : Integrable (fun x => E x ^ 2) μ) (hiA : Integrable (fun x => A x ^ 2) μ)
    (hbound : ∀ x, gap x ≤ E x * A x)
    (hEb : (∫ x, E x ^ 2 ∂μ) ≤ 36 * D ^ 4 * K)
    (hAb : (∫ x, A x ^ 2 ∂μ) * (N : ℝ) ^ 7 ≤ 1100 ^ 2 * D ^ 2 * C) :
    Integrable gap μ ∧ (∫ x, gap x ∂μ) ^ 2 * (N : ℝ) ^ 7 ≤ 6600 ^ 2 * D ^ 6 * K * C := by
  have hc := AdamHeavyTailedHistory.integral_abs_product_bound μ (C := 1) (by norm_num)
    hmg hmE hmA hE hA hiE hiA (fun x => by simpa only [abs_of_nonneg (hg x), one_mul] using hbound x)
  have hb : (∫ x, gap x ∂μ) ≤ Real.sqrt (∫ x, E x ^ 2 ∂μ) * Real.sqrt (∫ x, A x ^ 2 ∂μ) := by
    simpa only [abs_of_nonneg (hg _), one_mul] using hc.2
  refine ⟨hc.1, ?_⟩
  have hEn : 0 ≤ ∫ x, E x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg (E x))
  have hAn : 0 ≤ ∫ x, A x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg (A x))
  have hsq := mul_self_le_mul_self (integral_nonneg hg) hb
  have hEs := Real.sq_sqrt hEn
  have hAs := Real.sq_sqrt hAn
  have hsq' : (∫ x, gap x ∂μ) ^ 2 ≤ (∫ x, E x ^ 2 ∂μ) * (∫ x, A x ^ 2 ∂μ) := by
    rw [← sq, ← sq, mul_pow, hEs, hAs] at hsq
    exact hsq
  have hmul := mul_le_mul_of_nonneg_right hsq' (show 0 ≤ (N : ℝ) ^ 7 by positivity)
  have hp := mul_le_mul hEb hAb (mul_nonneg hAn (by positivity))
    (show 0 ≤ 36 * D ^ 4 * K by positivity)
  nlinarith only [hmul, hp]

open LongTails.Proofs.HessianAdaptiveCubicMeasurability
open LongTails.Proofs.HessianAdaptiveCubicStochasticBounds

lemma measurable_energy {X : Type*} [MeasurableSpace X] (p : Public)
    (s : X → State p.d) (f : Point p.d → ℝ) (xstar : Point p.d)
    (hs : MeasurableState p s) (hf : Continuous f) : Measurable (fun x => energy p f xstar (s x)) := by
  have hw := hs.weight
  have hp := hf.measurable.comp hs.point
  have hk := hs.scale
  have hz := hs.dual
  exact (hw.mul (hp.sub_const _)).add ((hk.div_const 2).mul ((hz.sub_const _).norm.pow_const 2))

lemma model_accuracy_squared {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hmin : IsMinOn f p.C xstar)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (N : ℕ) (hN : 1 ≤ N) (C : ℝ) (hC : 1 ≤ C)
    (hiK : Integrable (fun ξ => (roundState p g H ξ N).scale ^ 2) P)
    (hiM : Integrable (fun ξ => noiseSum p f xstar g H N ξ ^ 2) P)
    (hM : (∫ ξ, noiseSum p f xstar g H N ξ ^ 2 ∂P) ≤ p.σg ^ 2 * (N : ℝ) ^ 6)
    (hmove : (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) ≤ 8 * p.D ^ 2 * C) :
    Integrable (fun ξ => f (roundState p g H ξ N).point - f xstar) P ∧
      (∫ ξ, f (roundState p g H ξ N).point - f xstar ∂P) ^ 2 * (N : ℝ) ^ 7 ≤
        6600 ^ 2 * p.D ^ 6 * (∫ ξ, (roundState p g H ξ N).scale ^ 2 ∂P) * C := by
  let E := fun ξ => energy p f xstar (roundState p g H ξ N)
  let K := fun ξ => (roundState p g H ξ N).scale
  let A := fun ξ => (roundState p g H ξ N).weight⁻¹
  let V := fun n ξ => movement p (modelAt p g H ξ n)
  have hinv (n : ℕ) (ξ : ℕ → Ω) := roundState_invariant p g H ξ hD hρ hσ hx n
  have hm (n : ℕ) := measurable_roundState p hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) n
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hgrad x).continuousAt)
  have hmE : Measurable E := measurable_energy p _ f xstar (hm N) hfcont
  have hE (ξ : ℕ → Ω) : 0 ≤ E ξ := energy_nonneg p f xstar _ (hinv N ξ) hmin
  have hEi := energy_second_moment P E K (noiseSum p f xstar g H N) p.D p.σg N hD hσ hmE hE hiK hiM hM
    (fun ξ => by simpa only [Nat.cast_add, Nat.cast_one] using roundState_scale_floor p g H ξ hρ.le N)
    (fun ξ => model_energy_upper_bound p g H ξ hD hρ hσ hx xstar hxstar hdiam f hf hgrad hPSD N)
  have hmA : Measurable A := (hm N).weight.inv
  have hA (ξ : ℕ → Ω) : 0 ≤ A ξ := inv_nonneg.mpr (hinv N ξ).weight
  have hV (n : ℕ) (ξ : ℕ → Ω) : 0 ≤ V n ξ :=
    (movement_bounds p _ hD (modelAt_invariant p g H ξ hD hρ hσ hx n) hdiam).1
  have hiV (n : ℕ) (_hn : n < N) : Integrable (V n) P :=
    integrable_movement p P (fun ξ => modelAt p g H ξ n)
      (measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
        (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) n) hD
      (fun ξ => modelAt_invariant p g H ξ hD hρ hσ hx n) hdiam
  have hAi := inverse_weight_second_moment P A V p.D C N hN hC hmA hA hV hiV
    (fun ξ => HessianAdaptiveCubicInverseWeights.inverse_round_weight p g H ξ hD hρ hσ hx hdiam N hN) hmove
  have hgap (ξ : ℕ → Ω) : 0 ≤ f (roundState p g H ξ N).point - f xstar :=
    sub_nonneg.mpr (hmin (hinv N ξ).point)
  have hbound (ξ : ℕ → Ω) : f (roundState p g H ξ N).point - f xstar ≤ E ξ * A ξ := by
    have hw : 0 < (roundState p g H ξ N).weight := (hinv N ξ).weight_pos.resolve_right (by
      rw [roundState_iteration]
      omega)
    have hk := (hinv N ξ).scale
    change _ ≤ energy p f xstar (roundState p g H ξ N) * (roundState p g H ξ N).weight⁻¹
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hw).2
    unfold energy
    have hn : 0 ≤ (roundState p g H ξ N).scale / 2 * ‖(roundState p g H ξ N).dual - xstar‖ ^ 2 := by positivity
    nlinarith
  exact accuracy_squared P _ E A p.D (∫ ξ, K ξ ^ 2 ∂P) C N
    (integral_nonneg (fun ξ => sq_nonneg (K ξ)))
    ((hfcont.measurable.comp (hm N).point).sub_const _) hmE hmA hgap hE hA hEi.1 hAi.1 hbound hEi.2 hAi.2

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

lemma model_accuracy_with_log {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hmin : IsMinOn f p.C xstar)
    (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (σh : ℝ)
    (hgint : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgmean : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x)
    (hgi : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (hhi : ∀ x ∈ p.C, Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2) μ)
    (hhb : ∀ x ∈ p.C, (∫ ω, ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2 ∂μ) ≤ σh ^ 2)
    (N : ℕ) (hN : 1 ≤ N) :
    let κ0 := 2 * p.ρ + p.σg / p.D ^ 2
    let C := 1 + (∫ ξ, Real.log ((modelAt p g H ξ N).scale) - Real.log κ0 ∂P) +
      ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))
    Integrable (fun ξ => f (roundState p g H ξ N).point - f xstar) P ∧
      (∫ ξ, f (roundState p g H ξ N).point - f xstar ∂P) ^ 2 * (N : ℝ) ^ 7 ≤
        6600 ^ 2 * p.D ^ 6 * (∫ ξ, (modelAt p g H ξ N).scale ^ 2 ∂P) * C := by
  dsimp only
  let κ0 := 2 * p.ρ + p.σg / p.D ^ 2
  let K := fun ξ => (modelAt p g H ξ N).scale
  let L := ∫ ξ, Real.log (K ξ) - Real.log κ0 ∂P
  let HN := ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))
  have hκ0 : 0 < κ0 := by dsimp [κ0]; positivity
  have hKl (ξ : ℕ → Ω) : κ0 ≤ K ξ := round_scale_lower_bound p g H ξ hD hρ hσ hx N
  have hmK : Measurable K := (measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) N).scale
  have hiK : Integrable (fun ξ => K ξ ^ 2) P :=
    model_scale_square_integrable p μ P hIID ω0 hD hρ hσ hx hdiam f hdiff hLip
      g H hg hH hPSD σh hgi hgb hhi hhb N
  have hlog := integral_log_scale_bound P K κ0 hκ0 hmK hKl hiK
  have hL : 0 ≤ L := integral_nonneg (fun ξ => sub_nonneg.mpr (Real.log_le_log hκ0 (hKl ξ)))
  have hHN : 0 ≤ HN := Finset.sum_nonneg (fun n _ => by positivity)
  have hnoisei (n : ℕ) : Integrable (fun ξ => normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2)))) P := by
    have he := (model_query_square_moment p μ P hIID ω0 hD hρ hσ hx g H hg hH hPSD
      (fun x ω => g x ω - gradient f x) (measurable_gradient_error p f g hg hdiff)
      p.σg hgi hgb n).1
    exact model_normalized_noise_integrable p P hD hρ hσ hx xstar hxstar hdiam f hdiff
      g H hg hH hPSD n he
  have hnoiseb (n : ℕ) : (∫ ξ, normalizedNoise p f xstar (modelAt p g H ξ n)
      (g (queryPoint (modelAt p g H ξ n)) (ξ (3 * n + 2))) ∂P) ≤ p.D ^ 2 / (n + 1) :=
    model_normalized_drift p μ P hIID ω0 hD hρ hσ hx xstar hxstar hdiam f hdiff
      g H hg hH hPSD hgint hgmean hgi hgb n (hnoisei n)
  have hmov := model_expected_movement p P hD hρ hσ hx xstar hxstar hdiam f hf hgrad hmin
    g H hg hH hPSD N (fun n _ => hnoisei n) (fun n _ => hnoiseb n) hlog.1
  have hmom (n : ℕ) := model_roundNoise_second_moment p μ P hIID ω0 hD hρ hσ hx f hdiff
    xstar hxstar hdiam g H hg hH hPSD hgi hgb n
  have hM := noiseSum_second_moment p μ P hIID ω0 hD hρ hσ hx f hdiff xstar g H hg hH hPSD
    hgint hgmean (fun n => (hmom n).1) (fun n => (hmom n).2) N
  have hmove : (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) ≤
      8 * p.D ^ 2 * (1 + L + HN) := by
    have hm' : (∫ ξ, ∑ n ∈ Finset.range N, movement p (modelAt p g H ξ n) ∂P) ≤
        p.D ^ 2 + 8 * p.D ^ 2 * L + 2 * p.D ^ 2 * HN := hmov
    nlinarith [mul_nonneg (sq_nonneg p.D) hHN]
  exact model_accuracy_squared p P hD hρ hσ hx xstar hxstar hdiam f hf hgrad hmin
    g H hg hH hPSD N hN (1 + L + HN) (by linarith) hiK hM.1 hM.2 hmove

open LongTails.Proofs.HessianAdaptiveCubicRate

lemma model_rate_squared {Ω : Type*} [MeasurableSpace Ω]
    (p : Public) (μ : Measure Ω) (P : Measure (ℕ → Ω))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (hIID : IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (ω0 : Ω)
    (hD : 0 < p.D) (hρ : 0 < p.ρ) (hσ : 0 ≤ p.σg) (hx : p.x0 ∈ p.C)
    (hdiam : ∀ x ∈ p.C, ∀ y ∈ p.C, ‖x - y‖ ≤ p.D)
    (xstar : Point p.d) (hxstar : xstar ∈ p.C)
    (f : Point p.d → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (hmin : IsMinOn f p.C xstar)
    (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (g : Point p.d → Ω → Point p.d) (H : Point p.d → Ω → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable (Function.uncurry H))
    (hPSD : ∀ x ∈ p.C, ∀ ω, IsPSD (H x ω)) (σh : ℝ)
    (hgint : ∀ x ∈ p.C, Integrable (g x) μ)
    (hgmean : ∀ x ∈ p.C, ∫ ω, g x ω ∂μ = gradient f x)
    (hgi : ∀ x ∈ p.C, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) μ)
    (hgb : ∀ x ∈ p.C, (∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂μ) ≤ p.σg ^ 2)
    (hhi : ∀ x ∈ p.C, Integrable (fun ω => ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2) μ)
    (hhb : ∀ x ∈ p.C, (∫ ω, ‖H x ω - fderiv ℝ (gradient f) x‖ ^ 2 ∂μ) ≤ σh ^ 2)
    (hσh : 0 ≤ σh) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (fun ξ => f (roundState p g H ξ N).point - f xstar) P ∧
      (∫ ξ, f (roundState p g H ξ N).point - f xstar ∂P) ^ 2 ≤
        4000000000000 * (1 + Real.log ((1 + σh / (p.ρ * p.D)) * N)) ^ 2 *
          (p.σg ^ 2 * p.D ^ 2 / N + σh ^ 2 * p.D ^ 4 / (N : ℝ) ^ 4 +
            p.ρ ^ 2 * p.D ^ 6 / (N : ℝ) ^ 7) := by
  let κ0 := 2 * p.ρ + p.σg / p.D ^ 2
  let k := fun ξ => (modelAt p g H ξ N).scale
  let K := ∫ ξ, k ξ ^ 2 ∂P
  let L := ∫ ξ, Real.log (k ξ) - Real.log κ0 ∂P
  let HN := ∑ n ∈ Finset.range N, (1 / ((n : ℝ) + 1))
  let r := σh / (p.ρ * p.D)
  let J := 1 + Real.log ((1 + r) * N)
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hNp : 0 < (N : ℝ) := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hJ : 1 ≤ J := by
    dsimp [J]
    apply le_add_of_nonneg_right
    apply Real.log_nonneg
    nlinarith
  have hJlog : 1 + Real.log N ≤ J := by
    dsimp [J]
    apply add_le_add_right
    apply Real.log_le_log hNp
    nlinarith
  have hκ0 : 0 < κ0 := by dsimp [κ0]; positivity
  have hKl (ξ : ℕ → Ω) : κ0 ≤ k ξ := round_scale_lower_bound p g H ξ hD hρ hσ hx N
  have hmK : Measurable k := (measurable_modelAt p hD hρ hσ hx g H hg hH hPSD
    (fun k (ξ : ℕ → Ω) => ξ k) (fun k => measurable_pi_apply k) N).scale
  have hiK : Integrable (fun ξ => k ξ ^ 2) P :=
    model_scale_square_integrable p μ P hIID ω0 hD hρ hσ hx hdiam f hdiff hLip
      g H hg hH hPSD σh hgi hgb hhi hhb N
  have hlog := integral_log_scale_bound P k κ0 hκ0 hmK hKl hiK
  have hKpos : 0 < K := by
    have hb := integral_mono (integrable_const (κ0 ^ 2)) hiK
      (fun ξ => pow_le_pow_left₀ hκ0.le (hKl ξ) 2)
    simp only [integral_const, probReal_univ, one_smul] at hb
    exact lt_of_lt_of_le (sq_pos_of_pos hκ0) hb
  have hclosed := model_scale_closed_bound p μ P hIID ω0 hD hρ hσ hx hdiam xstar hxstar
    f hf hgrad hmin hdiff hLip g H hg hH hPSD σh hgint hgmean hgi hgb hhi hhb N
  have hrat := noise_scale_ratios p.ρ p.σg σh p.D hρ hσ hD
  have hraw : K ≤ κ0 ^ 2 * (36 + 20 * HN) +
      18 * (p.σg ^ 2 / p.D ^ 4) * ((N : ℝ) + 1) ^ 6 +
      8 * (σh ^ 2 / p.D ^ 2) * (N : ℝ) ^ 3 := by
    dsimp [K, k, κ0, HN]
    convert hclosed using 1
    ring
  have hnorm := normalized_scale_ratio κ0 K (p.σg ^ 2 / p.D ^ 4)
    (σh ^ 2 / p.D ^ 2) r HN N hκ0 hNp.le hrat.1 hrat.2 hraw
  have hpoly := normalized_scale_polynomial (K / κ0 ^ 2) HN N r hNr hr (harmonic_le_count N) hnorm
  have hC : 1 + L + HN ≤ 9 * J := normalization_log_factor (K / κ0 ^ 2) L HN N r
    (div_pos hKpos (sq_pos_of_pos hκ0)) hNr hr (harmonic_bound N) hlog.2 hpoly
  have hHNnonneg : 0 ≤ HN := Finset.sum_nonneg (fun n _ => by positivity)
  have hkbound := scale_rate_bound p.ρ p.σg σh p.D K HN N hD hNr hHNnonneg
    (harmonic_bound N) (harmonic_le_count N) hclosed
  have hrescale := scale_rate_rescale p.D N K p.ρ p.σg σh J hD hNp hJlog hkbound
  have hacc := model_accuracy_with_log p μ P hIID ω0 hD hρ hσ hx hdiam xstar hxstar
    f hf hgrad hmin hdiff hLip g H hg hH hPSD σh hgint hgmean hgi hgb hhi hhb N hN
  refine ⟨hacc.1, ?_⟩
  exact squared_rate_algebra _ p.D K (1 + L + HN) J N
    (p.σg ^ 2 * p.D ^ 2 / N) (σh ^ 2 * p.D ^ 4 / (N : ℝ) ^ 4)
    (p.ρ ^ 2 * p.D ^ 6 / (N : ℝ) ^ 7) hD hNp hKpos.le hJ
    (by positivity) (by positivity) (by positivity) hC hrescale hacc.2

end LongTails.Proofs.HessianAdaptiveCubicAccuracy
