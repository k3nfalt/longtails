import LongTails.Proofs.MinimaxLmoDescent
import LongTails.Proofs.MinimaxLmoMartingale
import LongTails.Proofs.LmoRecursions

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO constantMomentum)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax clip)
open OracleTemplate.NormBallLMO

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)} {R ρ : ℝ}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}
  {lmo : Space d₁ → Space d₁}

lemma norm_le_dual (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (w : Space d₁) :
    ‖w‖ ≤ (∑ i, N (EuclideanSpace.single i (1 : ℝ)) + 1) * dualNorm N w := by
  set S := ∑ i, N (EuclideanSpace.single i (1 : ℝ)) + 1
  have hS : 0 < S := by
    have : 0 ≤ ∑ i, N (EuclideanSpace.single i (1 : ℝ)) := Finset.sum_nonneg fun i _ => apply_nonneg N _
    positivity
  by_cases hw : w = 0
  · subst hw; simp only [norm_zero]; exact mul_nonneg hS.le (dualNorm_nonneg hR 0)
  · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set v := (S * ‖w‖)⁻¹ • w
    have hNv : N v ≤ 1 := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have h := seminorm_le_norm N w
      rw [inv_mul_le_iff₀ (by positivity)]
      nlinarith
    have hin := inner_le_dualNorm hR w hNv
    rw [inner_smul_right, real_inner_self_eq_norm_sq] at hin
    rw [inv_mul_le_iff₀ (by positivity)] at hin
    nlinarith

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p)
include H

lemma gx_continuous (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hL₀ : 0 ≤ L₀)
    (hL₁ : 0 ≤ L₁) : Continuous (fun z : Space d₁ × Space d₂ => gx z.1 z.2) := by
  rw [Metric.continuous_iff]
  intro z ε hε
  set S := ∑ i, N (EuclideanSpace.single i (1 : ℝ)) + 1
  have hS : 0 < S := by
    have : 0 ≤ ∑ i, N (EuclideanSpace.single i (1 : ℝ)) := Finset.sum_nonneg fun i _ => apply_nonneg N _
    positivity
  set M := L₀ + L₁ * dualNorm N (gx z.1 z.2)
  have hM : 0 ≤ M := by have := dualNorm_nonneg hR (gx z.1 z.2); positivity
  set r := min (1 / (2 * (L₁ + 1) * S)) (ε / (2 * (S * (M + 1) * S)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  refine ⟨r, hr, fun z' hz' => ?_⟩
  rw [dist_eq_norm] at hz' ⊢
  have h1 : ‖z'.1 - z.1‖ < r := lt_of_le_of_lt (norm_fst_le (z' - z)) hz'
  have h2 : ‖z'.2 - z.2‖ < r := lt_of_le_of_lt (norm_snd_le (z' - z)) hz'
  have hsum0 : 0 ≤ ∑ i, N (EuclideanSpace.single i (1 : ℝ)) :=
    Finset.sum_nonneg fun i _ => apply_nonneg N _
  have hN1 : N (z.1 - z'.1) ≤ (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * r := by
    rw [← map_neg_eq_map, neg_sub]
    exact (seminorm_le_norm N _).trans (mul_le_mul_of_nonneg_left h1.le hsum0)
  have hdist : N (z.1 - z'.1) + ‖z.2 - z'.2‖ ≤ S * r := by
    rw [norm_sub_rev] at h2
    have : S * r = (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * r + r := by simp only [S]; ring
    linarith
  have hSr1 : S * r ≤ 1 / (2 * (L₁ + 1)) := by
    have := min_le_left (1 / (2 * (L₁ + 1) * S)) (ε / (2 * (S * (M + 1) * S)))
    calc S * r ≤ S * (1 / (2 * (L₁ + 1) * S)) := mul_le_mul_of_nonneg_left this hS.le
      _ = 1 / (2 * (L₁ + 1)) := by field_simp
  have hloc : L₁ * (N (z.1 - z'.1) + ‖z.2 - z'.2‖) ≤ 1 := by
    have : L₁ * (N (z.1 - z'.1) + ‖z.2 - z'.2‖) ≤ L₁ * (1 / (2 * (L₁ + 1))) :=
      mul_le_mul_of_nonneg_left (hdist.trans hSr1) hL₁
    have h3 : L₁ * (1 / (2 * (L₁ + 1))) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hsm := H.smooth_x z.1 z.2 z'.1 z'.2 hloc
  have hnd := norm_le_dual hR (gx z.1 z.2 - gx z'.1 z'.2)
  rw [norm_sub_rev] at hnd
  have hSr2 : S * r ≤ ε / (2 * (S * (M + 1))) := by
    have := min_le_right (1 / (2 * (L₁ + 1) * S)) (ε / (2 * (S * (M + 1) * S)))
    calc S * r ≤ S * (ε / (2 * (S * (M + 1) * S))) := mul_le_mul_of_nonneg_left this hS.le
      _ = ε / (2 * (S * (M + 1))) := by field_simp
  calc ‖gx z'.1 z'.2 - gx z.1 z.2‖ ≤ S * dualNorm N (gx z.1 z.2 - gx z'.1 z'.2) := hnd
    _ ≤ S * (M * (S * r)) := by
        refine mul_le_mul_of_nonneg_left (hsm.trans (mul_le_mul_of_nonneg_left hdist hM)) hS.le
    _ ≤ S * ((M + 1) * (ε / (2 * (S * (M + 1))))) := by
        refine mul_le_mul_of_nonneg_left ?_ hS.le
        exact mul_le_mul (by linarith) hSr2 (by positivity) (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

omit H in
lemma wt_sq_sum_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), wt a k j ^ 2 ≤ ((1 - a) ^ k) ^ 2 + a := by
  have hq0 : 0 ≤ 1 - a := by linarith
  have hq1 : 1 - a < 1 := by linarith
  rw [Finset.sum_range_succ']
  have h0 : wt a k 0 ^ 2 = ((1 - a) ^ k) ^ 2 := by simp [wt]
  rw [h0]
  have hsum : ∑ i ∈ Finset.range k, wt a k (i + 1) ^ 2 =
      ∑ i ∈ Finset.range k, a ^ 2 * ((1 - a) ^ (k - 1 - i)) ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    simp only [wt, Nat.add_one_ne_zero, ↓reduceIte, mul_pow]
    rw [show k - (i + 1) = k - 1 - i by omega]
  rw [hsum, Finset.sum_range_reflect (fun m => a ^ 2 * ((1 - a) ^ m) ^ 2) k]
  have hb : ∑ m ∈ Finset.range k, a ^ 2 * ((1 - a) ^ m) ^ 2 ≤ a := by
    calc ∑ m ∈ Finset.range k, a ^ 2 * ((1 - a) ^ m) ^ 2
        ≤ ∑ m ∈ Finset.range k, a ^ 2 * (1 - a) ^ m := by
          gcongr with m
          rw [sq]
          exact mul_le_of_le_one_left (pow_nonneg hq0 m) (pow_le_one₀ hq0 hq1.le)
      _ = a ^ 2 * ∑ m ∈ Finset.range k, (1 - a) ^ m := by rw [Finset.mul_sum]
      _ ≤ a ^ 2 * (1 / (1 - (1 - a))) := by gcongr; exact geom_sum_le hq0 hq1 k
      _ = a := by rw [sub_sub_cancel]; field_simp
  linarith

theorem noise_bound [IsProbabilityMeasure p] (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hlmo : Measurable lmo) (hσx : 0 ≤ σx) {γ a β c : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (k : ℕ) :
    Integrable (fun ξ => ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖) (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ‖noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k‖ ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        Real.sqrt 2 * σx * ((1 - a) ^ k + Real.sqrt a) := by
  have hgc := gx_continuous H hR hL₀ hL₁
  have hpath := measurable_gpath lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c) x₁ y₁ ox oy
    hlmo H.measurable_x H.measurable_y
  let S : ℕ → (ℕ → Ω) → Space d₁ × Space d₂ := fun j ξ =>
    ((cpath lmo γ a β c x₁ y₁ ox oy ξ j).1, (cpath lmo γ a β c x₁ y₁ ox oy ξ j).2.1)
  have hS : ∀ j, Measurable (S j) := fun j => (hpath j).fst.prodMk (hpath j).snd.fst
  have hdep : ∀ j (ξ ξ' : ℕ → Ω), (∀ i, i < j → ξ i = ξ' i) → S j ξ = S j ξ' := by
    intro j ξ ξ' h
    simp only [S, cpath, gpath_congr lmo (fun _ => γ) (constantMomentum a) (fun _ => β) (fun _ => c)
      x₁ y₁ ox oy j h]
  let Wf : ℕ → Space d₁ × Space d₂ → Ω → Space d₁ := fun j z ω => wt a k j • (ox z.1 z.2 ω - gx z.1 z.2)
  have hW : ∀ j, Measurable (Function.uncurry (Wf j)) := fun j => by
    change Measurable fun w : (Space d₁ × Space d₂) × Ω => wt a k j • (ox w.1.1 w.1.2 w.2 - gx w.1.1 w.1.2)
    have h1 : Measurable fun w : (Space d₁ × Space d₂) × Ω => ox w.1.1 w.1.2 w.2 - gx w.1.1 w.1.2 :=
      H.measurable_x.sub (hgc.measurable.comp measurable_fst)
    exact h1.const_smul (wt a k j)
  have hWi : ∀ j z, Integrable (Wf j z) p := fun j z => by
    show Integrable (fun ω => wt a k j • (ox z.1 z.2 ω - gx z.1 z.2)) p
    exact Integrable.smul (wt a k j) ((H.integrable_x z.1 z.2).sub (integrable_const _))
  have hW0 : ∀ j z, ∫ ω, Wf j z ω ∂p = 0 := by
    intro j z
    simp only [Wf, integral_smul, integral_sub (H.integrable_x z.1 z.2) (integrable_const _),
      H.unbiased_x z.1 z.2]
    simp
  have hW2 : ∀ j z, Integrable (fun ω => ‖Wf j z ω‖ ^ 2) p := by
    intro j z
    simp only [Wf, norm_smul, mul_pow]
    exact (H.variance_x_integrable z.1 z.2).const_mul _
  let v : ℕ → Space d₁ × Space d₂ → ℝ := fun j _ => wt a k j ^ 2 * σx ^ 2
  have hvle : ∀ j z, ∫ ω, ‖Wf j z ω‖ ^ 2 ∂p ≤ v j z := by
    intro j z
    simp only [Wf, v, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (H.variance_x z.1 z.2) (sq_nonneg _)
  obtain ⟨hi, hle⟩ := mm_martingale_first_moment p S hS hdep Wf hW hWi hW0 hW2 v
    (fun j => measurable_const) (fun j z => by positivity) hvle (fun j => integrable_const _) (k + 1)
  have heq : ∀ ξ, ∑ j ∈ Finset.range (k + 1), Wf j (S j ξ) (ξ j) =
      noiseSum lmo γ a β c x₁ y₁ gx ox oy ξ k := fun ξ => rfl
  simp only [heq] at hi hle
  refine ⟨hi, hle.trans ?_⟩
  simp only [v, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [← Finset.sum_mul]
  have hw := wt_sq_sum_le ha ha1 k
  have hsq : Real.sqrt ((∑ j ∈ Finset.range (k + 1), wt a k j ^ 2) * σx ^ 2) ≤
      σx * ((1 - a) ^ k + Real.sqrt a) := by
    rw [Real.sqrt_le_left (by have := pow_nonneg (by linarith : (0:ℝ) ≤ 1 - a) k; positivity)]
    have hsa := Real.sq_sqrt ha.le
    have hpk := pow_nonneg (by linarith : (0:ℝ) ≤ 1 - a) k
    have hs0 := Real.sqrt_nonneg a
    nlinarith [mul_le_mul_of_nonneg_right hw (sq_nonneg σx), mul_nonneg hpk hs0]
  have := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg 2)
  linarith

end OracleTemplate.MinimaxLmo
