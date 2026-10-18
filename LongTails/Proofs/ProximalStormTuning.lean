import LongTails.Proofs.ProximalStormWindow
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

noncomputable def pLam (Lbar Γh : ℝ) : ℝ := Γh / Lbar

noncomputable def pEta (Lbar Γh : ℝ) : ℝ := 1 / (60 * Γh * Lbar)

noncomputable def pA (Γh : ℝ) : ℝ := 1 / (400 * Γh ^ 2)

noncomputable def pC (Γh : ℝ) : ℝ := 1 / (800 * Γh ^ 2)

noncomputable def pW (Γh : ℝ) : ℕ := ⌈800 * Γh ^ 2⌉₊

noncomputable def pT0 (Γh : ℝ) : ℕ := ⌈800 * Γh ^ 2 * (5 + 4 * Real.log Γh)⌉₊

lemma tune_inner {Lbar Γh : ℝ} (hL : 0 < Lbar) (hΓ : 1 ≤ Γh) :
    InnerTune Lbar (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) Γh := by
  have hΓ0 : 0 < Γh := by linarith
  refine ⟨by unfold pLam; positivity, by unfold pEta; positivity, by unfold pA; positivity,
    ?_, ?_, ?_, ?_, ?_⟩
  · unfold pA; rw [div_le_one (by positivity)]; nlinarith
  · unfold pEta pLam
    rw [show Lbar + 1 / (Γh / Lbar) = Lbar * (1 + 1 / Γh) by field_simp]
    rw [show 1 / (60 * Γh * Lbar) * (Lbar * (1 + 1 / Γh)) = (1 + 1 / Γh) / (60 * Γh) by
      field_simp]
    rw [div_le_iff₀ (by positivity)]
    have : 1 / Γh ≤ 1 := by rw [div_le_one hΓ0]; exact hΓ
    nlinarith
  · unfold pEta pA
    rw [show 8 * Lbar ^ 2 * (1 / (60 * Γh * Lbar)) ^ 2 = 8 / (3600 * Γh ^ 2) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg Γh]
  · unfold pLam; rw [mul_div_cancel₀ _ hL.ne']
  · unfold pA; field_simp; norm_num

lemma one_sub_pow_le_exp {c : ℝ} (hc1 : c ≤ 1) (n : ℕ) :
    (1 - c) ^ n ≤ Real.exp (-(c * n)) := by
  have h := Real.add_one_le_exp (-c)
  have h1 : (1 - c) ^ n ≤ Real.exp (-c) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith) n
  rw [← Real.exp_nat_mul] at h1
  convert h1 using 2; ring

lemma exp_five_ge : (143 : ℝ) ≤ Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h5]
  have : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  calc (143 : ℝ) ≤ 2.7 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) this 5

lemma transient_le {Γh : ℝ} (hΓ : 1 ≤ Γh) :
    (1 - pC Γh) ^ pT0 Γh ≤ 1 / (143 * Γh ^ 4) := by
  have hΓ0 : 0 < Γh := by linarith
  have hc0 : 0 ≤ pC Γh := by unfold pC; positivity
  have hc1 : pC Γh ≤ 1 := by unfold pC; rw [div_le_one (by positivity)]; nlinarith
  refine (one_sub_pow_le_exp hc1 _).trans ?_
  have hlog : 0 ≤ Real.log Γh := Real.log_nonneg hΓ
  have hT : 5 + 4 * Real.log Γh ≤ pC Γh * pT0 Γh := by
    have h := Nat.le_ceil (800 * Γh ^ 2 * (5 + 4 * Real.log Γh))
    unfold pC pT0
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  have he : Real.exp (-(pC Γh * pT0 Γh)) ≤ Real.exp (-(5 + 4 * Real.log Γh)) :=
    Real.exp_le_exp.mpr (by linarith)
  have heq : Real.exp (-(5 + 4 * Real.log Γh)) = (Real.exp 5)⁻¹ * (Γh ^ 4)⁻¹ := by
    rw [show -(5 + 4 * Real.log Γh) = -5 + -(Real.log (Γh ^ 4)) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_add, Real.exp_neg, Real.exp_neg,
      Real.exp_log (by positivity)]
  refine he.trans (le_of_eq_of_le heq ?_)
  rw [one_div, mul_inv]
  gcongr
  exact exp_five_ge

lemma inner_const {L Γ Γh : ℝ} (hL : 0 < L) (hΓ : 1 ≤ Γh) (hΓ0 : 0 ≤ Γ) (hΓΓ : Γ ≤ Γh)
    {W : ℕ} (hW : 800 * Γh ^ 2 ≤ (W : ℝ)) :
    4 * pLam L Γh ^ 2 / pEta L Γh * ((1 - pC Γh) ^ pT0 Γh * ((L + 1 / pLam L Γh) +
        pEta L Γh / pA Γh * (Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2)) +
      1 / pC Γh * (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2) +
      (W : ℝ) * (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) ≤ (W : ℝ) / 6 := by
  have hΓh0 : 0 < Γh := by linarith
  have htr := transient_le hΓ
  have htr0 : 0 ≤ (1 - pC Γh) ^ pT0 Γh := by
    apply pow_nonneg; unfold pC; rw [sub_nonneg, div_le_one (by positivity)]; nlinarith
  have h1 : L + 1 / pLam L Γh ≤ 2 * L := by
    unfold pLam; rw [one_div_div]
    have : L / Γh ≤ L := div_le_self hL.le hΓ
    linarith
  have h1' : 0 ≤ L + 1 / pLam L Γh := by unfold pLam; positivity
  have hea : pEta L Γh / pA Γh = 20 * Γh / (3 * L) := by
    unfold pEta pA; field_simp; ring
  have hk : 4 * pLam L Γh ^ 2 / pEta L Γh = 240 * Γh ^ 3 / L := by
    unfold pLam pEta; field_simp; ring
  have hkk : 4 * pLam L Γh ^ 2 / pEta L Γh * (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2) =
      16 * Γ ^ 2 / (400 * Γh ^ 2) := by
    unfold pLam pEta pA; field_simp; ring
  have hC0 : (L + 1 / pLam L Γh) + pEta L Γh / pA Γh * (Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2) ≤
      29 * Γh ^ 3 * L := by
    rw [hea]
    have hsq : (L + 1 / pLam L Γh) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
    have hΓ2 : Γ ^ 2 ≤ Γh ^ 2 := pow_le_pow_left₀ hΓ0 hΓΓ 2
    have hprod : Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2 ≤ Γh ^ 2 * (4 * L ^ 2) :=
      mul_le_mul hΓ2 hsq (sq_nonneg _) (sq_nonneg _)
    have h20 : 0 ≤ 20 * Γh / (3 * L) := by positivity
    have h3 : 20 * Γh / (3 * L) * (Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2) ≤
        20 * Γh / (3 * L) * (Γh ^ 2 * (4 * L ^ 2)) := mul_le_mul_of_nonneg_left hprod h20
    have h4 : 20 * Γh / (3 * L) * (Γh ^ 2 * (4 * L ^ 2)) = 80 / 3 * Γh ^ 3 * L := by
      field_simp; ring
    have h5 : 2 * L ≤ 2 * Γh ^ 3 * L := by
      have : 1 ≤ Γh ^ 3 := one_le_pow₀ hΓ
      nlinarith
    nlinarith
  have hpart1 : 4 * pLam L Γh ^ 2 / pEta L Γh * ((1 - pC Γh) ^ pT0 Γh *
      ((L + 1 / pLam L Γh) + pEta L Γh / pA Γh * (Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2))) ≤
      240 * 29 / 143 * Γh ^ 2 := by
    rw [hk]
    have hA : 0 ≤ 240 * Γh ^ 3 / L := by positivity
    calc 240 * Γh ^ 3 / L * ((1 - pC Γh) ^ pT0 Γh *
          ((L + 1 / pLam L Γh) + pEta L Γh / pA Γh * (Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2)))
        ≤ 240 * Γh ^ 3 / L * (1 / (143 * Γh ^ 4) * (29 * Γh ^ 3 * L)) := by
          apply mul_le_mul_of_nonneg_left _ hA
          have hnn : 0 ≤ (L + 1 / pLam L Γh) + pEta L Γh / pA Γh *
              (Γ ^ 2 * (L + 1 / pLam L Γh) ^ 2) := by
            rw [hea]; positivity
          exact mul_le_mul htr hC0 hnn (by positivity)
      _ = 240 * 29 / 143 * Γh ^ 2 := by field_simp
  have hpart2 : 4 * pLam L Γh ^ 2 / pEta L Γh * (1 / pC Γh *
      (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) ≤ 32 * Γh ^ 2 := by
    rw [show 4 * pLam L Γh ^ 2 / pEta L Γh * (1 / pC Γh *
      (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) = 1 / pC Γh *
      (4 * pLam L Γh ^ 2 / pEta L Γh * (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) by ring,
      hkk]
    unfold pC
    rw [show 1 / (1 / (800 * Γh ^ 2)) * (16 * Γ ^ 2 / (400 * Γh ^ 2)) = 32 * Γ ^ 2 by
      field_simp; ring]
    nlinarith [pow_le_pow_left₀ hΓ0 hΓΓ 2]
  have hpart3 : 4 * pLam L Γh ^ 2 / pEta L Γh * ((W : ℝ) *
      (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) ≤ (W : ℝ) / 25 := by
    rw [show 4 * pLam L Γh ^ 2 / pEta L Γh * ((W : ℝ) *
      (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) = (W : ℝ) *
      (4 * pLam L Γh ^ 2 / pEta L Γh * (4 * pEta L Γh * pA Γh * Γ ^ 2 / pLam L Γh ^ 2)) by ring,
      hkk]
    have : 16 * Γ ^ 2 / (400 * Γh ^ 2) ≤ 1 / 25 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_le_pow_left₀ hΓ0 hΓΓ 2]
    have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg _
    nlinarith
  rw [mul_add, mul_add]
  nlinarith

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma lintegral_ofReal_const_mul' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : α → ℝ} (hu : Measurable u) {C : ℝ} (hC : 0 ≤ C) (w : α → ℝ)
    (hwm : Measurable w) :
    ∫⁻ x, ENNReal.ofReal (w x * (C * u x)) ∂μ =
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (w x * u x) ∂μ := by
  have hm : Measurable fun x => ENNReal.ofReal (w x * u x) :=
    ENNReal.measurable_ofReal.comp (hwm.mul hu)
  rw [← lintegral_const_mul _ hm]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul hC]
  congr 1; ring

lemma Hyp.inner_relative (H : Hyp p f g Lbar Γ xstar) {Γh : ℝ} (hΓ : 1 ≤ Γh) (hΓΓ : Γ ≤ Γh)
    {W : ℕ} (hW : 800 * Γh ^ 2 ≤ (W : ℝ))
    {X : (ℕ → Ω) → E} (hX : Measurable X) {n0 : ℕ}
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n0 → ξ i = ξ' i) → X ξ = X ξ')
    (w : E → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) :
    ∑ j ∈ Finset.range (W), ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (pLam Lbar Γh ^ 2 *
        ‖phiGrad f (pLam Lbar Γh) (X ξ) (innerRun g (pLam Lbar Γh) (pEta Lbar Γh) (pA Γh) (X ξ) ξ n0
          (pT0 Γh + j)).1‖ ^ 2)) ∂P ≤
      ENNReal.ofReal ((W : ℝ) / 6) *
        ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * ‖X ξ - prox f (pLam Lbar Γh) (X ξ)‖ ^ 2) ∂P := by
  have hL := H.Lbar_pos
  have hΓh0 : 0 < Γh := by linarith
  set lam := pLam Lbar Γh
  set eta := pEta Lbar Γh
  set a := pA Γh
  set c := pC Γh
  have T := tune_inner hL hΓ
  have hc0 : 0 < c := by simp only [c, pC]; positivity
  have hc1 : c * lam ≤ eta / 2 := by
    simp only [c, lam, eta, pC, pLam, pEta]
    rw [show 1 / (800 * Γh ^ 2) * (Γh / Lbar) = 1 / (800 * Γh * Lbar) by field_simp,
      show 1 / (60 * Γh * Lbar) / 2 = 1 / (120 * Γh * Lbar) by field_simp; ring]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hc2 : c ≤ a / 2 := by
    simp only [c, a, pC, pA]
    rw [show 1 / (400 * Γh ^ 2) / 2 = 1 / (800 * Γh ^ 2) by field_simp; ring]
  have hc : c ≤ 1 := by
    simp only [c, pC]; rw [div_le_one (by positivity)]; nlinarith
  have hwin := H.inner_window T hX hdep w hw hw0 hc0 hc1 hc2 hc (pT0 Γh) (W)
  have hD : Measurable fun ξ => ‖X ξ - prox f lam (X ξ)‖ ^ 2 :=
    (H.dist2_continuous T.lam_pos).measurable.comp hX
  have hwX : Measurable fun ξ => w (X ξ) := hw.comp hX
  have hwX0 : ∀ ξ, 0 ≤ w (X ξ) := fun ξ => hw0 _
  set E0 := ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * ‖X ξ - prox f lam (X ξ)‖ ^ 2) ∂P
  set C0 := (Lbar + 1 / lam) + eta / a * (Γ ^ 2 * (Lbar + 1 / lam) ^ 2)
  set kK := 4 * eta * a * Γ ^ 2 / lam ^ 2
  have hC0 : 0 ≤ C0 := by
    have : 0 < lam := T.lam_pos
    have : 0 < a := T.a_pos
    have : 0 ≤ eta := T.eta_nn
    positivity
  have hkK : 0 ≤ kK := by
    have : 0 < a := T.a_pos
    have : 0 ≤ eta := T.eta_nn
    positivity
  have e1 : ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (C0 * ‖X ξ - prox f lam (X ξ)‖ ^ 2)) ∂P =
      ENNReal.ofReal C0 * E0 := lintegral_ofReal_const_mul' hD hC0 _ hwX
  have e2 : ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (4 * eta * a * Γ ^ 2 *
      ‖X ξ - prox f lam (X ξ)‖ ^ 2 / lam ^ 2)) ∂P = ENNReal.ofReal kK * E0 := by
    rw [← lintegral_ofReal_const_mul' hD hkK _ hwX]
    refine lintegral_congr fun ξ => ?_
    congr 1; simp only [kK]; ring
  have hG : Measurable fun ξ => ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0
      (pT0 Γh + 0)).1‖ ^ 2 := by
    exact ((H.phiGrad_continuous lam).measurable.comp
      (hX.prodMk (measurable_innerRun H.meas lam eta a hX n0 _).fst)).norm.pow_const 2
  have e3 : ∀ j, ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (lam ^ 2 *
      ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 (pT0 Γh + j)).1‖ ^ 2)) ∂P =
      ENNReal.ofReal (4 * lam ^ 2 / eta) * ∫⁻ ξ, ENNReal.ofReal (w (X ξ) * (eta / 4 *
        ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 (pT0 Γh + j)).1‖ ^ 2)) ∂P := by
    intro j
    have hGj : Measurable fun ξ => ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0
        (pT0 Γh + j)).1‖ ^ 2 :=
      ((H.phiGrad_continuous lam).measurable.comp
        (hX.prodMk (measurable_innerRun H.meas lam eta a hX n0 _).fst)).norm.pow_const 2
    have heta : 0 < eta := by simp only [eta, pEta]; positivity
    rw [lintegral_ofReal_const_mul' hGj (by positivity : (0 : ℝ) ≤ eta / 4) _ hwX,
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      lintegral_ofReal_const_mul' hGj (by positivity : (0 : ℝ) ≤ lam ^ 2) _ hwX]
    congr 2
    field_simp
  clear hG
  simp_rw [e3]
  rw [← Finset.mul_sum]
  rw [e1, e2] at hwin
  have hpow : (1 - ENNReal.ofReal c) ^ pT0 Γh = ENNReal.ofReal ((1 - c) ^ pT0 Γh) := by
    rw [ENNReal.ofReal_pow (by linarith), ENNReal.ofReal_sub _ hc0.le, ENNReal.ofReal_one]
  have hinv : (ENNReal.ofReal c)⁻¹ = ENNReal.ofReal (1 / c) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hc0]
  have hnat : (W : ℝ≥0∞) = ENNReal.ofReal (W : ℝ) := by
    rw [ENNReal.ofReal_natCast]
  rw [hpow, hinv, hnat] at hwin
  calc ENNReal.ofReal (4 * lam ^ 2 / eta) * ∑ j ∈ Finset.range (W), ∫⁻ ξ,
        ENNReal.ofReal (w (X ξ) * (eta / 4 *
          ‖phiGrad f lam (X ξ) (innerRun g lam eta a (X ξ) ξ n0 (pT0 Γh + j)).1‖ ^ 2)) ∂P
      ≤ ENNReal.ofReal (4 * lam ^ 2 / eta) * (ENNReal.ofReal ((1 - c) ^ pT0 Γh) *
          (ENNReal.ofReal C0 * E0) + ENNReal.ofReal (1 / c) * (ENNReal.ofReal kK * E0) +
          ENNReal.ofReal (W : ℝ) * (ENNReal.ofReal kK * E0)) := by gcongr
    _ = ENNReal.ofReal (4 * lam ^ 2 / eta * ((1 - c) ^ pT0 Γh * C0 + 1 / c * kK +
          (W : ℝ) * kK)) * E0 := by
        have hp : 0 ≤ (1 - c) ^ pT0 Γh := pow_nonneg (by linarith) _
        have hq : 0 ≤ 4 * lam ^ 2 / eta := by
          have : 0 < eta := by simp only [eta, pEta]; positivity
          positivity
        have hc' : 0 ≤ 1 / c := by positivity
        have hW' : (0 : ℝ) ≤ W := Nat.cast_nonneg _
        have t1 : 0 ≤ (1 - c) ^ pT0 Γh * C0 := mul_nonneg hp hC0
        have t2 : 0 ≤ 1 / c * kK := mul_nonneg hc' hkK
        have t3 : 0 ≤ (W : ℝ) * kK := mul_nonneg hW' hkK
        have hsum : ENNReal.ofReal ((1 - c) ^ pT0 Γh * C0 + 1 / c * kK + (W : ℝ) * kK) =
            ENNReal.ofReal ((1 - c) ^ pT0 Γh) * ENNReal.ofReal C0 +
              ENNReal.ofReal (1 / c) * ENNReal.ofReal kK +
              ENNReal.ofReal (W : ℝ) * ENNReal.ofReal kK := by
          rw [ENNReal.ofReal_add (add_nonneg t1 t2) t3, ENNReal.ofReal_add t1 t2,
            ENNReal.ofReal_mul hp, ENNReal.ofReal_mul hc', ENNReal.ofReal_mul hW']
        rw [ENNReal.ofReal_mul hq, hsum]
        ring
    _ ≤ ENNReal.ofReal ((W : ℝ) / 6) * E0 := by
        gcongr
        exact inner_const hL hΓ H.Γ_nn hΓΓ hW

end OracleTemplate.ProximalStorm
