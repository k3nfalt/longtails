import LongTails.Proofs.ManyConstraintTuning
import LongTails.Proofs.ManyConstraintFinalAlgebra

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintAccuracy

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep LongTails.Proofs.ManyConstraintBall
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintInner
  LongTails.Proofs.ManyConstraintEpochEnergy LongTails.Proofs.ManyConstraintMulti
  LongTails.Proofs.ManyConstraintTuning LongTails.Proofs.ManyConstraintFinalAlgebra
  LongTails.Proofs.ManyConstraintLower OracleTemplate.Katyusha

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E} {κ R ε : ℝ} {x0 : E}

lemma Dgap_x0_le (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) :
    Dgap law loss P σ κ R (knobs m κ σ ε L R x0) xs x0 ≤
      σ * R + LtT κ σ ε L * R ^ 2 / 2 + c0 σ κ R (knobs m κ σ ε L R x0) := by
  set k := knobs m κ σ ε L R x0
  have hR0 : ‖x0 - xs‖ ≤ R := H.radius
  have hmod := H.reg.model xs x0
  have hG := meanGrad_norm_le H.reg H.σ_nonneg
  have hin : ⟪meanGrad law grad xs, x0 - xs⟫ ≤ σ * R := by
    calc _ ≤ ‖meanGrad law grad xs‖ * ‖x0 - xs‖ := real_inner_le_norm _ _
      _ ≤ σ * R := mul_le_mul hG hR0 (norm_nonneg _) H.σ_nonneg
  have hsq : ‖x0 - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR0 2
  have hpen0 : hpen k.β P x0 ≤ k.β / 2 * R ^ 2 := by
    unfold hpen
    have : ∀ j, pen k.β (P j) x0 ≤ k.β / 2 * R ^ 2 := by
      intro j
      rw [pen_eq_infDist (H.proj j)]
      have hd : Metric.infDist x0 (K j) ≤ ‖x0 - xs‖ := by
        rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (mem_iInter.mp H.feasible j)
      have : Metric.infDist x0 (K j) ^ 2 ≤ R ^ 2 :=
        (pow_le_pow_left₀ Metric.infDist_nonneg hd 2).trans hsq
      exact mul_le_mul_of_nonneg_left this (by have := H.β_pos; positivity)
    calc (𝔼 j, pen k.β (P j) x0) ≤ 𝔼 _j : Fin m, k.β / 2 * R ^ 2 :=
          Finset.expect_le_expect fun j _ => this j
      _ = _ := Fintype.expect_const _
  have hpenxs : hpen k.β P xs = 0 := by
    have hz : ∀ j, pen k.β (P j) xs = 0 := fun j =>
      pen_zero_of_mem (H.proj j) (mem_iInter.mp H.feasible j)
    simp [hpen, hz]
  have hreg0 : reg k.μ k.x0 x0 = 0 := by simp [reg, k, knobs]
  have hregxs : 0 ≤ reg k.μ k.x0 xs := by unfold reg; have := H.μ_nonneg; positivity
  have hLt : LtT κ σ ε L = L + k.β := rfl
  have hL2 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ L / 2 by linarith [H.L_pos])
  unfold Dgap Phi Fsm
  rw [hreg0, hpenxs, hLt]
  have : k.x0 = x0 := rfl
  rw [this] at hregxs ⊢
  nlinarith [hpen0]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
lemma c0_bounds (hκ : 1 ≤ κ) (_hσ : 0 ≤ σ) (hε : 0 < ε) (hL : 0 < L) (hR : 0 < R) :
    c0 σ κ R (knobs m κ σ ε L R x0) ≤ ε / 384 ∧
      12 * c0 σ κ R (knobs m κ σ ε L R x0) ≤ ε / 32 := by
  have hb : 0 < σ ^ 2 / ε + L := by have : 0 ≤ σ ^ 2 / ε := by positivity
                                    linarith
  have h1 : κ * σ ^ 2 / (2 * betaT κ σ ε L) ≤ ε / 768 := by
    unfold betaT
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : σ ^ 2 ≤ ε * (σ ^ 2 / ε + L) := by
      rw [mul_add, mul_div_cancel₀ _ hε.ne']; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ 768 * κ by linarith)]
  have h2 : muT ε R / 2 * R ^ 2 = ε / 768 := by unfold muT; field_simp; ring
  unfold c0
  change κ * σ ^ 2 / (2 * betaT κ σ ε L) + muT ε R / 2 * R ^ 2 ≤ _ ∧
    12 * (κ * σ ^ 2 / (2 * betaT κ σ ε L) + muT ε R / 2 * R ^ 2) ≤ _
  constructor <;> nlinarith

variable [IsProbabilityMeasure law]

set_option maxHeartbeats 2000000 in
lemma ED_bound (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hR : 0 < R) :
    (𝔼 jss : Fin (ST m κ σ ε L R) → Fin (2 * m) → Fin m, ∫ ξ,
      Dgap law loss P σ κ R (knobs m κ σ ε L R x0) xs
        (run grad P (knobs m κ σ ε L R x0) (ST m κ σ ε L R) ⟨x0, x0, x0⟩ jss ξ).s
        ∂(Measure.infinitePi fun _ : ℕ => law)) ≤ ε / 16 := by
  set k := knobs m κ σ ε L R x0
  set S := ST m κ σ ε L R
  set D := Dgap law loss P σ κ R k xs
  set inf := Measure.infinitePi fun _ : ℕ => law
  have hL := H.L_pos
  have hσ := H.σ_nonneg
  obtain ⟨hτ, hτh, hα, htune, hq6, hcoef, hd, hθe, hτt⟩ :=
    tuning_facts (m := m) (σ := σ) (R := R) hκ hε hL hR
  have ht := tT_pos (m := m) (κ := κ) (σ := σ) (ε := ε) (L := L) (R := R)
  have hLt := LtT_pos (σ := σ) hκ hε hL
  have hθ1 : 1 ≤ k.θ := by
    change 1 ≤ theta (kp m κ σ ε L R); rw [hθe]
    have := mul_nonneg hα.le (show 0 ≤ muT ε R by unfold muT; positivity); linarith
  have hθ0 : 0 < k.θ := by linarith
  set q := k.θ ^ k.M
  have hq : 1 + k.τ / 6 ≤ q := hq6
  have hτk : 0 < k.τ := H.τ_pos
  have hτv : k.τ = 1 / (2 * (tT m κ σ ε L R : ℝ)) := hτt
  have hq1 : 1 < q := by linarith
  have hws : (k.M : ℝ) ≤ wsum k.θ k.M := by
    unfold wsum
    calc (k.M : ℝ) = ∑ _i ∈ Finset.range k.M, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => one_le_pow₀ hθ1
  have hM1 : (1 : ℝ) ≤ k.M := by
    change (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ); have := NeZero.pos m; exact_mod_cast (by omega)
  have hws0 : 0 < wsum k.θ k.M := by linarith
  have hx0 : x0 ∈ closedBall k.x0 k.ρ := mem_closedBall_self hR.le
  have hmulti := multi_epoch H S ⟨x0, x0, x0⟩ hx0 hx0 hx0
  have hc : 0 ≤ 1 / 2 - k.τ := by linarith [H.τ_half]
  have hdpos : 0 ≤ k.τ / (2 * k.α) := div_nonneg H.τ_pos.le (by linarith [H.α_pos])
  have hcm : Measurable (fun ξ : ℕ → Ξ => (tri (⟨x0, x0, x0⟩ : St E), ξ)) :=
    measurable_const.prodMk measurable_id
  have hrun : ∀ jss, Measurable (fun ξ : ℕ → Ξ => tri (run grad P k S ⟨x0, x0, x0⟩ jss ξ)) :=
    fun jss => (run_measurable_joint H S jss).comp hcm
  have hmem : ∀ jss ξ, (run grad P k S ⟨x0, x0, x0⟩ jss ξ).s ∈ closedBall k.x0 k.ρ ∧
      (run grad P k S ⟨x0, x0, x0⟩ jss ξ).y ∈ closedBall k.x0 k.ρ ∧
      (run grad P k S ⟨x0, x0, x0⟩ jss ξ).z ∈ closedBall k.x0 k.ρ :=
    fun jss ξ => run_mem H S _ jss ξ hx0 hx0 hx0
  have hDi : ∀ jss, Integrable (fun ξ => D (run grad P k S ⟨x0, x0, x0⟩ jss ξ).s) inf := by
    intro jss
    refine Integrable.of_bound (((Dgap_measurable H).comp (measurable_fst.comp (hrun jss))
      ).aestronglyMeasurable) (Dbound law loss grad P L σ κ R k xs)
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]; exact Dgap_abs_le H (hmem jss ξ).1
  have hPi : ∀ jss, Integrable (fun ξ => Pot law loss P σ κ R k xs
      (run grad P k S ⟨x0, x0, x0⟩ jss ξ)) inf := by
    intro jss
    have hm : Measurable (fun ξ => Pot law loss P σ κ R k xs (run grad P k S ⟨x0, x0, x0⟩ jss ξ)) := by
      have := (Pot_measurable H).comp (hrun jss)
      simpa only [Function.comp_def, untri_tri] using this
    refine Integrable.of_bound hm.aestronglyMeasurable (Pbound law loss grad P L σ κ R k xs)
      (Filter.Eventually.of_forall fun ξ => ?_)
    obtain ⟨a, b, c⟩ := hmem jss ξ
    obtain ⟨h0, h1⟩ := Pot_bounds H a b c
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  set A := 𝔼 jss : Fin S → Fin k.M → Fin m, ∫ ξ, D (run grad P k S ⟨x0, x0, x0⟩ jss ξ).s ∂inf
  set Pt := 𝔼 jss : Fin S → Fin k.M → Fin m, ∫ ξ, Pot law loss P σ κ R k xs
    (run grad P k S ⟨x0, x0, x0⟩ jss ξ) ∂inf
  have hAP : 1 / 2 * wsum k.θ k.M * A ≤ Pt := by
    simp only [A, Pt]
    rw [Finset.mul_expect]
    refine Finset.expect_le_expect fun jss _ => ?_
    rw [← integral_const_mul]
    refine integral_mono ((hDi jss).const_mul _) (hPi jss) fun ξ => ?_
    obtain ⟨a, b, c⟩ := hmem jss ξ
    have e2 := Dgap_nonneg H (run grad P k S ⟨x0, x0, x0⟩ jss ξ).y
    unfold Pot
    nlinarith [mul_nonneg hc e2, mul_nonneg hdpos (sq_nonneg
      ‖(run grad P k S ⟨x0, x0, x0⟩ jss ξ).z - xs‖)]
  have hgeom := geom_le hq1 S
  set W := wsum k.θ k.M * err L σ κ R k
  have herr0 : 0 ≤ err L σ κ R k := by
    unfold err c0
    have := H.β_pos
    have : 0 ≤ κ * σ ^ 2 / (2 * k.β) := by have := H.κ_pos; positivity
    have : 0 ≤ k.μ / 2 * R ^ 2 := by have := H.μ_nonneg; positivity
    have : 0 ≤ σ ^ 2 / (2 * (L + k.β) * k.b) := by
      have := H.b_pos; positivity
    nlinarith [H.τ_pos]
  have hW0 : 0 ≤ W := mul_nonneg hws0.le herr0
  have hqS : 0 < q ^ S := pow_pos (by linarith) S
  have hmain : q ^ S * Pt ≤ Pot law loss P σ κ R k xs ⟨x0, x0, x0⟩ + q ^ S / (q - 1) * W := by
    calc q ^ S * Pt ≤ _ := hmulti
      _ ≤ _ := by gcongr
  set Pot0 := Pot law loss P σ κ R k xs ⟨x0, x0, x0⟩
  have hA : A ≤ 2 * Pot0 / (wsum k.θ k.M * q ^ S) + 2 * err L σ κ R k / (q - 1) := by
    have h1 : 1 / 2 * wsum k.θ k.M * A * q ^ S ≤ Pot0 + q ^ S / (q - 1) * W := by
      nlinarith [mul_le_mul_of_nonneg_right hAP hqS.le]
    have hq0 : 0 < q - 1 := by linarith
    have : A ≤ (Pot0 + q ^ S / (q - 1) * W) / (1 / 2 * wsum k.θ k.M * q ^ S) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc A ≤ _ := this
      _ = 2 * Pot0 / (wsum k.θ k.M * q ^ S) + 2 * err L σ κ R k / (q - 1) := by
        simp only [W]; field_simp
  have hD0 := Dgap_x0_le H
  have hD00 := Dgap_nonneg H x0
  obtain ⟨hc0, h12c0⟩ := c0_bounds (m := m) (x0 := x0) hκ hσ hε hL hR
  have hdval : k.τ / (2 * k.α) = 3 * (k.M : ℝ) * muT ε R := hd
  have hμR : muT ε R * R ^ 2 = ε / 384 := by unfold muT; field_simp
  have hR2 : ‖x0 - xs‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) H.radius 2
  set Y := 2 * σ * R + 2 * LtT κ σ ε L * R ^ 2 + 3 * ε
  have hY0 : 0 < Y := by
    have : 0 ≤ 2 * σ * R := by have := mul_nonneg hσ hR.le; linarith
    have : 0 ≤ 2 * LtT κ σ ε L * R ^ 2 := by have := mul_nonneg hLt.le (sq_nonneg R); linarith
    linarith
  have hPot0 : 2 * Pot0 / wsum k.θ k.M ≤ Y := by
    have hP : Pot0 = 1 / 2 * wsum k.θ k.M * D x0 + (1 / 2 - k.τ) * D x0 +
        k.τ / (2 * k.α) * ‖x0 - xs‖ ^ 2 := by simp only [Pot0, Pot, D]
    rw [div_le_iff₀ hws0, hP, hdval]
    have hterm : 3 * (k.M : ℝ) * muT ε R * ‖x0 - xs‖ ^ 2 ≤ 3 * wsum k.θ k.M * (ε / 384) := by
      have : (k.M : ℝ) * (muT ε R * ‖x0 - xs‖ ^ 2) ≤ wsum k.θ k.M * (ε / 384) := by
        rw [← hμR]
        have hμ0 : 0 ≤ muT ε R := div_nonneg hε.le (by positivity)
        exact mul_le_mul hws (mul_le_mul_of_nonneg_left hR2 hμ0)
          (mul_nonneg hμ0 (sq_nonneg _)) hws0.le
      calc 3 * (k.M : ℝ) * muT ε R * ‖x0 - xs‖ ^ 2 =
          3 * ((k.M : ℝ) * (muT ε R * ‖x0 - xs‖ ^ 2)) := by ring
        _ ≤ 3 * (wsum k.θ k.M * (ε / 384)) := by gcongr
        _ = _ := by ring
    have hcD : (1 / 2 - k.τ) * D x0 ≤ 1 / 2 * wsum k.θ k.M * D x0 := by
      have : 1 / 2 - k.τ ≤ 1 / 2 * wsum k.θ k.M := by linarith [H.τ_pos]
      exact mul_le_mul_of_nonneg_right this hD00
    have hσR : 0 ≤ σ * R := mul_nonneg hσ hR.le
    have hLR : 0 ≤ LtT κ σ ε L * R ^ 2 := mul_nonneg hLt.le (sq_nonneg R)
    have e1 := mul_le_mul_of_nonneg_left hD0 hws0.le
    have e2 := mul_le_mul_of_nonneg_left hc0 hws0.le
    have e3 : 0 ≤ wsum k.θ k.M * (σ * R) := mul_nonneg hws0.le hσR
    have e4 : 0 ≤ wsum k.θ k.M * (LtT κ σ ε L * R ^ 2) := mul_nonneg hws0.le hLR
    have e5 : 0 ≤ wsum k.θ k.M * ε := mul_nonneg hws0.le hε.le
    have hYw : Y * wsum k.θ k.M = 2 * (wsum k.θ k.M * (σ * R)) +
        2 * (wsum k.θ k.M * (LtT κ σ ε L * R ^ 2)) + 3 * (wsum k.θ k.M * ε) := by
      simp only [Y]; ring
    rw [hYw]
    linarith [e1, e2, e3, e4, e5, hcD, hterm]
  have hX : 64 * Y / ε ≤ q ^ S := by
    refine pow_ge ht ?_ (by positivity) (Nat.le_ceil _)
    rw [hτv] at hq
    have : 1 / (2 * (tT m κ σ ε L R : ℝ)) / 6 = 1 / (12 * (tT m κ σ ε L R : ℝ)) := by
      field_simp; ring
    linarith
  have htrans : 2 * Pot0 / (wsum k.θ k.M * q ^ S) ≤ ε / 64 := by
    rw [show 2 * Pot0 / (wsum k.θ k.M * q ^ S) = 2 * Pot0 / wsum k.θ k.M / q ^ S by
      field_simp]
    rw [div_le_iff₀ hqS]
    have h64 : ε / 64 * (64 * Y / ε) = Y := by field_simp
    calc 2 * Pot0 / wsum k.θ k.M ≤ Y := hPot0
      _ = ε / 64 * (64 * Y / ε) := h64.symm
      _ ≤ ε / 64 * q ^ S := mul_le_mul_of_nonneg_left hX (by positivity)
  have hτpos := H.τ_pos
  have hnoise : 2 * err L σ κ R k / (q - 1) ≤ 24 * (tT m κ σ ε L R : ℝ) * err L σ κ R k := by
    rw [div_le_iff₀ (by linarith)]
    have : k.τ / 6 ≤ q - 1 := by linarith
    have h24 : 24 * (tT m κ σ ε L R : ℝ) * (k.τ / 6) = 2 := by
      rw [hτv]; field_simp; ring
    have hc24 : 0 ≤ 24 * (tT m κ σ ε L R : ℝ) * err L σ κ R k :=
      mul_nonneg (by linarith) herr0
    calc 2 * err L σ κ R k = (24 * (tT m κ σ ε L R : ℝ) * (k.τ / 6)) * err L σ κ R k := by
          rw [h24]
      _ = (24 * (tT m κ σ ε L R : ℝ) * err L σ κ R k) * (k.τ / 6) := by ring
      _ ≤ (24 * (tT m κ σ ε L R : ℝ) * err L σ κ R k) * (q - 1) :=
          mul_le_mul_of_nonneg_left this hc24
  have hb := bT_ge (m := m) (σ := σ) (R := R) hκ hε hL
  have herr : 24 * (tT m κ σ ε L R : ℝ) * err L σ κ R k ≤ ε / 64 + ε / 32 := by
    unfold err
    have hτ2 : 24 * (tT m κ σ ε L R : ℝ) * k.τ = 12 := by
      rw [hτv]; field_simp; ring
    have hbR : (0 : ℝ) < k.b := by exact_mod_cast H.b_pos
    have hLtk : L + k.β = LtT κ σ ε L := rfl
    have hs1 : 24 * (tT m κ σ ε L R : ℝ) * (σ ^ 2 / (2 * (L + k.β) * k.b)) ≤ ε / 64 := by
      rw [hLtk]
      have hbb : 768 * (tT m κ σ ε L R : ℝ) * σ ^ 2 / ε ≤ LtT κ σ ε L * k.b := by
        have h' : (tT m κ σ ε L R : ℝ) * (768 * σ ^ 2 / ε) / LtT κ σ ε L ≤ k.b := by
          refine le_trans ?_ hb
          apply div_le_div_of_nonneg_right _ hLt.le
          apply mul_le_mul_of_nonneg_left _ ht.le
          linarith
        rw [div_le_iff₀ hLt] at h'
        calc 768 * (tT m κ σ ε L R : ℝ) * σ ^ 2 / ε = (tT m κ σ ε L R : ℝ) * (768 * σ ^ 2 / ε) := by
              ring
          _ ≤ _ := by linarith
      rw [show 24 * (tT m κ σ ε L R : ℝ) * (σ ^ 2 / (2 * LtT κ σ ε L * k.b)) =
          12 * (tT m κ σ ε L R : ℝ) * σ ^ 2 / (LtT κ σ ε L * k.b) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hbb
      nlinarith
    have hs2 : 24 * (tT m κ σ ε L R : ℝ) * (k.τ * c0 σ κ R k) ≤ ε / 32 := by
      rw [show 24 * (tT m κ σ ε L R : ℝ) * (k.τ * c0 σ κ R k) =
        (24 * (tT m κ σ ε L R : ℝ) * k.τ) * c0 σ κ R k by ring, hτ2]
      exact h12c0
    nlinarith
  have hfinal : A ≤ ε / 16 := by linarith
  exact hfinal

end LongTails.Proofs.ManyConstraintAccuracy
