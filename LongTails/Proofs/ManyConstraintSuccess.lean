import LongTails.Proofs.ManyConstraintAccuracy
import LongTails.Proofs.ManyConstraintCleanup

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintSuccess

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep LongTails.Proofs.ManyConstraintBall
  LongTails.Proofs.ManyConstraintRun LongTails.Proofs.ManyConstraintInner
  LongTails.Proofs.ManyConstraintEpochEnergy LongTails.Proofs.ManyConstraintMulti
  LongTails.Proofs.ManyConstraintTuning LongTails.Proofs.ManyConstraintLower
  LongTails.Proofs.ManyConstraintAccuracy LongTails.Proofs.ManyConstraintCleanup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E} {κ R ε : ℝ} {x0 : E}

lemma pos_gap (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) (s : E) :
    max (objective law loss s - objective law loss xs) 0 ≤
      Dgap law loss P σ κ R (knobs m κ σ ε L R x0) xs s + muT ε R / 2 * R ^ 2 := by
  set k := knobs m κ σ ε L R x0
  have hD := Dgap_nonneg H s
  have hpen0 : 0 ≤ hpen k.β P s := hpen_nonneg H.β_pos.le s
  have hpenxs : hpen k.β P xs = 0 := by
    have hz : ∀ j, pen k.β (P j) xs = 0 := fun j =>
      pen_zero_of_mem (H.proj j) (mem_iInter.mp H.feasible j)
    simp [hpen, hz]
  have hr0 : 0 ≤ reg k.μ k.x0 s := by unfold reg; have := H.μ_nonneg; positivity
  have hr1 : reg k.μ k.x0 xs ≤ k.μ / 2 * R ^ 2 := by
    unfold reg
    have : ‖xs - k.x0‖ ≤ R := by rw [norm_sub_rev]; exact H.radius
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) this 2)
      (by have := H.μ_nonneg; positivity)
  have hc0 : 0 ≤ c0 σ κ R k := by
    unfold c0
    have := H.β_pos; have := H.κ_pos; have := H.μ_nonneg
    positivity
  have hμ : k.μ = muT ε R := rfl
  apply max_le
  · unfold Dgap Phi Fsm
    rw [hpenxs, ← hμ]
    linarith
  · have : 0 ≤ muT ε R / 2 * R ^ 2 := by rw [← hμ]; have := H.μ_nonneg; positivity
    linarith

lemma dist_from_gap (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) (s : E) :
    Metric.infDist s (⋂ j, K j) ^ 2 ≤
      4 * κ * Dgap law loss P σ κ R (knobs m κ σ ε L R x0) xs s / betaT κ σ ε L +
        4 * κ ^ 2 * σ ^ 2 / betaT κ σ ε L ^ 2 := by
  set k := knobs m κ σ ε L R x0
  set d := Metric.infDist s (⋂ j, K j)
  have hβ : 0 < k.β := H.β_pos
  have hκ := H.κ_pos
  have hlow := Phi_lower_dist H.reg H.L_pos H.σ_nonneg H.proj H.convex H.feasible H.minimal
    hκ hβ H.μ_nonneg H.radius s (H.regular s)
  set D := Dgap law loss P σ κ R k xs s
  have hk : -(σ * d) + k.β / (2 * κ) * d ^ 2 ≤ D := by
    have : 0 ≤ κ * σ ^ 2 / (2 * k.β) := by positivity
    simp only [D, Dgap, c0]
    linarith
  have h1 : d ^ 2 ≤ 2 * κ / k.β * D + 2 * κ * σ / k.β * d := by
    have e : k.β / (2 * κ) * d ^ 2 ≤ D + σ * d := by linarith
    have hpos : 0 < k.β / (2 * κ) := by positivity
    have : d ^ 2 ≤ (D + σ * d) / (k.β / (2 * κ)) := by rw [le_div_iff₀ hpos]; linarith
    calc d ^ 2 ≤ _ := this
      _ = 2 * κ / k.β * D + 2 * κ * σ / k.β * d := by field_simp
  have h2 : 2 * κ * σ / k.β * d ≤ d ^ 2 / 2 + (2 * κ * σ / k.β) ^ 2 / 2 := by
    nlinarith [sq_nonneg (d - 2 * κ * σ / k.β)]
  have hb : k.β = betaT κ σ ε L := rfl
  rw [← hb]
  have h4 : (2 * κ * σ / k.β) ^ 2 = 4 * κ ^ 2 * σ ^ 2 / k.β ^ 2 := by field_simp; ring
  rw [h4] at h2
  have h3 : 2 * κ / k.β * D = 1 / 2 * (4 * κ * D / k.β) := by ring
  have h5 : 4 * κ ^ 2 * σ ^ 2 / k.β ^ 2 / 2 = 1 / 2 * (4 * κ ^ 2 * σ ^ 2 / k.β ^ 2) := by ring
  rw [h3] at h1
  rw [h5] at h2
  linarith

lemma obj_point (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) (hκ1 : 1 ≤ κ)
    (hε : 0 < ε) (hR : 0 < R) {s p : E}
    (hmove : ‖p - s‖ ≤ 2 * Metric.infDist s (⋂ j, K j)) :
    max (objective law loss p - objective law loss xs) 0 ≤
      11 / 5 * Dgap law loss P σ κ R (knobs m κ σ ε L R x0) xs s + ε / 7 := by
  set D := Dgap law loss P σ κ R (knobs m κ σ ε L R x0) xs s
  set d := Metric.infDist s (⋂ j, K j)
  have hL := H.L_pos
  have hσ := H.σ_nonneg
  have hD0 := Dgap_nonneg H s
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  have hcl := cleanup_objective H.reg hL hσ H.convex H.feasible H.minimal hmove
  have hpos := pos_gap H s
  have hdist := dist_from_gap H s
  have hμR : muT ε R / 2 * R ^ 2 = ε / 768 := by unfold muT; field_simp; ring
  set T := σ ^ 2 / ε + L
  have hT : 0 < T := by have : 0 ≤ σ ^ 2 / ε := by positivity
                        linarith
  have hβ : betaT κ σ ε L = 384 * κ * T := rfl
  have hκ : 0 < κ := by linarith
  have hamgm : 3 * σ * d ≤ ε / 8 + 18 * σ ^ 2 / ε * d ^ 2 := by
    have h := sq_nonneg (12 * σ * d / ε - 1 / 2)
    have : 0 ≤ ε / 8 + 18 * σ ^ 2 / ε * d ^ 2 - 3 * σ * d := by
      have e : ε / 8 + 18 * σ ^ 2 / ε * d ^ 2 - 3 * σ * d =
          ε / 8 * (12 * σ * d / ε - 1) ^ 2 + 0 := by field_simp; ring
      rw [e]; positivity
    linarith
  have hTdef : T = σ ^ 2 / ε + L := rfl
  have hcoef : 18 * σ ^ 2 / ε + 4 * L ≤ 18 * T := by
    rw [hTdef]
    have : 18 * σ ^ 2 / ε = 18 * (σ ^ 2 / ε) := by ring
    linarith
  have hσT : σ ^ 2 ≤ ε * T := by
    rw [hTdef, mul_add, mul_div_cancel₀ _ hε.ne']; nlinarith
  have hdist' : (18 * σ ^ 2 / ε + 4 * L) * d ^ 2 ≤ 3 / 16 * D + ε / 2048 := by
    have hc0 : 0 ≤ 18 * σ ^ 2 / ε + 4 * L := by positivity
    have e1 := mul_le_mul_of_nonneg_left hdist hc0
    rw [hβ] at e1
    have e2 : (18 * σ ^ 2 / ε + 4 * L) * (4 * κ * D / (384 * κ * T)) ≤ 3 / 16 * D := by
      have : (18 * σ ^ 2 / ε + 4 * L) * (4 * κ * D / (384 * κ * T)) =
          (18 * σ ^ 2 / ε + 4 * L) / T * (D / 96) := by field_simp; ring
      rw [this]
      have : (18 * σ ^ 2 / ε + 4 * L) / T ≤ 18 := by rw [div_le_iff₀ hT]; linarith
      nlinarith [mul_le_mul_of_nonneg_right this (show 0 ≤ D / 96 by positivity)]
    have e3 : (18 * σ ^ 2 / ε + 4 * L) * (4 * κ ^ 2 * σ ^ 2 / (384 * κ * T) ^ 2) ≤ ε / 2048 := by
      have : (18 * σ ^ 2 / ε + 4 * L) * (4 * κ ^ 2 * σ ^ 2 / (384 * κ * T) ^ 2) =
          (18 * σ ^ 2 / ε + 4 * L) / T * (σ ^ 2 / T) / 36864 := by field_simp; ring
      rw [this]
      have h1 : (18 * σ ^ 2 / ε + 4 * L) / T ≤ 18 := by rw [div_le_iff₀ hT]; linarith
      have h2 : σ ^ 2 / T ≤ ε := by rw [div_le_iff₀ hT]; linarith
      have h3 : 0 ≤ (18 * σ ^ 2 / ε + 4 * L) / T := by positivity
      have h4 : (18 * σ ^ 2 / ε + 4 * L) / T * (σ ^ 2 / T) ≤ 18 * ε :=
        mul_le_mul h1 h2 (by positivity) (by norm_num)
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  nlinarith

lemma obj_abs_le (H : Hyp law loss grad L σ xs K P κ R (knobs m κ σ ε L R x0)) {y : E} {r : ℝ}
    (hy : ‖y - xs‖ ≤ r) :
    |objective law loss y - objective law loss xs| ≤ σ * r + L / 2 * r ^ 2 := by
  have hr : 0 ≤ r := (norm_nonneg _).trans hy
  have hmod := H.reg.model xs y
  have hsup := H.reg.support H.L_pos xs y
  have hnn : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ y - grad ξ xs‖ ^ 2 ∂law := by
    have : 0 ≤ ∫ ξ, ‖grad ξ y - grad ξ xs‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
    have := H.L_pos; positivity
  have hG := meanGrad_norm_le H.reg H.σ_nonneg
  have hi := abs_real_inner_le_norm (meanGrad law grad xs) (y - xs)
  have hi' : ‖meanGrad law grad xs‖ * ‖y - xs‖ ≤ σ * r := mul_le_mul hG hy (norm_nonneg _) H.σ_nonneg
  have hsq : ‖y - xs‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hL2 : L / 2 * ‖y - xs‖ ^ 2 ≤ L / 2 * r ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by linarith [H.L_pos])
  have hL0 : 0 ≤ L / 2 * ‖y - xs‖ ^ 2 := by have := H.L_pos; positivity
  rw [abs_le]
  constructor
  · nlinarith [neg_abs_le ⟪meanGrad law grad xs, y - xs⟫]
  · nlinarith [le_abs_self ⟪meanGrad law grad xs, y - xs⟫]

end LongTails.Proofs.ManyConstraintSuccess
