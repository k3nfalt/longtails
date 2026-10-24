import LongTails.Proofs.CyclicPerceptronCounting
import LongTails.Proofs.CyclicPerceptronParameters
import LongTails.Proofs.CyclicPerceptronPairing

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronCertificate

open LongTails.Setups.CyclicFullWidthPerceptron
open CyclicPerceptronBlocks CyclicPerceptronComparisonDynamics CyclicPerceptronBootstrap
open CyclicPerceptronBounds CyclicPerceptronCounting CyclicPerceptronCone

structure Certificate {d : ℕ} (α μ H δ κ : ℝ) (p u₀ w : Features d)
    (m : ℕ) (σ : ℝ) (c : Coordinates d) (s : Comparison d) : Prop where
  errors : Errors α μ H m c s
  comparison_bound : ComparisonBound m s
  potential : Potential σ δ κ p u₀ m s
  loss_bound : σ ≤ m
  progress : κ * m ≤ ⟪w, s.U⟫
  positive_count : (s.positivePairs : ℝ) ≤ 32 / κ ^ 3 + 1

lemma certificate_count {d : ℕ} (α μ H δ κ : ℝ) (p u₀ w : Features d)
    (m : ℕ) (σ : ℝ) (c : Coordinates d) (s : Comparison d)
    (hs : Certificate α μ H δ κ p u₀ w m σ c s)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 6)
    (hp : ‖p‖ ≤ 1) (hu : ‖u₀‖ ≤ 1) (hw : ‖w‖ = 1) :
    (m : ℝ) ≤ 68 / κ ^ 4 := by
  exact total_count_bound κ s.positivePairs m hκ hκ₁ hs.positive_count
    (potential_count σ δ κ p u₀ w m s hs.potential hκ hκ₁ hδ hδ₁ hp hu hw hs.progress)

lemma certificate_start {d : ℕ} (α μ H δ κ : ℝ) (p u₀ w : Features d)
    (hκ : 0 < κ) :
    Certificate α μ H δ κ p u₀ w 0 0 (coordinateStart d) (comparisonStart d) := by
  constructor
  · constructor <;> simp [coordinateStart, comparisonStart]
  · constructor <;> simp [comparisonStart]
  · exact potential_start δ κ p u₀
  · simp
  · simp [comparisonStart]
  · simp only [comparisonStart, Nat.cast_zero]
    positivity

lemma certificate_step {d : ℕ} (b : Bool) (α μ H δ κ β : ℝ) (p u₀ w u : Features d)
    (m : ℕ) (σ : ℝ) (c : Coordinates d) (s : Comparison d)
    (hs : Certificate α μ H δ κ p u₀ w m σ c s)
    (hα : 0 ≤ α) (hα₁ : α ≤ 1) (hμ : μ ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (hH : 1 ≤ H) (hmH : (m : ℝ) ≤ H)
    (hsmall : α * H ^ 2 ≤ 1 / 1024)
    (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 6)
    (hp : κ ≤ ‖p‖) (hp₁ : ‖p‖ ≤ 1) (hu₀ : ‖u₀‖ ≤ 1) (hw : ‖w‖ = 1)
    (hpu₀ : ⟪p, u₀⟫ = ‖p‖ ^ 2) (hpu : 0 ≤ ⟪p, u⟫)
    (hu : ‖u‖ ≤ 1) (hwu : κ ≤ ⟪w, u⟫)
    (hPN : b = false → u = u₀ ∧ ⟪s.U, u₀⟫ ≤ ⟪s.U, p⟫ + 2 * δ / κ ∧
      comparisonBias s * κ ^ 4 ≤ 1)
    (hNP : b = true → ⟪s.U, u⟫ ≤ δ) :
    Certificate α μ H δ κ p u₀ w (m + 1) (σ + β)
      (pairedCoordinates b α μ β c u) (comparisonStep b β s u) := by
  have hc := envelope_of_errors α μ H m c s hα hμ hH (Nat.cast_nonneg _) hmH
    hsmall hs.errors hs.comparison_bound
  constructor
  · simpa only [Nat.cast_add, Nat.cast_one] using errors_step b α μ β H m c s u
      hα hα₁ hβ hβ₁ hμ hH hmH hu hsmall hc hs.errors
  · simpa only [Nat.cast_add, Nat.cast_one] using comparison_bound_step b β m s u
      hβ hβ₁ (Nat.cast_nonneg _) hu hs.comparison_bound
  · cases hb : b with
    | false =>
        obtain ⟨heq, hscore, _⟩ := hPN hb
        subst u
        exact potential_positive σ β δ κ p u₀ m s hs.potential hpu₀ hscore
    | true => exact potential_negative σ β δ κ p u₀ u m s hs.potential hpu hu (hNP hb)
  · push_cast
    linarith [hs.loss_bound]
  · simp only [comparisonStep, inner_add_right, Nat.cast_add, Nat.cast_one]
    linarith [hs.progress]
  · cases hb : b with
    | false =>
        obtain ⟨_, _, hC⟩ := hPN hb
        have hm := potential_count σ δ κ p u₀ w m s hs.potential
          hκ hκ₁ hδ hδ₁ hp₁ hu₀ hw hs.progress
        have hk := positive_count_obstruction s p u₀ σ δ κ m hs.potential hκ hκ₁
          hs.loss_bound hδ₁ hp hu₀ hm hC
        simp only [comparisonStep, Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_one]
        linarith
    | true => simpa [comparisonStep] using hs.positive_count

lemma negative_score_guards {d : ℕ} (η μ β H j : ℝ) (c : Coordinates d)
    (s : Comparison d) (u : Features d) (hη : 0 < η) (hη₁ : η ^ 2 ≤ 1)
    (hμ : 0 < μ) (hμ₁ : μ ^ 2 ≤ 1) (hβ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hH : 1 ≤ H) (hj : 0 ≤ j) (hjH : j ≤ H) (hu : ‖u‖ ≤ 1)
    (he : Errors (η ^ 2) μ H j c s) (hc : Envelope H c) (hs : ComparisonBound j s) :
    let score := margin (-(1 + β * η ^ 2 * μ ^ 2), -μ • u) (realize η μ c)
    (0 < score → -(256 * η ^ 2 * H ^ 3) ≤ ⟪s.U, u⟫) ∧
    (score ≤ 0 → ⟪s.U, u⟫ ≤ 256 * η ^ 2 * H ^ 3) := by
  have herr := score_error (η ^ 2) μ β H j c s u (sq_nonneg η) hη₁
    hβ hβ₁ hμ₁ hH hj hjH hu he hc hs
  have hscale : 0 < η * μ ^ 2 := by positivity
  dsimp only
  rw [negative_margin]
  have heq : η ^ 4 = (η ^ 2) ^ 2 := by ring
  rw [heq]
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  constructor
  · intro h
    have hz := (mul_pos_iff_of_pos_left hscale).mp h
    linarith
  · intro h
    have hz := (mul_le_mul_iff_right₀ hscale).mp (show η * μ ^ 2 * _ ≤ η * μ ^ 2 * 0 by simpa using h)
    linarith

lemma reference_bias_guard {d : ℕ} (η μ H j κ : ℝ) (c : Coordinates d)
    (s : Comparison d) (hη : 0 < η) (hμ : 0 < μ)
    (hH : 1 ≤ H) (hj : 0 ≤ j) (hjH : j ≤ H)
    (he : Errors (η ^ 2) μ H j c s) (hc : Envelope H c) (hs : ComparisonBound j s)
    (hsmall : 256 * η ^ 2 * H ^ 4 * κ ^ 4 ≤ 1)
    (hscore : margin (1, 0) (realize η μ c) ≤ 0) :
    comparisonBias s * κ ^ 4 ≤ 1 := by
  rw [reference_margin] at hscore
  have hz : bias c ≤ 0 := (mul_le_mul_iff_right₀ (by positivity : 0 < η ^ 3 * μ ^ 2)).mp (by simpa using hscore)
  have herr := bias_error (η ^ 2) μ H j c s (sq_nonneg η) hH hj hjH he hc hs
  have hb : comparisonBias s ≤ 256 * η ^ 2 * H ^ 4 := by
    have hh := (abs_le.mp herr).1
    linarith
  exact (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ κ ^ 4)).trans hsmall

lemma balanced_pairing {d : ℕ} (η μ H j ci cj : ℝ) (c : Coordinates d)
    (s : Comparison d) (ui uj : Features d) (hη : 0 < η) (hη₁ : η ^ 2 ≤ 1)
    (hμ : 0 < μ) (hμ₁ : μ ≤ 1) (hH : 1 ≤ H) (hjH : j ≤ H)
    (hsmall : η ^ 2 * H ^ 2 ≤ 1 / 1024) (hμH : μ * H ≤ 1 / 4096)
    (hci : 1 ≤ ci) (hci₂ : ci ≤ 2) (hcj : 1 ≤ cj) (hcj₂ : cj ≤ 2)
    (hui : ‖ui‖ ≤ 1) (huj : ‖uj‖ ≤ 1)
    (he : Errors (η ^ 2) μ H j c s) (hc : Envelope H c) :
    let θ := realize η μ c
    0 < margin (1, 0) (move θ η (direction (1, 0) θ)) ∧
      margin (-cj, -μ • uj) (move θ η (direction (1, 0) θ)) < 0 ∧
      margin (1, 0) (move θ η (direction (-ci, -μ • ui) θ)) < 0 ∧
      0 < margin (-cj, -μ • uj) (move θ η (direction (-ci, -μ • ui) θ)) := by
  have hH0 : 0 ≤ H := by linarith
  have hsmall' : η ^ 2 * H ≤ 1 / 1024 := by
    have hm := mul_le_mul_of_nonneg_left (show H ≤ H ^ 2 by nlinarith) (sq_nonneg η)
    linarith
  have ha : |c.a - 1| ≤ 5 * η ^ 2 * H :=
    he.a_error.trans (mul_le_mul_of_nonneg_left hjH (by positivity))
  obtain ⟨hh, hh₃⟩ := CyclicPerceptronPairing.reference_feature_bounds η μ H c
    hη hμ hμ₁ hH hsmall' hc ha
  have hv := CyclicPerceptronPairing.head_norm_bound η μ H c hη hμ hμ₁ hH hsmall' hc
  have hgi := CyclicPerceptronPairing.residual_feature_bound η μ H c ui
    hη hμ hμ₁ hH hsmall' hc hui
  have hgj := CyclicPerceptronPairing.residual_feature_bound η μ H c uj
    hη hμ hμ₁ hH hsmall' hc huj
  exact CyclicPerceptronPairing.unbalanced_margins (realize η μ c) η μ ci cj (μ * H) ui uj
    hη hη₁ hμ.le hμ₁ (by nlinarith) (by positivity) hμH hci hci₂ hcj hcj₂ hui huj
    hh hh₃ (by nlinarith [hv]) hgi hgj

end LongTails.Proofs.CyclicPerceptronCertificate
