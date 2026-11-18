import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace LongTails.Proofs.PreferenceTranscriptDistance

noncomputable def squareDistance (a b : ℝ) : ℝ := (Real.sqrt a - Real.sqrt b) ^ 2

lemma root_product_bound {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a * Real.sqrt b ≤ a + b := by
  nlinarith only [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

lemma split_distance {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    squareDistance (a*p) (b*q) + squareDistance (a*(1-p)) (b*(1-q)) =
      squareDistance a b + Real.sqrt a * Real.sqrt b *
        (squareDistance p q + squareDistance (1-p) (1-q)) := by
  unfold squareDistance
  simp only [Real.sqrt_mul ha, Real.sqrt_mul hb]
  ring_nf
  simp only [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hp.1, Real.sq_sqrt hq.1,
    Real.sq_sqrt (sub_nonneg.mpr hp.2), Real.sq_sqrt (sub_nonneg.mpr hq.2)]
  ring

lemma squareDistance_le {a b τ : ℝ} (hτ : 0 < τ) (ha : τ ≤ a) (hb : τ ≤ b) :
    squareDistance a b ≤ (a-b)^2 / (4*τ) := by
  have ha' := hτ.le.trans ha
  have hb' := hτ.le.trans hb
  have hprod : (Real.sqrt a + Real.sqrt b)^2 * squareDistance a b = (a-b)^2 := by
    unfold squareDistance
    rw [← mul_pow]
    congr 1
    nlinarith only [Real.sq_sqrt ha', Real.sq_sqrt hb']
  have hsum : 2 * Real.sqrt τ ≤ Real.sqrt a + Real.sqrt b := by
    linarith only [Real.sqrt_le_sqrt ha, Real.sqrt_le_sqrt hb]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.sqrt τ) hsum 2
  rw [mul_pow, Real.sq_sqrt hτ.le] at hs
  apply (le_div_iff₀ (by positivity)).mpr
  have hD : 0 ≤ squareDistance a b := sq_nonneg _
  nlinarith only [hprod, mul_le_mul_of_nonneg_right hs hD]

lemma split_distance_le {a b p q τ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hτ : 0 < τ) (hp : p ∈ Set.Icc τ (1 - τ)) (hq : q ∈ Set.Icc τ (1 - τ)) :
    squareDistance (a*p) (b*q) + squareDistance (a*(1-p)) (b*(1-q)) ≤
      squareDistance a b + (a+b) * (p-q)^2 / (4*τ) := by
  rw [split_distance ha hb ⟨hτ.le.trans hp.1, by linarith [hp.2]⟩
    ⟨hτ.le.trans hq.1, by linarith [hq.2]⟩]
  have h₁ := squareDistance_le hτ hp.1 hq.1
  have h₂ := squareDistance_le hτ (show τ ≤ 1-p by linarith [hp.2])
    (show τ ≤ 1-q by linarith [hq.2])
  rw [show (1-p-(1-q))^2 = (p-q)^2 by ring] at h₂
  have hr := root_product_bound ha hb
  have hterm : 0 ≤ (p-q)^2 / (4*τ) := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left (add_le_add h₁ h₂)
    (mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)), mul_le_mul_of_nonneg_right hr hterm,
    show (a+b) * (p-q)^2 / (4*τ) = (a+b) * ((p-q)^2 / (4*τ)) by ring]

end LongTails.Proofs.PreferenceTranscriptDistance
