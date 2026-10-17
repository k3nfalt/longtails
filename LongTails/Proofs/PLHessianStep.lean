import LongTails.Proofs.PLHessianGeometry
import LongTails.Proofs.PLHessianHuber
import LongTails.Proofs.HeavyTailedPLStep
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance

open Set Metric MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.PLHessian

lemma hub_eq (hb : 0 < b) (t : ℝ) :
    hub a b t = (min (max (t - a) 0) b) ^ 2 / (2 * b) + max (t - a - b) 0 := by
  unfold hub
  split_ifs with h1 h2
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), min_eq_left hb.le]; simp
  · rw [max_eq_left (by linarith), min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [max_eq_left (by linarith), min_eq_right (by linarith), max_eq_left (by linarith)]
    field_simp; ring

lemma hub_continuous (hb : 0 < b) : Continuous (hub a b) := by
  have : hub a b = fun t => (min (max (t - a) 0) b) ^ 2 / (2 * b) + max (t - a - b) 0 :=
    funext (hub_eq hb)
  rw [this]; fun_prop

lemma hub_le_self (ha : 0 ≤ a) (hb : 0 < b) {t : ℝ} (ht : 0 ≤ t) : hub a b t ≤ t := by
  have h1 := hub_le_dhub_mul ha hb t
  have h2 := dhub_le_one (a := a) hb t
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] {f : E → ℝ} {u : E}

def minSet (f : E → ℝ) (u : E) : Set E := {y | f y = f u}

noncomputable def distSq (f : E → ℝ) (u : E) (x : E) : ℝ := infDist x (minSet f u) ^ 2

lemma minSet_closed (hc : Continuous f) : IsClosed (minSet f u) :=
  isClosed_eq hc continuous_const

lemma nearest [NormedSpace ℝ E] [FiniteDimensional ℝ E] (hc : Continuous f) (x : E) :
    ∃ p, f p = f u ∧ infDist x (minSet f u) = ‖x - p‖ := by
  obtain ⟨p, hp, h⟩ := (minSet_closed (u := u) hc).exists_infDist_eq_dist ⟨u, rfl⟩ x
  exact ⟨p, hp, by rw [h, dist_eq_norm]⟩

lemma distSq_le (x p : E) (hp : f p = f u) : distSq f u x ≤ ‖x - p‖ ^ 2 := by
  unfold distSq
  have h := infDist_le_dist_of_mem (x := x) (show p ∈ minSet f u from hp)
  rw [dist_eq_norm] at h
  have := infDist_nonneg (x := x) (s := minSet f u)
  nlinarith

lemma distSq_continuous : Continuous (distSq f u) := by
  unfold distSq
  exact (continuous_infDist_pt _).pow 2



section Algebra

lemma cost_common {η μ L σ K Φ Φ0 sk lam c G2 : ℝ}
    (hη : 0 < η) (hμ : 0 < μ) (hL : 0 < L) (hK : 1 ≤ K) (hΦ : 0 ≤ Φ)
    (hΦ0 : 0 < Φ0) (hsk : 1 ≤ sk) (hlam : lam = 32 * sk / μ)
    (h1 : 16 * L * η ≤ 1) (h2 : 768 * sk * K * L * σ ^ 2 * η ≤ μ * Φ0)
    (hG2 : G2 ≤ 2 * L * Φ) (hc : c ≤ Φ / (Φ0 / 4)) :
    lam * (c * (L * η ^ 2 * σ ^ 2) +
        (2 * η ^ 2 * G2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4))) ≤
      η * Φ / 2 + η ^ 2 * σ ^ 2 := by
  have hcΦ : c * Φ0 ≤ 4 * Φ := by
    rw [le_div_iff₀ (by positivity)] at hc; linarith
  have key : 768 * sk * L * σ ^ 2 * η ≤ μ * Φ0 := by
    have : 768 * sk * L * σ ^ 2 * η ≤ 768 * sk * K * L * σ ^ 2 * η := by
      have : 0 ≤ 768 * sk * L * σ ^ 2 * η := by positivity
      nlinarith
    linarith
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have e : (2 * η ^ 2 * G2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4)) =
      4 * η ^ 2 * G2 * σ ^ 2 / Φ0 + 4 * L ^ 2 * η ^ 4 * K * σ ^ 4 / Φ0 := by
    field_simp
  rw [e, hlam]
  have t1 : 32 * sk / μ * (c * (L * η ^ 2 * σ ^ 2)) ≤ η * Φ / 6 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
    have : 32 * sk * (c * (L * η ^ 2 * σ ^ 2)) * Φ0 ≤ 128 * sk * Φ * L * η ^ 2 * σ ^ 2 := by
      have hp : 0 ≤ 32 * sk * (L * η ^ 2 * σ ^ 2) := by positivity
      nlinarith
    have : 128 * sk * Φ * L * η ^ 2 * σ ^ 2 * 6 ≤ η * Φ * μ * Φ0 := by
      have hp : 0 ≤ η * Φ := by positivity
      nlinarith
    nlinarith
  have t2 : 32 * sk / μ * (4 * η ^ 2 * G2 * σ ^ 2 / Φ0) ≤ η * Φ / 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hμ, mul_div_assoc', div_le_iff₀ hΦ0] at *
    have hp : 0 ≤ 32 * sk * 4 * η ^ 2 * σ ^ 2 := by positivity
    have : 32 * sk * (4 * η ^ 2 * G2 * σ ^ 2) ≤ 32 * sk * 4 * η ^ 2 * σ ^ 2 * (2 * L * Φ) := by
      nlinarith
    have hp2 : 0 ≤ η * Φ := by positivity
    nlinarith
  have t3 : 32 * sk / μ * (4 * L ^ 2 * η ^ 4 * K * σ ^ 4 / Φ0) ≤ η ^ 2 * σ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hμ, mul_div_assoc', div_le_iff₀ hΦ0]
    have hLη : 8 * sk * L * η * K * σ ^ 2 ≤ μ * Φ0 := by
      have : 0 ≤ sk * L * η * K * σ ^ 2 := by positivity
      nlinarith
    have hA : 0 ≤ 8 * sk * L * η * K * σ ^ 2 := by positivity
    have hB : 0 ≤ η ^ 2 * σ ^ 2 := by positivity
    calc 32 * sk * (4 * L ^ 2 * η ^ 4 * K * σ ^ 4)
        = (16 * L * η) * (8 * sk * L * η * K * σ ^ 2) * (η ^ 2 * σ ^ 2) := by ring
      _ ≤ 1 * (μ * Φ0) * (η ^ 2 * σ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ hB
          exact mul_le_mul h1 hLη hA zero_le_one
      _ = η ^ 2 * σ ^ 2 * μ * Φ0 := by ring
  have hsplit : 32 * sk / μ * (c * (L * η ^ 2 * σ ^ 2) +
      (4 * η ^ 2 * G2 * σ ^ 2 / Φ0 + 4 * L ^ 2 * η ^ 4 * K * σ ^ 4 / Φ0)) =
      32 * sk / μ * (c * (L * η ^ 2 * σ ^ 2)) + 32 * sk / μ * (4 * η ^ 2 * G2 * σ ^ 2 / Φ0) +
        32 * sk / μ * (4 * L ^ 2 * η ^ 4 * K * σ ^ 4 / Φ0) := by ring
  rw [hsplit]
  linarith

lemma hub_contract {η μ Φ c hbm hb0 G2 r : ℝ} (hη : 0 < η) (hμ : 0 < μ) (hc0 : 0 ≤ c)
    (hG2' : 2 * μ * Φ ≤ G2) (hconv : hbm + c * (η / 2 * G2) ≤ hb0) (hF2 : hb0 ≤ c * Φ + r) :
    hbm ≤ (1 - μ * η / 2) * hb0 + μ * η / 2 * r - c * (η / 2 * G2) / 2 := by
  have h1 : c * (μ * η * Φ) ≤ c * (η / 2 * G2) := by
    apply mul_le_mul_of_nonneg_left _ hc0; nlinarith
  have h2 : μ * η / 2 * (hb0 - r) ≤ μ * η / 2 * (c * Φ) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

set_option maxHeartbeats 1000000 in
lemma step_alg {η μ L σ K Φ Φ0 D sk lam c hbm hb0 ip G2 r : ℝ}
    (hη : 0 < η) (hμ : 0 < μ) (hL : 0 < L) (hK : 1 ≤ K) (hΦ : 0 ≤ Φ) (hΦ0 : 0 < Φ0)
    (hsk : 1 ≤ sk) (hlam : lam = 32 * sk / μ) (hD : μ * D ≤ 16 * Φ)
    (h1 : 16 * L * η ≤ 1) (h2 : 768 * sk * K * L * σ ^ 2 * η ≤ μ * Φ0)
    (h3 : 196 * sk * L ^ 2 * η ^ 2 ≤ 1)
    (hG2 : G2 ≤ 2 * L * Φ) (hG2' : 2 * μ * Φ ≤ G2) (hc0 : 0 ≤ c) (hc : c ≤ Φ / (Φ0 / 4))
    (hb0nn : 0 ≤ hb0) (hconv : hbm + c * (η / 2 * G2) ≤ hb0) (hF2 : hb0 ≤ c * Φ + r)
    (hcase : (Φ ≤ ip ∧ r ≤ 4 * η ^ 2 * L ^ 2 * Φ) ∨ (-(6 * sk * Φ) ≤ ip ∧ c = 1 ∧ r = 0)) :
    (D - 2 * η * ip + η ^ 2 * G2 + η ^ 2 * σ ^ 2) +
      lam * (hbm + c * (L * η ^ 2 * σ ^ 2) +
        (2 * η ^ 2 * G2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4))) ≤
      (1 - μ * η / 32) * (D + lam * hb0) - η / 2 * Φ + 2 * η ^ 2 * σ ^ 2 := by
  have hcost := cost_common hη hμ hL hK hΦ hΦ0 hsk hlam h1 h2 hG2 hc
  have hcon := hub_contract hη hμ hc0 hG2' hconv hF2
  have hlam0 : 0 ≤ lam := by rw [hlam]; positivity
  have hlamμ : lam * μ = 32 * sk := by rw [hlam]; field_simp
  have hηG : η ^ 2 * G2 ≤ η * Φ / 8 := by
    have : η ^ 2 * G2 ≤ η ^ 2 * (2 * L * Φ) := mul_le_mul_of_nonneg_left hG2 (by positivity)
    have : η ^ 2 * (2 * L * Φ) ≤ η * Φ / 8 := by
      have hp : 0 ≤ η * Φ := by positivity
      nlinarith
    linarith
  have hsplit : lam * (hbm + c * (L * η ^ 2 * σ ^ 2) +
        (2 * η ^ 2 * G2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4))) =
      lam * hbm + lam * (c * (L * η ^ 2 * σ ^ 2) +
        (2 * η ^ 2 * G2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4))) := by ring
  rw [hsplit]
  have hlhbm := mul_le_mul_of_nonneg_left hcon hlam0
  have hdist : lam * ((1 - μ * η / 2) * hb0 + μ * η / 2 * r - c * (η / 2 * G2) / 2) =
      lam * ((1 - μ * η / 2) * hb0) + lam * (μ * η / 2 * r) - lam * (c * (η / 2 * G2) / 2) := by
    ring
  rw [hdist] at hlhbm
  have hgoal : (1 - μ * η / 32) * (D + lam * hb0) - η / 2 * Φ + 2 * η ^ 2 * σ ^ 2 =
      D - μ * η / 32 * D + lam * ((1 - μ * η / 32) * hb0) - η / 2 * Φ + 2 * η ^ 2 * σ ^ 2 := by
    ring
  rw [hgoal]
  have hfinal : -(η * Φ) ≤ -(η / 2 * Φ) - μ * η / 32 * D := by
    have : μ * η / 32 * D ≤ η * Φ / 2 := by
      have := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ η / 32)
      nlinarith
    linarith
  have hhb : lam * ((1 - μ * η / 2) * hb0) ≤ lam * ((1 - μ * η / 32) * hb0) := by
    apply mul_le_mul_of_nonneg_left _ hlam0
    apply mul_le_mul_of_nonneg_right _ hb0nn
    nlinarith
  generalize lam * (c * (L * η ^ 2 * σ ^ 2) +
      (2 * η ^ 2 * G2 * σ ^ 2 + 2 * L ^ 2 * η ^ 4 * (K * σ ^ 4)) / (2 * (Φ0 / 4))) = X at hcost ⊢
  rcases hcase with ⟨hip, hr⟩ | ⟨hip, hc1, hr⟩
  · have hr4 : lam * (μ * η / 2 * r) ≤ 3 / 8 * (η * Φ) := by
      have : lam * (μ * η / 2 * r) = 16 * sk * η * r := by
        have : lam * (μ * η / 2 * r) = (lam * μ) * η / 2 * r := by ring
        rw [this, hlamμ]; ring
      rw [this]
      have : 16 * sk * η * r ≤ 16 * sk * η * (4 * η ^ 2 * L ^ 2 * Φ) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      have : 16 * sk * η * (4 * η ^ 2 * L ^ 2 * Φ) ≤ 3 / 8 * (η * Φ) := by
        have hp : 0 ≤ η * Φ := by positivity
        nlinarith
      linarith
    have hG0 : 0 ≤ G2 := le_trans (by positivity) hG2'
    have hcG : 0 ≤ lam * (c * (η / 2 * G2) / 2) :=
      mul_nonneg hlam0 (div_nonneg (mul_nonneg hc0 (mul_nonneg (by positivity) hG0)) (by norm_num))
    have hipη : η * Φ ≤ η * ip := mul_le_mul_of_nonneg_left hip hη.le
    linarith only [hlhbm, hcost, hhb, hr4, hcG, hηG, hipη, hfinal]
  · have e1 : lam * (μ * η / 2 * r) = 0 := by rw [hr]; ring
    have e2 : lam * (c * (η / 2 * G2) / 2) = lam * η * G2 / 4 := by rw [hc1]; ring
    have hgain : 16 * sk * η * Φ ≤ lam * η * G2 / 4 := by
      have h5 : lam * η * (2 * μ * Φ) ≤ lam * η * G2 :=
        mul_le_mul_of_nonneg_left hG2' (mul_nonneg hlam0 hη.le)
      have h6 : lam * η * (2 * μ * Φ) = 2 * (lam * μ) * η * Φ := by ring
      rw [hlamμ] at h6
      linarith only [h5, h6]
    have hipb : -(2 * η * ip) ≤ 12 * sk * η * Φ := by
      have h7 := mul_le_mul_of_nonneg_left hip (by linarith : (0 : ℝ) ≤ 2 * η)
      have h8 : 2 * η * -(6 * sk * Φ) = -(12 * sk * η * Φ) := by ring
      linarith only [h7, h8]
    have hskΦ : η * Φ ≤ sk * η * Φ := by
      have hp : 0 ≤ η * Φ := mul_nonneg hη.le hΦ
      have h9 := mul_le_mul_of_nonneg_right hsk hp
      linarith only [h9]
    have hp0 : 0 ≤ η * Φ := mul_nonneg hη.le hΦ
    linarith only [hlhbm, e1, e2, hcost, hhb, hgain, hηG, hipb, hskΦ, hfinal, hp0]

end Algebra


section HubFacts

variable {a b : ℝ}

lemma hub_decrease (ha : 0 ≤ a) (hb : 0 < b) {Φ δ : ℝ} (hδ : 0 ≤ δ) :
    hub a b Φ ≤ dhub a b (Φ - δ) * Φ + δ ^ 2 / b := by
  have t1 := hub_tangent (a := a) hb Φ (Φ - δ)
  have t2 := hub_le_dhub_mul ha hb (Φ - δ)
  have t3 := dhub_lip (a := a) hb (show Φ - δ ≤ Φ by linarith)
  have t4 : (dhub a b Φ - dhub a b (Φ - δ)) * δ ≤ (Φ - (Φ - δ)) / b * δ :=
    mul_le_mul_of_nonneg_right t3 hδ
  have e : (Φ - (Φ - δ)) / b * δ = δ ^ 2 / b := by ring
  nlinarith

lemma hub_decrease_far (ha : 0 ≤ a) (hb : 0 < b) {Φ δ : ℝ} (hδ : 0 ≤ δ) (hfar : a + b ≤ Φ - δ) :
    dhub a b (Φ - δ) = 1 ∧ hub a b Φ ≤ dhub a b (Φ - δ) * Φ + 0 := by
  have h1 := dhub_of_ge (a := a) hb (Φ - δ) hfar
  refine ⟨h1, ?_⟩
  rw [h1, hub_of_ge hb Φ (by linarith)]
  linarith

end HubFacts

end OracleTemplate.PLHessian
