import LongTails.Algorithms.RobustGeneralizedAccelerated
import LongTails.Proofs.StochasticGeneralizedTuning

namespace OracleTemplate.RobustGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

lemma radius_pos (p : Params) (hR : 0 < p.R) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    {a : ℝ} (ha : 0 < a) : 0 < radius p a := by
  have hℓ := StochasticGeneralized.confidence_log_gt_one hδ hδ1
  unfold radius confidence
  positivity

lemma correction_variance (p : Params) (hε : 0 < p.ε) {a : ℝ} (ha : 0 < a)
    (hℓ : 0 < confidence p) :
    p.σ^2/(correctionSize p a : ℝ) ≤ p.ε/(1073741824*a*(confidence p)^2) := by
  have hm : 0 < (correctionSize p a : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hb : 1073741824*p.σ^2*a*(confidence p)^2/p.ε ≤ (correctionSize p a : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  apply (div_le_div_iff₀ hm (by positivity)).mpr
  have h := (div_le_iff₀ hε).mp hb
  nlinarith only [h]

lemma pilot_variance (p : Params) {a : ℝ} (hB : 0 < radius p a) :
    (p.σ^2/(pilotSize p a : ℝ))/(radius p a/6)^2 ≤ 1/16 := by
  have hm : 0 < (pilotSize p a : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hb : 576*p.σ^2/(radius p a)^2 ≤ (pilotSize p a : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)
  have h := (div_le_iff₀ (sq_pos_of_pos hB)).mp hb
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < radius p a/6))).mpr
  apply (div_le_iff₀ hm).mpr
  nlinarith only [h]

lemma energy_tuning_small {R a ℓ H : ℝ} (hR : 0 < R) (ha : 0 < a)
    (hℓ : 1 ≤ ℓ) (hH : H ≤ 3*R) :
    (ℓ/R^2)*(a*(3*(R/(64*a*ℓ))/2)*H+8*a^2*(3*(R/(64*a*ℓ))/2)^2) ≤ 1 := by
  have hℓp : 0 < ℓ := by linarith
  have he : (ℓ/R^2)*(a*(3*(R/(64*a*ℓ))/2)*H+
      8*a^2*(3*(R/(64*a*ℓ))/2)^2) = 3*H/(128*R)+9/(2048*ℓ) := by
    field_simp; ring
  rw [he]
  have h1 : 3*H/(128*R) ≤ 9/128 := by
    apply (div_le_iff₀ (by positivity : 0 < 128*R)).mpr
    nlinarith only [hH]
  have h2 : 9/(2048*ℓ) ≤ 9/2048 := by
    apply (div_le_iff₀ (by positivity : 0 < 2048*ℓ)).mpr
    nlinarith only [hℓ]
  linarith

lemma energy_tuning_exponent {R ε a ℓ H v : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (ha : 0 < a) (hℓ : 1 ≤ ℓ) (hH0 : 0 ≤ H) (hH : H ≤ 3*R)
    (hv0 : 0 ≤ v) (hv : v ≤ ε/(1073741824*a*ℓ^2)) :
    (ℓ/R^2)*(a*H*(2*v/(R/(64*a*ℓ)))+14*a^2*v)+
      2*(ℓ/R^2)^2*(a^2*H^2+100*a^4*(3*(R/(64*a*ℓ))/2)^2)*v ≤
      ε*a/(1048576*R^2) := by
  have hℓp : 0 < ℓ := by linarith
  have hmono :
      (ℓ/R^2)*(a*H*(2*v/(R/(64*a*ℓ)))+14*a^2*v)+
        2*(ℓ/R^2)^2*(a^2*H^2+100*a^4*(3*(R/(64*a*ℓ))/2)^2)*v ≤
      (ℓ/R^2)*(a*(3*R)*(2*v/(R/(64*a*ℓ)))+14*a^2*v)+
        2*(ℓ/R^2)^2*(a^2*(3*R)^2+100*a^4*(3*(R/(64*a*ℓ))/2)^2)*v := by
    gcongr
  have he :
      (ℓ/R^2)*(a*(3*R)*(2*v/(R/(64*a*ℓ)))+14*a^2*v)+
        2*(ℓ/R^2)^2*(a^2*(3*R)^2+100*a^4*(3*(R/(64*a*ℓ))/2)^2)*v =
      (402*ℓ^2+14*ℓ+225/2048)*a^2*v/R^2 := by
    field_simp; ring
  apply hmono.trans
  rw [he]
  have hcoef : 402*ℓ^2+14*ℓ+225/2048 ≤ 1024*ℓ^2 := by
    nlinarith [sq_nonneg (ℓ-1)]
  calc
    _ ≤ (1024*ℓ^2)*a^2*v/R^2 := by gcongr
    _ ≤ (1024*ℓ^2)*a^2*(ε/(1073741824*a*ℓ^2))/R^2 := by gcongr
    _ = _ := by field_simp; ring

end OracleTemplate.RobustGeneralized
