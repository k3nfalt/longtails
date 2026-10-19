import LongTails.Proofs.SymmetricReverseFisherBudget
import LongTails.Proofs.SymmetricReverseFisherExecution
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherAccuracy
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory
open LongTails.Proofs.SymmetricReverseFisherContraction
open LongTails.Proofs.SymmetricReverseFisherBudget
lemma small_accuracy_public {p : Params} (μ x : Space p) {d s B δ ε : ℝ}
    (hd : 1 ≤ d) (hs : 0 ≤ s) (hsa : s ≤ ‖μ‖) (haB : ‖μ‖ ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (haε : ‖μ‖^2 ≤ ε/10000) (hx : ‖x‖ = 1) :
    ‖(gdStep μ (1/(48+20*B)))^[iterations d s B δ ε] x - μ‖^2 ≤ ε := by
  have hB : 0 ≤ B := (norm_nonneg μ).trans haB
  have hη : 0 < 1/(48+20*B) := by positivity
  have hη48 : 1/(48+20*B) ≤ 1/48 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hsε : s^2 ≤ ε := by nlinarith
  exact iterate_small_signal_accuracy μ x hη hη48 hε hε1 hx haε
    (small_budget_cost hd hB hδ hδ1 hε hε1 hsε)
lemma axis_positive_accuracy {p : Params} (e x : Space p) {d s a B δ ε : ℝ}
    (hd : 1 ≤ d) (hs : 0 ≤ s) (hsa : s ≤ a) (haB : a ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (haε : ε/10000 < a^2) (he : ‖e‖ = 1) (hx : ‖x‖ = 1)
    (hζ : δ/d ≤ ⟪x,e⟫) :
    ‖(gdStep (a • e) (1/(48+20*B)))^[iterations d s B δ ε] x - a • e‖^2 ≤ ε := by
  have ha : 0 < a := by nlinarith
  have hB : 0 ≤ B := ha.le.trans haB
  let η := 1/(48+20*B)
  let m := signalStrength a
  let L := Real.log (logArgument d B δ ε)
  let n₁ := ⌈2/(η*m)*Real.log (1/⟪x,e⟫)⌉₊
  let n₂ := ⌈4/(η*m)*Real.log (1/⟪x,e⟫)⌉₊
  let J := ⌈2880/(η*m)*L⌉₊
  let K := iterations d s B δ ε
  let k := K-(n₁+n₂)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη48 : η ≤ 1/48 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hηL : η*(48+20*a) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (show 48+20*a ≤ 48+20*B by linarith) hη.le
    have hc : η*(48+20*B) = 1 := by dsimp [η]; field_simp
    linarith
  have hζ0 : 0 < ⟪x,e⟫ := (div_pos hδ (by linarith : 0<d)).trans_le hζ
  have hζ1 : ⟪x,e⟫ ≤ 1 := by simpa only [hx,he,mul_one] using real_inner_le_norm x e
  have hcost : n₁+n₂+J ≤ K := positive_budget_cost hd hs hsa haB hδ hδ1 hε hε1 haε hζ hζ1
  have hK : n₁+n₂ ≤ K := by omega
  have hsum : n₁+n₂+k = K := Nat.add_sub_of_le hK
  have hkJ : J ≤ k := by dsimp [k]; omega
  have hb := positive_signal_bound e x he ha hη hη48 hηL hζ0 hx
    (show 2/(η*signalStrength a)*Real.log (1/⟪x,e⟫) ≤ n₁ from Nat.le_ceil _)
    (show 4/(η*signalStrength a)*Real.log (1/⟪x,e⟫) ≤ n₂ from Nat.le_ceil _) k
  rw [hsum] at hb
  have hk : 2880/(η*signalStrength a)*Real.log (logArgument d B δ ε) ≤ (k:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hkJ)
  have hH : 0 < logArgument d B δ ε := by
    have h := (logArgument_bounds hd hB hδ hδ1 hε hε1).1
    linarith
  have ht := exponential_tail_accuracy hH hη (strength_bounds ha).1 hε.le
    (prefactor_absorbed hd ha.le haB hδ hδ1 hε hε1 haε) hk
  have hn := hb.trans ht
  nlinarith [norm_nonneg ((gdStep (a • e) η)^[K] x - a • e)]
open LongTails.Proofs.SymmetricReverseFisherExecution
lemma accuracy_of_projection {p : Params} (μ x : Space p) {d s B δ ε : ℝ}
    (hd : 1 ≤ d) (hs : 0 ≤ s) (hsa : s ≤ ‖μ‖) (haB : ‖μ‖ ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hμ : μ ≠ 0) (hx : ‖x‖ = 1) (hζ : δ/d ≤ |⟪x, ‖μ‖⁻¹ • μ⟫|) :
    min (‖(gdStep μ (1/(48+20*B)))^[iterations d s B δ ε] x - μ‖^2)
      (‖(gdStep μ (1/(48+20*B)))^[iterations d s B δ ε] x + μ‖^2) ≤ ε := by
  by_cases haε : ‖μ‖^2 ≤ ε/10000
  · exact (min_le_left _ _).trans (small_accuracy_public μ x hd hs hsa haB hδ hδ1 hε hε1 haε hx)
  have haε' : ε/10000 < ‖μ‖^2 := lt_of_not_ge haε
  have ha : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
  let e := ‖μ‖⁻¹ • μ
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, inv_mul_cancel₀ ha.ne']
  have hμe : ‖μ‖ • e = μ := by dsimp [e]; rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  change δ/d ≤ |⟪x,e⟫| at hζ
  by_cases hsign : 0 ≤ ⟪x,e⟫
  · have hp : δ/d ≤ ⟪x,e⟫ := by simpa only [abs_of_nonneg hsign] using hζ
    have hh := axis_positive_accuracy e x hd hs hsa haB hδ hδ1 hε hε1 haε' he hx hp
    rw [hμe] at hh
    exact (min_le_left _ _).trans hh
  · have hp : δ/d ≤ ⟪x,-e⟫ := by
      rw [inner_neg_right]
      simpa only [abs_of_neg (lt_of_not_ge hsign)] using hζ
    have he' : ‖-e‖ = 1 := by simpa only [norm_neg] using he
    have hh := axis_positive_accuracy (-e) x hd hs hsa haB hδ hδ1 hε hε1 haε' he' hx hp
    have hneg : ‖μ‖ • (-e) = -μ := by rw [smul_neg, hμe]
    rw [hneg, iterate_neg_parameter, sub_neg_eq_add] at hh
    exact (min_le_right _ _).trans hh
end LongTails.Proofs.SymmetricReverseFisherAccuracy
