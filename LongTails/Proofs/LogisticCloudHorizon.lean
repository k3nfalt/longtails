import LongTails.Proofs.LogisticCloudTuning
import Mathlib.Analysis.Complex.ExponentialBounds

open LongTails.Setups.LogisticDefectCloud
open LongTails.Proofs.LogisticCloudTuning

namespace LongTails.Proofs.LogisticCloudHorizon

lemma horizons (p : Params) (hp : spec.valid p) :
    let δ := rate p*p.μ
    640*Real.sqrt p.a ≤ (1+δ/80)^lowTime p*radius p ∧
    4 ≤ (highTime p:ℝ)*δ ∧ (1+δ)^highTime p ≤ 512 ∧
    entryTime p+lowTime p+highTime p ≤
      ⌈2^58*(1+p.a/p.μ)*Real.log (1/radius p)⌉₊ := by
  intro δ
  obtain ⟨hb,hb',hr,hR,_⟩ := tiny p hp
  have ha : p.a ≤ 1/16 := (scales p hp).ha'
  have ha₀ : 0 < p.a := (scales p hp).ha
  have hμ : 0 < p.μ := (scales p hp).hμ
  have hη : 0 < rate p := (scales p hp).hη
  have hδ : 0 < δ := mul_pos hη hμ
  have hδ' : δ ≤ 1 := by
    change rate p*p.μ ≤ 1
    have ht : rate p*(p.a+p.μ) ≤ 1/2^48 := (scales p hp).tune
    nlinarith [mul_pos hη ha₀]
  have hb₁ : small p ≤ 1 := by linarith
  have hR₁ : radius p ≤ 1/1024 := by
    have H := pow_le_pow_of_le_one hb.le hb₁ (show 1 ≤ 4 by decide)
    simp only [pow_one] at H
    linarith
  have h M (hc : M*radius p ≤ 1) : M ≤ 1/radius p :=
    (le_div_iff₀ hr).mpr hc
  have hbig : 1024 ≤ 1/radius p := h _ (by linarith)
  have hM : 1 ≤ 1024/radius p := (le_div_iff₀ hr).mpr (by linarith)
  have hA : 1 ≤ amplification p := by
    exact (le_div_iff₀ (pow_pos hb 3)).mpr (by simpa using pow_le_one₀ hb.le hb₁ (n:=3))
  have hA' : amplification p ≤ 1/radius p := by
    apply one_div_le_one_div_of_le hr
    exact hR.trans (pow_le_pow_of_le_one hb.le hb₁ (show 3 ≤ 4 by decide))
  have hw := (warmup_horizon (q:=1+δ/80) (by linarith) (by linarith) hM).1
  change 1024/radius p ≤ (1+δ/80)^lowTime p at hw
  have hJ : 4/δ ≤ (highTime p:ℝ) := Nat.le_ceil _
  have hJ' : (highTime p:ℝ) < 4/δ+1 := Nat.ceil_lt_add_one (by positivity)
  have hJδ := (div_le_iff₀ hδ).mp hJ
  have hJδ' : (highTime p:ℝ)*δ ≤ 5 := by
    have H := mul_le_mul_of_nonneg_right hJ'.le hδ.le
    rw [add_mul,div_mul_cancel₀ _ hδ.ne'] at H
    linarith
  refine ⟨?_,hJδ,?_,?_⟩
  · have H := (div_le_iff₀ hr).mp hw
    linarith [Real.sqrt_le_one.mpr (show p.a ≤ 1 by linarith)]
  · have H := pow_le_pow_left₀ (show 0 ≤ 1+δ by linarith)
      (show 1+δ ≤ Real.exp δ by linarith [Real.add_one_le_exp δ]) (highTime p)
    rw [← Real.exp_nat_mul] at H
    refine H.trans ((Real.exp_le_exp.mpr hJδ').trans ?_)
    have H' := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 5
    rw [← Real.exp_nat_mul] at H'
    norm_num at H' ⊢
    linarith
  · let l := Real.log (1/radius p)
    have hl : 1 ≤ l := by
      apply (Real.le_log_iff_exp_le (by positivity)).mpr
      linarith [Real.exp_one_lt_three]
    have hla : Real.log (amplification p) ≤ l := Real.log_le_log (by linarith) hA'
    have hlm : Real.log (1024/radius p) ≤ 2*l := by
      rw [show (1024:ℝ)/radius p = 1024*(1/radius p) by ring, Real.log_mul (by norm_num) (by positivity)]
      linarith [Real.log_le_log (by norm_num : (0:ℝ)<1024) hbig]
    have HE := logarithmic_stage hδ (by norm_num : (0:ℝ)<4) (by linarith) hA
    have HK := logarithmic_stage hδ (by norm_num : (0:ℝ)<80) (by linarith) hM
    change (entryTime p:ℝ)*δ ≤ _ at HE
    change (lowTime p:ℝ)*δ ≤ _ at HK
    have H : ((entryTime p+lowTime p+highTime p:ℕ):ℝ)*δ ≤ 1024*l := by
      push_cast
      linarith
    apply (Nat.cast_le (α := ℝ)).mp
    refine le_trans ?_ (Nat.le_ceil _)
    apply (mul_le_mul_iff_of_pos_right hδ).mp
    refine H.trans_eq ?_
    change 1024*l = 2^58*(1+p.a/p.μ)*l*(1/(2^48*(p.a+p.μ))*p.μ)
    field_simp [hμ.ne', (add_pos ha₀ hμ).ne']
    ring

end LongTails.Proofs.LogisticCloudHorizon
