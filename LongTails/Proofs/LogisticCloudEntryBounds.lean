import LongTails.Proofs.LogisticCloudTuning
import LongTails.Proofs.LogisticCloudCone

open LongTails.Setups.LogisticDefectCloud
open LongTails.Proofs.LogisticCloudTuning
open LongTails.Proofs.LogisticCloudCone

namespace LongTails.Proofs.LogisticCloudEntryBounds

lemma amplification_bounds {a μ κ b r : ℝ} (ha : 0 < a) (ha' : a ≤ 1)
    (hμ : 0 < μ) (hμ' : μ ≤ 1) (hκ : 0 < κ) (hb : 0 < b)
    (hb' : b ≤ 1) (hr : 0 ≤ r) (hr' : r ≤ b^4) (hc : 2^34*b^2 ≤ a*μ*κ)
    {F : ℝ} (hF : 0 ≤ F) (hF' : F ≤ 2/b^3) :
    r*F ≤ 2*b ∧ 256*r^3/μ*F^2 ≤ a*κ*r/128 ∧
    (1/b^3 ≤ F → 4096 ≤ μ*κ*F ∧ 4096 ≤ a*κ*F) := by
  have hb3 := pow_pos hb 3
  have hsmall : r*F ≤ 2*b := by
    apply (mul_le_mul hr' hF' hF (pow_nonneg hb.le 4)).trans
    exact le_of_eq (by field_simp)
  have hh := pow_le_pow_left₀ (mul_nonneg hr hF) hsmall 2
  refine ⟨hsmall,?_,?_⟩
  · rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
    nlinarith only [mul_le_mul_of_nonneg_left hh hr,mul_le_mul_of_nonneg_right hc hr,
      mul_nonneg (mul_nonneg ha.le hμ.le) (mul_nonneg hκ.le hr)]
  · intro hF₀
    have hscale : 1 ≤ F*b^3 := (div_le_iff₀ hb3).mp hF₀
    have h22 : b^3 ≤ b^2 := by nlinarith [mul_le_mul_of_nonneg_right hb' (sq_nonneg b)]
    have hm := mul_le_mul_of_nonneg_right hc hF
    have hm' := mul_le_mul_of_nonneg_left h22 hF
    have hA := mul_le_mul_of_nonneg_right ha' (mul_nonneg (mul_nonneg hμ.le hκ.le) hF)
    have hM := mul_le_mul_of_nonneg_right hμ' (mul_nonneg (mul_nonneg ha.le hκ.le) hF)
    exact ⟨by nlinarith only [hscale,hm,hm',hA],by nlinarith only [hscale,hm,hm',hM]⟩

lemma numerical_entry {a β P T E r μ : ℝ} (ha : 0 < a) (ha' : a ≤ 1/16)
    (hβ : 4/5 ≤ β) (hβ' : β ≤ 1) (hP : 0 < P) (hT : 0 < T) (hμ : 0 < μ)
    (eP : E ≤ a*P/64) (eT : E ≤ a*T/64)
    (floorP : 4096*r ≤ μ*P) (floorT : 4096*r ≤ μ*T) (x : Point)
    (hp : |x.p-P| ≤ E) (hq : |x.q+a*P| ≤ E) (hu : |x.u-β*P| ≤ E)
    (ht : |x.t-T| ≤ E) (hv : |x.v-T| ≤ E) :
    Cone a x ∧ x.q ≤ 0 ∧ 320*r ≤ μ*mass x ∧ 64*r ≤ μ*x.v ∧ P/2 ≤ mass x := by
  obtain ⟨hp₁,hp₂⟩ := abs_le.mp hp
  obtain ⟨hq₁,hq₂⟩ := abs_le.mp hq
  obtain ⟨hu₁,hu₂⟩ := abs_le.mp hu
  obtain ⟨ht₁,ht₂⟩ := abs_le.mp ht
  obtain ⟨hv₁,hv₂⟩ := abs_le.mp hv
  have hA := mul_le_mul_of_nonneg_right ha' hP.le
  have hB := mul_le_mul_of_nonneg_right ha' hT.le
  have hC := mul_le_mul_of_nonneg_right hβ hP.le
  have hD := mul_le_mul_of_nonneg_right hβ' hP.le
  have hfloor : P/2 ≤ x.p := by linarith
  have hU : P/2 ≤ x.p+x.q+x.u := by linarith
  have hV : T/2 ≤ x.v := by linarith
  dsimp [mass]
  refine ⟨⟨by linarith,?_,by linarith,by linarith,by linarith,by linarith,by linarith⟩,
    by linarith [mul_pos ha hP],?_,?_,hU⟩
  · nlinarith [mul_le_mul_of_nonneg_left hfloor ha.le,mul_pos ha hP]
  · nlinarith only [floorP,mul_le_mul_of_nonneg_left hU hμ.le,mul_pos hμ hP]
  · nlinarith only [floorT,mul_le_mul_of_nonneg_left hV hμ.le,mul_pos hμ hT]

lemma tuning_facts (p : Params) (hp : spec.valid p) :
    let g := 1+rate p*p.μ/4
    let F := g^(entryTime p)
    let b := small p
    let r := radius p
    let κ := projectionSize p
    0 < b ∧ b ≤ 1 ∧ 0 < κ ∧ κ ≤ 1 ∧ 1 ≤ F ∧
    amplification p ≤ F ∧ F ≤ 2/b^3 ∧ r*F ≤ 2*b ∧
    256*r^3/p.μ*F^2 ≤ p.a*κ*r/128 ∧ 4096 ≤ p.μ*κ*F ∧ 4096 ≤ p.a*κ*F := by
  intro g F b r κ
  obtain ⟨hb,hs,hr,hR,hc⟩ := tiny p hp
  have ha : 0 < p.a := (scales p hp).ha
  have ha' : p.a ≤ 1/16 := (scales p hp).ha'
  have hμ : 0 < p.μ := (scales p hp).hμ
  have hμ' : p.μ ≤ 1/10 := (scales p hp).hμ'
  have hη : 0 < rate p := (scales p hp).hη
  have hη' : rate p*(p.a+p.μ) ≤ 1/2^48 := (scales p hp).tune
  have ρ := hp.2.2.2.2.2.2.1
  have ρ' := hp.2.2.2.2.2.2.2.1
  have hκ : 0 < κ := by dsimp [κ,projectionSize]; positivity
  have hκ' : κ ≤ 1 := by
    dsimp [κ,projectionSize]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul ρ'.le ρ'.le ρ.le (by norm_num : (0:ℝ) ≤ 1), Nat.cast_nonneg (α:=ℝ) p.d]
  have hb' : b ≤ 1 := by change small p ≤ 1; linarith
  have hM : 1 ≤ amplification p := by
    dsimp [amplification]
    rw [le_div_iff₀ (pow_pos hb 3)]
    simpa only [one_mul] using (pow_le_one₀ hb.le hb' (n:=3))
  have hg : 1 < g := by dsimp [g]; nlinarith [mul_pos hη hμ]
  have hg' : g ≤ 2 := by dsimp [g]; nlinarith [mul_pos hη ha]
  obtain ⟨hl,hu⟩ := warmup_horizon hg hg' hM
  change amplification p ≤ F at hl
  change F ≤ 2*(1/b^3) at hu
  rw [mul_one_div] at hu
  have B := amplification_bounds ha (by linarith) hμ (by linarith) hκ hb hb'
    hr.le hR hc (zero_le_one.trans (hM.trans hl)) hu
  exact ⟨hb,hb',hκ,hκ',hM.trans hl,hl,hu,B.1,B.2.1,(B.2.2 hl).1,(B.2.2 hl).2⟩

end LongTails.Proofs.LogisticCloudEntryBounds
