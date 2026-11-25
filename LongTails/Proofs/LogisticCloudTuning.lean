import LongTails.Setups.LogisticDefectCloud
import LongTails.Proofs.LogisticCloudDrift

open LongTails.Setups.LogisticDefectCloud
open LongTails.Proofs.LogisticCloudDrift

namespace LongTails.Proofs.LogisticCloudTuning

noncomputable def rate (p : Params) := 1/(2^48*(p.a+p.μ))
noncomputable def radius (p : Params) := p.r*Real.sqrt p.L
noncomputable def small (p : Params) := p.a*p.μ*p.ρ/(2^20*(p.d+2 : ℝ))
noncomputable def projectionSize (p : Params) := p.ρ^2/(32*(p.d+2 : ℝ))
noncomputable def amplification (p : Params) := 1/(small p)^3
noncomputable def entryTime (p : Params) :=
  ⌈Real.log (amplification p)/Real.log (1+rate p*p.μ/4)⌉₊
noncomputable def lowTime (p : Params) :=
  ⌈Real.log (1024/radius p)/Real.log (1+rate p*p.μ/80)⌉₊
noncomputable def highTime (p : Params) := ⌈4/(rate p*p.μ)⌉₊

noncomputable def scales (p : Params) (hp : spec.valid p) : Scales := by
  have hμ := hp.2.2.1
  have hμ' := hp.2.2.2.1
  have ha := hp.2.2.2.2.1
  have ha' := hp.2.2.2.2.2.1
  refine ⟨p.a,p.μ,Real.sqrt (1-p.a^2),rate p,ha,ha',hμ,hμ',?_,?_,?_,?_⟩
  · have h := mul_nonneg (sub_nonneg.mpr ha') (show 0 ≤ 1/16+p.a by linarith)
    exact (Real.le_sqrt (by norm_num) (by nlinarith : 0 ≤ 1-p.a^2)).mpr (by nlinarith)
  · apply Real.sqrt_le_one.mpr
    linarith [sq_nonneg p.a]
  · dsimp [rate]; positivity
  · dsimp [rate]
    rw [div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by norm_num)]
    exact le_of_eq (by ring)

lemma tiny (p : Params) (hp : spec.valid p) :
    0 < small p ∧ small p ≤ p.a / 2^20 ∧ 0 < radius p ∧ radius p ≤ (small p)^4 ∧
    2^34*(small p)^2 ≤ p.a*p.μ*projectionSize p := by
  obtain ⟨_,hL,hμ,hμ',ha,ha',hρ,hρ',hr,hR⟩ := hp
  let D : ℝ := p.d+2
  have hD : 1 ≤ D := by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) p.d]
  have hD' : 0 < D := by linarith
  have hm : p.μ*p.ρ ≤ D := by
    nlinarith [mul_le_mul hμ' hρ'.le hρ.le (by norm_num : (0:ℝ) ≤ 1/10)]
  refine ⟨by dsimp [small]; positivity,?_,by dsimp [radius]; positivity,hR,?_⟩
  · change p.a*p.μ*p.ρ/(2^20*D) ≤ _
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hm ha.le]
  · change 2^34*(p.a*p.μ*p.ρ/(2^20*D))^2 ≤ p.a*p.μ*(p.ρ^2/(32*D))
    have ham : p.a*p.μ ≤ 2*D := by
      nlinarith [mul_le_mul ha' hμ' hμ.le (by norm_num : (0:ℝ) ≤ 1/16)]
    field_simp [hD'.ne']
    nlinarith only [ham]

lemma logarithmic_stage {δ c M : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hδ' : δ ≤ c) (hM : 1 ≤ M) :
    (⌈Real.log M / Real.log (1+δ/c)⌉₊:ℝ)*δ ≤ 2*c*Real.log M+δ := by
  have hx := div_pos hδ hc
  have hx' := (div_le_one hc).mpr hδ'
  have hlog := Real.le_log_one_add_of_nonneg hx.le
  have hlow : δ/c/2 ≤ Real.log (1+δ/c) := by
    apply le_trans _ hlog
    apply (le_div_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hx' hx.le]
  have hlog' : 0 < Real.log (1+δ/c) := by linarith
  have hm := Real.log_nonneg hM
  have H := Nat.ceil_lt_add_one (div_nonneg hm hlog'.le)
  have hfrac : Real.log M/Real.log (1+δ/c)*δ ≤ 2*c*Real.log M := by
    rw [div_mul_eq_mul_div,div_le_iff₀ hlog']
    have H₁ : δ ≤ 2*c*Real.log (1+δ/c) := by
      have H₂ := (div_le_iff₀ hc).mp (show δ/c ≤ 2*Real.log (1+δ/c) by linarith)
      linarith
    nlinarith only [mul_le_mul_of_nonneg_left H₁ hm]
  nlinarith only [hfrac,mul_le_mul_of_nonneg_right H.le hδ.le]

lemma warmup_horizon {q M : ℝ} (hq : 1 < q) (hq' : q ≤ 2) (hM : 1 ≤ M) :
    let n := ⌈Real.log M / Real.log q⌉₊
    M ≤ q ^ n ∧ q ^ n ≤ 2 * M := by
  intro n
  have hq₀ : 0 < q := by linarith
  have hM₀ : 0 < M := by linarith
  have hl := Real.log_pos hq
  have hratio := div_nonneg (Real.log_nonneg hM) hl.le
  have hlo : Real.log M ≤ n * Real.log q :=
    (div_le_iff₀ hl).mp (Nat.le_ceil _)
  have hhi : (n : ℝ) ≤ Real.log M / Real.log q + 1 := (Nat.ceil_lt_add_one hratio).le
  have hlog : Real.log (q ^ n) ≤ Real.log (q * M) := by
    rw [Real.log_pow, Real.log_mul hq₀.ne' hM₀.ne']
    have H := mul_le_mul_of_nonneg_right hhi hl.le
    rw [add_mul, div_mul_cancel₀ _ hl.ne'] at H
    linarith
  refine ⟨(Real.log_le_log_iff hM₀ (pow_pos hq₀ _)).mp (by rwa [Real.log_pow]), ?_⟩
  exact ((Real.log_le_log_iff (pow_pos hq₀ _) (mul_pos hq₀ hM₀)).mp hlog).trans
    (mul_le_mul_of_nonneg_right hq' hM₀.le)

end LongTails.Proofs.LogisticCloudTuning
