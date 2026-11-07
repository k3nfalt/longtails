import LongTails.Proofs.HeavyTailSaddleRecovery
import LongTails.Proofs.StochasticEnvelopeExecution
open scoped BigOperators
open LongTails.Algorithms.HeavyTailSaddleEstimator
namespace LongTails.Proofs.HeavyTailSaddleCost
lemma conjugate_exponent_bounds {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    2 ≤ p/(p-1) ∧ 1/(p-1)=p/(p-1)-1 ∧ p*(1/(p-1))=p/(p-1) := by
  have hd : 0 < p-1 := by linarith
  refine ⟨(le_div_iff₀ hd).mpr (by nlinarith),?_,?_⟩
  · field_simp
    ring
  · ring
lemma log_two_bounds : (1:ℝ)/2 ≤ Real.log 2 ∧ Real.log 2 ≤ 1 := by
  constructor
  · have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  · have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
lemma log_le_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  have hh := Real.log_le_sub_one_of_pos (div_pos hs (by norm_num : (0:ℝ)<2))
  rw [Real.log_div (ne_of_gt hs) (by norm_num)] at hh
  rw [Real.log_sqrt hx.le] at hh
  nlinarith [log_two_bounds.2]
lemma recovery_mass_upper {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L)
    {j : ℕ} (hj : j < recoveryStages L μ) : recoveryMass μ j ≤ 30*L := by
  have hL : 0 < L := hm.trans_le hmL
  have ht := (LongTails.Proofs.HeavyTailSaddleRecovery.recovery_terminal_mass hm
    (show μ ≤ 15*L by linarith)).2
  have hh : (2:ℝ)^j ≤ 2^(recoveryStages L μ-1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact (mul_le_mul_of_nonneg_right hh hm.le).trans ht
lemma recovery_stages_log_bound {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) :
    (recoveryStages L μ : ℝ) ≤ 6+2*Real.log (L/μ) := by
  have hk : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hkp : 0 < L/μ := lt_of_lt_of_le (by norm_num) hk
  have hratio : 1 ≤ 15*L/μ := by rw [mul_div_assoc]; nlinarith
  have hl2 := log_two_bounds.1
  have hl2p : 0 < Real.log 2 := by linarith
  have hl15 : Real.log 15 ≤ 4*Real.log 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<15) (show (15:ℝ) ≤ 2^4 by norm_num)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hh
  have hlk := Real.log_nonneg hk
  have hb : Real.logb 2 (15*L/μ) ≤ 4+2*Real.log (L/μ) := by
    rw [Real.logb,div_le_iff₀ hl2p]
    rw [mul_div_assoc,Real.log_mul (by norm_num : (15:ℝ) ≠ 0) hkp.ne']
    nlinarith [mul_le_mul_of_nonneg_right hl2 hlk]
  have hn : 0 ≤ Real.logb 2 (15*L/μ) := by
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hratio) hl2p.le
  have hc := (Nat.ceil_lt_add_one hn).le
  unfold recoveryStages
  rw [max_eq_right hratio]
  push_cast
  linarith
lemma recovery_stages_sqrt_bound {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) :
    (recoveryStages L μ : ℝ) ≤ 8*Real.sqrt (L/μ) := by
  have hk : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hs : 1 ≤ Real.sqrt (L/μ) := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hl := log_le_sqrt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hk)
  linarith [recovery_stages_log_bound hm hmL]
lemma horizon_cost_bound {L m κ Λ : ℝ} (hκ : 1 ≤ κ) (hΛ : 1 ≤ Λ)
    (hratio : L/m ≤ 3*κ) (hlog : Real.log κ ≤ Λ) :
    (kernelHorizon L m : ℝ)+1 ≤ 1024*Λ := by
  have hkp : 0 < κ := by linarith
  have hb : (1:ℝ)/32 ≤ Real.log (32/31) := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<32/31)
    norm_num at hh ⊢
    exact hh
  have hbp : 0 < Real.log (32/31) := by linarith
  have ha : max 1 ((2:ℝ)^18*L/m) ≤ (2:ℝ)^18*3*κ := by
    apply max_le
    · nlinarith
    · have hh := mul_le_mul_of_nonneg_left hratio (show (0:ℝ) ≤ 2^18 by positivity)
      simpa only [mul_div_assoc,mul_assoc] using hh
  have halog : Real.log (max 1 ((2:ℝ)^18*L/m)) ≤ 20+Λ := by
    have hh := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)) ha
    rw [Real.log_mul (by positivity : (2:ℝ)^18*3 ≠ 0) hkp.ne',
      Real.log_mul (by positivity : (2:ℝ)^18 ≠ 0) (by norm_num : (3:ℝ) ≠ 0),Real.log_pow] at hh
    have hthree := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_two_bounds.2]
  have hlognonneg : 0 ≤ Real.log (max 1 ((2:ℝ)^18*L/m)) := Real.log_nonneg (le_max_left _ _)
  have hc := (Nat.ceil_lt_add_one (div_nonneg hlognonneg hbp.le)).le
  have hq : Real.log (max 1 ((2:ℝ)^18*L/m))/Real.log (32/31) ≤ 32*(20+Λ) := by
    apply (div_le_iff₀ hbp).mpr
    have hh := mul_le_mul_of_nonneg_right hb (show 0 ≤ 20+Λ by linarith)
    nlinarith
  change (⌈Real.logb (32/31) (max 1 ((2:ℝ)^18*L/m))⌉₊ : ℝ)+1 ≤ _
  rw [Real.logb]
  linarith

lemma depth_cost_bound {p σ m B s Λ : ℝ} (hr : 2 ≤ p/(p-1)) (hσ : 0 ≤ σ)
    (ha : 0 < Real.sqrt (m*B)) (hscale : σ/Real.sqrt (m*B) ≤ 2*s)
    (hΛ : 1 ≤ Λ) (hlog : Real.log (max 1 s) ≤ Λ) :
    (kernelDepth p σ m B : ℝ)+1 ≤ 32*(p/(p-1))*Λ := by
  let r := p/(p-1)
  let a := (2:ℝ)^24*σ/Real.sqrt (m*B)
  let b := (2:ℝ)^25*max 1 s
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb1 : 1 ≤ b := by dsimp [b]; nlinarith [le_max_left (1:ℝ) s]
  have hab : a ≤ b := by
    have hh := mul_le_mul_of_nonneg_left hscale (show (0:ℝ) ≤ 2^24 by positivity)
    have hs := le_max_right (1:ℝ) s
    dsimp [a,b]
    rw [mul_div_assoc]
    nlinarith
  have hpow : max 1 (a^r) ≤ b^r :=
    max_le (Real.one_le_rpow hb1 hr0) (Real.rpow_le_rpow ha0 hab hr0)
  have hmaxp : 0 < max 1 (a^r) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hl := Real.log_le_log hmaxp hpow
  rw [Real.log_rpow (lt_of_lt_of_le (by norm_num) hb1)] at hl
  have hblog : Real.log b = 25*Real.log 2+Real.log (max 1 s) := by
    dsimp [b]
    rw [Real.log_mul (by positivity : (2:ℝ)^25 ≠ 0)
      (ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_left _ _))),Real.log_pow]
    norm_num
  rw [hblog] at hl
  have hl2 := log_two_bounds.1
  have hl2p : 0 < Real.log 2 := by linarith
  have hb : Real.logb 2 (max 1 (a^r)) ≤ 25*r+2*r*Λ := by
    rw [Real.logb,div_le_iff₀ hl2p]
    have h1 := mul_le_mul_of_nonneg_left hlog hr0
    have h2 := mul_le_mul_of_nonneg_right hl2 (show 0 ≤ r*Λ by positivity)
    nlinarith
  have hn := Real.logb_nonneg (by norm_num : (1:ℝ)<2) (le_max_left 1 (a^r))
  have hc := (Nat.ceil_lt_add_one hn).le
  have hmul := mul_le_mul_of_nonneg_left hΛ hr0
  change (⌈Real.logb 2 (max 1 (a^r))⌉₊ : ℝ)+1 ≤ 32*r*Λ
  have hr2 : 2 ≤ r := hr
  nlinarith

lemma batch_scale_identity {p c σ a b : ℝ} (hp : 1 < p) (hc : 0 < c)
    (hσ : 0 ≤ σ) (ha : 0 < a) (hb : 0 < b) :
    (c*σ^p/(a*b^(p-1)))^(1/(p-1))*(b/a) = c^(1/(p-1))*(σ/a)^(p/(p-1)) := by
  have hd : 0 < p-1 := by linarith
  have hr : 0 < p/(p-1) := div_pos (by linarith) hd
  have hq : 0 < 1/(p-1) := by positivity
  by_cases hs : σ=0
  · simp only [hs,Real.zero_rpow (by linarith : p ≠ 0),mul_zero,zero_div,
      Real.zero_rpow hq.ne',Real.zero_rpow hr.ne',zero_mul]
  · have hspos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hs)
    apply Real.log_injOn_pos (by change (0:ℝ) < _; positivity) (by change (0:ℝ) < _; positivity)
    simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_rpow]
    field_simp
    ring
lemma kernel_batch_scaled_bound {p σ m H B : ℝ} (hp : 1 < p) (hσ : 0 ≤ σ)
    (ha : 0 < Real.sqrt (m*B)) (hb : 0 < Real.sqrt (H*B)) (J : ℕ) :
    (kernelBatch p σ m H B J : ℝ)*(Real.sqrt (H*B)/Real.sqrt (m*B)) ≤
      2*(Real.sqrt (H*B)/Real.sqrt (m*B))+
      ((2:ℝ)^36*(J+1))^(1/(p-1))*(σ/Real.sqrt (m*B))^(p/(p-1)) := by
  have hi := batch_scale_identity hp (show (0:ℝ)<2^36*(J+1) by positivity) hσ ha hb
  have hn : 0 ≤ ((2:ℝ)^36*((J+1)*σ^p)/(Real.sqrt (m*B)*(Real.sqrt (H*B))^(p-1)))^(1/(p-1)) :=
    Real.rpow_nonneg (by positivity) _
  have hc := (Nat.ceil_lt_add_one hn).le
  have hh := mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.sqrt (H*B)/Real.sqrt (m*B) by positivity)
  have hi' : ((2:ℝ)^36*((J+1)*σ^p)/(Real.sqrt (m*B)*(Real.sqrt (H*B))^(p-1)))^(1/(p-1))*
      (Real.sqrt (H*B)/Real.sqrt (m*B)) =
      ((2:ℝ)^36*(J+1))^(1/(p-1))*(σ/Real.sqrt (m*B))^(p/(p-1)) := by
    simpa only [mul_assoc] using hi
  unfold kernelBatch
  push_cast
  nlinarith

lemma doubling_sum_bound (w : ℕ → ℝ) (K : ℕ) (h0 : ∀ j, 0 ≤ w j)
    (hs : ∀ j, j+1 < K → 2*w j ≤ w (j+1)) :
    ∑ j ∈ Finset.range K,w j ≤ 2*w (K-1) := by
  cases K with
  | zero => simpa using mul_nonneg (by norm_num : (0:ℝ)≤2) (h0 0)
  | succ K =>
    induction K with
    | zero => simp; linarith [h0 0]
    | succ K ih =>
      have hi := ih (fun j hj => hs j (by omega))
      have hh := hs K (by omega)
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel] at hi ⊢
      linarith
lemma noise_halving_growth {σ m B r : ℝ} (hσ : 0 ≤ σ) (hm : 0 < m) (hB : 0 < B) (hr : 2 ≤ r) :
    2*(σ/Real.sqrt (m*B))^r ≤ (σ/Real.sqrt (m*(B/2)))^r := by
  have ha : 0 < Real.sqrt (m*B) := Real.sqrt_pos.mpr (mul_pos hm hB)
  have hb : 0 < Real.sqrt 2 := by positivity
  have he : σ/Real.sqrt (m*(B/2)) = Real.sqrt 2*(σ/Real.sqrt (m*B)) := by
    rw [show m*(B/2)=(m*B)/2 by ring,Real.sqrt_div (mul_nonneg hm.le hB.le)]
    field_simp
  have hbase : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hp := Real.rpow_le_rpow_of_exponent_le hbase hr
  have hp' : 2 ≤ (Real.sqrt 2)^r := by
    simpa only [Real.rpow_two,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] using hp
  rw [he,Real.mul_rpow (Real.sqrt_nonneg 2) (div_nonneg hσ ha.le)]
  exact mul_le_mul_of_nonneg_right hp' (Real.rpow_nonneg (div_nonneg hσ ha.le) r)
lemma refinement_noise_sum {σ m B r : ℝ} (hσ : 0 ≤ σ) (hm : 0 < m) (hB : 0 < B)
    (hr : 2 ≤ r) (K : ℕ) :
    ∑ j ∈ Finset.range K,(σ/Real.sqrt (m*refinementEnvelope B j))^r ≤
      2*(σ/Real.sqrt (m*refinementEnvelope B (K-1)))^r := by
  apply doubling_sum_bound
  · intro j
    exact Real.rpow_nonneg (by positivity) _
  · intro j _
    rw [LongTails.Proofs.HeavyTailSaddleRecovery.refinement_envelope_succ]
    exact noise_halving_growth hσ hm (LongTails.Proofs.HeavyTailSaddleRecovery.refinement_envelope_pos hB j) hr

lemma sqrt_stage_ratio {m H B : ℝ} (hm : 0 < m) (hH : 0 ≤ H) (hB : 0 < B) :
    Real.sqrt (H*B)/Real.sqrt (m*B)=Real.sqrt H/Real.sqrt m := by
  rw [Real.sqrt_mul hH,Real.sqrt_mul hm.le]
  have hb := (Real.sqrt_pos.mpr hB).ne'
  field_simp
lemma epoch_steps_cost_bound {m H δ Λ : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hΛ : 1 ≤ Λ)
    (he0 : 0 ≤ epochLog m H δ) (he : epochLog m H δ ≤ 2^22*Λ) :
    (epochSteps m H δ : ℝ) ≤ 2^25*(Real.sqrt H/Real.sqrt m)*Λ := by
  have hH : 0 < H := hm.trans_le hmH
  have hsm := Real.sqrt_pos.mpr hm
  have hratio : 1 ≤ Real.sqrt H/Real.sqrt m := (le_div_iff₀ hsm).mpr (by simpa using Real.sqrt_le_sqrt hmH)
  have hn : 0 ≤ 4*Real.sqrt H*epochLog m H δ/Real.sqrt m := by positivity
  have hc := (Nat.ceil_lt_add_one hn).le
  have ht := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*(Real.sqrt H/Real.sqrt m) by positivity)
  have hv := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ Real.sqrt H/Real.sqrt m by positivity)
  have heq : 4*Real.sqrt H*epochLog m H δ/Real.sqrt m = 4*(Real.sqrt H/Real.sqrt m)*epochLog m H δ := by ring
  rw [heq] at hc
  change (⌈4*Real.sqrt H*epochLog m H δ/Real.sqrt m⌉₊ : ℝ) ≤ _
  rw [heq]
  nlinarith
lemma refresh_repetitions_cost_bound {δ Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hl0 : 0 ≤ Real.log (1/δ)) (hl : Real.log (1/δ) ≤ 15*Λ) :
    (refreshRepetitions δ : ℝ) ≤ 64*Λ := by
  have hc := (Nat.ceil_lt_add_one (mul_nonneg (by norm_num : (0:ℝ)≤4) hl0)).le
  unfold refreshRepetitions
  push_cast
  linarith
lemma refresh_batch_cost_bound {p σ L R : ℝ} (hσ : 0 ≤ σ) (hL : 0 < L) (hR : 0 < R) :
    (refreshBatch p σ L R : ℝ) ≤ 2+((2:ℝ)^24)^(1/(p-1))*(σ/(L*R))^(p/(p-1)) := by
  have hx : 0 ≤ σ/(L*R) := by positivity
  have hn : 0 ≤ ((2:ℝ)^24*(σ/(L*R))^p)^(1/(p-1)) := Real.rpow_nonneg (by positivity) _
  have hc := (Nat.ceil_lt_add_one hn).le
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤2^24) (Real.rpow_nonneg hx p),← Real.rpow_mul hx] at hc
  have heq : p*(1/(p-1))=p/(p-1) := by ring
  rw [heq] at hc
  unfold refreshBatch
  push_cast
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤2^24) (Real.rpow_nonneg hx p),← Real.rpow_mul hx,heq]
  linarith

lemma noise_ratio_bound {σ m B t : ℝ} (hσ : 0 ≤ σ) (hm : 0 < m) (hB : 0 < B) (ht : 0 < t)
    (hBt : t^2/(2*m) ≤ B) : σ/Real.sqrt (m*B) ≤ 2*(σ/t) := by
  have ha := Real.sqrt_pos.mpr (mul_pos hm hB)
  have hsq := Real.sq_sqrt (mul_nonneg hm.le hB.le)
  have hb := (div_le_iff₀ (show 0 < 2*m by positivity)).mp hBt
  have hta : t ≤ 2*Real.sqrt (m*B) := by nlinarith [Real.sqrt_nonneg (m*B)]
  apply (div_le_iff₀ ha).mpr
  have hh := mul_le_mul_of_nonneg_left hta hσ
  have hh' := (le_div_iff₀ ht).mpr hh
  convert hh' using 1
  ring
lemma kernel_level_power_bound {p σ m B s : ℝ} (hr : 0 ≤ p/(p-1)) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (ha : 0 < Real.sqrt (m*B)) (hscale : σ/Real.sqrt (m*B) ≤ 2*s) :
    (2:ℝ)^(kernelDepth p σ m B) ≤ 2*(1+2^(25*(p/(p-1)))*s^(p/(p-1))) := by
  let r := p/(p-1)
  let a := (2:ℝ)^24*σ/Real.sqrt (m*B)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ (2:ℝ)^25*s := by
    have hh := mul_le_mul_of_nonneg_left hscale (show (0:ℝ)≤2^24 by positivity)
    dsimp [a]
    rw [mul_div_assoc]
    nlinarith
  have hp := Real.rpow_le_rpow ha0 hab hr
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤2^25) hs] at hp
  have he : ((2:ℝ)^25)^r = (2:ℝ)^(25*r) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [he] at hp
  have hc := OracleTemplate.ScalarHeavyTailEstimator.dyadic_ceil_upper (a^r)
  have hn := Real.rpow_nonneg ha0 r
  have hmax : max 1 (a^r) ≤ 1+(2:ℝ)^(25*r)*s^r := by
    apply max_le
    · have hnprod : 0 ≤ (2:ℝ)^(25*r)*s^r := by positivity
      linarith
    · linarith
  exact hc.trans (mul_le_mul_of_nonneg_left hmax (by norm_num))

lemma cast_finset_sup_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ j ∈ s, (f j : ℝ) ≤ B) : ((s.sup f : ℕ) : ℝ) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sup_insert,Nat.cast_max]
    exact max_le (hf a (Finset.mem_insert_self _ _)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
lemma refinement_max_reply_cost_bound {p σ L m B s Λ : ℝ} (K : ℕ) (hΛ : 1 ≤ Λ) (hs : 0 ≤ s)
    (hhor : (kernelHorizon L m : ℝ)+1 ≤ 1024*Λ)
    (hlevel : ∀ j, j < K → (2:ℝ)^(refinementDepth p σ m B j) ≤
      2*(1+2^(25*(p/(p-1)))*s^(p/(p-1)))) :
    (refinementMaxReply p σ L m B K : ℝ) ≤ 2^14*Λ*(1+2^(25*(p/(p-1)))*s^(p/(p-1))) := by
  let X := (2:ℝ)^(25*(p/(p-1)))*s^(p/(p-1))
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hbound : ∀ j ∈ Finset.range K,
      (((kernelHorizon L m+1)*(1+3*2^(refinementDepth p σ m B j)) : ℕ) : ℝ) ≤ 8192*Λ*(1+X) := by
    intro j hj
    have hl := hlevel j (Finset.mem_range.mp hj)
    have ht : 1+3*(2:ℝ)^(refinementDepth p σ m B j) ≤ 8*(1+X) := by dsimp [X]; nlinarith
    have hh := mul_le_mul hhor ht (show 0 ≤ 1+3*(2:ℝ)^(refinementDepth p σ m B j) by positivity)
      (show 0 ≤ 1024*Λ by linarith)
    push_cast
    nlinarith
  have hmax := cast_finset_sup_le (Finset.range K)
    (fun j => (kernelHorizon L m+1)*(1+3*2^(refinementDepth p σ m B j)))
    (show 0 ≤ 8192*Λ*(1+X) by positivity) hbound
  unfold refinementMaxReply
  push_cast
  have hh : 1 ≤ Λ*(1+X) := by nlinarith
  change 1+(↑((Finset.range K).sup (fun j => (kernelHorizon L m+1)*(1+3*2^(refinementDepth p σ m B j)))) : ℝ) ≤ 2^14*Λ*(1+X)
  nlinarith

noncomputable def recoveryCostLog (κ s δ : ℝ) (K : ℕ) : ℝ :=
  1+Real.log (2+κ+(K+1)/δ+s)
lemma recovery_cost_log_bounds {κ s δ : ℝ} (hκ : 1 ≤ κ) (hs : 0 ≤ s) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (K : ℕ) :
    let Λ := recoveryCostLog κ s δ K
    1 ≤ Λ ∧ Real.log κ ≤ Λ ∧ Real.log (max 1 s) ≤ Λ ∧
      Real.log ((K+1)/δ) ≤ Λ ∧ 1 ≤ (K+1:ℝ)/δ ∧ Real.log Λ ≤ Λ := by
  intro Λ
  let Z := 2+κ+(K+1:ℝ)/δ+s
  have hq : 0 ≤ (K+1:ℝ)/δ := by positivity
  have hZ : 1 ≤ Z := by dsimp [Z]; linarith
  have hlogZ := Real.log_nonneg hZ
  have hΛ : 1 ≤ Λ := by dsimp [Λ,recoveryCostLog]; linarith
  have hκZ : κ ≤ Z := by dsimp [Z]; linarith
  have hsZ : max 1 s ≤ Z := by apply max_le hZ; dsimp [Z]; linarith
  have hqZ : (K+1:ℝ)/δ ≤ Z := by dsimp [Z]; linarith
  have hk := Real.log_le_log (show 0 < κ by linarith) hκZ
  have hsl := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left 1 s)) hsZ
  have hql := Real.log_le_log (show 0 < (K+1:ℝ)/δ by positivity) hqZ
  have hΛlog := Real.log_le_sub_one_of_pos (show 0 < Λ by linarith)
  refine ⟨hΛ,?_,?_,?_,?_,by linarith⟩
  · dsimp [Λ,recoveryCostLog]; dsimp [Z] at hk; linarith
  · dsimp [Λ,recoveryCostLog]; dsimp [Z] at hsl; linarith
  · dsimp [Λ,recoveryCostLog]; dsimp [Z] at hql; linarith
  · apply (le_div_iff₀ hδ).mpr
    nlinarith [show (0:ℝ)≤K from Nat.cast_nonneg _]
lemma recovery_halving_count_bound (L μ ζ B : ℝ) (j : ℕ) :
    (recoveryHalvings L μ ζ B j : ℝ)+1 ≤ 6*((recoveryHalvings L μ ζ B 0 : ℝ)+1) := by
  by_cases hj : j=0
  · subst j
    nlinarith [show (0:ℝ)≤recoveryHalvings L μ ζ B 0 from Nat.cast_nonneg _]
  · simp only [recoveryHalvings,hj,ite_false,ite_true]
    push_cast
    nlinarith [show (0:ℝ) ≤ refinementSteps (recoveryEnvelope L μ ζ B 0) (recoveryTarget L μ ζ 0) from Nat.cast_nonneg _]
lemma recovery_stages_cost_log {L μ s δ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) (hs : 0 ≤ s)
    (hd : 0 < δ) (hd1 : δ ≤ 1) (K : ℕ) :
    (recoveryStages L μ : ℝ) ≤ 8*recoveryCostLog (L/μ) s δ K := by
  have hk : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hh := recovery_cost_log_bounds hk hs hd hd1 K
  have hj := recovery_stages_log_bound hm hmL
  linarith [hh.1,hh.2.1]
lemma recovery_cost_log_two {κ s δ : ℝ} (hκ : 1 ≤ κ) (hs : 0 ≤ s) (hd : 0 < δ)
    (hd1 : δ ≤ 1) (K : ℕ) : 2 ≤ recoveryCostLog κ s δ K := by
  have hq := (recovery_cost_log_bounds hκ hs hd hd1 K).2.2.2.2.1
  have hz : (4:ℝ) ≤ 2+κ+(K+1)/δ+s := by linarith
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) hz
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  unfold recoveryCostLog
  linarith [log_two_bounds.1]
lemma stage_confidence_log_bound {δ Λ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) (hΛ : 1 ≤ Λ)
    (J K N : ℕ) (hJ : (J:ℝ)+1 ≤ 9*Λ) (hN : (N:ℝ)+1 ≤ 6*((K:ℝ)+1))
    (hlΛ : Real.log Λ ≤ Λ) (hlq : Real.log ((K+1:ℝ)/δ) ≤ Λ) :
    0 ≤ Real.log (1/(δ/(2*(J+1))/(N+1)/2)) ∧
      Real.log (1/(δ/(2*(J+1))/(N+1)/2)) ≤ 15*Λ := by
  have hJe : (0:ℝ)<J+1 := by positivity
  have hNe : (0:ℝ)<N+1 := by positivity
  have he : 1/(δ/(2*(J+1))/(N+1)/2)=4*(J+1:ℝ)*(N+1:ℝ)/δ := by field_simp; ring
  rw [he]
  have ha : 1 ≤ 4*(J+1:ℝ)*(N+1:ℝ)/δ := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [show (0:ℝ)≤J from Nat.cast_nonneg _,show (0:ℝ)≤N from Nat.cast_nonneg _]
  refine ⟨Real.log_nonneg ha,?_⟩
  have hprod := mul_le_mul hJ hN (show 0 ≤ (N:ℝ)+1 by positivity) (show 0 ≤ 9*Λ by linarith)
  have hb : 4*(J+1:ℝ)*(N+1:ℝ)/δ ≤ 216*Λ*((K+1:ℝ)/δ) := by
    apply (div_le_iff₀ hd).mpr
    have heq : 216*Λ*((K+1:ℝ)/δ)*δ=216*Λ*(K+1:ℝ) := by field_simp
    rw [heq]
    nlinarith
  have h216 : Real.log 216 ≤ 8 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<216) (show (216:ℝ)≤2^8 by norm_num)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_two_bounds.2]
  have hl := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ha) hb
  rw [Real.log_mul (by positivity : (216:ℝ)*Λ ≠ 0) (by positivity : (K+1:ℝ)/δ ≠ 0),
    Real.log_mul (by norm_num : (216:ℝ) ≠ 0) (by linarith : Λ ≠ 0)] at hl
  linarith

lemma epoch_log_cost_bound {m H η κ Λ : ℝ} (hm : 0 < m) (hmH : m ≤ H) (hη : 0 < η)
    (hκ : 1 ≤ κ) (hΛ : 1 ≤ Λ) (hv : Real.sqrt H/Real.sqrt m ≤ 4*Real.sqrt κ)
    (hlκ : Real.log κ ≤ Λ) (hlη0 : 0 ≤ Real.log (1/η)) (hlη : Real.log (1/η) ≤ 15*Λ) :
    0 ≤ epochLog m H η ∧ epochLog m H η ≤ 2^22*Λ := by
  have hH : 0 < H := hm.trans_le hmH
  have hsm := Real.sqrt_pos.mpr hm
  have hv1 : 1 ≤ Real.sqrt H/Real.sqrt m := (le_div_iff₀ hsm).mpr (by simpa using Real.sqrt_le_sqrt hmH)
  have hvp : 0 < Real.sqrt H/Real.sqrt m := by positivity
  have hkp : 0 < κ := by linarith
  have hsk := Real.sqrt_pos.mpr hkp
  have hlv0 := Real.log_nonneg hv1
  have hlv : Real.log (Real.sqrt H/Real.sqrt m) ≤ 2+Λ/2 := by
    have hh := Real.log_le_log hvp hv
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hsk.ne',Real.log_sqrt hkp.le,
      show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_two_bounds.2]
  have hlC0 : 0 ≤ Real.log 100000 := Real.log_nonneg (by norm_num)
  have hlC : Real.log 100000 ≤ 17 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<100000) (show (100000:ℝ)≤2^17 by norm_num)
    rw [Real.log_pow] at hh
    norm_num only [Nat.cast_ofNat] at hh
    linarith [log_two_bounds.2]
  have he : 100000*Real.sqrt H/(Real.sqrt m*η)=100000*(Real.sqrt H/Real.sqrt m)*(1/η) := by ring
  unfold epochLog
  rw [he,Real.log_mul (by positivity : (100000:ℝ)*(Real.sqrt H/Real.sqrt m) ≠ 0) (by positivity : (1:ℝ)/η ≠ 0),
    Real.log_mul (by norm_num : (100000:ℝ) ≠ 0) hvp.ne']
  constructor <;> nlinarith
lemma recovery_stage_geometry_cost {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L)
    {j : ℕ} (hj : j < recoveryStages L μ) :
    μ ≤ recoveryMass μ j ∧ recoveryMass μ j ≤ 30*L ∧
    recoveryMass μ j ≤ recoverySmoothness L μ j ∧
    Real.sqrt (recoverySmoothness L μ j)/Real.sqrt (recoveryMass μ j) ≤ 4*Real.sqrt (L/μ) := by
  have hL : 0 < L := hm.trans_le hmL
  have hmj := LongTails.Proofs.HeavyTailSaddleRecovery.recovery_mass_pos hm j
  have hlow := LongTails.Proofs.HeavyTailSaddleRecovery.recovery_mass_ge hm.le j
  have hhigh := recovery_mass_upper hm hmL hj
  have hH : recoveryMass μ j ≤ recoverySmoothness L μ j := by unfold recoverySmoothness; linarith
  have hk : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hratio : recoverySmoothness L μ j/recoveryMass μ j ≤ 16*(L/μ) := by
    have hh := div_le_div_of_nonneg_left (show 0 ≤ 15*L by positivity) hm hlow
    have he : recoverySmoothness L μ j/recoveryMass μ j = 1+(15*L-μ)/recoveryMass μ j := by
      unfold recoverySmoothness
      field_simp
      ring
    rw [he]
    have ht : (15*L-μ)/recoveryMass μ j ≤ 15*L/recoveryMass μ j := div_le_div_of_nonneg_right (by linarith) hmj.le
    simp only [mul_div_assoc] at hh ht
    linarith
  refine ⟨hlow,hhigh,hH,?_⟩
  have hs := Real.sqrt_le_sqrt hratio
  rw [Real.sqrt_div (show 0 ≤ recoverySmoothness L μ j from hmj.le.trans hH),
    Real.sqrt_mul (show (0:ℝ)≤16 by norm_num)] at hs
  norm_num at hs ⊢
  exact hs

lemma refinement_envelope_antitone {B : ℝ} (hB : 0 ≤ B) {i j : ℕ} (hij : i ≤ j) :
    refinementEnvelope B j ≤ refinementEnvelope B i := by
  exact div_le_div_of_nonneg_left hB (by positivity : (0:ℝ)<2^i)
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hij)
lemma refinement_profile_noise_bounds {σ m B t r : ℝ} (hσ : 0 ≤ σ) (hm : 0 < m)
    (hB : 0 < B) (ht : 0 < t) (hr : 2 ≤ r) (K : ℕ)
    (hlast : t^2/(2*m) ≤ refinementEnvelope B (K-1)) :
    (∀ j, j < K → σ/Real.sqrt (m*refinementEnvelope B j) ≤ 2*(σ/t)) ∧
    (∑ j ∈ Finset.range K,(σ/Real.sqrt (m*refinementEnvelope B j))^r) ≤ 2^(r+1)*(σ/t)^r := by
  have hBp (j : ℕ) := LongTails.Proofs.HeavyTailSaddleRecovery.refinement_envelope_pos hB j
  constructor
  · intro j hj
    exact noise_ratio_bound hσ hm (hBp j) ht
      (hlast.trans (refinement_envelope_antitone hB.le (by omega)))
  · have hh := refinement_noise_sum hσ hm hB hr K
    have hs := noise_ratio_bound hσ hm (hBp (K-1)) ht hlast
    have hp := Real.rpow_le_rpow (show 0 ≤ σ/Real.sqrt (m*refinementEnvelope B (K-1)) by positivity)
      hs (show 0 ≤ r by linarith)
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (div_nonneg hσ ht.le)] at hp
    have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
    nlinarith

open LongTails.Proofs.HeavyTailSaddleRecovery
lemma recovery_scale_pos {L μ ζ : ℝ} (hm : 0 < μ) (hζ : 0 < ζ) : 0 < recoveryScale L μ ζ := by
  have hJ : 0 < recoveryStages L μ := by unfold recoveryStages; omega
  unfold recoveryScale
  positivity
lemma actual_profile_noise_bounds {σ L μ ζ r : ℝ} (hσ : 0 ≤ σ) (hm : 0 < μ) (hζ : 0 < ζ)
    (hr : 2 ≤ r) (initialBound : ℝ) (j : ℕ) :
    let m := recoveryMass μ j
    let B := recoveryEnvelope L μ ζ initialBound j
    let K := recoveryHalvings L μ ζ initialBound j
    let t := recoveryScale L μ ζ
    (∀ k, k < K → σ/Real.sqrt (m*refinementEnvelope B k) ≤ 2*(σ/t)) ∧
      (∑ k ∈ Finset.range K,(σ/Real.sqrt (m*refinementEnvelope B k))^r) ≤ 2^(r+1)*(σ/t)^r := by
  intro m B K t
  have hh := recovery_refinement_envelopes (L:=L) hm hζ initialBound j
  have hl : t^2/(2*m) ≤ refinementEnvelope B (K-1) := by
    have ht := hh.2.2.2.1
    change (t^2/m)/2 ≤ refinementEnvelope B (K-1) at ht
    convert ht using 1
    ring
  exact refinement_profile_noise_bounds hσ (recovery_mass_pos hm j) hh.1 (recovery_scale_pos hm hζ) hr K hl
lemma actual_profile_depth_bound {p σ L μ ζ δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (initialBound : ℝ) (j k : ℕ) (hk : k < recoveryHalvings L μ ζ initialBound j) :
    let t := recoveryScale L μ ζ
    let Λ := recoveryCostLog (L/μ) (σ/t) δ (recoveryHalvings L μ ζ initialBound 0)
    (refinementDepth p σ (recoveryMass μ j) (recoveryEnvelope L μ ζ initialBound j) k : ℝ)+1 ≤
      32*(p/(p-1))*Λ := by
  intro t Λ
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hlog := recovery_cost_log_bounds hκ (div_nonneg hσ ht.le) hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hB := (recovery_refinement_envelopes (L:=L) hm hζ initialBound j).1
  have hscale := (actual_profile_noise_bounds hσ hm hζ (conjugate_exponent_bounds hp hp2).1 initialBound j).1 k hk
  exact depth_cost_bound (conjugate_exponent_bounds hp hp2).1 hσ
    (Real.sqrt_pos.mpr (mul_pos (recovery_mass_pos hm j) (refinement_envelope_pos hB k)))
    hscale hlog.1 hlog.2.2.1
lemma actual_profile_horizon_bound {σ L μ ζ δ : ℝ} (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L)
    (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1) (initialBound : ℝ) (j : ℕ) :
    let t := recoveryScale L μ ζ
    let Λ := recoveryCostLog (L/μ) (σ/t) δ (recoveryHalvings L μ ζ initialBound 0)
    (kernelHorizon (3*L) (recoveryMass μ j) : ℝ)+1 ≤ 1024*Λ := by
  intro t Λ
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hlog := recovery_cost_log_bounds hκ (div_nonneg hσ ht.le) hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hratio := div_le_div_of_nonneg_left (show 0 ≤ 3*L by linarith) hm (recovery_mass_ge hm.le j)
  rw [mul_div_assoc] at hratio
  apply horizon_cost_bound hκ hlog.1 ?_ hlog.2.1
  simpa only [mul_div_assoc] using hratio

lemma mean_reply_multiplier_bound {r Λ : ℝ} (hΛ : 0 ≤ Λ) (h D : ℕ)
    (hh : (h:ℝ)+1 ≤ 1024*Λ) (hD : (D:ℝ)+1 ≤ 32*r*Λ) :
    (((h+1)*(1+3*(D+1)) : ℕ) : ℝ) ≤ 2^17*r*Λ^2 := by
  have hd : 1+3*((D:ℝ)+1) ≤ 128*r*Λ := by
    nlinarith [show (0:ℝ)≤D from Nat.cast_nonneg _]
  have hp := mul_le_mul hh hd (show 0 ≤ 1+3*((D:ℝ)+1) by positivity)
    (show 0 ≤ 1024*Λ by positivity)
  push_cast
  nlinarith
lemma batch_coefficient_bound {p r Λ : ℝ} (hp : 1 < p) (hr : r=p/(p-1))
    (D : ℕ) (hD : (D:ℝ)+1 ≤ 32*r*Λ) :
    ((2:ℝ)^36*(D+1))^(1/(p-1)) ≤ ((2:ℝ)^41*r*Λ)^(r-1) := by
  have hq : 0 ≤ 1/(p-1) := by positivity
  have hbase : (2:ℝ)^36*(D+1) ≤ (2:ℝ)^41*r*Λ := by nlinarith
  have hh := Real.rpow_le_rpow (by positivity : (0:ℝ)≤2^36*(D+1)) hbase hq
  have he : 1/(p-1)=r-1 := by
    rw [hr]
    field_simp [ne_of_gt (show 0 < p-1 by linarith)]
    ring
  simpa only [he] using hh

lemma actual_epoch_work_bound {σ L μ ζ δ : ℝ} (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L)
    (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1) (initialBound : ℝ)
    {j : ℕ} (hj : j < recoveryStages L μ) :
    let m := recoveryMass μ j
    let H := recoverySmoothness L μ j
    let K := recoveryHalvings L μ ζ initialBound j
    let η := recoveryConfidence L μ δ/(K+1)/2
    let Λ := recoveryCostLog (L/μ) (σ/recoveryScale L μ ζ) δ (recoveryHalvings L μ ζ initialBound 0)
    0 ≤ epochLog m H η ∧ epochLog m H η ≤ 2^22*Λ ∧
      (epochSteps m H η : ℝ) ≤ 2^25*(Real.sqrt H/Real.sqrt m)*Λ ∧
      (refreshRepetitions η : ℝ) ≤ 64*Λ ∧ 0 ≤ Real.log (1/η) ∧ Real.log (1/η) ≤ 15*Λ := by
  intro m H K η Λ
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hs : 0 ≤ σ/recoveryScale L μ ζ := div_nonneg hσ ht.le
  have hlog := recovery_cost_log_bounds hκ hs hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hJ := recovery_stages_cost_log hm hmL hs hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hJ' : (recoveryStages L μ : ℝ)+1 ≤ 9*Λ := by change _ ≤ 9*recoveryCostLog _ _ _ _; linarith [hlog.1]
  have hN := recovery_halving_count_bound L μ ζ initialBound j
  have hconf := stage_confidence_log_bound hd hd1 hlog.1 (recoveryStages L μ)
    (recoveryHalvings L μ ζ initialBound 0) K hJ' hN hlog.2.2.2.2.2 hlog.2.2.2.1
  have hη : 0 < η := by dsimp [η,recoveryConfidence]; positivity
  have hgeo := recovery_stage_geometry_cost hm hmL hj
  have hm' := LongTails.Proofs.HeavyTailSaddleRecovery.recovery_mass_pos hm j
  have hell := epoch_log_cost_bound hm' hgeo.2.2.1 hη hκ hlog.1 hgeo.2.2.2 hlog.2.1 hconf.1 hconf.2
  exact ⟨hell.1,hell.2,epoch_steps_cost_bound hm' hgeo.2.2.1 hlog.1 hell.1 hell.2,
    refresh_repetitions_cost_bound hlog.1 hconf.1 hconf.2,hconf.1,hconf.2⟩

lemma mean_calls_sum_bound {v r Λ A : ℝ} (hv : 0 ≤ v) (hr : 0 ≤ r) (hΛ : 0 ≤ Λ)
    (N K : ℕ) (batch reply : ℕ → ℕ) (w : ℕ → ℝ)
    (hN : (N:ℝ) ≤ 2^25*v*Λ)
    (hR : ∀ j, j < K → (reply j : ℝ) ≤ 2^17*r*Λ^2)
    (hB : ∀ j, j < K → (batch j : ℝ)*v ≤ 2*v+A*w j) :
    ((∑ j ∈ Finset.range K,N*batch j*reply j : ℕ) : ℝ) ≤
      2^43*r*Λ^3*v*K+2^42*r*Λ^3*A*(∑ j ∈ Finset.range K,w j) := by
  let C := (2:ℝ)^42*r*Λ^3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsingle (j : ℕ) (hj : j ∈ Finset.range K) :
      ((N*batch j*reply j : ℕ) : ℝ) ≤ 2*C*v+C*A*w j := by
    have hn := mul_le_mul hN (hR j (Finset.mem_range.mp hj)) (Nat.cast_nonneg (reply j))
      (show 0 ≤ (2:ℝ)^25*v*Λ by positivity)
    have hn' := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (batch j) : (0:ℝ) ≤ batch j)
    have hb := mul_le_mul_of_nonneg_left (hB j (Finset.mem_range.mp hj)) hC
    push_cast
    dsimp [C] at hb ⊢
    nlinarith
  have hh := Finset.sum_le_sum hsingle
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range] at hh
  simp only [nsmul_eq_mul] at hh
  rw [← Finset.mul_sum] at hh
  push_cast at hh ⊢
  dsimp [C] at hh
  nlinarith

lemma refresh_noise_scale {L m B : ℝ} (hL : 0 < L) (hm : 0 < m) (hB : 0 < B) (σ : ℝ) :
    σ/(L*Real.sqrt (B/m))=(m/L)*(σ/Real.sqrt (m*B)) := by
  rw [Real.sqrt_div hB.le,Real.sqrt_mul hm.le]
  have hsm := (Real.sqrt_pos.mpr hm).ne'
  have hsB := (Real.sqrt_pos.mpr hB).ne'
  field_simp
  rw [Real.sq_sqrt hm.le]
lemma refresh_batch_noise_bound {p σ L m B : ℝ} (hp : 1 < p) (hσ : 0 ≤ σ)
    (hL : 0 < L) (hm : 0 < m) (hB : 0 < B) (hratio : m/L ≤ 16) :
    (refreshBatch p σ L (Real.sqrt (B/m)) : ℝ) ≤
      2+2^(28*(p/(p-1)))*(σ/Real.sqrt (m*B))^(p/(p-1)) := by
  let r := p/(p-1)
  have hd : 0 < p-1 := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hq : 1/(p-1) ≤ r := div_le_div_of_nonneg_right (by linarith : (1:ℝ)≤p) hd.le
  have hx : 0 ≤ σ/Real.sqrt (m*B) := by positivity
  have hR : 0 < Real.sqrt (B/m) := by positivity
  have hscale : σ/(L*Real.sqrt (B/m)) ≤ 16*(σ/Real.sqrt (m*B)) := by
    rw [refresh_noise_scale hL hm hB]
    exact mul_le_mul_of_nonneg_right hratio hx
  have hn := Real.rpow_le_rpow (show 0 ≤ σ/(L*Real.sqrt (B/m)) by positivity) hscale hr
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤16) hx] at hn
  have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2^24) hq
  have h16 : (16:ℝ)^r=2^(4*r) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  have h24 : ((2:ℝ)^24)^r=2^(24*r) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [h16] at hn
  rw [h24] at hc
  have hmul := mul_le_mul hc hn (Real.rpow_nonneg (show 0 ≤ σ/(L*Real.sqrt (B/m)) by positivity) r)
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (24*r))
  have heq : (2:ℝ)^(24*r)*(2^(4*r)*(σ/Real.sqrt (m*B))^r)=2^(28*r)*(σ/Real.sqrt (m*B))^r := by
    rw [← mul_assoc,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 2
    ring
  rw [heq] at hmul
  have hb := refresh_batch_cost_bound (p:=p) hσ hL hR
  linarith

lemma fixed_calls_sum_bound {Λ A : ℝ} (hA : 0 ≤ A)
    (M K : ℕ) (batch : ℕ → ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hM : (M:ℝ) ≤ 64*Λ) (hB : ∀ j, j < K → (batch j : ℝ) ≤ 2+A*w j) :
    ((∑ j ∈ Finset.range K,256*batch j*M : ℕ) : ℝ) ≤
      32768*Λ*K+16384*Λ*A*(∑ j ∈ Finset.range K,w j) := by
  have hsingle (j : ℕ) (hj : j ∈ Finset.range K) :
      ((256*batch j*M : ℕ) : ℝ) ≤ 32768*Λ+16384*Λ*A*w j := by
    have hwj := hw j
    have hh := mul_le_mul (hB j (Finset.mem_range.mp hj)) hM (Nat.cast_nonneg M)
      (show 0 ≤ 2+A*w j by positivity)
    push_cast
    nlinarith
  have hh := Finset.sum_le_sum hsingle
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range] at hh
  simp only [nsmul_eq_mul] at hh
  rw [← Finset.mul_sum] at hh
  push_cast at hh ⊢
  nlinarith

lemma actual_refinement_mean_bound {p σ L μ ζ δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (initialBound : ℝ) {j : ℕ} (hj : j < recoveryStages L μ) :
    let m := recoveryMass μ j
    let H := recoverySmoothness L μ j
    let B := recoveryEnvelope L μ ζ initialBound j
    let K := recoveryHalvings L μ ζ initialBound j
    let d := recoveryConfidence L μ δ
    let r := p/(p-1)
    let Λ := recoveryCostLog (L/μ) (σ/recoveryScale L μ ζ) δ (recoveryHalvings L μ ζ initialBound 0)
    let v := Real.sqrt H/Real.sqrt m
    (refinementMeanCalls p σ (3*L) m H B d K : ℝ) ≤
      2^43*r*Λ^3*v*K+2^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1)*
        (∑ k ∈ Finset.range K,(σ/Real.sqrt (m*refinementEnvelope B k))^r) := by
  intro m H B K d r Λ v
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hlog := recovery_cost_log_bounds hκ (div_nonneg hσ ht.le) hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hr2 := (conjugate_exponent_bounds hp hp2).1
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hm' := recovery_mass_pos hm j
  have hgeo := recovery_stage_geometry_cost hm hmL hj
  have hH : 0 < H := hm'.trans_le hgeo.2.2.1
  have hB := (recovery_refinement_envelopes (L:=L) hm hζ initialBound j).1
  have he := actual_epoch_work_bound hσ hm hmL hζ hd hd1 initialBound hj
  have hhor := actual_profile_horizon_bound hσ hm hmL hζ hd hd1 initialBound j
  have hdepth (k : ℕ) (hk : k < K) := actual_profile_depth_bound hp hp2 hσ hm hmL hζ hd hd1 initialBound j k hk
  have hreply (k : ℕ) (hk : k < K) :
      (((kernelHorizon (3*L) m+1)*(1+3*(refinementDepth p σ m B k+1)) : ℕ) : ℝ) ≤ 2^17*r*Λ^2 :=
    mean_reply_multiplier_bound (show 0 ≤ Λ by change 0 ≤ recoveryCostLog _ _ _ _; linarith [hlog.1])
      (kernelHorizon (3*L) m) (refinementDepth p σ m B k) hhor (hdepth k hk)
  have hbatch (k : ℕ) (hk : k < K) :
      (refinementBatch p σ m H B k : ℝ)*v ≤ 2*v+((2:ℝ)^41*r*Λ)^(r-1)*(σ/Real.sqrt (m*refinementEnvelope B k))^r := by
    have hBk := refinement_envelope_pos hB k
    have hh := kernel_batch_scaled_bound hp hσ
      (Real.sqrt_pos.mpr (mul_pos hm' hBk)) (Real.sqrt_pos.mpr (mul_pos hH hBk)) (refinementDepth p σ m B k)
    rw [sqrt_stage_ratio hm' hH.le hBk] at hh
    have hc := batch_coefficient_bound hp (rfl : r=p/(p-1)) (refinementDepth p σ m B k) (hdepth k hk)
    have hmul := mul_le_mul_of_nonneg_right hc
      (Real.rpow_nonneg (show 0 ≤ σ/Real.sqrt (m*refinementEnvelope B k) by positivity) r)
    exact hh.trans (add_le_add_right hmul (2*v))
  exact mean_calls_sum_bound (show 0 ≤ v by dsimp [v]; positivity) hr0
    (show 0 ≤ Λ by change 0 ≤ recoveryCostLog _ _ _ _; linarith [hlog.1])
    (epochSteps m H (d/(K+1)/2)) K (refinementBatch p σ m H B)
    (fun k => (kernelHorizon (3*L) m+1)*(1+3*(refinementDepth p σ m B k+1)))
    (fun k => (σ/Real.sqrt (m*refinementEnvelope B k))^r) he.2.2.1 hreply hbatch

lemma actual_refinement_fixed_bound {p σ L μ ζ δ : ℝ} (hp : 1 < p)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (initialBound : ℝ) {j : ℕ} (hj : j < recoveryStages L μ) :
    let m := recoveryMass μ j
    let B := recoveryEnvelope L μ ζ initialBound j
    let K := recoveryHalvings L μ ζ initialBound j
    let d := recoveryConfidence L μ δ
    let r := p/(p-1)
    let Λ := recoveryCostLog (L/μ) (σ/recoveryScale L μ ζ) δ (recoveryHalvings L μ ζ initialBound 0)
    (refinementFixedCalls p σ (3*L) m B d K : ℝ) ≤
      32768*Λ*K+16384*Λ*2^(28*r)*
        (∑ k ∈ Finset.range K,(σ/Real.sqrt (m*refinementEnvelope B k))^r) := by
  intro m B K d r Λ
  have hm' := recovery_mass_pos hm j
  have hL : 0 < L := hm.trans_le hmL
  have hB := (recovery_refinement_envelopes (L:=L) hm hζ initialBound j).1
  have he := actual_epoch_work_bound hσ hm hmL hζ hd hd1 initialBound hj
  have hgeo := recovery_stage_geometry_cost hm hmL hj
  have hratio : m/(3*L) ≤ 16 := (div_le_iff₀ (by positivity)).mpr (by dsimp [m]; linarith [hgeo.2.1])
  exact fixed_calls_sum_bound (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (28*r))
    (refreshRepetitions (d/(K+1)/2)) K
    (fun k => refreshBatch p σ (3*L) (Real.sqrt (refinementEnvelope B k/m)))
    (fun k => (σ/Real.sqrt (m*refinementEnvelope B k))^r)
    (fun k => Real.rpow_nonneg (by positivity) r) he.2.2.2.1
    (fun k _ => refresh_batch_noise_bound hp hσ (by positivity) hm' (refinement_envelope_pos hB k) hratio)


lemma actual_refinement_max_bound {p σ L μ ζ δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (initialBound : ℝ) (j : ℕ) :
    let r := p/(p-1)
    let s := σ/recoveryScale L μ ζ
    let Λ := recoveryCostLog (L/μ) s δ (recoveryHalvings L μ ζ initialBound 0)
    (refinementMaxReply p σ (3*L) (recoveryMass μ j) (recoveryEnvelope L μ ζ initialBound j)
      (recoveryHalvings L μ ζ initialBound j) : ℝ) ≤ 2^14*Λ*(1+2^(25*r)*s^r) := by
  intro r s Λ
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hs : 0 ≤ s := div_nonneg hσ ht.le
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hlog := recovery_cost_log_bounds hκ hs hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hr := (conjugate_exponent_bounds hp hp2).1
  have hnoise := (actual_profile_noise_bounds (L:=L) hσ hm hζ hr initialBound j).1
  have hB := (recovery_refinement_envelopes (L:=L) hm hζ initialBound j).1
  have hm' := recovery_mass_pos hm j
  apply refinement_max_reply_cost_bound _ hlog.1 hs
    (actual_profile_horizon_bound hσ hm hmL hζ hd hd1 initialBound j)
  intro k hk
  exact kernel_level_power_bound (by linarith) hσ hs
    (Real.sqrt_pos.mpr (mul_pos hm' (refinement_envelope_pos hB k))) (hnoise k hk)


lemma actual_cap_log_bound {σ L μ ζ δ : ℝ} (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L)
    (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1) (initialBound : ℝ) {j : ℕ}
    (hj : j < recoveryStages L μ) :
    0 ≤ Real.log (1/recoveryConfidence L μ δ) ∧
      Real.log (1/recoveryConfidence L μ δ) ≤
        15*recoveryCostLog (L/μ) (σ/recoveryScale L μ ζ) δ (recoveryHalvings L μ ζ initialBound 0) := by
  let d := recoveryConfidence L μ δ
  let K := recoveryHalvings L μ ζ initialBound j
  have hd' : 0 < d := by dsimp [d,recoveryConfidence]; positivity
  have hd1' : d ≤ 1 := by
    dsimp [d,recoveryConfidence]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show (0:ℝ)≤recoveryStages L μ from Nat.cast_nonneg _]
  have hη : 0 < d/(K+1)/2 := by positivity
  have hηd : d/(K+1)/2 ≤ d := by
    apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    apply (div_le_iff₀ (by positivity : (0:ℝ)<K+1)).mpr
    nlinarith [show (0:ℝ)≤K from Nat.cast_nonneg _]
  have hi : 1/d ≤ 1/(d/(K+1)/2) := one_div_le_one_div_of_le hη hηd
  have hh := actual_epoch_work_bound hσ hm hmL hζ hd hd1 initialBound hj
  exact ⟨Real.log_nonneg ((le_div_iff₀ hd').mpr (by simpa using hd1')),
    (Real.log_le_log (by positivity) hi).trans hh.2.2.2.2.2⟩

lemma cap_tail_cost_bound {Λ X : ℝ} (hΛ : 1 ≤ Λ) (hX : 0 ≤ X) (M : ℕ) {η : ℝ}
    (hM : (M:ℝ) ≤ 2^14*Λ*(1+X)) (hl0 : 0 ≤ Real.log (1/η))
    (hl : Real.log (1/η) ≤ 15*Λ) :
    (⌈(M:ℝ)*Real.log (1/η)⌉₊ : ℝ) ≤ 1+2^18*Λ^2*(1+X) := by
  have hh := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg M) hl0)
  have hm := mul_le_mul hM hl hl0 (by positivity : 0 ≤ (2:ℝ)^14*Λ*(1+X))
  have hpos : 0 ≤ Λ^2*(1+X) := by positivity
  nlinarith


lemma mean_noise_coefficient_identity {r Λ : ℝ} (hr : 0 < r) (hΛ : 0 < Λ) :
    2*((2:ℝ)^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1))*2^(r+1)=
      2^(42*r+3)*r^r*Λ^(r+2) := by
  rw [Real.mul_rpow (by positivity : (0:ℝ)≤2^41*r) hΛ.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2^41) hr.le]
  have htwo : ((2:ℝ)^41)^(r-1)=2^(41*(r-1)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [htwo,Real.rpow_sub hr,Real.rpow_one,Real.rpow_sub hΛ,Real.rpow_one]
  have hl : Λ^(r+2)=Λ^r*Λ^2 := by rw [Real.rpow_add hΛ]; norm_num
  have ht : (2:ℝ)^(42*r+3)=2^43*(2^(41*(r-1))*2^(r+1)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    rw [show (43:ℕ)=(43:ℕ) from rfl, ← Real.rpow_natCast (2:ℝ) 43,
      ← Real.rpow_add (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  rw [hl,ht]
  field_simp

lemma noise_coefficient_bounds {r Λ : ℝ} (hr : 2 ≤ r) (hΛ : 1 ≤ Λ) :
    let C := (2:ℝ)^(43*r+42)*r^r*Λ^(r+2)
    2*((2:ℝ)^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1))*2^(r+1) ≤ C ∧
    16384*Λ*2^(28*r)*2^(r+1) ≤ C ∧
    2^18*Λ^2*2^(25*r) ≤ C := by
  intro C
  have hrp : 0 < r := by linarith
  have hΛp : 0 < Λ := by linarith
  have hrr : 1 ≤ r^r := Real.one_le_rpow (by linarith) (by linarith)
  have hΛr : 0 ≤ Λ^(r+2) := Real.rpow_nonneg hΛp.le _
  have h1 : Λ ≤ Λ^(r+2) := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hΛ (show (1:ℝ)≤r+2 by linarith))
  have h2 : Λ^2 ≤ Λ^(r+2) := by
    simpa using (Real.rpow_le_rpow_of_exponent_le hΛ (show (2:ℝ)≤r+2 by linarith))
  have hpow (a : ℝ) (ha : a ≤ 43*r+42) : (2:ℝ)^a ≤ 2^(43*r+42) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hbase : (2:ℝ)^(43*r+42)*Λ^(r+2) ≤ C := by
    dsimp [C]
    have hh := mul_le_mul_of_nonneg_left hrr (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (43*r+42))
    simpa using mul_le_mul_of_nonneg_right hh hΛr
  refine ⟨?_,?_,?_⟩
  · rw [mean_noise_coefficient_identity hrp hΛp]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hpow _ (by linarith))
      (Real.rpow_nonneg hrp.le r)) hΛr
  · have heq : (16384:ℝ)*Λ*2^(28*r)*2^(r+1)=2^(29*r+15)*Λ := by
      have hh : (2:ℝ)^(29*r+15)=16384*(2^(28*r)*2^(r+1)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        rw [show (16384:ℝ)=2^(14:ℝ) by norm_num,← Real.rpow_add (by norm_num : (0:ℝ)<2)]
        congr 1
        ring
      rw [hh]
      ring
    rw [heq]
    exact (mul_le_mul (hpow _ (by linarith)) h1 hΛp.le (by positivity)).trans hbase
  · have heq : (2:ℝ)^18*Λ^2*2^(25*r)=2^(25*r+18)*Λ^2 := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
      norm_num
      ring
    rw [heq]
    exact (mul_le_mul (hpow _ (by linarith)) h2 (sq_nonneg Λ) (by positivity)).trans hbase


lemma stage_cost_algebra {r Λ v K x F M T : ℝ} (hr : 2 ≤ r) (hΛ : 1 ≤ Λ)
    (hv : 1 ≤ v) (hK : 1 ≤ K) (hx : 0 ≤ x)
    (hF : F ≤ 32768*Λ*K+16384*Λ*2^(28*r)*2^(r+1)*x)
    (hM : M ≤ 2^43*r*Λ^3*v*K+2^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1)*2^(r+1)*x)
    (hT : T ≤ 1+2^18*Λ^2*(1+2^(25*r)*x)) :
    F+2*M+T ≤ 2^48*r*Λ^3*v*K+2^(43*r+44)*r^r*Λ^(r+2)*x := by
  let D := r*Λ^3*v*K
  let C := (2:ℝ)^(43*r+42)*r^r*Λ^(r+2)
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hvK : 1 ≤ v*K := by nlinarith
  have hrv : 1 ≤ r*v := by nlinarith
  have hrvK : 1 ≤ r*v*K := by nlinarith
  have hc1 : Λ ≤ Λ^3 := by nlinarith [sq_nonneg (Λ-1)]
  have hc2 : Λ^2 ≤ Λ^3 := by nlinarith [sq_nonneg (Λ-1)]
  have hDcube : Λ^3 ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hrvK (show 0 ≤ Λ^3 by positivity)
    dsimp [D]
    nlinarith
  have hDK : Λ*K ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hrv (show 0 ≤ Λ^3*K by positivity)
    have hh' := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ K by linarith)
    dsimp [D]
    nlinarith
  have hD2 : Λ^2 ≤ D := hc2.trans hDcube
  have hD1 : 1 ≤ D := (hΛ.trans hc1).trans hDcube
  have hn := noise_coefficient_bounds hr hΛ
  have hn1 := mul_le_mul_of_nonneg_right hn.1 hx
  have hn2 := mul_le_mul_of_nonneg_right hn.2.1 hx
  have hn3 := mul_le_mul_of_nonneg_right hn.2.2 hx
  have hC : 0 ≤ C*x := by dsimp [C]; positivity
  have heq : (2:ℝ)^(43*r+44)=4*2^(43*r+42) := by
    rw [show 43*r+44=(43*r+42)+2 by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  rw [heq]
  dsimp only [D,C] at hD0 hDK hD2 hD1 hC
  nlinarith only [hF,hM,hT,hn1,hn2,hn3,hD0,hDK,hD2,hD1,hC]


lemma actual_recovery_stage_cost {p σ L μ ζ δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (initialBound : ℝ) {j : ℕ} (hj : j < recoveryStages L μ) :
    let r := p/(p-1)
    let s := σ/recoveryScale L μ ζ
    let Λ := recoveryCostLog (L/μ) s δ (recoveryHalvings L μ ζ initialBound 0)
    let v := Real.sqrt (recoverySmoothness L μ j)/Real.sqrt (recoveryMass μ j)
    (recoveryStageCap p σ L μ ζ initialBound δ j : ℝ) ≤
      2^48*r*Λ^3*v*(recoveryHalvings L μ ζ initialBound j)+2^(43*r+44)*r^r*Λ^(r+2)*s^r := by
  intro r s Λ v
  let m := recoveryMass μ j
  let H := recoverySmoothness L μ j
  let B := recoveryEnvelope L μ ζ initialBound j
  let K := recoveryHalvings L μ ζ initialBound j
  let d := recoveryConfidence L μ δ
  let W := ∑ k ∈ Finset.range K,(σ/Real.sqrt (m*refinementEnvelope B k))^r
  have hr := (conjugate_exponent_bounds hp hp2).1
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hs : 0 ≤ s := div_nonneg hσ ht.le
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hlog := recovery_cost_log_bounds hκ hs hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hΛ : 1 ≤ Λ := hlog.1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hgeo := recovery_stage_geometry_cost hm hmL hj
  have hmp := recovery_mass_pos hm j
  have hv : 1 ≤ v := (le_div_iff₀ (Real.sqrt_pos.mpr hmp)).mpr (by simpa using Real.sqrt_le_sqrt hgeo.2.2.1)
  have hK : (1:ℝ) ≤ K := by
    exact_mod_cast (recovery_refinement_envelopes (L:=L) hm hζ initialBound j).2.1
  have hw : W ≤ 2^(r+1)*s^r := (actual_profile_noise_bounds (L:=L) hσ hm hζ hr initialBound j).2
  have hf := actual_refinement_fixed_bound hp hσ hm hmL hζ hd hd1 initialBound hj
  have hmean := actual_refinement_mean_bound hp hp2 hσ hm hmL hζ hd hd1 initialBound hj
  have hmax := actual_refinement_max_bound hp hp2 hσ hm hmL hζ hd hd1 initialBound j
  have hcaplog := actual_cap_log_bound hσ hm hmL hζ hd hd1 initialBound hj
  have htail := cap_tail_cost_bound hΛ (show 0 ≤ (2:ℝ)^(25*r)*s^r by positivity) _ hmax hcaplog.1 hcaplog.2
  have hF : (refinementFixedCalls p σ (3*L) m B d K : ℝ) ≤
      32768*Λ*K+16384*Λ*2^(28*r)*2^(r+1)*s^r := by
    have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ 16384*Λ*2^(28*r) by positivity)
    calc
      _ ≤ 32768*Λ*K+16384*Λ*2^(28*r)*W := hf
      _ ≤ _ := by nlinarith only [hh]
  have hM : (refinementMeanCalls p σ (3*L) m H B d K : ℝ) ≤
      2^43*r*Λ^3*v*K+2^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1)*2^(r+1)*s^r := by
    have hh := mul_le_mul_of_nonneg_left hw
      (show 0 ≤ 2^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1) by positivity)
    calc
      _ ≤ 2^43*r*Λ^3*v*K+2^42*r*Λ^3*((2:ℝ)^41*r*Λ)^(r-1)*W := hmean
      _ ≤ _ := by nlinarith only [hh]
  have hh := stage_cost_algebra hr hΛ hv hK (Real.rpow_nonneg hs r) hF hM htail
  simpa only [recoveryStageCap,refinementCap,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh


lemma rational_geometric_sum (J : ℕ) :
    ∑ j ∈ Finset.range J, (3/4:ℝ)^j ≤ 4 := by
  have he : (1-(3/4:ℝ))*(∑ j ∈ Finset.range J,(3/4:ℝ)^j)=1-(3/4:ℝ)^J := by
    induction J with
    | zero => norm_num
    | succ J ih => rw [Finset.sum_range_succ,pow_succ]; nlinarith
  nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤3/4) J]
lemma stage_ratio_rational_bound {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) (j : ℕ) :
    Real.sqrt (recoverySmoothness L μ j / recoveryMass μ j) ≤
      1+Real.sqrt (15*(L/μ))*(3/4:ℝ)^j := by
  have hL : 0 < L := hm.trans_le hmL
  have hk : 0 < L/μ := div_pos hL hm
  have hp : 0 < (2:ℝ)^j := by positivity
  have hq : 0 ≤ (3/4:ℝ)^j := by positivity
  have hsq : 1 ≤ (2:ℝ)^j*((3/4:ℝ)^j)^2 := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      have hi := ih (by positivity) (by positivity)
      rw [pow_succ (2:ℝ),pow_succ (3/4:ℝ)]
      nlinarith
  have he : recoverySmoothness L μ j / recoveryMass μ j = 1+(15*(L/μ)-1)/(2:ℝ)^j := by
    unfold recoverySmoothness recoveryMass
    field_simp
    ring
  have hs := Real.sq_sqrt (show 0 ≤ 15*(L/μ) by positivity)
  have hn := Real.sqrt_nonneg (15*(L/μ))
  have hr : 0 ≤ 1+Real.sqrt (15*(L/μ))*(3/4:ℝ)^j := by positivity
  apply (Real.sqrt_le_left hr).mpr
  rw [he]
  have ht := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 15*(L/μ) by positivity)
  have hx : 0 ≤ (2:ℝ)^j*Real.sqrt (15*(L/μ))*(3/4:ℝ)^j := by positivity
  have hb : (15*(L/μ)-1)/(2:ℝ)^j ≤ (1+Real.sqrt (15*(L/μ))*(3/4:ℝ)^j)^2-1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith
lemma stage_ratio_sum_bound {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) :
    ∑ j ∈ Finset.range (recoveryStages L μ),
      Real.sqrt (recoverySmoothness L μ j / recoveryMass μ j) ≤ 24*Real.sqrt (L/μ) := by
  have hL : 0 < L := hm.trans_le hmL
  have hk : 0 ≤ L/μ := by positivity
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (recoveryStages L μ)) =>
    stage_ratio_rational_bound hm hmL j)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    mul_one,← Finset.mul_sum] at hsum
  have hg := mul_le_mul_of_nonneg_left (rational_geometric_sum (recoveryStages L μ))
    (Real.sqrt_nonneg (15*(L/μ)))
  have hs : Real.sqrt (15*(L/μ)) ≤ 4*Real.sqrt (L/μ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [Real.sq_sqrt hk]
  linarith [recovery_stages_sqrt_bound hm hmL]
lemma weighted_stage_ratio_sum_bound {L μ ζ initialBound : ℝ}
    (hm : 0 < μ) (hmL : μ ≤ L) :
    ∑ j ∈ Finset.range (recoveryStages L μ),
      Real.sqrt (recoverySmoothness L μ j / recoveryMass μ j) *
        recoveryHalvings L μ ζ initialBound j ≤
      128*Real.sqrt (L/μ)*(recoveryHalvings L μ ζ initialBound 0+1) := by
  let v := fun j => Real.sqrt (recoverySmoothness L μ j / recoveryMass μ j)
  let K := recoveryHalvings L μ ζ initialBound 0
  have hpoint (j : ℕ) : v j * recoveryHalvings L μ ζ initialBound j ≤
      4*v j + if j=0 then v 0*K else 0 := by
    by_cases hj : j=0
    · subst j
      change v 0 * (K:ℝ) ≤ 4*v 0 + v 0*K
      nlinarith [Real.sqrt_nonneg (recoverySmoothness L μ 0 / recoveryMass μ 0)]
    · simp only [recoveryHalvings, ite_eq_right hj, Nat.cast_ofNat]
      ring_nf
      simp
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (recoveryStages L μ)) => hpoint j)
  have hJ : 0 < recoveryStages L μ := by unfold recoveryStages; omega
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_ite_eq', Finset.mem_range, hJ, ite_true] at hsum
  have hv0 : v 0 ≤ 4*Real.sqrt (L/μ) := by
    have he : recoverySmoothness L μ 0 / recoveryMass μ 0 = 15*(L/μ) := by
      simp [recoverySmoothness, recoveryMass]
      ring
    dsimp [v]
    rw [he]
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith [Real.sq_sqrt (div_nonneg (le_trans hm.le hmL) hm.le)]
  have hvsum := stage_ratio_sum_bound hm hmL
  change ∑ j ∈ Finset.range (recoveryStages L μ), v j ≤ 24*Real.sqrt (L/μ) at hvsum
  have hK := mul_le_mul_of_nonneg_right hv0 (show (0:ℝ)≤K by positivity)
  change ∑ j ∈ Finset.range (recoveryStages L μ), v j * recoveryHalvings L μ ζ initialBound j ≤ _
  change ∑ j ∈ Finset.range (recoveryStages L μ), v j * recoveryHalvings L μ ζ initialBound j ≤ 128*Real.sqrt (L/μ)*((K:ℝ)+1)
  nlinarith [Real.sqrt_nonneg (L/μ), mul_nonneg (Real.sqrt_nonneg (L/μ)) (show (0:ℝ)≤K by positivity)]

lemma recovery_coefficient_bounds {r Λ : ℝ} (hr : 2 ≤ r) (hΛ : 1 ≤ Λ) :
    (2:ℝ)^55*r*Λ^3 ≤ ((2:ℝ)^50*r)^(r+2)*Λ^(r+3) ∧
    2^(43*r+47)*r^r*Λ^(r+3) ≤ ((2:ℝ)^50*r)^(r+2)*Λ^(r+3) := by
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have heq : ((2:ℝ)^50*r)^(r+2)=2^(50*(r+2))*r^(r+2) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2^50) hr0]
    congr 1
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  rw [heq]
  have hpow (a : ℝ) (ha : a ≤ 50*(r+2)) : (2:ℝ)^a ≤ 2^(50*(r+2)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hrpow : r ≤ r^(r+2) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hr1 (show (1:ℝ)≤r+2 by linarith)
  have hrr := Real.rpow_le_rpow_of_exponent_le hr1 (show r≤r+2 by linarith)
  have hΛpow : Λ^3 ≤ Λ^(r+3) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hΛ (show (3:ℝ)≤r+3 by linarith)
  constructor
  · have ht : (2:ℝ)^55 ≤ 2^(50*(r+2)) := by simpa using hpow 55 (by linarith)
    exact mul_le_mul (mul_le_mul ht hrpow hr0 (by positivity)) hΛpow (by positivity) (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hpow _ (by linarith)) hrr (Real.rpow_nonneg hr0 r) (by positivity)) (by positivity)

lemma actual_recovery_cost {p σ L μ ζ δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (initialBound : ℝ) :
    let r := p/(p-1)
    let s := σ/recoveryScale L μ ζ
    let Λ := recoveryCostLog (L/μ) s δ (recoveryHalvings L μ ζ initialBound 0)
    (recoveryCalls p σ L μ ζ initialBound δ : ℝ) ≤
      ((2:ℝ)^50*r)^(r+2)*Λ^(r+3)*
        (Real.sqrt (L/μ)*(recoveryHalvings L μ ζ initialBound 0+1)+s^r) := by
  intro r s Λ
  let J := recoveryStages L μ
  let K := recoveryHalvings L μ ζ initialBound 0
  let D := (2:ℝ)^48*r*Λ^3
  let C := (2:ℝ)^(43*r+44)*r^r*Λ^(r+2)*s^r
  have hr := (conjugate_exponent_bounds hp hp2).1
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hs : 0 ≤ s := div_nonneg hσ ht.le
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hlog := recovery_cost_log_bounds hκ hs hd hd1 K
  have hΛ : 1 ≤ Λ := hlog.1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (j : ℕ) (hj : j ∈ Finset.range J) :
      (recoveryStageCap p σ L μ ζ initialBound δ j : ℝ) ≤
        D*(Real.sqrt (recoverySmoothness L μ j/recoveryMass μ j)*recoveryHalvings L μ ζ initialBound j)+C := by
    have hj' := Finset.mem_range.mp hj
    have h := actual_recovery_stage_cost hp hp2 hσ hm hmL hζ hd hd1 initialBound hj'
    have hgeo := recovery_stage_geometry_cost hm hmL hj'
    have hH : 0 ≤ recoverySmoothness L μ j := (recovery_mass_pos hm j).le.trans hgeo.2.2.1
    rw [Real.sqrt_div hH]
    dsimp only [D,C]
    nlinarith only [h]
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hgeom := mul_le_mul_of_nonneg_left (weighted_stage_ratio_sum_bound (ζ:=ζ) (initialBound:=initialBound) hm hmL) hD
  have hstage := mul_le_mul_of_nonneg_right (recovery_stages_cost_log hm hmL hs hd hd1 K) hC
  have hc := recovery_coefficient_bounds hr hΛ
  have hc1 := mul_le_mul_of_nonneg_right hc.1
    (show 0 ≤ Real.sqrt (L/μ)*(K+1:ℝ) by positivity)
  have hc2 := mul_le_mul_of_nonneg_right hc.2 (Real.rpow_nonneg hs r)
  have heq : (2:ℝ)^(43*r+47)=8*2^(43*r+44) := by
    rw [show 43*r+47=(43*r+44)+3 by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
    norm_num
    ring
  have hΛeq : Λ^(r+3)=Λ^(r+2)*Λ := by
    rw [show r+3=(r+2)+1 by ring,Real.rpow_add (by linarith : 0<Λ),Real.rpow_one]
  rw [heq,hΛeq] at hc2
  rw [hΛeq] at hc1 ⊢
  unfold recoveryCalls
  rw [LongTails.Proofs.StochasticEnvelopeExecution.slotCalls_sum]
  simp only [Nat.zero_add,Nat.cast_sum]
  dsimp only [D,C] at hgeom hstage hsum
  nlinarith only [hsum,hgeom,hstage,hc1,hc2]


end LongTails.Proofs.HeavyTailSaddleCost
