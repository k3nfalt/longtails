import LongTails.Proofs.HeavyTailSaddleOuter
import LongTails.Proofs.HeavyTailSaddleCost
open scoped BigOperators
open LongTails.Algorithms.HeavyTailSaddleEstimator
open LongTails.Proofs.HeavyTailSaddleCost
open LongTails.Proofs.HeavyTailSaddleRecovery
namespace LongTails.Proofs.HeavyTailSaddleOuterCost
noncomputable def initialCostLog (L μ Δ G ε : ℝ) : ℝ :=
  Real.log (2+(L/μ)^3*L*(Δ+G^2/μ)/ε^2)
noncomputable def outerCostLog (p σ L μ Δ G ε δ : ℝ) : ℝ :=
  1+Real.log (2+L/μ+1/δ+L*Δ/ε^2+((L/μ)*(σ/ε))^(p/(p-1))+initialCostLog L μ Δ G ε)
lemma power_controls_base {x r : ℝ} (hx : 0 ≤ x) (hr : 1 ≤ r) : x ≤ 1+x^r := by
  by_cases hx1 : x ≤ 1
  · linarith [Real.rpow_nonneg hx r]
  · have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤x) hr
    simp only [Real.rpow_one] at hh
    linarith
lemma outer_log_controls {κ A u Q δ r : ℝ} (hκ : 1 ≤ κ) (hA : 0 ≤ A) (hu : 0 ≤ u)
    (hQ : 0 ≤ Q) (hd : 0 < δ) (hd1 : δ ≤ 1) (hr : 2 ≤ r) :
    let Z := 2+κ+1/δ+A+(κ*u)^r+Q
    let Λ := 1+Real.log Z
    1 ≤ Z ∧ 1 ≤ Λ ∧ Λ ≤ Z ∧ κ ≤ Z ∧ 1+A ≤ Z ∧ 1+Q ≤ Z ∧
      1/δ ≤ Z ∧ κ*u ≤ Z ∧ Real.log κ ≤ Λ ∧ Real.log (1+A) ≤ Λ := by
  intro Z Λ
  have hκ0 : 0 ≤ κ := by linarith
  have hp : 0 ≤ (κ*u)^r := by positivity
  have hdi : 0 ≤ 1/δ := by positivity
  have hdi1 : 1 ≤ 1/δ := (le_div_iff₀ hd).mpr (by simpa using hd1)
  have hZ : 1 ≤ Z := by dsimp [Z]; linarith
  have hlog := Real.log_nonneg hZ
  have hΛ : 1 ≤ Λ := by dsimp [Λ]; linarith
  have hΛZ : Λ ≤ Z := by
    have hh := Real.log_le_sub_one_of_pos (show 0<Z by linarith)
    dsimp [Λ]
    linarith
  have hkZ : κ ≤ Z := by dsimp [Z]; linarith
  have hAZ : 1+A ≤ Z := by dsimp [Z]; linarith
  refine ⟨hZ,hΛ,hΛZ,hkZ,hAZ,?_,?_,?_,?_,?_⟩
  · dsimp [Z]; linarith
  · dsimp [Z]; linarith
  · have hh := power_controls_base (mul_nonneg hκ0 hu) (show 1≤r by linarith)
    dsimp [Z]; linarith
  · have hh := Real.log_le_log (show 0<κ by linarith) hkZ
    dsimp [Λ]; linarith
  · have hh := Real.log_le_log (show 0<1+A by linarith) hAZ
    dsimp [Λ]; linarith

lemma shared_recovery_log_bound {κ A u Q δ r s : ℝ} (hκ : 1 ≤ κ) (hA : 0 ≤ A)
    (hu : 0 ≤ u) (hQ : 0 ≤ Q) (hd : 0 < δ) (hd1 : δ ≤ 1) (hr : 2 ≤ r) (hs : 0 ≤ s)
    (K T : ℕ)
    (hcount : (K:ℝ)+1 ≤ 128*(1+Q)*(1+Real.log (2+κ+1/δ+A+(κ*u)^r+Q)))
    (hT : (T:ℝ)+2 ≤ 4096*(1+A))
    (hnoise : s ≤ 2^23*(1+Real.log (2+κ+1/δ+A+(κ*u)^r+Q))*(κ*u)) :
    recoveryCostLog κ s (δ/(T+2)) K ≤ 32*(1+Real.log (2+κ+1/δ+A+(κ*u)^r+Q)) := by
  let Z := 2+κ+1/δ+A+(κ*u)^r+Q
  let Λ := 1+Real.log Z
  have hh := outer_log_controls hκ hA hu hQ hd hd1 hr
  have hZ : 1 ≤ Z := hh.1
  have hΛ : 1 ≤ Λ := hh.2.1
  have hΛZ : Λ ≤ Z := hh.2.2.1
  have hkZ : κ ≤ Z := hh.2.2.2.1
  have hAZ : 1+A ≤ Z := hh.2.2.2.2.1
  have hQZ : 1+Q ≤ Z := hh.2.2.2.2.2.1
  have hiZ : 1/δ ≤ Z := hh.2.2.2.2.2.2.1
  have huZ : κ*u ≤ Z := hh.2.2.2.2.2.2.2.1
  have hZ0 : 0 ≤ Z := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hcountZ : (K:ℝ)+1 ≤ 128*Z*Z := by
    calc
      _ ≤ 128*(1+Q)*Λ := hcount
      _ ≤ _ := by gcongr
  have hTZ : (T:ℝ)+2 ≤ 4096*Z := hT.trans (mul_le_mul_of_nonneg_left hAZ (by norm_num))
  have hq : ((K:ℝ)+1)/(δ/(T+2)) ≤ 2^19*Z^4 := by
    calc
      _ = ((K:ℝ)+1)*((T:ℝ)+2)*(1/δ) := by field_simp
      _ ≤ (128*Z*Z)*(4096*Z)*Z := by gcongr
      _ = _ := by ring
  have hsZ : s ≤ 2^23*Z^2 := by
    calc
      _ ≤ 2^23*Λ*(κ*u) := hnoise
      _ ≤ (2:ℝ)^23*Z*Z := by gcongr
      _ = _ := by ring
  have hz2 : Z^2 ≤ Z^4 := by nlinarith only [hZ,sq_nonneg (Z-1)]
  have hz1 : Z ≤ Z^4 := by nlinarith only [hZ,sq_nonneg (Z-1)]
  have harg : 2+κ+((K:ℝ)+1)/(δ/(T+2))+s ≤ 2^26*Z^4 := by
    nlinarith only [hq,hsZ,hkZ,hz2,hz1,hZ]
  have hp : 0 < 2+κ+((K:ℝ)+1)/(δ/(T+2))+s := by positivity
  have hl := Real.log_le_log hp harg
  rw [Real.log_mul (by norm_num : (2:ℝ)^26 ≠ 0) (by positivity : Z^4 ≠ 0),Real.log_pow,Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  change 1+Real.log (2+κ+((K:ℝ)+1)/(δ/(T+2))+s) ≤ 32*Λ
  dsimp only [Λ]
  nlinarith only [hl,log_two_bounds.2,Real.log_nonneg hZ]

lemma floored_refinement_count_bound {B e Z : ℝ} (he : 0 < e) (hZ : 1 ≤ Z)
    (hB : B/e ≤ Z) :
    (refinementSteps (max B e) e : ℝ)+1 ≤ 3+2*Real.log Z := by
  have hratio : max B e/e ≤ Z := by
    apply (div_le_iff₀ he).mpr
    exact max_le ((div_le_iff₀ he).mp hB) (by nlinarith)
  have hx : 1 ≤ max 1 (max B e/e) := le_max_left _ _
  have hxZ : max 1 (max B e/e) ≤ Z := max_le hZ hratio
  have hl := Real.log_le_log (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx) hxZ
  have hl0 := Real.log_nonneg hx
  have hZ0 := Real.log_nonneg hZ
  have h2 := log_two_bounds.1
  have h2p : 0 < Real.log 2 := by linarith
  have hb0 : 0 ≤ Real.logb 2 (max 1 (max B e/e)) := by rw [Real.logb]; positivity
  have hb : Real.logb 2 (max 1 (max B e/e)) ≤ 2*Real.log Z := by
    rw [Real.logb,div_le_iff₀ h2p]
    nlinarith [mul_le_mul_of_nonneg_right h2 hZ0]
  have hc := (Nat.ceil_lt_add_one hb0).le
  unfold refinementSteps
  push_cast
  linarith
lemma recovery_target_zero_identity {L μ ζ : ℝ} (hm : 0 < μ) (hζ : 0 ≤ ζ) :
    recoveryTarget L μ ζ 0 = ζ/(1000000*(recoveryStages L μ:ℝ)^2) := by
  have hJ : 0 < recoveryStages L μ := by unfold recoveryStages; omega
  have hs := Real.sq_sqrt (mul_nonneg hm.le hζ)
  unfold recoveryTarget recoveryScale recoveryMass
  simp only [pow_zero,one_mul]
  field_simp
  nlinarith
lemma recovery_count_from_ratio {L μ ζ B Z : ℝ} (hm : 0 < μ) (hζ : 0 < ζ)
    (hZ : 1 ≤ Z) (hB : B*1000000*(recoveryStages L μ:ℝ)^2/ζ ≤ Z) :
    (recoveryHalvings L μ ζ B 0 : ℝ)+1 ≤ 3+2*Real.log Z := by
  have he := recovery_target_pos (L:=L) hm hζ 0
  unfold recoveryHalvings recoveryEnvelope
  simp only [ite_true]
  apply floored_refinement_count_bound he hZ
  rw [recovery_target_zero_identity hm hζ.le]
  convert hB using 1
  field_simp
lemma recovery_stages_sq_bound {L μ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L) :
    (recoveryStages L μ:ℝ)^2 ≤ 64*(L/μ) := by
  have hs := recovery_stages_sqrt_bound hm hmL
  have hk : 0 ≤ L/μ := div_nonneg (hm.le.trans hmL) hm.le
  nlinarith [Real.sq_sqrt hk, Real.sqrt_nonneg (L/μ), show (0:ℝ) ≤ recoveryStages L μ from Nat.cast_nonneg _]
lemma cold_count_bound {L μ Δ G ε : ℝ} (hm : 0 < μ) (hmL : μ ≤ L)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    (recoveryHalvings L μ (coarseAccuracy L ε) (3*(L/μ)^2*(Δ+G^2/μ)) 0 : ℝ)+1 ≤
      128*(1+Real.log (2+(L/μ)^3*L*(Δ+G^2/μ)/ε^2)) := by
  let κ := L/μ
  let X := Δ+G^2/μ
  let Y := κ^3*L*X/ε^2
  have hL : 0 < L := hm.trans_le hmL
  have hk : 0 < κ := div_pos hL hm
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have he : 0 < coarseAccuracy L ε := by unfold coarseAccuracy; positivity
  have hJ := recovery_stages_sq_bound hm hmL
  have hmul := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 3*κ^2*X*1000000*1048576*L/ε^2 by positivity)
  have hr : (3*κ^2*X)*1000000*(recoveryStages L μ:ℝ)^2/coarseAccuracy L ε ≤ 2^48*Y := by
    have hnorm : (3*κ^2*X*1000000*1048576*L/ε^2)*(64*(L/μ)) = 201326592000000*Y := by
      dsimp [Y,κ]
      ring
    rw [hnorm] at hmul
    have heq : (3*κ^2*X)*1000000*(recoveryStages L μ:ℝ)^2/coarseAccuracy L ε =
        (3*κ^2*X*1000000*1048576*L/ε^2)*(recoveryStages L μ:ℝ)^2 := by
      unfold coarseAccuracy
      field_simp
    rw [heq]
    nlinarith
  have hz : 1 ≤ (2:ℝ)^48*(2+Y) := by nlinarith
  have hb := recovery_count_from_ratio hm he hz (hr.trans (by nlinarith))
  have hl : Real.log ((2:ℝ)^48*(2+Y)) ≤ 48+Real.log (2+Y) := by
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_bounds.2]
  change (recoveryHalvings L μ (coarseAccuracy L ε) (3*κ^2*X) 0:ℝ)+1 ≤ 128*(1+Real.log (2+Y))
  nlinarith [Real.log_nonneg (show 1 ≤ 2+Y by linarith)]
lemma fine_count_bound {L μ ε Λ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hlκ : Real.log (L/μ) ≤ Λ) :
    (recoveryHalvings L μ (fineAccuracy L μ ε) (fineInitialBound L μ ε) 0 : ℝ)+1 ≤ 128*Λ := by
  let κ := L/μ
  have hL : 0 < L := hm.trans_le hmL
  have hk : 1 ≤ κ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hkp : 0 < κ := by linarith
  have he : 0 < fineAccuracy L μ ε := by unfold fineAccuracy; positivity
  have hJ := recovery_stages_sq_bound hm hmL
  change (recoveryStages L μ:ℝ)^2 ≤ 64*κ at hJ
  have hmul := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 3000000*κ^2 by positivity)
  have hr : fineInitialBound L μ ε*1000000*(recoveryStages L μ:ℝ)^2/fineAccuracy L μ ε ≤ 2^28*κ^3 := by
    have heq : fineInitialBound L μ ε*1000000*(recoveryStages L μ:ℝ)^2/fineAccuracy L μ ε =
        3000000*κ^2*(recoveryStages L μ:ℝ)^2 := by
      unfold fineInitialBound coarseAccuracy fineAccuracy
      dsimp [κ]
      field_simp
      ring
    rw [heq]
    nlinarith [pow_nonneg hkp.le 3]
  have hz : 1 ≤ (2:ℝ)^28*κ^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hk 3]
  have hb := recovery_count_from_ratio hm he hz hr
  have hl : Real.log ((2:ℝ)^28*κ^3) ≤ 28+3*Real.log κ := by
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_bounds.2]
  change Real.log κ ≤ Λ at hlκ
  linarith
lemma outer_steps_upper {L Δ ε : ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ) :
    (outerSteps L Δ ε:ℝ)+1 ≤ 3+4096*(L*Δ/ε^2) := by
  have hx : 0 ≤ 4096*L*Δ/ε^2 := by positivity
  have hc := (Nat.ceil_lt_add_one hx).le
  unfold outerSteps
  push_cast
  ring_nf at hc ⊢
  linarith
lemma warm_count_bound {L μ Δ ε Λ : ℝ} (hm : 0 < μ) (hmL : μ ≤ L)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hΛ : 1 ≤ Λ)
    (hlκ : Real.log (L/μ) ≤ Λ) (hlA : Real.log (1+L*Δ/ε^2) ≤ Λ) :
    (recoveryHalvings L μ (coarseAccuracy L ε)
      (12*(L/μ)*(Δ+(outerSteps L Δ ε+1)*coarseAccuracy L ε)) 0 : ℝ)+1 ≤ 128*Λ := by
  let κ := L/μ
  let A := L*Δ/ε^2
  let T := outerSteps L Δ ε
  let J := (recoveryStages L μ:ℝ)
  have hL : 0 < L := hm.trans_le hmL
  have hk : 1 ≤ κ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hkp : 0 < κ := by linarith
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have he : 0 < coarseAccuracy L ε := by unfold coarseAccuracy; positivity
  have hJ : J^2 ≤ 64*κ := recovery_stages_sq_bound hm hmL
  have hT : (T:ℝ)+1 ≤ 3+4096*A := outer_steps_upper hL.le hΔ
  have hmul := mul_le_mul_of_nonneg_left hJ
    (show 0 ≤ 12000000*κ*(1048576*A+(T:ℝ)+1) by positivity)
  have hTmul := mul_le_mul_of_nonneg_left hT (show 0 ≤ 768000000*κ^2 by positivity)
  have hr : (12*κ*(Δ+(T+1)*coarseAccuracy L ε))*1000000*J^2/coarseAccuracy L ε ≤
      2^51*κ^2*(1+A) := by
    have heq : (12*κ*(Δ+(T+1)*coarseAccuracy L ε))*1000000*J^2/coarseAccuracy L ε =
        12000000*κ*(1048576*A+(T:ℝ)+1)*J^2 := by
      unfold coarseAccuracy
      dsimp [A]
      field_simp
      ring
    rw [heq]
    nlinarith [sq_nonneg κ, mul_nonneg (sq_nonneg κ) hA]
  have hz : 1 ≤ (2:ℝ)^51*κ^2*(1+A) := by
    nlinarith [sq_nonneg (κ-1), mul_nonneg (sq_nonneg κ) hA]
  have hb := recovery_count_from_ratio hm he hz hr
  have hl : Real.log ((2:ℝ)^51*κ^2*(1+A)) ≤ 51+2*Real.log κ+Real.log (1+A) := by
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by norm_num) (by positivity),Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [log_two_bounds.2]
  change Real.log κ ≤ Λ at hlκ
  change Real.log (1+A) ≤ Λ at hlA
  linarith

lemma coarse_noise_scale {L μ ε : ℝ} (hL : 0 < L) (hm : 0 < μ) (he : 0 < ε) (σ : ℝ) :
    σ/recoveryScale L μ (coarseAccuracy L ε) =
      1024000*(recoveryStages L μ)*Real.sqrt (L/μ)*(σ/ε) := by
  have hsm := (Real.sqrt_pos.mpr hm).ne'
  have hsL := (Real.sqrt_pos.mpr hL).ne'
  have hJ : (recoveryStages L μ : ℝ) ≠ 0 := by
    have : 0 < recoveryStages L μ := by unfold recoveryStages; omega
    positivity
  unfold recoveryScale coarseAccuracy
  rw [Real.sqrt_mul hm.le,Real.sqrt_div (sq_nonneg ε),Real.sqrt_sq he.le,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤1048576),Real.sqrt_div hL.le]
  norm_num
  field_simp
  ring
lemma fine_noise_scale {L μ ε : ℝ} (hL : 0 < L) (hm : 0 < μ) (he : 0 < ε) (σ : ℝ) :
    σ/recoveryScale L μ (fineAccuracy L μ ε) =
      1024000*(recoveryStages L μ)*(L/μ)*(σ/ε) := by
  have hroot : Real.sqrt (μ*fineAccuracy L μ ε)=μ*ε/(1024*L) := by
    apply (Real.sqrt_eq_iff_eq_sq (by unfold fineAccuracy; positivity) (by positivity)).mpr
    unfold fineAccuracy
    field_simp
    ring
  unfold recoveryScale
  rw [hroot]
  field_simp
  ring

lemma outer_noise_scale_bounds {σ L μ ε Λ : ℝ} (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L)
    (he : 0 < ε) (hΛ : 1 ≤ Λ) (hlκ : Real.log (L/μ) ≤ Λ) :
    σ/recoveryScale L μ (coarseAccuracy L ε) ≤ 2^23*Λ*Real.sqrt (L/μ)*(σ/ε) ∧
    σ/recoveryScale L μ (fineAccuracy L μ ε) ≤ 2^23*Λ*(L/μ)*(σ/ε) := by
  have hL := hm.trans_le hmL
  have hΛ0 : 0 ≤ Λ := by linarith
  have hk : 0 ≤ L/μ := by positivity
  have hu : 0 ≤ σ/ε := by positivity
  have hJ : (recoveryStages L μ : ℝ) ≤ 8*Λ := by
    have hh := LongTails.Proofs.HeavyTailSaddleCost.recovery_stages_log_bound hm hmL
    linarith
  rw [coarse_noise_scale hL hm he,fine_noise_scale hL hm he]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hJ (mul_nonneg (Real.sqrt_nonneg (L/μ)) hu)
    have hp := mul_nonneg hΛ0 (mul_nonneg (Real.sqrt_nonneg (L/μ)) hu)
    nlinarith only [hh,hp]
  · have hh := mul_le_mul_of_nonneg_right hJ (mul_nonneg hk hu)
    have hp := mul_nonneg hΛ0 (mul_nonneg hk hu)
    nlinarith only [hh,hp]


lemma outer_coefficient_bound {r : ℝ} (hr : 2 ≤ r) :
    ((2:ℝ)^50*r)^(r+2)*2^(28*r+27) ≤ ((2:ℝ)^80*r)^(r+2) := by
  have hr0 : 0 ≤ r := by linarith
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2^50) hr0,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2^80) hr0]
  have h50 : ((2:ℝ)^50)^(r+2)=2^(50*(r+2)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]; norm_num
  have h80 : ((2:ℝ)^80)^(r+2)=2^(80*(r+2)) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]; norm_num
  rw [h50,h80]
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    (show 50*(r+2)+(28*r+27) ≤ 80*(r+2) by linarith)
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2)] at hh
  have ht := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hr0 (r+2))
  nlinarith only [ht]
lemma outer_cost_algebra {r Λ D N C : ℝ} (hr : 2 ≤ r) (hΛ : 1 ≤ Λ)
    (hD : 0 ≤ D) (hN : 0 ≤ N)
    (hC : C ≤ ((2:ℝ)^50*r)^(r+2)*2^(5*r+35)*Λ^(r+4)*D+
      ((2:ℝ)^50*r)^(r+2)*2^(28*r+27)*Λ^(2*r+3)*N) :
    C ≤ ((2:ℝ)^80*r)^(r+2)*Λ^(2*r+3)*(D+N) := by
  have hr0 : 0 ≤ r := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have hp : 0 ≤ ((2:ℝ)^50*r)^(r+2) := by positivity
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
    (show 5*r+35 ≤ 28*r+27 by linarith)
  have hlog := Real.rpow_le_rpow_of_exponent_le hΛ (show r+4 ≤ 2*r+3 by linarith)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul hpow hlog
    (Real.rpow_nonneg hΛ0 (r+4)) (by positivity)) hp
  have hc := outer_coefficient_bound hr
  have hcD := mul_le_mul_of_nonneg_right hh hD
  have hc' := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hΛ0 (2*r+3))
  have hcD' := mul_le_mul_of_nonneg_right hc' hD
  have hcN := mul_le_mul_of_nonneg_right hc' hN
  nlinarith only [hC,hcD,hcD',hcN]

lemma outer_parameter_controls {p σ L μ Δ G ε δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hΔ : 0 ≤ Δ) (he : 0 < ε)
    (hd : 0 < δ) (hd1 : δ ≤ 1) :
    let Q := initialCostLog L μ Δ G ε
    let Λ := outerCostLog p σ L μ Δ G ε δ
    0 ≤ Q ∧ 1 ≤ Λ ∧ Real.log (L/μ) ≤ Λ ∧ Real.log (1+L*Δ/ε^2) ≤ Λ := by
  intro Q Λ
  have hL := hm.trans_le hmL
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hQ : 0 ≤ Q := by
    apply Real.log_nonneg
    have hx : 0 ≤ (L/μ)^3*L*(Δ+G^2/μ)/ε^2 := by positivity
    linarith
  have hh := outer_log_controls hκ (show 0 ≤ L*Δ/ε^2 by positivity)
    (show 0 ≤ σ/ε by positivity) hQ hd hd1 (conjugate_exponent_bounds hp hp2).1
  exact ⟨hQ,hh.2.1,hh.2.2.2.2.2.2.2.2.1,hh.2.2.2.2.2.2.2.2.2⟩
lemma outer_confidence_bounds {L Δ ε δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) :
    0 < outerConfidence L Δ ε δ ∧ outerConfidence L Δ ε δ ≤ 1 := by
  unfold outerConfidence
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [show (0:ℝ)≤outerSteps L Δ ε from Nat.cast_nonneg _]
lemma actual_outer_recovery_log_bounds {p σ L μ Δ G ε δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hΔ : 0 ≤ Δ) (he : 0 < ε)
    (hd : 0 < δ) (hd1 : δ ≤ 1) :
    let T := outerSteps L Δ ε
    let ζc := coarseAccuracy L ε
    let ζf := fineAccuracy L μ ε
    let d := outerConfidence L Δ ε δ
    let Λ := outerCostLog p σ L μ Δ G ε δ
    (∀ j, recoveryCostLog (L/μ) (σ/recoveryScale L μ ζc) d
      (recoveryHalvings L μ ζc (coarseInitialBound L μ Δ G ζc T j) 0) ≤ 32*Λ) ∧
    recoveryCostLog (L/μ) (σ/recoveryScale L μ ζf) d
      (recoveryHalvings L μ ζf (fineInitialBound L μ ε) 0) ≤ 32*Λ := by
  intro T ζc ζf d Λ
  let Q := initialCostLog L μ Δ G ε
  have hL := hm.trans_le hmL
  have hh := outer_parameter_controls (G:=G) hp hp2 hσ hm hmL hΔ he hd hd1
  have hQ : 0 ≤ Q := hh.1
  have hΛ : 1 ≤ Λ := hh.2.1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hA : 0 ≤ L*Δ/ε^2 := by positivity
  have hu : 0 ≤ σ/ε := by positivity
  have hζc : 0 < ζc := by dsimp [ζc,coarseAccuracy]; positivity
  have hζf : 0 < ζf := by dsimp [ζf,fineAccuracy]; positivity
  have hsc : 0 ≤ σ/recoveryScale L μ ζc := div_nonneg hσ (recovery_scale_pos hm hζc).le
  have hsf : 0 ≤ σ/recoveryScale L μ ζf := div_nonneg hσ (recovery_scale_pos hm hζf).le
  have hT : (T:ℝ)+2 ≤ 4096*(1+L*Δ/ε^2) := by
    have ht := outer_steps_upper (ε:=ε) hL.le hΔ
    change (outerSteps L Δ ε:ℝ)+2 ≤ _
    linarith
  have hn := outer_noise_scale_bounds hσ hm hmL he hΛ hh.2.2.1
  have hsk : Real.sqrt (L/μ) ≤ L/μ := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    nlinarith only [hκ,sq_nonneg (L/μ-1)]
  have hnc : σ/recoveryScale L μ ζc ≤ 2^23*Λ*((L/μ)*(σ/ε)) := by
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsk hu)
      (show 0 ≤ (2:ℝ)^23*Λ by positivity)
    nlinarith only [hn.1,ht]
  have hnf : σ/recoveryScale L μ ζf ≤ 2^23*Λ*((L/μ)*(σ/ε)) := by
    nlinarith only [hn.2]
  have hcold := cold_count_bound (G:=G) hm hmL hΔ he
  change _ ≤ 128*(1+Q) at hcold
  have hwarm := warm_count_bound hm hmL hΔ he hΛ hh.2.2.1 hh.2.2.2
  have hfine := fine_count_bound hm hmL he hΛ hh.2.2.1
  have hcounts (j : ℕ) :
      (recoveryHalvings L μ ζc (coarseInitialBound L μ Δ G ζc T j) 0 : ℝ)+1 ≤ 128*(1+Q)*Λ := by
    by_cases hj : j=0
    · subst j
      simp only [coarseInitialBound,ite_true]
      have ht := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ 128*(1+Q) by positivity)
      nlinarith only [hcold,ht]
    · simp only [coarseInitialBound,hj,ite_false]
      have ht := mul_nonneg hQ hΛ0
      nlinarith only [hwarm,ht]
  constructor
  · intro j
    exact shared_recovery_log_bound hκ hA hu hQ hd hd1 (conjugate_exponent_bounds hp hp2).1 hsc
      _ T (hcounts j) hT hnc
  · apply shared_recovery_log_bound hκ hA hu hQ hd hd1 (conjugate_exponent_bounds hp hp2).1 hsf _ T _ hT hnf
    change (recoveryHalvings L μ ζf (fineInitialBound L μ ε) 0 : ℝ)+1 ≤ 128*(1+Q)*Λ
    have ht := mul_nonneg hQ hΛ0
    nlinarith only [hfine,ht]

lemma deterministic_outer_sum_bound {Λ A Q : ℝ} (hΛ : 1 ≤ Λ) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (T Kf : ℕ) (K : ℕ → ℕ) (hT : (T:ℝ) ≤ 2+4096*A)
    (hcold : (K 0:ℝ)+1 ≤ 128*(1+Q))
    (hwarm : ∀ j, j ≠ 0 → (K j:ℝ)+1 ≤ 128*Λ) (hfine : (Kf:ℝ)+1 ≤ 128*Λ) :
    (∑ j ∈ Finset.range T, ((K j:ℝ)+1))+((Kf:ℝ)+1) ≤ 2^20*Λ*(1+A+Q) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hpoint (j : ℕ) : (K j:ℝ)+1 ≤ 128*Λ+if j=0 then 128*(1+Q) else 0 := by
    by_cases hj : j=0
    · subst j
      simp only [ite_true]
      linarith
    · simp only [hj,ite_false,add_zero]
      exact hwarm j hj
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range T) => hpoint j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum ⊢
  have hzero : (∑ j ∈ Finset.range T,if j=0 then 128*(1+Q) else 0) ≤ 128*(1+Q) := by
    simp only [Finset.sum_ite_eq']
    split_ifs
    · rfl
    · positivity
  have ht := mul_le_mul_of_nonneg_left hT (show 0 ≤ 128*Λ by positivity)
  have hq := mul_le_mul_of_nonneg_right hΛ (show 0 ≤ 1+Q by positivity)
  have hAΛ := mul_nonneg hΛ0 hA
  have hQΛ := mul_nonneg hΛ0 hQ
  nlinarith only [hsum,hzero,hfine,ht,hq,hAΛ,hQΛ,hΛ]

lemma stochastic_outer_sum_bound {r κ Λ u A sc sf : ℝ} (T : ℕ)
    (hr : 2 ≤ r) (hk : 1 ≤ κ) (hΛ : 1 ≤ Λ) (hu : 0 ≤ u) (hA : 0 ≤ A)
    (hT : (T:ℝ) ≤ 2+4096*A) (hsc0 : 0 ≤ sc) (hsf0 : 0 ≤ sf)
    (hsc : sc ≤ 2^23*Λ*Real.sqrt κ*u) (hsf : sf ≤ 2^23*Λ*κ*u) :
    (T:ℝ)*sc^r+sf^r ≤ 2^(23*r+12)*Λ^r*(A*κ^(r/2)+κ^r)*u^r := by
  have hr0 : 0 ≤ r := by linarith
  have hk0 : 0 ≤ κ := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  let C := (2:ℝ)^(23*r)*Λ^r*u^r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsqr : (Real.sqrt κ)^r=κ^(r/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hk0]
    congr 1
    ring
  have h23 : ((2:ℝ)^23)^r=2^(23*r) := by
    rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    norm_num
  have hscpow : sc^r ≤ C*κ^(r/2) := by
    have hh := Real.rpow_le_rpow hsc0 hsc hr0
    rw [Real.mul_rpow (by positivity : (0:ℝ)≤2^23*Λ*Real.sqrt κ) hu,
      Real.mul_rpow (by positivity : (0:ℝ)≤2^23*Λ) (Real.sqrt_nonneg κ),
      Real.mul_rpow (by norm_num : (0:ℝ)≤2^23) hΛ0,h23,hsqr] at hh
    dsimp [C]
    nlinarith only [hh]
  have hsfpow : sf^r ≤ C*κ^r := by
    have hh := Real.rpow_le_rpow hsf0 hsf hr0
    rw [Real.mul_rpow (by positivity : (0:ℝ)≤2^23*Λ*κ) hu,
      Real.mul_rpow (by positivity : (0:ℝ)≤2^23*Λ) hk0,
      Real.mul_rpow (by norm_num : (0:ℝ)≤2^23) hΛ0,h23] at hh
    dsimp [C]
    nlinarith only [hh]
  have hhalf : κ^(r/2) ≤ κ^r := Real.rpow_le_rpow_of_exponent_le hk (by linarith)
  have ht := mul_le_mul hT hscpow (Real.rpow_nonneg hsc0 r) (by positivity : (0:ℝ)≤2+4096*A)
  have hhalfC := mul_le_mul_of_nonneg_left hhalf hC
  have hfullC : 0 ≤ C*κ^r := mul_nonneg hC (Real.rpow_nonneg hk0 r)
  have heq : 2^(23*r+12)*Λ^r*(A*κ^(r/2)+κ^r)*u^r = 4096*C*(A*κ^(r/2)+κ^r) := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
    norm_num
    dsimp [C]
    ring
  rw [heq]
  nlinarith only [ht,hsfpow,hhalfC,hfullC]

lemma recovery_cost_with_common_log {p σ L μ ζ δ Λ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hζ : 0 < ζ) (hd : 0 < δ) (hd1 : δ ≤ 1)
    (hΛ : 1 ≤ Λ) (initialBound : ℝ)
    (hlog : recoveryCostLog (L/μ) (σ/recoveryScale L μ ζ) δ
      (recoveryHalvings L μ ζ initialBound 0) ≤ 32*Λ) :
    let r := p/(p-1)
    let s := σ/recoveryScale L μ ζ
    (recoveryCalls p σ L μ ζ initialBound δ : ℝ) ≤
      ((2:ℝ)^50*r)^(r+2)*2^(5*r+15)*Λ^(r+3)*
        (Real.sqrt (L/μ)*(recoveryHalvings L μ ζ initialBound 0+1)+s^r) := by
  intro r s
  have hr := (conjugate_exponent_bounds hp hp2).1
  have hr0 : 0 ≤ r := by dsimp [r]; linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  have ht := recovery_scale_pos (L:=L) hm hζ
  have hs : 0 ≤ s := div_nonneg hσ ht.le
  have hκ : 1 ≤ L/μ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hbase := recovery_cost_log_bounds hκ hs hd hd1 (recoveryHalvings L μ ζ initialBound 0)
  have hpow := Real.rpow_le_rpow (show 0 ≤ recoveryCostLog (L/μ) s δ (recoveryHalvings L μ ζ initialBound 0) by linarith [hbase.1])
    hlog (show 0 ≤ r+3 by linarith)
  have heq : (32*Λ)^(r+3)=2^(5*r+15)*Λ^(r+3) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤32) hΛ0]
    have hh : (32:ℝ)^(r+3)=2^(5*r+15) := by
      rw [show (32:ℝ)=2^(5:ℝ) by norm_num,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      congr 1
      ring
    rw [hh]
  rw [heq] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ ((2:ℝ)^50*r)^(r+2) by positivity)
  have hh := mul_le_mul_of_nonneg_right hmul
    (show 0 ≤ Real.sqrt (L/μ)*(recoveryHalvings L μ ζ initialBound 0+1)+s^r by positivity)
  have hc := actual_recovery_cost hp hp2 hσ hm hmL hζ hd hd1 initialBound
  exact hc.trans (by convert hh using 1; ring)

lemma outer_raw_cost_algebra {r κ Λ A Q u S Nsum C : ℝ} (hr : 2 ≤ r) (hk : 1 ≤ κ)
    (hΛ : 1 ≤ Λ) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hu : 0 ≤ u)
    (hS : S ≤ 2^20*Λ*(1+A+Q))
    (hN : Nsum ≤ 2^(23*r+12)*Λ^r*(A*κ^(r/2)+κ^r)*u^r)
    (hC : C ≤ ((2:ℝ)^50*r)^(r+2)*2^(5*r+15)*Λ^(r+3)*(Real.sqrt κ*S+Nsum)) :
    C ≤ ((2:ℝ)^80*r)^(r+2)*Λ^(2*r+3)*
      (Real.sqrt κ*(1+A+Q)+(A*κ^(r/2)+κ^r)*u^r) := by
  have hr0 : 0 ≤ r := by linarith
  have hk0 : 0 ≤ κ := by linarith
  have hΛ0 : 0 ≤ Λ := by linarith
  let W := ((2:ℝ)^50*r)^(r+2)*2^(5*r+15)*Λ^(r+3)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hd := mul_le_mul_of_nonneg_left hS (mul_nonneg hW (Real.sqrt_nonneg κ))
  have hn := mul_le_mul_of_nonneg_left hN hW
  have hdeq : W*Real.sqrt κ*(2^20*Λ*(1+A+Q)) =
      ((2:ℝ)^50*r)^(r+2)*2^(5*r+35)*Λ^(r+4)*(Real.sqrt κ*(1+A+Q)) := by
    have ht : (2:ℝ)^(5*r+35)=2^(5*r+15)*2^20 := by
      rw [show 5*r+35=(5*r+15)+20 by ring,Real.rpow_add (by norm_num : (0:ℝ)<2)]
      norm_num
    have hl : Λ^(r+4)=Λ^(r+3)*Λ := by
      rw [show r+4=(r+3)+1 by ring,Real.rpow_add (by linarith : 0<Λ),Real.rpow_one]
    rw [ht,hl]
    dsimp [W]
    ring
  have hneq : W*(2^(23*r+12)*Λ^r*(A*κ^(r/2)+κ^r)*u^r) =
      ((2:ℝ)^50*r)^(r+2)*2^(28*r+27)*Λ^(2*r+3)*((A*κ^(r/2)+κ^r)*u^r) := by
    have ht : (2:ℝ)^(28*r+27)=2^(5*r+15)*2^(23*r+12) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      congr 1
      ring
    have hl : Λ^(2*r+3)=Λ^(r+3)*Λ^r := by
      rw [← Real.rpow_add (by linarith : 0<Λ)]
      congr 1
      ring
    rw [ht,hl]
    dsimp [W]
    ring
  rw [hdeq] at hd
  rw [hneq] at hn
  apply outer_cost_algebra hr hΛ (by positivity) (by positivity)
  change C ≤ W*(Real.sqrt κ*S+Nsum) at hC
  calc
    C ≤ W*(Real.sqrt κ*S+Nsum) := hC
    _ = W*Real.sqrt κ*S+W*Nsum := by ring
    _ ≤ _ := add_le_add hd hn

lemma sum_affine_cost_bound {W a n nf cf kf : ℝ} (T : ℕ) (cost k : ℕ → ℝ)
    (hc : ∀ j, j < T → cost j ≤ W*(a*k j+n))
    (hf : cf ≤ W*(a*kf+nf)) :
    (∑ j ∈ Finset.range T,cost j)+cf ≤ W*(a*((∑ j ∈ Finset.range T,k j)+kf)+(T:ℝ)*n+nf) := by
  have hh := Finset.sum_le_sum (fun j (hj : j ∈ Finset.range T) => hc j (Finset.mem_range.mp hj))
  simp only [mul_add,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  nlinarith only [hh,hf]


lemma actual_saddle_cost {p σ L μ Δ G ε δ : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hm : 0 < μ) (hmL : μ ≤ L) (hΔ : 0 ≤ Δ) (he : 0 < ε)
    (hd : 0 < δ) (hd1 : δ ≤ 1) :
    let r := p/(p-1)
    let κ := L/μ
    let A := L*Δ/ε^2
    let u := σ/ε
    let Q := initialCostLog L μ Δ G ε
    let Λ := outerCostLog p σ L μ Δ G ε δ
    (saddleCalls p σ L μ Δ G ε δ : ℝ) ≤ ((2:ℝ)^80*r)^(r+2)*Λ^(2*r+3)*
      (Real.sqrt κ*(1+A+Q)+(A*κ^(r/2)+κ^r)*u^r) := by
  intro r κ A u Q Λ
  let T := outerSteps L Δ ε
  let ζc := coarseAccuracy L ε
  let ζf := fineAccuracy L μ ε
  let d := outerConfidence L Δ ε δ
  let B := fun j => coarseInitialBound L μ Δ G ζc T j
  let K := fun j => recoveryHalvings L μ ζc (B j) 0
  let Kf := recoveryHalvings L μ ζf (fineInitialBound L μ ε) 0
  let sc := σ/recoveryScale L μ ζc
  let sf := σ/recoveryScale L μ ζf
  let W := ((2:ℝ)^50*r)^(r+2)*2^(5*r+15)*Λ^(r+3)
  have hr := (conjugate_exponent_bounds hp hp2).1
  have hL := hm.trans_le hmL
  have hk : 1 ≤ κ := (le_div_iff₀ hm).mpr (by simpa using hmL)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hh := outer_parameter_controls (G:=G) hp hp2 hσ hm hmL hΔ he hd hd1
  have hQ : 0 ≤ Q := hh.1
  have hΛ : 1 ≤ Λ := hh.2.1
  have hζc : 0 < ζc := by dsimp [ζc,coarseAccuracy]; positivity
  have hζf : 0 < ζf := by dsimp [ζf,fineAccuracy]; positivity
  have hdc := outer_confidence_bounds (L:=L) (Δ:=Δ) (ε:=ε) hd hd1
  have hsc : 0 ≤ sc := div_nonneg hσ (recovery_scale_pos hm hζc).le
  have hsf : 0 ≤ sf := div_nonneg hσ (recovery_scale_pos hm hζf).le
  have hT : (T:ℝ) ≤ 2+4096*A := by
    have ht := outer_steps_upper (ε:=ε) hL.le hΔ
    linarith only [ht]
  have hcold : (K 0:ℝ)+1 ≤ 128*(1+Q) := by
    exact cold_count_bound hm hmL hΔ he
  have hwarm (j : ℕ) (hj : j ≠ 0) : (K j:ℝ)+1 ≤ 128*Λ := by
    dsimp only [K,B]
    simp only [coarseInitialBound,hj,ite_false]
    exact warm_count_bound hm hmL hΔ he hΛ hh.2.2.1 hh.2.2.2
  have hfine : (Kf:ℝ)+1 ≤ 128*Λ := fine_count_bound hm hmL he hΛ hh.2.2.1
  have hS := deterministic_outer_sum_bound hΛ hA hQ T Kf K hT hcold hwarm hfine
  have hn := outer_noise_scale_bounds hσ hm hmL he hΛ hh.2.2.1
  have hN := stochastic_outer_sum_bound T hr hk hΛ hu hA hT hsc hsf hn.1 hn.2
  have hlogs := actual_outer_recovery_log_bounds (G:=G) hp hp2 hσ hm hmL hΔ he hd hd1
  have hcost (j : ℕ) (_ : j < T) : (recoveryCalls p σ L μ ζc (B j) d:ℝ) ≤ W*(Real.sqrt κ*((K j:ℝ)+1)+sc^r) :=
    recovery_cost_with_common_log hp hp2 hσ hm hmL hζc hdc.1 hdc.2 hΛ (B j) (hlogs.1 j)
  have hcostf : (recoveryCalls p σ L μ ζf (fineInitialBound L μ ε) d:ℝ) ≤ W*(Real.sqrt κ*((Kf:ℝ)+1)+sf^r) :=
    recovery_cost_with_common_log hp hp2 hσ hm hmL hζf hdc.1 hdc.2 hΛ (fineInitialBound L μ ε) hlogs.2
  have hpre := sum_affine_cost_bound T (fun j => (recoveryCalls p σ L μ ζc (B j) d:ℝ))
    (fun j => (K j:ℝ)+1) hcost hcostf
  have hexeq : (saddleCalls p σ L μ Δ G ε δ:ℝ) =
      (∑ j ∈ Finset.range T,(recoveryCalls p σ L μ ζc (B j) d:ℝ))+
        (recoveryCalls p σ L μ ζf (fineInitialBound L μ ε) d:ℝ) := by
    unfold saddleCalls coarseCalls
    rw [LongTails.Proofs.StochasticEnvelopeExecution.slotCalls_sum]
    simp only [Nat.zero_add,Nat.cast_add,Nat.cast_sum]
    ring
  rw [← hexeq] at hpre
  exact outer_raw_cost_algebra hr hk hΛ hA hQ hu hS hN (by simpa only [add_assoc] using hpre)


end LongTails.Proofs.HeavyTailSaddleOuterCost
