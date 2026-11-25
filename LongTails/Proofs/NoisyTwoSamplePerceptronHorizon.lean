import LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
import Mathlib.Analysis.Complex.ExponentialBounds

open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronComplement

namespace LongTails.Proofs.NoisyTwoSamplePerceptronHorizon

noncomputable def ratio (p : Params) := ‖p.x₀‖^2/p.signal^2
noncomputable def scale (p : Params) := Real.sqrt p.d/p.μ
noncomputable def confidenceLog (p : Params) := Real.log (2^62*ratio p/p.ρ^3)
noncomputable def geometryLog (p : Params) := Real.log (2^15*scale p*ratio p)
noncomputable def factor (p : Params) := 2^27*confidenceLog p*geometryLog p
noncomputable def horizon (p : Params) := ⌈scale p*factor p*Real.log (scale p*factor p)⌉₊
noncomputable def noiseScale (p : Params) := max (p.d:ℝ) (Real.log ((horizon p:ℝ)/p.ρ))
noncomputable def sigma (p : Params) := p.signal/(4096*(horizon p:ℝ)*Real.sqrt (noiseScale p))
noncomputable def noiseBound (p : Params) := p.signal/(1024*(horizon p:ℝ))

lemma signal_le_norm {d : ℕ} (i : Fin d) (hi : finRotate d i ≠ i)
    (x : LongTails.Setups.FiniteLogisticTwoTap.Weights d) : |slowProjection i x| ≤ ‖x‖ := by
  have H := abs_real_inner_le_norm (TwoTapGaussianBounds.mode i (-1)) x
  rw [TwoTapGaussianBounds.mode_unit i hi (by norm_num),one_mul,TwoTapGaussianBounds.mode_inner] at H
  convert H using 1
  rw [← abs_neg]
  congr 1
  dsimp [slowProjection]
  ring

lemma valid_scales (p : Params) (hp : spec.valid p) :
    14 ≤ scale p ∧ 1 ≤ ratio p ∧ 1 ≤ confidenceLog p ∧ 1 ≤ geometryLog p ∧
      1 ≤ Real.log (scale p*factor p) ∧ 1 ≤ horizon p := by
  obtain ⟨hd,hμ,hμ',hs,⟨i,hi⟩,hρ,hρ'⟩ := hp
  have hn : NeZero p.d := ⟨by omega⟩
  have hne : finRotate p.d i ≠ i := by simp [finRotate_apply]; omega
  have hV := hi.trans (signal_le_norm i hne p.x₀)
  have hC : 1 ≤ ratio p := (one_le_div (sq_pos_of_pos hs)).mpr (pow_le_pow_left₀ hs.le hV 2)
  have hD : (2:ℝ) ≤ p.d := by exact_mod_cast hd
  have hX : 14 ≤ scale p := by
    apply (le_div_iff₀ hμ).mpr
    nlinarith [Real.sqrt_nonneg (p.d:ℝ),Real.sq_sqrt (by positivity : (0:ℝ) ≤ p.d)]
  have hLg {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (Real.exp_one_lt_three.le.trans hx)
  have hρ₃ : p.ρ^3 ≤ 1 := by simpa using pow_le_pow_left₀ hρ.le hρ'.le 3
  have h₁ : 1 ≤ confidenceLog p := hLg ((le_div_iff₀ (pow_pos hρ _)).mpr (by linarith))
  have h₂ : 1 ≤ geometryLog p := hLg (by nlinarith [mul_le_mul_of_nonneg_left hC (by linarith : 0 ≤ scale p)])
  have hF : 1 ≤ factor p := by
    dsimp [factor]
    nlinarith [mul_le_mul h₁ h₂ (by norm_num) (by linarith)]
  have hXF : 3 ≤ scale p*factor p := by nlinarith [mul_le_mul_of_nonneg_left hF (by linarith : 0 ≤ scale p)]
  have hU := hLg hXF
  refine ⟨hX,hC,h₁,h₂,hU,?_⟩
  change 1 ≤ ⌈_⌉₊
  apply Nat.ceil_pos.mpr
  positivity

lemma delta_bounds (p : Params) (hp : spec.valid p) :
    0 < gamma p.d*p.μ ∧ gamma p.d*p.μ ≤ 1/56 ∧
      0 ≤ Real.sqrt 2/Real.sqrt p.d ∧ Real.sqrt 2/Real.sqrt p.d ≤ 1 ∧
      0 ≤ Real.sqrt (1-2/(p.d:ℝ)) ∧ Real.sqrt (1-2/(p.d:ℝ)) ≤ 1 := by
  have hd : (2:ℝ) ≤ p.d := by exact_mod_cast hp.1
  have hμ := hp.2.1
  have hs := Real.sqrt_pos.mpr (show (0:ℝ) < p.d by linarith)
  have hx := (valid_scales p hp).1
  have H : gamma p.d*p.μ = 1/(4*scale p) := by dsimp [gamma,scale]; field_simp
  refine ⟨by dsimp [gamma]; positivity,?_,by positivity,?_,Real.sqrt_nonneg _,?_⟩
  · rw [H]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  · exact (div_le_one hs).mpr (Real.sqrt_le_sqrt hd)
  · apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [div_nonneg (by norm_num : 0 ≤ (2:ℝ)) (by linarith : (0:ℝ) ≤ p.d)]⟩

noncomputable def terminalBound (p : Params) := 16*‖p.x₀‖*(2^15*scale p*ratio p)
noncomputable def blockLength (p : Params) := ⌈4096*confidenceLog p*Real.log (scale p*factor p)⌉₊+1

lemma horizon_bounds (p : Params) (hp : spec.valid p) :
    let T := (horizon p : ℝ)
    let U := Real.log (scale p*factor p)
    let L := confidenceLog p
    5 ≤ Real.log T ∧ Real.log T ≤ 3*U ∧
    5 ≤ noiseScale p ∧ Real.log (noiseScale p) ≤ 3*U+L ∧
    Real.log (ratio p) ≤ L ∧ Real.log (1/p.ρ) ≤ L ∧ Real.log (scale p) ≤ U := by
  obtain ⟨hx,hC,hL,hG,hU,hT⟩ := valid_scales p hp
  have hρ := hp.2.2.2.2.2.1
  have hρ' := hp.2.2.2.2.2.2
  have hμ := hp.2.1
  have hμ' := hp.2.2.1
  let Z := scale p*factor p
  have hZ := Real.exp_log (show 0 < Z by dsimp [Z,factor]; positivity)
  have hF : 2^27 ≤ factor p := by
    dsimp [factor]
    nlinarith [mul_le_mul hL hG (by norm_num) (by linarith)]
  have hZ' : 2^27 ≤ Z := by
    nlinarith [mul_le_mul_of_nonneg_right hx (by linarith : 0 ≤ factor p)]
  intro T U L
  have hT' : Z*U ≤ T := Nat.le_ceil _
  have hTU : Z*U ≤ Z^2 := by
    dsimp [U]
    change Z*Real.log Z ≤ Z^2
    nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (show 0 < Z by linarith))
      (show 0 ≤ Z by linarith)]
  have hT₀ : 0 < T := by dsimp [T]; exact_mod_cast (by omega : 0 < horizon p)
  have H₁ : 5 ≤ Real.log T := by
    apply (Real.le_log_iff_exp_le hT₀).mpr
    have hE : Real.exp 5 ≤ 3^5 := by
      rw [show (5:ℝ)=(5:ℕ)*1 by norm_num,Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 5
    have hQU := mul_le_mul_of_nonneg_left hU (show 0 ≤ Z by linarith)
    change Z*1 ≤ Z*U at hQU
    linarith
  have H₂ : Real.log T ≤ 3*U := by
    have hceil : T ≤ Z*U+1 := (Nat.ceil_lt_add_one (show 0 ≤ Z*U by positivity)).le
    have hT₂ : T ≤ Z^3 := by
      nlinarith [mul_nonneg (show 0 ≤ Z-2 by linarith) (sq_nonneg Z),sq_nonneg (Z-1)]
    have HH := Real.log_le_log hT₀ hT₂
    rw [Real.log_pow] at HH
    exact_mod_cast HH
  have hρ₃ : p.ρ^3 ≤ 1 := by simpa using pow_le_pow_left₀ hρ.le hρ'.le 3
  have hLC : Real.log (ratio p) ≤ L := by
    apply Real.log_le_log (by linarith)
    apply (le_div_iff₀ (pow_pos hρ 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hρ₃ (by linarith : 0 ≤ ratio p)]
  have hLρ : Real.log (1/p.ρ) ≤ L := by
    apply Real.log_le_log (by positivity)
    apply (div_le_div_iff₀ hρ (pow_pos hρ 3)).mpr
    have H := pow_le_pow_left₀ hρ.le hρ'.le 2
    nlinarith [mul_le_mul_of_nonneg_left H hρ.le,mul_le_mul_of_nonneg_left hC hρ.le]
  have hUX : Real.log (scale p) ≤ U := by
    apply Real.log_le_log (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left (show 1 ≤ factor p by linarith) (by linarith : 0 ≤ scale p)]
  have hTr : Real.log (T/p.ρ) = Real.log T+Real.log (1/p.ρ) := by
    rw [Real.log_div hT₀.ne' hρ.ne',Real.log_div one_ne_zero hρ.ne',Real.log_one]
    ring
  have hM : 5 ≤ noiseScale p := by
    apply le_trans _ (le_max_right _ _)
    change 5 ≤ Real.log (T/p.ρ)
    rw [hTr]
    linarith [Real.log_nonneg ((one_le_div hρ).mpr hρ'.le)]
  refine ⟨H₁,H₂,hM,?_,hLC,hLρ,hUX⟩
  have hd : (0:ℝ) < p.d := by exact_mod_cast (by have := hp.1; omega : 0 < p.d)
  have hs := Real.sq_sqrt hd.le
  dsimp only [noiseScale]
  rw [max_def]
  split
  · change Real.log (Real.log (T/p.ρ)) ≤ _
    rw [hTr]
    have hpos : 0 < Real.log T+Real.log (1/p.ρ) := by
      linarith [Real.log_nonneg ((one_le_div hρ).mpr hρ'.le)]
    linarith [Real.log_le_sub_one_of_pos hpos]
  · have hh : Real.sqrt p.d ≤ scale p := by
      apply (le_div_iff₀ hμ).mpr
      exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (by change p.μ ≤ 1; change p.μ ≤ 1/10 at hμ'; linarith)
    have H := Real.log_le_log hd (show (p.d:ℝ) ≤ (scale p)^2 by nlinarith [pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2])
    rw [Real.log_pow] at H
    push_cast at H
    linarith

lemma count_budget (p : Params) (hp : spec.valid p) :
    (7*scale p*geometryLog p+1)*(blockLength p:ℝ) ≤ horizon p := by
  obtain ⟨hx,_,hL,hG,hU,_⟩ := valid_scales p hp
  let U := Real.log (scale p*factor p)
  have h₁ : 1 ≤ scale p*geometryLog p := one_le_mul_of_one_le_of_one_le (by linarith) hG
  have h₂ : 1 ≤ confidenceLog p*U := one_le_mul_of_one_le_of_one_le hL hU
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ 4096*confidenceLog p*U by nlinarith only [h₂])).le
  have hB : (blockLength p:ℝ) ≤ 4100*(confidenceLog p*U) := by
    dsimp [blockLength]
    push_cast
    linarith only [hc,h₂]
  have hT : scale p*factor p*U ≤ horizon p := Nat.le_ceil _
  apply le_trans _ hT
  have hh := mul_le_mul (show 7*scale p*geometryLog p+1 ≤ 8*(scale p*geometryLog p) by linarith)
    hB (Nat.cast_nonneg _) (by nlinarith only [h₁])
  dsimp [factor]
  nlinarith only [hh,mul_nonneg (by linarith only [h₁] : 0 ≤ scale p*geometryLog p)
    (by linarith only [h₂] : 0 ≤ confidenceLog p*U)]

lemma block_dilution (p : Params) (hp : spec.valid p) :
    let n := blockLength p - 1
    2*terminalBound p/((1+c)^n*sigma p) ≤ p.ρ/(2*(horizon p:ℝ)) := by
  obtain ⟨hx,hC,hL,hG,hU,hT⟩ := valid_scales p hp
  obtain ⟨_,hTU,hM,hLM,hLC,hLρ,hUX⟩ := horizon_bounds p hp
  have hr := hp.2.2.2.2.2.1
  have hs := hp.2.2.2.1
  let T := (horizon p:ℝ)
  let M := noiseScale p
  let U := Real.log (scale p*factor p)
  let L := confidenceLog p
  have hT₀ : 0 < T := by dsimp [T]; exact_mod_cast (by omega : 0 < horizon p)
  have hM₀ : 0 < M := by dsimp [M]; linarith
  have hC₀ : 0 < ratio p := by linarith
  have hX₀ : 0 < scale p := by linarith
  have hV : ‖p.x₀‖ ≤ ratio p*p.signal := by
    have HC := (one_le_div (sq_pos_of_pos hs)).mp hC
    dsimp [ratio]
    rw [div_mul_eq_mul_div,le_div_iff₀ (sq_pos_of_pos hs)]
    have H : p.signal ≤ ‖p.x₀‖ := by nlinarith [norm_nonneg p.x₀]
    nlinarith only [mul_le_mul_of_nonneg_right H (mul_nonneg (norm_nonneg p.x₀) hs.le)]
  let J := 2^33*scale p*(ratio p)^2*T^2*M*(1/p.ρ)
  have hJ₀ : 0 < J := by dsimp [J]; positivity
  have hlogJ : Real.log J ≤ 51*L*U := by
    have H₁ : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)]
    have hlog : Real.log J = 33*Real.log 2+Real.log (scale p)+2*Real.log (ratio p)+
        2*Real.log T+Real.log M+Real.log (1/p.ρ) := by
      dsimp [J]
      repeat rw [Real.log_mul (by positivity) (by positivity)]
      simp [Real.log_pow]
    rw [hlog]
    change Real.log T ≤ 3*U at hTU
    change Real.log M ≤ 3*U+L at hLM
    change Real.log (scale p) ≤ U at hUX
    change Real.log (ratio p) ≤ L at hLC
    change Real.log (1/p.ρ) ≤ L at hLρ
    change 1 ≤ L at hL
    change 1 ≤ U at hU
    nlinarith only [H₁,hTU,hLM,hUX,hLC,hLρ,mul_le_mul_of_nonneg_left hU (le_trans zero_le_one hL),
      mul_le_mul_of_nonneg_right hL (le_trans zero_le_one hU),
      mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hU),hL,hU]
  have hc₀ : 0 ≤ c := by dsimp [c]; positivity
  have hc' : 1/4 ≤ Real.log (1+c) := by
    have hh := Real.le_log_one_add_of_nonneg hc₀
    apply le_trans _ hh
    apply (le_div_iff₀ (by linarith)).mpr
    dsimp [c]
    nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num),Real.sqrt_nonneg 2]
  intro n
  have hn : 4096*L*U ≤ (n:ℝ) := by
    dsimp [n,blockLength]; exact Nat.le_ceil _
  have hpow : J ≤ (1+c)^n := by
    apply (Real.log_le_log_iff hJ₀ (by positivity)).mp
    rw [Real.log_pow]
    have hLU := mul_nonneg (show 0 ≤ L by exact le_trans zero_le_one hL) (show 0 ≤ U by exact le_trans zero_le_one hU)
    nlinarith only [hlogJ,hn,mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg n),hLU]
  have hS : 0 < sigma p := by dsimp [sigma]; positivity
  apply (div_le_div_iff₀ (mul_pos (by positivity) hS) (by positivity)).mpr
  change 2*(16*‖p.x₀‖*(2^15*scale p*ratio p))*(2*T) ≤ p.ρ*((1+c)^n*(p.signal/(4096*T*Real.sqrt M)))
  rw [← mul_div_assoc,← mul_div_assoc,le_div_iff₀ (by positivity)]
  have hroot : Real.sqrt M ≤ M := Real.sqrt_le_self_iff.mpr (Or.inr (by dsimp [M]; linarith))
  have hprod := mul_le_mul hV hroot (Real.sqrt_nonneg _) (mul_nonneg hC₀.le hs.le)
  have HJ : (2^33*scale p*ratio p^2*T^2*M) ≤ p.ρ*(1+c)^n := by
    dsimp [J] at hpow
    rw [← div_eq_mul_one_div,div_le_iff₀ hr] at hpow
    linarith
  nlinarith only [mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (mul_nonneg hX₀.le hC₀.le) (sq_nonneg T)),
    mul_le_mul_of_nonneg_right HJ hs.le]

end LongTails.Proofs.NoisyTwoSamplePerceptronHorizon
