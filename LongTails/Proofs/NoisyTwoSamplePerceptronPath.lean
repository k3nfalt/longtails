import LongTails.Proofs.NoisyTwoSamplePerceptronHorizon
import LongTails.Proofs.NoisyTwoSamplePerceptronGaussian

open scoped RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap (Weights signedInput answer Separates)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronExecution
open LongTails.Proofs.NoisyTwoSamplePerceptronDynamics
open LongTails.Proofs.NoisyTwoSamplePerceptronSignal
open LongTails.Proofs.NoisyTwoSamplePerceptronComplement
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronHorizon

namespace LongTails.Proofs.NoisyTwoSamplePerceptronPath

def count (b : ℕ → Bool) (n : ℕ) := ∑ j ∈ Finset.range n, if b j then 1 else 0

lemma count_succ (b : ℕ → Bool) (n : ℕ) : count b (n+1) = count b n + (if b n then 1 else 0) :=
  Finset.sum_range_succ ..

lemma normalized_prefix (T : ℕ) (b : ℕ → Bool) (u : ℕ → ℝ) {q e : ℝ}
    (hq : 1 ≤ q) (he : 0 ≤ e) (hu : ∀ i, 0 ≤ u i)
    (hone : ∀ i < T, u (i+1) ≤ 2*u i+e)
    (hrep : ∀ i, i+2 ≤ T → b i=b (i+1) → u (i+1) ≤ u i+2*e)
    (hmix : ∀ i, i+2 ≤ T → b i≠b (i+1) → u (i+2) ≤ q*u i+3*e)
    (n : ℕ) (hn : n ≤ T) :
    u n ≤ q^(count b n)*(2*u 0+4*n*e) := by
  let v := fun t => u t/q^(count b t)
  have hp (t : ℕ) : 0 < q^(count b t) := pow_pos (by linarith) _
  have hmono (t : ℕ) : q^(count b t) ≤ q^(count b (t+1)) := by
    apply pow_le_pow_right₀ hq
    rw [count_succ]
    omega
  have H (i : ℕ) (k : ℝ) (hk : 0 ≤ k) (l : ℝ) (hl : 0 ≤ l)
      (hs : u (i+1) ≤ k*u i+l) : v (i+1) ≤ k*v i+l := by
    dsimp [v]
    rw [div_le_iff₀ (hp _)]
    have h₁ : u i/q^(count b i)*q^(count b (i+1)) ≥ u i := by
      calc
        u i = u i/q^(count b i)*q^(count b i) := (div_mul_cancel₀ _ (hp _).ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (hmono _) (div_nonneg (hu _) (hp _).le)
    have h₂ := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := count b (i+1)) hq) hl
    nlinarith only [hs,mul_le_mul_of_nonneg_left h₁ hk,h₂]
  have hh := partition_prefix v T he (fun i hi => H i 2 (by norm_num) e he (hone i hi))
    (fun i hi => by
      by_cases hb : b i=b (i+1)
      · left
        simpa using H i 1 zero_le_one (2*e) (by linarith) (by simpa using hrep i hi hb)
      · right
        have hc : count b (i+2)=count b i+1 := by
          rw [count_succ,count_succ]
          cases h : b i <;> cases h' : b (i+1) <;> simp_all
        dsimp [v]
        rw [div_le_iff₀ (hp _),hc,pow_succ]
        have hh' := div_mul_cancel₀ (u i) (hp i).ne'
        have H₁ : 1 ≤ q^(count b i)*q := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq) hq
        nlinarith only [hmix i hi hb,congrArg (fun z : ℝ => z*q) hh',
          mul_le_mul_of_nonneg_right H₁ (show 0 ≤ 3*e by linarith)])
    (fun i => div_nonneg (hu _) (hp _).le) 0 n (by omega)
  rw [Nat.zero_add] at hh
  change u n/q^(count b n) ≤ 2*(u 0/q^(count b 0))+4*n*e at hh
  simpa [count, mul_comm] using (div_le_iff₀ (hp n)).mp hh

lemma slow_move {d : ℕ} (μ η σ : ℝ) (i : Fin d) (hi : finRotate d i ≠ i) (x g : Weights d) (b : Bool) :
    slowProjection i (move μ η σ i x g b) = (if b then 1+η*μ else 1)*slowProjection i x+
      σ*slowProjection i g := by
  simp only [move,slow_add,slow_smul,answer]
  cases b <;> simp [slow_first,slow_second _ _ hi]
  ring

lemma projected_move_bounds (p : Params) (hp : spec.valid p) (i : Fin p.d)
    (hi : finRotate p.d i ≠ i) (σ e : ℝ) (g : ℕ → Weights p.d)
    (X : ℕ → Weights p.d) (b : ℕ → Bool) (T : ℕ) (he : 0 ≤ e)
    (hstep : ∀ n < T, X (n+1) = move p.μ (gamma p.d) σ i (X n) (g n) (b n))
    (hmargin : ∀ n < T, (answer (signedInput p.μ i (b n)) (X n)).margin ≤ 0)
    (hnoise : ∀ n < T, ‖σ • proj (coords i (g n))‖ ≤ e) (n : ℕ) (hn : n ≤ T) :
    let u := fun k => ‖proj (coords i (X k))‖
    u n ≤ (1+gamma p.d*p.μ/2)^(count b n)*(2*u 0+4*n*e) := by
  let δ := gamma p.d*p.μ
  let a := Real.sqrt 2/Real.sqrt p.d
  let B := Real.sqrt (1-2/(p.d:ℝ))
  let R := fun j => proj (coords i (X j))
  let E := fun j => σ • proj (coords i (g j))
  obtain ⟨hδ,hδ',ha,ha',hB,hB'⟩ := delta_bounds p hp
  change 0 < δ at hδ
  have hL (v : Bool) := matrix_norm hδ.le hδ' ha ha' hB hB' v
  have H (j : ℕ) (hj : j < T) : R (j+1)=R j+matrix δ a B (b j) (R j)+E j := by
    dsimp [R,E]
    rw [hstep _ hj,proj_move hp.1 i hi]
  have hnon (j : ℕ) (hj : j < T) : ⟪matrix δ a B (b j) (R j),R j⟫ ≤ 0 := by
    have K := score_split hp.1 i p.μ (X j) (b j)
    have hγ : 0 ≤ gamma p.d := by dsimp [gamma]; positivity
    have HM := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*gamma p.d) (hmargin j hj)
    cases h : b j <;> simp only [h,Bool.false_eq_true,ite_false,ite_true,add_zero] at K HM ⊢
    · exact K ▸ HM
    · rw [K] at HM
      exact le_of_add_le_of_nonneg_left HM (mul_nonneg hδ.le (sq_nonneg _))
  apply normalized_prefix T b (fun j => ‖R j‖) (by linarith : 1 ≤ 1+δ/2) he (fun _ => norm_nonneg _) _ _ _ n hn
  · intro j hj
    rw [H j hj]
    have K := ((matrix δ a B (b j)).le_opNorm (R j)).trans
      (mul_le_mul_of_nonneg_right (hL _) (norm_nonneg _))
    linarith only [norm_add_le (R j+matrix δ a B (b j) (R j)) (E j),
      norm_add_le (R j) (matrix δ a B (b j) (R j)),K,hnoise j hj,norm_nonneg (R j)]
  · intro j hj heq
    have K := hnon (j+1) (by omega)
    rw [← heq] at K
    have hsym (x y : _) : ⟪matrix δ a B (b j) x,y⟫=⟪x,matrix δ a B (b j) y⟫ := by
      cases b j <;> apply action_symmetric
    have HH := repeated_move _ hsym (hL _) _ _ _ (H j (by omega)) K
    linarith only [HH,hnoise j (by omega)]
  · intro j hj heq
    have hflip : b (j+1) = !(b j) := by cases h : b j <;> cases hh : b (j+1) <;> simp_all
    rw [H (j+1) (by omega),hflip]
    have HH := mixed_noisy hδ.le hδ' ha ha' hB hB' (b j) (R j) (R (j+1)) (E j) (E (j+1)) (H j (by omega))
    linarith only [HH,hnoise j (by omega),hnoise (j+1) (by omega)]

lemma signal_prefix (p : Params) (hp : spec.valid p) (i : Fin p.d)
    (hi : finRotate p.d i ≠ i) (σ e : ℝ) (g : ℕ → Weights p.d)
    (X : ℕ → Weights p.d) (b : ℕ → Bool) (T : ℕ) (he : 0 ≤ e)
    (hstep : ∀ n < T, X (n+1) = move p.μ (gamma p.d) σ i (X n) (g n) (b n))
    (hnoise : ∀ n < T, |σ*slowProjection i (g n)| ≤ e) (n : ℕ) (hn : n ≤ T) :
    (1+gamma p.d*p.μ)^(count b n)*(|slowProjection i (X 0)|-n*e) ≤ |slowProjection i (X n)| := by
  let δ := gamma p.d*p.μ
  have hδ : 0 < δ := (delta_bounds p hp).1
  induction n with
  | zero => simp [count]
  | succ n ih =>
    have IH := ih (by omega)
    let a := if b n then 1+δ else 1
    have ha : 0 ≤ a := by dsimp [a]; split <;> linarith
    have hpow : (1+δ)^count b (n+1) = a*(1+δ)^count b n := by
      rw [count_succ]
      cases h : b n <;> simp [h,a,pow_succ,mul_comm]
    have H := slow_move p.μ (gamma p.d) σ i hi (X n) (g n) (b n)
    change _ = a*slowProjection i (X n)+σ*slowProjection i (g n) at H
    rw [← hstep n (by omega)] at H
    have Hab := abs_sub (slowProjection i (X (n+1))) (σ*slowProjection i (g n))
    rw [H,add_sub_cancel_right,abs_mul,abs_of_nonneg ha] at Hab
    rw [← H] at Hab
    change (1+δ)^count b (n+1)*_ ≤ _
    have h1 := one_le_pow₀ (n := count b (n+1)) (show 1 ≤ 1+δ by linarith)
    change (1+δ)^count b n*_ ≤ _ at IH
    rw [Nat.cast_succ]
    nlinarith only [mul_le_mul_of_nonneg_left IH ha,Hab,hnoise n (by omega),H,
      mul_le_mul_of_nonneg_right h1 he,congrArg (fun z : ℝ => z*(|slowProjection i (X 0)|-n*e)) hpow]

lemma gap_count {δ X C : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/56) (hX : 4*X*δ=1)
    (hC : 1 ≤ C) (m : ℕ) (hweak : ((1+δ)/(1+δ/2))^(2*m) ≤ 512*X*C) :
    (m:ℝ) ≤ 6*X*Real.log (2^15*X*C) := by
  have hx : 0 < X := by_contra (by intro h; nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hδ.le])
  let v := δ/(2+δ)
  have hv : 0 < v := div_pos hδ (by linarith)
  have Hrat : (1+δ)/(1+δ/2) = 1+v := by dsimp [v]; field_simp; ring
  have hlog := Real.le_log_one_add_of_nonneg hv.le
  have hsmall : δ/3 ≤ Real.log (1+v) := by
    apply le_trans _ hlog
    dsimp [v]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hδ' hδ.le]
  have hweak' := Real.log_le_log (by positivity) hweak
  rw [Real.log_pow,Hrat] at hweak'
  push_cast at hweak'
  have hC₀ : 0 < C := by linarith
  have hbig := Real.log_le_log (show 0 < 512*X*C by positivity)
    (show 512*X*C ≤ 2^15*X*C by nlinarith [mul_nonneg hx.le (by linarith : 0 ≤ C)])
  have H : (2:ℝ)*m*(δ/3) ≤ Real.log (2^15*X*C) :=
    (mul_le_mul_of_nonneg_left hsmall (by positivity)).trans (hweak'.trans hbig)
  have HH := mul_le_mul_of_nonneg_left H hx.le
  have Hm : (m:ℝ)*(4*X*δ) = m := by rw [hX,mul_one]
  calc
    (m:ℝ) = 6*(X*((2:ℝ)*m*(δ/3))) := by linear_combination -Hm
    _ ≤ 6*(X*Real.log (2^15*X*C)) := mul_le_mul_of_nonneg_left HH (by norm_num)
    _ = _ := by ring

lemma option_two_count (p : Params) (hp : spec.valid p) (i : Fin p.d) (X : Weights p.d)
    (m : ℕ) (hs : (1+gamma p.d*p.μ)^m*p.signal/2 ≤ |slowProjection i X|)
    (hr : ‖proj (coords i X)‖ ≤ (1+gamma p.d*p.μ/2)^m*(8*‖p.x₀‖))
    (hm : (answer (signedInput p.μ i true) X).margin ≤ 0) :
    (m:ℝ) ≤ 6*scale p*geometryLog p := by
  let δ := gamma p.d*p.μ
  let R := proj (coords i X)
  let A := matrix δ (Real.sqrt 2/Real.sqrt p.d) (Real.sqrt (1-2/(p.d:ℝ))) true
  obtain ⟨hd,hd',ha,ha',hb,hb'⟩ := delta_bounds p hp
  change 0 < δ at hd
  have hγ : 0 ≤ gamma p.d := by dsimp [gamma]; positivity
  have hδX : 4*scale p*δ=1 := by
    have hD : (0:ℝ) < p.d := by exact_mod_cast (by have := hp.1; omega : 0 < p.d)
    have hs₀ := hp.2.1.ne'
    dsimp [δ,scale,gamma]; field_simp
  have HH := score_split hp.1 i p.μ X true
  change 2*gamma p.d*(answer (signedInput p.μ i true) X).margin =
    ⟪A R,R⟫+δ*(slowProjection i X)^2 at HH
  have H₁ := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2*gamma p.d) hm
  have H₂ := (abs_le.mp (abs_real_inner_le_norm (A R) R)).1
  have H₃ := (A.le_opNorm R).trans (mul_le_mul_of_nonneg_right (matrix_norm hd.le hd' ha ha' hb hb' true) (norm_nonneg _))
  have H : δ*(slowProjection i X)^2 ≤ ‖R‖^2/2 := by
    nlinarith only [HH,H₁,H₂,mul_le_mul_of_nonneg_right H₃ (norm_nonneg R)]
  have hs₀ := hp.2.2.2.1
  let Q := 1+δ
  let q := 1+δ/2
  have hQ : 0 < Q := by dsimp [Q]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  change Q^m*p.signal/2 ≤ _ at hs
  change ‖R‖ ≤ q^m*(8*‖p.x₀‖) at hr
  have HS := pow_le_pow_left₀ (by positivity) hs 2
  rw [sq_abs] at HS
  have HR := pow_le_pow_left₀ (norm_nonneg R) hr 2
  apply gap_count hd hd' hδX (valid_scales p hp).2.1 m
  change (Q/q)^(2*m) ≤ 512*scale p*ratio p
  rw [mul_comm 2 m,pow_mul,div_pow,div_pow]
  dsimp [ratio]
  have hqpos : 0 < (q^m)^2 := by positivity
  rw [div_le_iff₀ hqpos]
  field_simp [hs₀.ne']
  have HH' : δ*(Q^m)^2*p.signal^2 ≤ 128*(q^m)^2*‖p.x₀‖^2 := by
    nlinarith only [H,HR,mul_le_mul_of_nonneg_left HS hd.le]
  have hx := (valid_scales p hp).1
  nlinarith only [mul_le_mul_of_nonneg_left HH' (show 0 ≤ scale p by linarith),
    congrArg (fun y : ℝ => y*(Q^m)^2*p.signal^2) hδX]

end LongTails.Proofs.NoisyTwoSamplePerceptronPath
