import LongTails.Proofs.NoisyTwoSamplePerceptronPath
import LongTails.Proofs.NoisyTwoSamplePerceptronBlocks

open LongTails.Setups.FiniteLogisticTwoTap (Weights signedInput answer Separates)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronExecution
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
open LongTails.Proofs.NoisyTwoSamplePerceptronGaussian
open LongTails.Proofs.NoisyTwoSamplePerceptronComplement
open LongTails.Proofs.NoisyTwoSamplePerceptronPath
open LongTails.Proofs.NoisyTwoSamplePerceptronBlocks
open LongTails.Proofs.NoisyTwoSamplePerceptronHorizon

namespace LongTails.Proofs.NoisyTwoSamplePerceptronStopping

lemma count_mono (b : ℕ → Bool) : Monotone (count b) :=
  monotone_nat_of_le_succ (fun k => by rw [count_succ]; omega)

lemma has_block (b : ℕ → Bool) (T L : ℕ) (hL : 0 < L) (hT : (count b T+1)*L ≤ T) :
    ∃ s, s+L ≤ T ∧ ∀ j < L, b (s+j)=false := by
  by_contra! H
  have h (k : ℕ) (hk : k*L ≤ T) : k ≤ count b (k*L) := by
    induction k with
    | zero => omega
    | succ k ih =>
      rw [Nat.succ_mul] at hk ⊢
      obtain ⟨j,hj,hb⟩ := H (k*L) hk
      have HI := ih (by omega)
      have HH := count_mono b (show k*L ≤ k*L+j by omega)
      have HH' := count_mono b (show k*L+j+1 ≤ k*L+L by omega)
      have hyes : b (k*L+j)=true := by cases H : b (k*L+j) <;> simp_all
      rw [count_succ,hyes] at HH'
      simp at HH'
      omega
  have hh := (h (count b T+1) hT).trans (count_mono b hT)
  omega

lemma initial_residual {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i) (x : Weights d) :
    ‖proj (coords i x)‖ ≤ 3*‖x‖ := by
  have H := projected_bounds i x ‖x‖ (fun k => by
    have hh := ((component i k).le_opNorm x).trans (mul_le_mul_of_nonneg_right (component_norm hd i hi k) (norm_nonneg _))
    simpa [Real.norm_eq_abs] using hh)
  nlinarith [sq_nonneg (slowProjection i x),norm_nonneg x,norm_nonneg (proj (coords i x))]

lemma path_or_block (p : Params) (hp : spec.valid p) (i : Fin p.d) (hi : finRotate p.d i ≠ i)
    (hs : p.signal ≤ |slowProjection i p.x₀|) (g : ℕ → Weights p.d)
    (hnoise : ∀ n < horizon p,
      ‖sigma p • proj (coords i (g n))‖ ≤ noiseBound p ∧ |sigma p*slowProjection i (g n)| ≤ noiseBound p)
    (hfail : ¬Separates p.μ i (point p.μ (gamma p.d) (sigma p) i p.x₀ g (horizon p))) :
    ∃ s < horizon p, |forced p.μ (sigma p) i p.x₀ g s (blockLength p)| ≤ terminalBound p := by
  let T := horizon p
  let X := point p.μ (gamma p.d) (sigma p) i p.x₀ g
  let b := fun n => (choice p.μ i (X n)).getD false
  let e := noiseBound p
  let δ := gamma p.d*p.μ
  let q := 1+δ/2
  have hδ : 0 < δ := (delta_bounds p hp).1
  have hq : 1 ≤ q := by dsimp [q]; linarith
  obtain ⟨hx,hC,_,hG,_,hT⟩ := valid_scales p hp
  have hT₀ : 0 < (T:ℝ) := by exact_mod_cast (by change 0 < horizon p; omega : 0 < T)
  have hs₀ := hp.2.2.2.1
  have he : 0 ≤ e := by dsimp [e,noiseBound]; positivity
  have hTe : (T:ℝ)*e=p.signal/1024 := by
    change (T:ℝ)*(p.signal/(1024*T))=_
    field_simp
  have hV := hs.trans (signal_le_norm i hi p.x₀)
  have hchoice (n : ℕ) (hn : n < T) : choice p.μ i (X n) = some (b n) := by
    have H : ¬Separates p.μ i (X n) := by
      intro h
      have K := remains_separated p.μ (gamma p.d) (sigma p) i p.x₀ g n (T-n) h
      rw [Nat.add_sub_cancel' hn.le] at K
      exact hfail (K ▸ h)
    dsimp [b]
    cases h : choice p.μ i (X n) with
    | none => exact False.elim (H ((choice_none ..).mp h))
    | some v => rfl
  have hstep (n : ℕ) (hn : n < T) :
      X (n+1)=move p.μ (gamma p.d) (sigma p) i (X n) (g n) (b n) := by
    change (match choice p.μ i (X n) with
      | none => X n | some v => move p.μ (gamma p.d) (sigma p) i (X n) (g n) v) = _
    rw [hchoice n hn]
  have hmargin (n : ℕ) (hn : n < T) := choice_violated p.μ i (X n) (b n) (hchoice n hn)
  have HR (n : ℕ) (hn : n ≤ T) : ‖proj (coords i (X n))‖ ≤ q^(count b n)*(8*‖p.x₀‖) := by
    apply (projected_move_bounds p hp i hi (sigma p) e g X b T he hstep hmargin (fun k hk => (hnoise k hk).1) n hn).trans
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith : 0 ≤ q) _)
    change 2*‖proj (coords i p.x₀)‖+4*(n:ℝ)*e ≤ _
    nlinarith [initial_residual hp.1 i hi p.x₀,mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ T by exact_mod_cast hn) he]
  have HS (n : ℕ) (hn : n ≤ T) : (1+δ)^(count b n)*p.signal/2 ≤ |slowProjection i (X n)| := by
    have H := signal_prefix p hp i hi (sigma p) e g X b T he hstep (fun k hk => (hnoise k hk).2) n hn
    change (1+δ)^_*(|slowProjection i p.x₀|-n*e) ≤ _ at H
    apply le_trans _ H
    have HH : p.signal/2 ≤ |slowProjection i p.x₀|-n*e := by
      nlinarith [mul_le_mul_of_nonneg_right (show (n:ℝ) ≤ T by exact_mod_cast hn) he]
    nlinarith only [mul_le_mul_of_nonneg_left HH (pow_nonneg (show 0 ≤ 1+δ by linarith) (count b n))]
  have hcnt (n : ℕ) (hn : n ≤ T) : (count b n:ℝ) ≤ 7*scale p*geometryLog p := by
    induction n with
    | zero => simp only [count,Finset.range_zero,Finset.sum_empty,Nat.cast_zero]; nlinarith [mul_nonneg (show 0 ≤ scale p by linarith) (le_trans zero_le_one hG)]
    | succ n ih =>
      rw [count_succ]
      cases h : b n with
      | false => simpa using ih (by omega)
      | true =>
        have hm := hmargin n (by omega)
        rw [h] at hm
        have H := option_two_count p hp i (X n) _ (HS n (by omega)) (HR n (by omega)) hm
        simp only [↓reduceIte,Nat.cast_add,Nat.cast_one]
        nlinarith [mul_le_mul_of_nonneg_left hG (show 0 ≤ scale p by linarith)]
  have hrc (n : ℕ) (hn : n ≤ T) : |fast i (X n)| ≤ terminalBound p := by
    have hh := HR n hn
    have Hδ : δ*scale p=1/4 := by
      have hD : (0:ℝ) < p.d := by exact_mod_cast (by have := hp.1; omega : 0 < p.d)
      have hμ := hp.2.1.ne'
      dsimp [δ,scale,gamma]; field_simp
    have hL := Real.log_le_sub_one_of_pos (show 0 < q by linarith)
    have Hm := mul_le_mul_of_nonneg_right (hcnt n hn) hδ.le
    have Hpow : q^(count b n) ≤ 2^15*scale p*ratio p := by
      have hX : 0 < scale p := by linarith
      have hC₀ : 0 < ratio p := by linarith
      apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
      rw [Real.log_pow]
      change _ ≤ geometryLog p
      have H₁ : Real.log q ≤ δ/2 := by dsimp [q] at hL ⊢; linarith
      have H₂ : δ*scale p*geometryLog p=geometryLog p/4 := by rw [Hδ]; ring
      nlinarith only [Hm,H₂,hG,mul_le_mul_of_nonneg_left H₁ (Nat.cast_nonneg (count b n))]
    have hfast (k : Fin 4) : |proj (coords i (X n)) k| ≤ ‖proj (coords i (X n))‖ := by
      exact PiLp.norm_apply_le (p := 2) (proj (coords i (X n))) k
    rw [fast_value]
    dsimp [terminalBound]
    nlinarith only [abs_add_le (proj (coords i (X n)) 0) (proj (coords i (X n)) 1),
      hfast 0,hfast 1,hh,mul_le_mul_of_nonneg_right Hpow (norm_nonneg p.x₀)]
  have hL : 0 < blockLength p := Nat.succ_pos _
  have hB : (count b T+1)*blockLength p ≤ T := by
    exact_mod_cast (mul_le_mul_of_nonneg_right (add_le_add (hcnt T le_rfl) (le_refl (1:ℝ)))
      (Nat.cast_nonneg (blockLength p))).trans (count_budget p hp)
  obtain ⟨s,hst,hb⟩ := has_block b T (blockLength p) hL hB
  refine ⟨s,by omega,?_⟩
  rw [← follows_first hp.1 p.μ (sigma p) i hi p.x₀ g s (blockLength p) (fun j hj => by
    rw [hchoice _ (by omega),hb j hj])]
  exact hrc _ hst

end LongTails.Proofs.NoisyTwoSamplePerceptronStopping
