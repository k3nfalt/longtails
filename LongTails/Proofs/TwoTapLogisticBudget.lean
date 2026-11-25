import LongTails.Proofs.TwoTapLogisticDescent

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoTapLogisticBudget

open LongTails.Setups.TwoTapLogisticSeparation
open LongTails.Setups.TwoSampleQuadraticPerceptron (Space Features shift)
open LongTails.Algorithms.TwoTapLogisticGd
open LongTails.Proofs.LogisticRiskBudget
open LongTails.Proofs.TwoTapLogisticDescent

variable (p : Params) (X : Data p)

noncomputable def drift := |imbalance p p.start|+2
noncomputable def floorEnergy := if p.δ ≤ surplus p then p.δ/2 else min 1 ((p.δ/p.R)^2/(1+drift p))
noncomputable def scale := 5*(2+(drift p+2)/floorEnergy p)
noncomputable def initialBound := energy p p.start+2
noncomputable def radiusFactor := 4*Real.sqrt (scale p)/p.γ
noncomputable def curvature := initialBound p+4*radiusFactor p
noncomputable def augmented (θ : Space .conv p.d) := energy p θ+2*stepSize p*risk p X θ

lemma energy_nonneg (θ : Space .conv p.d) : 0 ≤ energy p θ := by
  unfold energy tapEnergy; positivity

lemma floor_pos (hp : spec.valid p) : 0 < floorEnergy p := by
  obtain ⟨hR,hγ,hδ⟩ := hp
  unfold floorEnergy drift
  split
  · positivity
  · apply lt_min <;> positivity

lemma scale_pos (hp : spec.valid p) : 0 < scale p := by
  have hu := floor_pos p hp
  unfold scale drift
  positivity

lemma curvature_pos (hp : spec.valid p) : 0 < curvature p := by
  obtain ⟨hR,hγ,hδ⟩ := hp
  have hE := energy_nonneg p p.start
  unfold curvature initialBound radiusFactor
  positivity

noncomputable def invStep :=
  let L := 1+8*p.R+32*p.R^2*curvature p
  L+(if p.δ ≤ surplus p then 4/p.δ else 0)

lemma tuning_eq : stepSize p = 1/invStep p := rfl

lemma tuning_limits (hp : spec.valid p) :
    0 < stepSize p ∧ stepSize p ≤ 1 ∧ stepSize p*p.R ≤ 1/8 ∧
      stepSize p*p.R^2*curvature p ≤ 1/32 := by
  have hm := curvature_pos p hp
  obtain ⟨hR,hγ,hδ⟩ := hp
  have hb : 1+8*p.R+32*p.R^2*curvature p ≤ invStep p := by
    unfold invStep
    split
    · apply le_add_of_nonneg_right
      positivity
    · simp
  have hd : 0 < invStep p := (by positivity : 0 < 1+8*p.R+32*p.R^2*curvature p).trans_le hb
  rw [tuning_eq]
  refine ⟨by positivity, (div_le_iff₀ hd).2 ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (sq_nonneg p.R) hm.le]
  · rw [div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (sq_nonneg p.R) hm.le]
  · rw [div_mul_eq_mul_div,div_mul_eq_mul_div,one_mul]
    apply (div_le_iff₀ hd).2
    nlinarith

lemma initial_risk (hp : spec.valid p) (h0 : Initial p X) : risk p X p.start ≤ 1 := by
  rcases h0 with h|⟨h,_⟩
  · linarith [hp.2.2,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  · exact h

lemma lower_taps (hp : spec.valid p) (θ : Space .conv p.d)
    (hX : ∀ i, ‖X i‖ ≤ p.R) (hF : risk p X θ ≤ Real.log 2-p.δ)
    (hD : |imbalance p θ| ≤ drift p) : min 1 ((p.δ/p.R)^2/(1+drift p)) ≤ tapEnergy p θ := by
  obtain ⟨hR,hγ,hδ⟩ := hp
  have hU : 0 ≤ tapEnergy p θ := by unfold tapEnergy; positivity
  have ht := mean_margin_bound p X θ hX
  have hh : p.δ/p.R ≤ Real.sqrt (tapEnergy p θ)*‖θ.2‖ := by
    apply (div_le_iff₀ hR).2
    nlinarith only [ht,hF]
  have hP := pow_le_pow_left₀ (by positivity : 0 ≤ p.δ/p.R) hh 2
  rw [mul_pow,Real.sq_sqrt hU] at hP
  exact radius_floor hP ((le_abs_self _).trans hD) (by dsimp [drift]; positivity) hU

lemma scaled_sum (hp : spec.valid p) (θ θ' : Space .conv p.d)
    (ht : floorEnergy p ≤ tapEnergy p θ) (hD : |imbalance p θ| ≤ drift p)
    (hF : risk p X θ ≤ 1) (hf : risk p X θ' ≤ risk p X θ)
    (hz : energy p θ' ≤ 4*energy p θ) :
    augmented p X θ+augmented p X θ' ≤ scale p*tapEnergy p θ := by
  have hu := floor_pos p hp
  obtain ⟨hη,hsmall,_,_⟩ := tuning_limits p hp
  have hsc : drift p+2 ≤ ((drift p+2)/floorEnergy p)*tapEnergy p θ := by
    have hn : 0 ≤ drift p+2 := by unfold drift; positivity
    calc _ = ((drift p+2)/floorEnergy p)*floorEnergy p := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left ht (div_nonneg hn hu.le)
  have hE : energy p θ ≤ 2*tapEnergy p θ+drift p := by
    have h := (le_abs_self _).trans hD
    unfold imbalance at h
    unfold energy
    linarith
  have h1 := mul_le_mul_of_nonneg_left hF hη.le
  have h2 := mul_le_mul_of_nonneg_left hf hη.le
  unfold augmented scale
  nlinarith only [hE,h1,h2,hz,hsc,hsmall]

structure Invariant (θ : Space .conv p.d) : Prop where
  monotone : risk p X θ ≤ risk p X p.start
  balance : |imbalance p θ-imbalance p p.start| ≤
    2*stepSize p*(risk p X p.start-risk p X θ)
  square : (p.γ/2)^2*((augmented p X θ)^2-(augmented p X p.start)^2) ≤
    4*scale p*((Real.log (2/risk p X θ))^3-(Real.log (2/risk p X p.start))^3)

lemma initial_invariant : Invariant p X p.start := by constructor <;> simp

lemma tap_floor_along (hp : spec.valid p) (θ : Space .conv p.d)
    (hX : ∀ i, ‖X i‖ ≤ p.R) (h0 : Initial p X) (H : Invariant p X θ)
    (hD : |imbalance p θ| ≤ drift p) : floorEnergy p ≤ tapEnergy p θ := by
  unfold floorEnergy
  split
  next h =>
    have hf := initial_risk p X hp h0
    have hη := (tuning_limits p hp).1
    have hδ := hp.2.2
    have hd : 4/p.δ ≤ invStep p := by
      have hm := curvature_pos p hp
      have hR := hp.1
      simp only [invStep,ite_eq_left h,le_add_iff_nonneg_left]
      positivity
    have hs : stepSize p ≤ p.δ/4 := by
      rw [tuning_eq,one_div]
      calc _ ≤ (4/p.δ)⁻¹ := inv_anti₀ (by positivity) hd
           _ = _ := by rw [inv_div]
    have hh := (le_abs_self _).trans H.balance
    have hb := mul_le_mul_of_nonneg_left (show risk p X p.start-risk p X θ ≤ 1 by
      linarith [risk_pos p X θ]) (show 0 ≤ 2*stepSize p by positivity)
    unfold surplus at h
    unfold imbalance tapEnergy at hh
    unfold tapEnergy
    nlinarith only [h,hh,hb,hs,sq_nonneg ‖θ.2‖]
  next h =>
    obtain hF|⟨_,hs⟩ := h0
    · exact lower_taps p X hp θ hX (H.monotone.trans hF) hD
    · exact (h hs).elim

lemma imbalance_bound (hp : spec.valid p) (θ : Space .conv p.d)
    (hf : risk p X p.start ≤ 1) (H : Invariant p X θ) : |imbalance p θ| ≤ drift p := by
  obtain ⟨hη,hsmall,_,_⟩ := tuning_limits p hp
  have hh : risk p X p.start-risk p X θ ≤ 1 := by linarith [risk_pos p X θ]
  have ht := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*stepSize p)
  have ha : |imbalance p θ| ≤ |imbalance p θ-imbalance p p.start|+|imbalance p p.start| :=
    by simpa using abs_add_le (imbalance p θ-imbalance p p.start) (imbalance p p.start)
  unfold drift
  linarith [H.balance]

lemma augmented_nonneg (hp : spec.valid p) (θ : Space .conv p.d) : 0 ≤ augmented p X θ := by
  have hη := (tuning_limits p hp).1
  have hF := risk_pos p X θ
  have hz := energy_nonneg p θ
  unfold augmented
  positivity

lemma radius_bound_sq (hp : spec.valid p) (θ : Space .conv p.d)
    (hf : risk p X p.start ≤ 1) (H : Invariant p X θ) :
    (augmented p X θ)^2 ≤ (initialBound p)^2+(radiusFactor p)^2*(Real.log (2/risk p X θ))^3 := by
  obtain ⟨hη,hsmall,_,_⟩ := tuning_limits p hp
  have hA := augmented_nonneg p X hp p.start
  have hE : augmented p X p.start ≤ initialBound p := by
    have hh := mul_le_mul_of_nonneg_left hf hη.le
    unfold augmented initialBound; linarith
  have hS := scale_pos p hp
  have hγ := hp.2.1
  have hratio : (p.γ/2)^2*(radiusFactor p)^2=4*scale p := by
    unfold radiusFactor; field_simp; nlinarith only [Real.sq_sqrt hS.le]
  have hl : 0 ≤ Real.log (2/risk p X p.start) :=
    Real.log_nonneg ((le_div_iff₀ (risk_pos _ _ _)).2 (by linarith))
  apply (le_of_mul_le_mul_left _ (by positivity : 0 < (p.γ/2)^2))
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hE 2) (sq_nonneg (p.γ/2))
  have hr := H.square
  rw [mul_add,← mul_assoc,hratio]
  nlinarith only [hh,hr,mul_nonneg hS.le (pow_nonneg hl 3)]

lemma propagate (hp : spec.valid p) (hX : ∀ i, ‖X i‖ ≤ p.R)
    (S : ∃ u v : Features p.d, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      (∀ i, p.γ ≤ ⟪X i+shift (X i),u⟫) ∧ (∀ i, p.γ ≤ ⟪X i-shift (X i),v⟫))
    (h0 : Initial p X) (θ : Space .conv p.d) (H : Invariant p X θ) :
    Invariant p X (advance p X (stepSize p) θ) ∧
      stepSize p*energy p (descent p X θ) ≤ 2*(risk p X θ-risk p X (advance p X (stepSize p) θ)) := by
  let η := stepSize p
  let f := risk p X θ
  let next := advance p X η θ
  have hR := hp.1
  have hγ := hp.2.1
  have hδ := hp.2.2
  obtain ⟨hη,_,hηR,hηC⟩ := tuning_limits p hp
  have hF0 := initial_risk p X hp h0
  have hf := H.monotone.trans hF0
  have hD := imbalance_bound p X hp θ hF0 H
  have hu := tap_floor_along p X hp θ hX h0 H hD
  have hE : 0 ≤ initialBound p := by unfold initialBound; linarith [energy_nonneg p p.start]
  have hK : 0 ≤ radiusFactor p := by unfold radiusFactor; positivity
  have hc := energy_controls_curvature (risk_pos p X θ) hf hE hK (radius_bound_sq p X hp θ hF0 H)
  have hfy := risk_pos p X θ
  have hcurv : η*p.R^2*energy p θ*f ≤ 1/32 := by
    have ht : energy p θ ≤ augmented p X θ := by unfold augmented; exact le_add_of_nonneg_right (by positivity)
    have hb : energy p θ*f ≤ curvature p := by
      apply (mul_le_mul_of_nonneg_right ht hfy.le).trans
      simpa [f,curvature,mul_comm] using hc
    have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ η*p.R^2 from mul_nonneg hη.le (sq_nonneg _))
    dsimp [η] at *
    nlinarith only [hh,hηC]
  have hdes := advance_risk p X θ η hη.le hR.le hX hf hηR hcurv
  have hdec : η*energy p (descent p X θ) ≤ 2*(risk p X θ-risk p X next) := by
    change _ ≤ _ - _ at hdes; dsimp [next]; linarith only [hdes]
  have hle : risk p X next ≤ risk p X θ := by
    linarith [mul_nonneg hη.le (energy_nonneg p (descent p X θ))]
  refine ⟨⟨hle.trans H.monotone,?_,?_⟩,hdec⟩
  · have hh := imbalance_variation p X θ η
    have hg := mul_le_mul_of_nonneg_left hdec hη.le
    have ht : |imbalance p next-imbalance p p.start| ≤
        |imbalance p next-imbalance p θ|+|imbalance p θ-imbalance p p.start| := abs_sub_le _ _ _
    change _ ≤ _ at ht
    dsimp only [η,next] at *
    nlinarith only [ht,hh,H.balance,hg]
  · have U := (floor_pos p hp).trans_le hu
    have hss := scaled_sum p X hp θ next hu hD hf hle (energy_next p X θ η hη.le hR.le hX hf hηR)
    have hs := radius_square_step (Q := intensity p X θ) (risk_pos p X next) hle (by linarith : risk p X θ ≤ 2)
      hη U (half_pos hγ) (scale_pos p hp).le (augmented_nonneg p X hp θ)
      (augmented_nonneg p X hp next) hss (descent_energy_lower p X θ hγ.le S) hdec
      (energy_charge p X θ η hη.le hdec)
    dsimp only [next,η] at hs
    linarith only [hs,H.square]

noncomputable def threshold := (4*(p.n : ℝ))⁻¹

noncomputable def radiusAtTarget :=
  initialBound p+radiusFactor p*Real.sqrt ((Real.log (8*(p.n : ℝ)))^3)

noncomputable def progressCost := (2+p.R)^2*(1+radiusAtTarget p)*scale p

lemma threshold_pos : 0 < threshold p := by unfold threshold; positivity

lemma radius_at_target (hp : spec.valid p) (θ : Space .conv p.d)
    (hf : risk p X p.start ≤ 1) (H : Invariant p X θ) (he : threshold p ≤ risk p X θ) :
    energy p θ ≤ radiusAtTarget p := by
  have hη := (tuning_limits p hp).1
  have hF := risk_pos p X θ
  have hL : 0 ≤ Real.log (2/risk p X θ) :=
    Real.log_nonneg ((le_div_iff₀ hF).2 (by linarith [H.monotone]))
  have hn : 0 < (p.n : ℝ) := by positivity
  have hlog : Real.log (2/risk p X θ) ≤ Real.log (8*(p.n : ℝ)) := by
    apply Real.log_le_log (by positivity)
    calc _ ≤ 2/threshold p := div_le_div_of_nonneg_left (by norm_num) (threshold_pos p) he
         _ = _ := by unfold threshold; field_simp; ring
  have hc := radius_bound_sq p X hp θ hf H
  have hγ := hp.2.1
  have hK : 0 ≤ radiusFactor p := by unfold radiusFactor; positivity
  have hE : 0 ≤ initialBound p := by unfold initialBound; linarith [energy_nonneg p p.start]
  have ht := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hlog 3) (sq_nonneg (radiusFactor p))
  apply (le_add_of_nonneg_right (by positivity : 0 ≤ 2*stepSize p*risk p X θ)).trans
  change augmented p X θ ≤ radiusAtTarget p
  unfold radiusAtTarget
  apply (sq_le_sq₀ (augmented_nonneg p X hp θ) (by positivity)).mp
  rw [add_sq,mul_pow,Real.sq_sqrt (pow_nonneg (hL.trans hlog) 3)]
  nlinarith only [hc,ht,mul_nonneg hE (mul_nonneg hK (Real.sqrt_nonneg ((Real.log (8*(p.n:ℝ)))^3)))]

lemma margin_abs_bound (hp : spec.valid p) (θ : Space .conv p.d)
    (hX : ∀ i, ‖X i‖ ≤ p.R) (i : Fin p.n) :
    |LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv p.d (X i) θ| ≤ p.R*energy p θ := by
  have hU : 0 ≤ tapEnergy p θ := by unfold tapEnergy; positivity
  have hr := hp.1
  have hc : ‖θ.1.1 • X i+θ.1.2 • shift (X i)‖ ≤ 2*Real.sqrt (tapEnergy p θ)*p.R := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have hb := LongTails.Proofs.LogisticSpatialResponse.filter_size_sq θ.1.1 θ.1.2 (X i)
    have hn := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hX i) 2)
      (show 0 ≤ 2*tapEnergy p θ by positivity)
    unfold tapEnergy at *
    rw [mul_pow,mul_pow,Real.sq_sqrt hU]
    nlinarith only [hb,hn,mul_nonneg hU (sq_nonneg p.R)]
  change |θ.1.1*⟪X i,θ.2⟫+θ.1.2*⟪shift (X i),θ.2⟫| ≤ _
  rw [← real_inner_smul_left,← real_inner_smul_left,← inner_add_left]
  apply (abs_real_inner_le_norm _ _).trans
  apply (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans
  unfold energy
  nlinarith only [mul_nonneg hr.le (sq_nonneg (Real.sqrt (tapEnergy p θ)-‖θ.2‖)),
    congrArg (fun z : ℝ => p.R*z) (Real.sq_sqrt hU)]

lemma population_posterior (θ : Space .conv p.d) :
    risk p X θ ≤ (1+(p.n:ℝ)*risk p X θ)*intensity p X θ := by
  have hn : 0 < (p.n:ℝ) := by positivity
  unfold risk intensity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let m := LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv p.d (X i) θ
  have hs := Finset.single_le_sum (f := fun j => (p.n:ℝ)⁻¹ *
    loss (LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv p.d (X j) θ))
    (fun j _ => mul_nonneg (inv_nonneg.mpr hn.le) (loss_pos _).le) (Finset.mem_univ i)
  change (p.n:ℝ)⁻¹*loss m ≤ risk p X θ at hs
  have hi := mul_le_mul_of_nonneg_left hs hn.le
  rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul] at hi
  have ht := mul_le_mul_of_nonneg_right (show 1+loss m ≤ 1+(p.n:ℝ)*risk p X θ by linarith)
    (Real.sigmoid_nonneg (-m))
  have hu := mul_le_mul_of_nonneg_left ((loss_le_weighted_posterior m).trans ht) (inv_nonneg.mpr hn.le)
  change _ ≤ (1+(p.n:ℝ)*risk p X θ)*((p.n:ℝ)⁻¹*Real.sigmoid (-m))
  convert hu using 1
  ring

lemma relative_gradient (hp : spec.valid p) (hX : ∀ i, ‖X i‖ ≤ p.R)
    (S : ∃ u v : Features p.d, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      (∀ i, p.γ ≤ ⟪X i+shift (X i),u⟫) ∧ (∀ i, p.γ ≤ ⟪X i-shift (X i),v⟫))
    (h0 : Initial p X)
    (θ : Space .conv p.d) (H : Invariant p X θ) (he : threshold p ≤ risk p X θ) :
    (p.γ/2)^2*(risk p X θ)^2 ≤ progressCost p*energy p (descent p X θ) ∧
    (p.γ/2)^2*(risk p X θ)^2 ≤
      ((2+p.R)*scale p)*(1+(p.n:ℝ)*risk p X θ)*energy p (descent p X θ) := by
  let Q := intensity p X θ
  let U := tapEnergy p θ
  let z := energy p θ
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun i _ => weights_nonneg _ _ _ _
  have hz := energy_nonneg p θ
  have hR := hp.1
  have hδ := hp.2.2
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hf := initial_risk p X hp h0
  have hcap := radius_at_target p X hp θ hf H he
  have hD := imbalance_bound p X hp θ hf H
  have hU := tap_floor_along p X hp θ hX h0 H hD
  have hd := descent_energy_lower p X θ hp.2.1.le S
  have hsep : 1+z ≤ scale p*U := by
    have hu := floor_pos p hp
    have ha : 0 ≤ drift p+2 := by unfold drift; positivity
    have hx := mul_le_mul_of_nonneg_left hU (div_nonneg ha hu.le)
    rw [div_mul_cancel₀ _ hu.ne'] at hx
    have hb := (le_abs_self _).trans hD
    dsimp [z,U,energy,imbalance,scale] at *
    have hpU : 0 ≤ tapEnergy p θ := by unfold tapEnergy; positivity
    nlinarith only [hx,hb,hpU,ha]
  have hr := risk_from_posterior (fun _ : Fin p.n => (p.n:ℝ)⁻¹) _
    (fun _ => by positivity) (p.R*z) (margin_abs_bound p X hp θ hX)
  change risk p X θ ≤ (1+Real.log 2+p.R*z)*Q at hr
  have hF : risk p X θ ≤ ((2+p.R)*(1+z))*Q := by
    apply hr.trans; apply mul_le_mul_of_nonneg_right _ hQ
    dsimp [z]; nlinarith only [hlog,hR,hz]
  have hsq := pow_le_pow_left₀ (risk_pos p X θ).le hF 2
  have hZ : 0 ≤ 1+z := by dsimp [z]; linarith
  have HA : 0 ≤ (2+p.R)^2*(1+radiusAtTarget p)*scale p :=
    by have := scale_pos p hp; have : 0 ≤ radiusAtTarget p := hz.trans hcap; positivity
  constructor
  · calc
      _ ≤ (p.γ/2)^2*(((2+p.R)*(1+z))*Q)^2 := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ((p.γ/2)^2*(2+p.R)^2*Q^2)*((1+z)*(1+z)) := by ring
      _ ≤ ((p.γ/2)^2*(2+p.R)^2*Q^2)*((1+radiusAtTarget p)*(scale p*U)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (by linarith : 1+z ≤ 1+radiusAtTarget p) hsep hZ (by linarith)
      _ = ((2+p.R)^2*(1+radiusAtTarget p)*scale p)*((p.γ/2)^2*U*Q^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hd HA
  · have hn := population_posterior p X θ
    change risk p X θ ≤ (1+(p.n:ℝ)*risk p X θ)*Q at hn
    have hfQ := mul_le_mul hF hn (risk_pos p X θ).le (by positivity)
    let C := (2+p.R)*(1+(p.n:ℝ)*risk p X θ)
    have hC : 0 ≤ C := by dsimp [C]; have := risk_pos p X θ; positivity
    calc
      _ ≤ (p.γ/2)^2*((((2+p.R)*(1+z))*Q)*((1+(p.n:ℝ)*risk p X θ)*Q)) :=
        mul_le_mul_of_nonneg_left (by simpa [sq] using hfQ) (sq_nonneg _)
      _ = ((p.γ/2)^2*C*Q^2)*(1+z) := by dsimp [C]; ring
      _ ≤ ((p.γ/2)^2*C*Q^2)*(scale p*U) := mul_le_mul_of_nonneg_left hsep (by positivity)
      _ = (C*scale p)*((p.γ/2)^2*U*Q^2) := by ring
      _ ≤ (C*scale p)*energy p (descent p X θ) := mul_le_mul_of_nonneg_left hd (by have := scale_pos p hp; positivity)
      _ = _ := by dsimp [C]; ring


lemma separates_at_threshold (θ : Space .conv p.d) (h : risk p X θ ≤ threshold p) :
    Separates p X θ := by
  intro i
  by_contra! hm
  have hn : 0 < (p.n : ℝ) := by positivity
  have hl : Real.log 2 ≤ loss (LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv p.d (X i) θ) := by
    apply Real.log_le_log (by norm_num)
    linarith [Real.one_le_exp (neg_nonneg.mpr hm)]
  have hh := Finset.single_le_sum (f := fun j => (p.n:ℝ)⁻¹ *
    loss (LongTails.Setups.TwoSampleQuadraticPerceptron.margin .conv p.d (X j) θ))
    (fun j _ => mul_nonneg (inv_nonneg.mpr hn.le) (loss_pos _).le) (Finset.mem_univ i)
  change (p.n:ℝ)⁻¹*_ ≤ risk p X θ at hh
  have ht := (mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hn.le)).trans (hh.trans h)
  unfold threshold at ht
  rw [mul_inv_rev] at ht
  have ht' := (le_of_mul_le_mul_left ht (inv_pos.mpr hn))
  linarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)]

lemma iterate_separates (hp : spec.valid p) (hX : ∀ i, ‖X i‖ ≤ p.R)
    (S : ∃ u v : Features p.d, ‖u‖ ≤ 1 ∧ ‖v‖ ≤ 1 ∧
      (∀ i, p.γ ≤ ⟪X i+shift (X i),u⟫) ∧ (∀ i, p.γ ≤ ⟪X i-shift (X i),v⟫))
    (h0 : Initial p X)
    (T : ℕ) (hT : (1+80*(p.n:ℝ)*(2+p.R)*scale p/(stepSize p*p.γ^2))*
      Real.log (1+4*((2+p.R)*(1+radiusAtTarget p))) ≤ T) :
    Separates p X ((advance p X (stepSize p))^[T] p.start) := by
  let v (t : ℕ) := (advance p X (stepSize p))^[t] p.start
  let f (t : ℕ) := risk p X (v t)
  let η := stepSize p
  let c := progressCost p
  have hη := (tuning_limits p hp).1
  have hγ := hp.2.1
  have e : ∀ t, v (t+1) = advance p X η (v t) :=
    fun t => Function.iterate_succ_apply' _ _ _
  have hinv : ∀ t, Invariant p X (v t) := by
    intro t
    induction t with
    | zero => exact initial_invariant p X
    | succ t ih => rw [e]; exact (propagate p X hp hX S h0 _ ih).1
  have hdec (t : ℕ) : η*energy p (descent p X (v t)) ≤ 2*(f t-f (t+1)) := by
    dsimp only [f]; rw [e]; exact (propagate p X hp hX S h0 _ (hinv t)).2
  have mono : Antitone f := by
    apply antitone_nat_of_succ_le
    intro t
    linarith [hdec t,mul_nonneg hη.le (energy_nonneg p (descent p X (v t)))]
  have hn : 0 < (p.n : ℝ) := by positivity
  have hZ : 0 ≤ radiusAtTarget p := by
    unfold radiusAtTarget initialBound radiusFactor
    have := energy_nonneg p p.start
    positivity
  have hc : 0 < c := by
    dsimp [c,progressCost]; have := scale_pos p hp; have := hp.1; positivity
  apply separates_at_threshold
  change f T ≤ threshold p
  by_contra! hfail
  let B := (2+p.R)*(1+radiusAtTarget p)
  let C := (2+p.R)*scale p
  let a := η*(p.γ/2)^2/(2*C)
  let r := a/(10*(p.n:ℝ))
  let k := (p.n:ℝ)/B
  let V (t : ℕ) := 1/f t
  have hR := hp.1
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; have := scale_pos p hp; positivity
  have ha : 0 < a := by dsimp [a,η]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hV (t : ℕ) : 0 < V t := one_div_pos.mpr (risk_pos p X (v t))
  have hgeom (t : ℕ) (ht : t < T) : r*(V t+k) ≤ V (t+1)-V t := by
    have H := relative_gradient p X hp hX S h0 _ (hinv t) (hfail.le.trans (mono ht.le))
    obtain ⟨h1,h2⟩ := H
    have hcB : c = C*B := by dsimp [c,C,B,progressCost]; ring
    have hf := risk_pos p X (v t)
    change 0 < f t at hf
    have hft : (4*(p.n:ℝ))⁻¹ < f t := hfail.trans_le (mono ht.le)
    have bound (K : ℝ) (hK : 0 < K) (hG : (p.γ/2)^2*(f t)^2 ≤ K*energy p (descent p X (v t))) :
        η*(p.γ/2)^2/(2*K) ≤ V (t+1)-V t := by
      apply reciprocal_progress (risk_pos p X (v (t+1))) (mono (Nat.le_succ t))
        (mul_nonneg hη.le (sq_nonneg _)) (by positivity)
      have hI := mul_le_mul_of_nonneg_left hG hη.le
      have hJ := mul_le_mul_of_nonneg_left (hdec t) hK.le
      nlinarith only [hI,hJ]
    have hleft : a/B ≤ V (t+1)-V t := by
      have h := bound c hc h1
      rw [hcB] at h
      simpa only [a,div_div,mul_assoc] using h
    have hright : a/(1+(p.n:ℝ)*f t) ≤ V (t+1)-V t := by
      have h := bound (C*(1+(p.n:ℝ)*f t)) (by positivity) h2
      dsimp only [a]; rwa [div_div,mul_assoc]
    have hsmall : 1 ≤ 4*(p.n:ℝ)*f t := by
      rw [← one_div] at hft
      linarith [(div_lt_iff₀ (show 0 < 4*(p.n:ℝ) by positivity)).mp hft]
    have hy : a/(5*(p.n:ℝ)*f t) ≤ a/(1+(p.n:ℝ)*f t) :=
      div_le_div_of_nonneg_left ha.le (by positivity) (by linarith)
    have hz1 : 2*(r*k) ≤ V (t+1)-V t := by
      apply le_trans _ hleft
      dsimp [r,k]
      field_simp
      nlinarith
    have hz2 : 2*(r*V t) ≤ V (t+1)-V t := by
      apply le_trans _ (hy.trans hright)
      dsimp [r,V]
      field_simp
      ring_nf
      exact le_rfl
    linarith only [hz1,hz2]
  have hpow : ∀ t ≤ T, (1+r)^t*k ≤ V t+k := by
    intro t
    induction t with
    | zero => intro; simp [le_add_of_nonneg_left (hV 0).le]
    | succ t ih =>
      intro h
      have hI := mul_le_mul_of_nonneg_left (ih (Nat.le_of_succ_le h)) (show 0 ≤ 1+r by positivity)
      rw [pow_succ]
      nlinarith only [hI,hgeom t h]
  have heq : (1+r)/r = 1+80*(p.n:ℝ)*(2+p.R)*scale p/(stepSize p*p.γ^2) := by
    have hscale := (scale_pos p hp).ne'
    have hsum : 2+p.R ≠ 0 := by positivity
    dsimp [r,a,C,η]
    field_simp [hscale,hsum]
    ring
  have hL := Real.one_sub_inv_le_log_of_pos (show 0 < 1+r by positivity)
  have hlog : r/(1+r) ≤ Real.log (1+r) := by
    apply le_trans _ hL
    apply (div_le_iff₀ (show 0 < 1+r by positivity)).2
    rw [sub_mul,one_mul,inv_mul_cancel₀ (by positivity)]
    linarith
  have hTlog : Real.log (1+4*B) ≤ (T:ℝ)*Real.log (1+r) := by
    rw [← heq] at hT
    change (1+r)/r*Real.log (1+4*B) ≤ T at hT
    have hh := mul_le_mul_of_nonneg_right hT (show 0 ≤ r/(1+r) by positivity)
    have he : (1+r)/r*Real.log (1+4*B)*(r/(1+r)) = Real.log (1+4*B) := by field_simp
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg T))
  rw [← Real.log_pow] at hTlog
  have hg := (Real.log_le_log_iff (show 0 < 1+4*B by positivity) (by positivity)).mp hTlog
  have hh := (mul_le_mul_of_nonneg_right hg hk.le).trans (hpow T le_rfl)
  have he : (1+4*B)*k = k+4*(p.n:ℝ) := by dsimp [k]; field_simp
  rw [he] at hh
  have hs : V T < 4*(p.n:ℝ) := by
    dsimp only [V]; rw [one_div]
    simpa [threshold] using (inv_lt_inv₀ (risk_pos p X (v T)) (threshold_pos p)).mpr hfail
  linarith

end LongTails.Proofs.TwoTapLogisticBudget
