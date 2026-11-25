import LongTails.Proofs.LogisticCloudCoordinates

open scoped RealInnerProductSpace
open LongTails.Setups.LogisticDefectCloud
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.LogisticCloudCoordinates

namespace LongTails.Proofs.LogisticCloudAlignment

variable {d : ℕ}

noncomputable def action (a b : Features d) (x : Weights d) : Weights d :=
  pack ⟪a,readout x⟫ ⟪b,readout x⟫ (x (.inl 0) • a + x (.inl 1) • b)

lemma action_add (a b : Features d) (w x : Weights d) :
    action a b (w+x) = action a b w + action a b x := by
  apply pack_ext <;> simp [action,inner_add_right,add_smul]
  abel

lemma action_smul (a b : Features d) (c : ℝ) (w : Weights d) :
    action a b (c • w) = c • action a b w := by
  apply pack_ext <;> simp [action,real_inner_smul_right,smul_add,smul_smul]

lemma action_sub (a b : Features d) (w x : Weights d) :
    action a b (w-x) = action a b w - action a b x := by
  have he := action_add a b (w-x) x
  rw [sub_add_cancel] at he
  exact eq_sub_of_add_eq he.symm

lemma norm_action (a b : Features d) (w : Weights d) :
    ‖action a b w‖ ≤ (‖a‖+‖b‖)*‖w‖ := by
  obtain ⟨hp,ht,hv⟩ := bounds w
  have h₁ := abs_real_inner_le_norm a (readout w)
  have h₂ := abs_real_inner_le_norm b (readout w)
  have h₃ := norm_add_le (w (.inl 0) • a) (w (.inl 1) • b)
  simp only [norm_smul,Real.norm_eq_abs] at h₃
  have hw := norm_pack_sq (w (.inl 0)) (w (.inl 1)) (readout w)
  rw [pack_readout] at hw
  apply le_of_sq_le_sq _ (by positivity)
  rw [action,norm_pack_sq]
  have h₄ := pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  have h₅ := pow_le_pow_left₀ (abs_nonneg _) h₂ 2
  have h₆ := pow_le_pow_left₀ (norm_nonneg _) h₃ 2
  have h₇ := sq_nonneg (|w (.inl 0)| *‖b‖-|w (.inl 1)| *‖a‖)
  simp only [sq_abs] at h₄ h₅
  have hs : (|w (.inl 0)| *‖a‖+|w (.inl 1)| *‖b‖)^2 ≤
      (w (.inl 0)^2+w (.inl 1)^2)*(‖a‖^2+‖b‖^2) := by
    rw [← sq_abs (w (.inl 0)), ← sq_abs (w (.inl 1))]
    nlinarith only [h₇]
  have hz : ‖a‖^2+‖b‖^2 ≤ (‖a‖+‖b‖)^2 := by
    nlinarith [mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  nlinarith only [h₄,h₅,h₆,hs,
    mul_le_mul_of_nonneg_right hz (sq_nonneg ‖w‖),
    congrArg (fun z : ℝ => z*(‖a‖^2+‖b‖^2)) hw]

lemma ortho_sum_norm (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0)
    (p t : ℝ) : ‖p • a+t • b‖^2 = p^2+t^2 := by
  rw [norm_add_sq_real,real_inner_smul_left,real_inner_smul_right,hab]
  simp [norm_smul,ha,hb]

lemma projection_le (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0)
    (w : Features d) : ⟪a,w⟫^2+⟪b,w⟫^2 ≤ ‖w‖^2 := by
  let v := ⟪a,w⟫ • a + ⟪b,w⟫ • b
  have hv := ortho_sum_norm a b ha hb hab ⟪a,w⟫ ⟪b,w⟫
  have he := norm_sub_sq_real v w
  simp only [v,inner_add_left,real_inner_smul_left] at he
  nlinarith only [he,hv,sq_nonneg ‖v-w‖]

lemma norm_action_unit (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) (w : Weights d) : ‖action a b w‖ ≤ ‖w‖ := by
  have hw := norm_pack_sq (w (.inl 0)) (w (.inl 1)) (readout w)
  rw [pack_readout] at hw
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [action,norm_pack_sq,ortho_sum_norm a b ha hb hab]
  linarith [projection_le a b ha hb hab (readout w)]

noncomputable def mode (a b : Features d) (p t : ℝ) : Weights d := pack p t (p • a+t • b)

lemma mode_eigen (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) (p t : ℝ) : action a b (mode a b p t) = mode a b p t := by
  have hba := (real_inner_comm _ _).trans hab
  simp [action,mode,inner_add_right,real_inner_smul_right,ha,hb,hab,hba]

lemma cubic_tracking {E : Type*} [NormedAddCommGroup E] {g C r K : ℝ}
    (hg : 1 ≤ g) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hs : 8*C*r^3 ≤ K*(g^3-g)) (x y : ℕ → E) (h₀ : x 0 = y 0)
    (hy : ∀ t, ‖y t‖ ≤ r*g^t)
    (hstep : ∀ t, ‖x (t+1)-y (t+1)‖ ≤ g*‖x t-y t‖+C*‖x t‖^3)
    (t : ℕ) (hsize : K*(g^t)^2 ≤ r) : ‖x t-y t‖ ≤ K*g^t*((g^t)^2-1) := by
  induction t with
  | zero => simp [h₀]
  | succ t ih =>
    have hg₀ := zero_le_one.trans hg
    have hp := pow_nonneg hg₀ t
    have ht : K*(g^t)^2 ≤ r := by
      refine le_trans ?_ hsize
      gcongr
      exact Nat.le_succ t
    have he := ih ht
    have he' : ‖x t-y t‖ ≤ r*g^t := by
      nlinarith [mul_le_mul_of_nonneg_right ht hp,mul_nonneg hK hp]
    have hx : ‖x t‖ ≤ 2*(r*g^t) := by linarith [norm_sub_norm_le (x t) (y t),hy t]
    have hc := pow_le_pow_left₀ (norm_nonneg _) hx 3
    have H := hstep t
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left he hg₀,mul_le_mul_of_nonneg_left hc hC,
      mul_le_mul_of_nonneg_right hs (pow_nonneg hp 3)]


noncomputable def linear (a b : Features d) (δ : ℝ) (w : Weights d) : Weights d :=
  w + δ • action a b w

noncomputable def growing (a b : Features d) (w : Weights d) : Weights d :=
  mode a b ((w (.inl 0)+⟪a,readout w⟫)/2) ((w (.inl 1)+⟪b,readout w⟫)/2)

noncomputable def falling (a b : Features d) (w : Weights d) : Weights d :=
  let p := (w (.inl 0)-⟪a,readout w⟫)/2
  let t := (w (.inl 1)-⟪b,readout w⟫)/2
  pack p t (-(p • a+t • b))

noncomputable def remainder (a b : Features d) (w : Weights d) : Weights d :=
  pack 0 0 (readout w - (⟪a,readout w⟫ • a+⟪b,readout w⟫ • b))

lemma split (a b : Features d) (w : Weights d) :
    growing a b w + falling a b w + remainder a b w = w := by
  apply pack_ext
  · simp [growing,falling,remainder,mode]
    ring
  · simp [growing,falling,remainder,mode]
    ring
  · simp [growing,falling,remainder,mode]
    module

lemma falling_eigen (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) (w : Weights d) :
    action a b (falling a b w) = -falling a b w := by
  have hba := (real_inner_comm _ _).trans hab
  apply pack_ext <;> simp [action,falling,inner_add_right,inner_neg_right,
    real_inner_smul_right,ha,hb,hab,hba]

lemma remainder_eigen (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) (w : Weights d) :
    action a b (remainder a b w) = 0 := by
  have hba := (real_inner_comm _ _).trans hab
  apply pack_ext <;> simp [action,remainder,inner_sub_right,inner_add_right,
    real_inner_smul_right,ha,hb,hab,hba]

lemma linear_path (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) (δ : ℝ) (w : Weights d) (k : ℕ) :
    (linear a b δ)^[k] w = (1+δ)^k • growing a b w +
      (1-δ)^k • falling a b w + remainder a b w := by
  induction k with
  | zero => simpa using (split a b w).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, linear, action_add,action_add,
      action_smul,action_smul,falling_eigen a b ha hb hab,remainder_eigen a b ha hb hab]
    have hg : action a b (growing a b w) = growing a b w := mode_eigen a b ha hb hab _ _
    rw [hg,pow_succ,pow_succ]
    module

lemma linear_norm (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) {δ : ℝ} (hδ : 0 ≤ δ) (w : Weights d) :
    ‖linear a b δ w‖ ≤ (1+δ)*‖w‖ := by
  refine (norm_add_le ..).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ]
  linarith [mul_le_mul_of_nonneg_left (norm_action_unit a b ha hb hab w) hδ]

lemma bounded_modes (a b : Features d) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a,b⟫ = 0) (w : Weights d) :
    ‖falling a b w‖ ≤ 4*‖w‖ ∧ ‖remainder a b w‖ ≤ 4*‖w‖ := by
  obtain ⟨hp,ht,hv⟩ := bounds w
  have H (v : Features d) (h : ‖v‖ = 1) : |⟪v,readout w⟫| ≤ ‖w‖ := by
    simpa [h] using (abs_real_inner_le_norm v (readout w)).trans
      (mul_le_mul_of_nonneg_left hv (norm_nonneg v))
  let p := (w (.inl 0)-⟪a,readout w⟫)/2
  let t := (w (.inl 1)-⟪b,readout w⟫)/2
  have P : |p| ≤ ‖w‖ := by
    dsimp [p]
    rw [abs_div]; norm_num; linarith [abs_sub (w (.inl 0)) ⟪a,readout w⟫,H a ha]
  have T : |t| ≤ ‖w‖ := by
    dsimp [t]
    rw [abs_div]; norm_num; linarith [abs_sub (w (.inl 1)) ⟪b,readout w⟫,H b hb]
  constructor
  · change ‖pack p t (-(p • a+t • b))‖ ≤ _
    apply le_of_sq_le_sq _ (by positivity)
    rw [norm_pack_sq,norm_neg,ortho_sum_norm a b ha hb hab]
    have hp' := pow_le_pow_left₀ (abs_nonneg _) P 2
    have ht' := pow_le_pow_left₀ (abs_nonneg _) T 2
    rw [sq_abs] at hp' ht'
    nlinarith [sq_nonneg ‖w‖]
  · apply le_of_sq_le_sq _ (by positivity)
    rw [remainder,norm_pack_sq]
    have he := norm_sub_le (readout w) (⟪a,readout w⟫ • a + ⟪b,readout w⟫ • b)
    have hh := norm_add_le (⟪a,readout w⟫ • a) (⟪b,readout w⟫ • b)
    simp only [norm_smul,Real.norm_eq_abs,ha,hb,mul_one] at hh
    have hle : ‖readout w - (⟪a,readout w⟫ • a+⟪b,readout w⟫ • b)‖ ≤ 4*‖w‖ := by
      linarith [H a ha,H b hb,norm_nonneg w]
    simpa using pow_le_pow_left₀ (norm_nonneg _) hle 2

end LongTails.Proofs.LogisticCloudAlignment
