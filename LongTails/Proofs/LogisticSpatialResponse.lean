import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open scoped RealInnerProductSpace

namespace LongTails.Proofs.LogisticSpatialResponse

open LongTails.Setups.TwoSampleQuadraticPerceptron
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

variable {d : ℕ}

lemma filtered_response (a b u v : ℝ) (x g : Features d) :
    ⟪a • x + b • shift x, u • g + v • shift g⟫ =
      (a*u+b*v)*⟪x,g⟫ +
      (a*v+b*u)*((⟪x,shift g⟫ + ⟪shift x,g⟫)/2) +
      (a*v-b*u)*((⟪x,shift g⟫ - ⟪shift x,g⟫)/2) := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_shift_shift]
  ring

lemma margin_from_history (a b : ℝ) (u v η : ℕ → ℝ) (w g : ℕ → Features d)
    (step : ∀ t, w (t+1) = w t + η t • (u t • g t + v t • shift (g t)))
    (x : Features d) (T : ℕ) :
    margin .conv d x ((a,b),w T) = margin .conv d x ((a,b),w 0) +
      ∑ t ∈ Finset.range T, η t * ((a*u t + b*v t)*⟪x,g t⟫ +
        (a*v t+b*u t)*((⟪x,shift (g t)⟫ + ⟪shift x,g t⟫)/2) +
        (a*v t-b*u t)*((⟪x,shift (g t)⟫ - ⟪shift x,g t⟫)/2)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ← filtered_response, ← add_assoc, ← ih, step T]
    simp only [margin, inner_add_right, real_inner_smul_right, inner_add_left,
      real_inner_smul_left]
    ring

lemma skew_response_bound (a b : ℝ) (u v η k : ℕ → ℝ) (T : ℕ) :
    |∑ t ∈ Finset.range T, η t * (a*v t-b*u t) * k t| ≤
      ∑ t ∈ Finset.range T, |η t| * |a*v t-b*u t| * |k t| := by
  simpa only [abs_mul] using
    (Finset.abs_sum_le_sum_abs (fun t => η t * (a*v t-b*u t) * k t) (Finset.range T))

lemma paired_margin (a b e f : ℝ) (x v h : Features d) :
    (margin .conv d x ((a+e,b+f),v+h) + margin .conv d x ((a-e,b-f),v-h))/2 =
      margin .conv d x ((a,b),v) + margin .conv d x ((e,f),h) := by
  simp only [margin, inner_add_right, inner_sub_right]
  ring

lemma filtered_norm_channels (a b : ℝ) (x : Features d) :
    4 * ‖a • x + b • shift x‖^2 =
      (a+b)^2 * ‖x + shift x‖^2 + (a-b)^2 * ‖x - shift x‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_shift_shift, real_inner_comm (shift x) x]
  ring

lemma shift_sum {ι : Type*} (s : Finset ι) (x : ι → Features d) :
    shift (∑ i ∈ s, x i) = ∑ i ∈ s, shift (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext j; simp [shift_apply]
  | insert i s h ih => simp only [Finset.sum_insert h, shift_add, ih]

lemma weighted_view_margin {ι : Type*} [Fintype ι] (x : ι → Features d)
    (w : ι → ℝ) (v : Features d) (σ γ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ‖v‖ ≤ 1)
    (h : ∀ i, γ ≤ ⟪x i + σ • shift (x i),v⟫) :
    γ*(∑ i, w i) ≤ ‖(∑ i, w i • x i) + σ • shift (∑ i, w i • x i)‖ := by
  let g := ∑ i, w i • x i
  have hs : ∑ i, w i * ⟪x i + σ • shift (x i),v⟫ = ⟪g + σ • shift g,v⟫ := by
    dsimp [g]
    simp only [shift_sum, shift_smul, inner_add_left, real_inner_smul_left,
      sum_inner, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  calc
    _ = ∑ i, w i * γ := by rw [← Finset.sum_mul]; ring
    _ ≤ ∑ i, w i * ⟪x i + σ • shift (x i),v⟫ := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (h i) (hw i)
    _ = ⟪g + σ • shift g,v⟫ := hs
    _ ≤ ‖g + σ • shift g‖ * ‖v‖ := real_inner_le_norm _ _
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hv (norm_nonneg (g+σ • shift g))

lemma uniform_filter_gradient {ι : Type*} [Fintype ι] (x : ι → Features d)
    (w : ι → ℝ) (u v : Features d) (a b γ : ℝ) (hγ : 0 ≤ γ)
    (hw : ∀ i, 0 ≤ w i) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hp : ∀ i, γ ≤ ⟪x i + shift (x i), u⟫)
    (hm : ∀ i, γ ≤ ⟪x i - shift (x i), v⟫) :
    let g := ∑ i, w i • x i
    γ^2 * (a^2+b^2) * (∑ i, w i)^2 ≤ 2 * ‖a • g + b • shift g‖^2 := by
  let g := ∑ i, w i • x i
  let Q := ∑ i, w i
  have hQ : 0 ≤ γ*Q := mul_nonneg hγ (Finset.sum_nonneg fun i _ => hw i)
  have hp' : γ*Q ≤ ‖g + shift g‖ := by
    simpa [g, Q] using weighted_view_margin x w u 1 γ hw hu (by simpa using hp)
  have hm' : γ*Q ≤ ‖g - shift g‖ := by
    simpa [g, Q, sub_eq_add_neg] using weighted_view_margin x w v (-1) γ hw hv
      (by simpa [sub_eq_add_neg] using hm)
  have pp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ hp' 2) (sq_nonneg (a+b))
  have pm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ hm' 2) (sq_nonneg (a-b))
  change γ^2*(a^2+b^2)*Q^2 ≤ 2*‖a • g + b • shift g‖^2
  nlinarith only [add_le_add pp pm, filtered_norm_channels a b g]

lemma momentum_pairing (a b : ℝ) (g v : Features d) :
    a*⟪g,v⟫ + b*⟪shift g,v⟫ = ⟪v,a • g+b • shift g⟫ := by
  simp only [inner_add_right, real_inner_smul_right, real_inner_comm v g,
    real_inner_comm v (shift g)]

lemma readout_energy_step (v h : Features d) (η : ℝ) :
    ‖v+η • h‖^2 = ‖v‖^2 + 2*η*⟪v,h⟫ + η^2*‖h‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm h v]
  ring

lemma layer_imbalance_step (a b η : ℝ) (g v : Features d) :
    let e := ⟪g,v⟫
    let f := ⟪shift g,v⟫
    let h := a • g+b • shift g
    ‖v+η • h‖^2 - ((a+η*e)^2+(b+η*f)^2) -
      (‖v‖^2-(a^2+b^2)) = η^2*(‖h‖^2-(e^2+f^2)) := by
  dsimp only
  rw [readout_energy_step, ← momentum_pairing]
  ring

lemma total_energy_step (a b η : ℝ) (g v : Features d) :
    let e := ⟪g,v⟫
    let f := ⟪shift g,v⟫
    let h := a • g+b • shift g
    (a+η*e)^2+(b+η*f)^2+‖v+η • h‖^2-(a^2+b^2+‖v‖^2) =
      4*η*(a*e+b*f) + η^2*(e^2+f^2+‖h‖^2) := by
  dsimp only
  rw [readout_energy_step, ← momentum_pairing]
  ring

lemma filtered_work {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (x : ι → Features d) (a b : ℝ) (v : Features d) :
    ∑ i, w i * margin .conv d (x i) ((a,b),v) =
      margin .conv d (∑ i, w i • x i) ((a,b),v) := by
  simp only [margin, shift_sum, shift_smul, sum_inner, real_inner_smul_left,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

lemma margin_increment (a b e f η : ℝ) (x v h : Features d) :
    margin .conv d x ((a+η*e,b+η*f),v+η • h) - margin .conv d x ((a,b),v) =
      η*(e*⟪x,v⟫+f*⟪shift x,v⟫+⟪a • x+b • shift x,h⟫) +
        η^2 * ⟪e • x+f • shift x,h⟫ := by
  simp only [margin, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

lemma mean_margin_increment {ι : Type*} [Fintype ι] (w : ι → ℝ) (x : ι → Features d)
    (a b η : ℝ) (v : Features d) :
    let g := ∑ i, w i • x i
    let e := ⟪g,v⟫
    let f := ⟪shift g,v⟫
    let h := a • g+b • shift g
    ∑ i, w i * (margin .conv d (x i) ((a+η*e,b+η*f),v+η • h) -
        margin .conv d (x i) ((a,b),v)) =
      η*(e^2+f^2+‖h‖^2) + η^2*⟪e • g+f • shift g,h⟫ := by
  dsimp only
  simp only [mul_sub, Finset.sum_sub_distrib, filtered_work]
  rw [margin_increment, real_inner_self_eq_norm_sq]
  ring

noncomputable def torque (a b : ℝ) (g v : Features d) : ℝ :=
  a*⟪shift g,v⟫-b*⟪g,v⟫

lemma alternating_torque (a b : ℝ) (h : Features d) :
    torque a b h (a • h+b • shift h) = (a^2-b^2)*⟪h,shift h⟫ := by
  simp only [torque, inner_add_right, real_inner_smul_right, inner_shift_shift,
    real_inner_comm (shift h) h]
  ring

lemma two_step_torque (a b η : ℝ) (v g h : Features d) :
    let V := v+η • (a • (g-h)+b • shift (g-h))
    η * (torque a b (g-h) v + torque a b (g+h) V) =
      2*η*torque a b g ((2:ℝ)⁻¹ • (v+V)) +
      η^2*torque a b h (a • g+b • shift g) -
      η^2*((a^2-b^2)*⟪h,shift h⟫) := by
  rw [← alternating_torque]
  simp only [torque, shift_add, shift_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_right]
  ring

lemma filter_size_sq (a b : ℝ) (x : Features d) :
    ‖a • x+b • shift x‖^2 ≤ 2*(a^2+b^2)*‖x‖^2 := by
  have hn := norm_add_le (a • x) (b • shift x)
  simp only [norm_smul, Real.norm_eq_abs, norm_shift] at hn
  have ht := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hv := mul_nonneg (sq_nonneg (|a|-|b|)) (sq_nonneg ‖x‖)
  rw [← sq_abs a, ← sq_abs b]
  nlinarith only [ht, hv]

lemma inner_bound_sq (x y : Features d) : ⟪x,y⟫^2 ≤ ‖x‖^2*‖y‖^2 := by
  simpa [sq_abs, mul_pow] using
    pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm x y) 2

lemma gradient_size_sq (a b : ℝ) (v g : Features d) :
    ⟪g,v⟫^2+⟪shift g,v⟫^2+‖a • g+b • shift g‖^2 ≤
      2*(a^2+b^2+‖v‖^2)*‖g‖^2 := by
  have hs := inner_bound_sq (shift g) v
  rw [norm_shift] at hs
  nlinarith only [hs, inner_bound_sq g v, filter_size_sq a b g]

lemma first_variation_sq (a b e f : ℝ) (x v h : Features d) :
    (e*⟪x,v⟫+f*⟪shift x,v⟫+⟪a • x+b • shift x,h⟫)^2 ≤
      4*‖x‖^2*(a^2+b^2+‖v‖^2)*(e^2+f^2+‖h‖^2) := by
  let E := ⟪e • x+f • shift x,v⟫
  let A := ⟪a • x+b • shift x,h⟫
  have he : E^2 ≤ (2*(e^2+f^2)*‖x‖^2)*‖v‖^2 :=
    (inner_bound_sq _ _).trans
      (mul_le_mul_of_nonneg_right (filter_size_sq e f x) (sq_nonneg _))
  have ha : A^2 ≤ (2*(a^2+b^2)*‖x‖^2)*‖h‖^2 :=
    (inner_bound_sq _ _).trans
      (mul_le_mul_of_nonneg_right (filter_size_sq a b x) (sq_nonneg _))
  have hid : E = e*⟪x,v⟫+f*⟪shift x,v⟫ := by
    simp [E, inner_add_left, real_inner_smul_left]
  rw [← hid]
  change (E+A)^2 ≤ _
  nlinarith only [he, ha, sq_nonneg (E-A),
    mul_nonneg (sq_nonneg ‖x‖) (mul_nonneg (sq_nonneg ‖v‖) (sq_nonneg ‖h‖)),
    mul_nonneg (sq_nonneg ‖x‖)
      (mul_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) (add_nonneg (sq_nonneg e) (sq_nonneg f)))]

lemma second_variation_bound (e f : ℝ) (x h : Features d) :
    |⟪e • x+f • shift x,h⟫| ≤ ‖x‖*(e^2+f^2+‖h‖^2) := by
  apply (abs_real_inner_le_norm _ _).trans
  have hn := norm_add_le (e • x) (f • shift x)
  simp only [norm_smul, Real.norm_eq_abs, norm_shift] at hn
  apply (mul_le_mul_of_nonneg_right hn (norm_nonneg h)).trans
  have hh : (|e|+|f|)*‖h‖ ≤ e^2+f^2+‖h‖^2 := by
    nlinarith [sq_nonneg (|e|-‖h‖), sq_nonneg (|f|-‖h‖), sq_abs e, sq_abs f,
      sq_nonneg e, sq_nonneg f]
  calc _ = ‖x‖*((|e|+|f|)*‖h‖) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hh (norm_nonneg _)

lemma channel_self_coupling (a b σ : ℝ) (g : Features d) (hσ : σ^2=1) :
    ⟪g+σ • shift g,a • g+b • shift g⟫ = (a+σ*b)/2 * ‖g+σ • shift g‖^2 := by
  have hx : (σ-1)*(σ+1)=0 := by nlinarith
  have h : σ=1 ∨ σ= -1 := (mul_eq_zero.mp hx).imp (by intro h; linarith) (by intro h; linarith)
  rcases h with rfl | rfl <;>
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, inner_shift_shift, real_inner_comm (shift g) g] <;> ring

lemma channel_pair (a b σ η : ℝ) (g k v : Features d) (hσ : σ^2=1) :
    let V := v+η • (a • g+b • shift g)
    let A := a + η*⟪g,v⟫ + η*⟪k,V⟫
    let B := b + η*⟪shift g,v⟫ + η*⟪shift k,V⟫
    A+σ*B = (1-η^2*‖g+σ • shift g‖^2/2)*(a+σ*b) +
      η*⟪(g+k)+σ • shift (g+k),V⟫ := by
  dsimp only
  have he := channel_self_coupling a b σ g hσ
  simp only [inner_add_left, inner_add_right, shift_add, real_inner_smul_left,
    real_inner_smul_right] at he ⊢
  linear_combination -η^2 * he

end LongTails.Proofs.LogisticSpatialResponse
