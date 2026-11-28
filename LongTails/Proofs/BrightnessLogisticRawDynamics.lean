import LongTails.Setups.BrightnessLogisticRaw
import Mathlib.Tactic

open scoped RealInnerProductSpace
open LongTails.Setups.BrightnessLogisticRaw

namespace LongTails.Proofs.BrightnessLogisticRawDynamics

lemma confidence (x : ℝ) : 0 ≤ vote x ∧ vote x ≤ 1 := by
  unfold vote
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 1+Real.exp x)).mpr
    linarith [Real.exp_pos x]

noncomputable def iterate (p : Params) (η : ℝ) (k : ℕ) :
    ℝ × LongTails.Setups.TwoSampleQuadraticPerceptron.Features p.d :=
  (fun w => w + η • (answer p.rows w).1)^[k] p.input.start

lemma initial (p : Params) (η : ℝ) : iterate p η 0 = (p.t/p.R,p.w) := rfl

lemma next (p : Params) (η : ℝ) (k : ℕ) :
    iterate p η (k+1) = iterate p η k + η • (answer p.rows (iterate p η k)).1 :=
  Function.iterate_succ_apply' _ k _

lemma norm_detail_force (p : Params) (hp : Valid p) (w : ℝ × LongTails.Setups.TwoSampleQuadraticPerceptron.Features p.d) :
    ‖(answer p.rows w).1.2‖ ≤ p.H := by
  change ‖(p.n : ℝ)⁻¹ • ∑ i, vote (score p.rows w i) • p.z i‖ ≤ p.H
  have hn : 0 < (p.n : ℝ) := by positivity
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i : Fin p.n, p.H := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      apply (norm_sum_le ..).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (confidence _).1]
      exact (mul_le_mul_of_nonneg_right (confidence _).2 (norm_nonneg _)).trans
        (by simpa using hp.detail i)
    _ = _ := by simp [Finset.sum_const,hn.ne']

lemma detail_displacement (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 ≤ η) (k : ℕ) :
    ‖(iterate p η k).2-p.w‖ ≤ k*η*p.H := by
  induction k with
  | zero => simp [initial]
  | succ k ih =>
    rw [next,Nat.cast_succ]
    change ‖(iterate p η k).2 + η • (answer p.rows (iterate p η k)).1.2 - p.w‖ ≤ _
    rw [show (iterate p η k).2 + η • (answer p.rows (iterate p η k)).1.2 - p.w =
        ((iterate p η k).2-p.w) + η • (answer p.rows (iterate p η k)).1.2 by abel]
    apply (norm_add_le ..).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hη]
    linarith [mul_le_mul_of_nonneg_left (norm_detail_force p hp (iterate p η k)) hη]

lemma small_step_fails (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 ≤ η) (k : ℕ)
    (hk : k*η*p.H^2 ≤ p.debt) : ¬ fits p.rows (iterate p η k) := by
  obtain ⟨i,j,a,_,_,ha,hb,hzero,hdebt⟩ := hp.balanced
  let v := iterate p η k
  have hinc (l : Fin p.n) : ⟪v.2,p.z l⟫ ≤ ⟪p.w,p.z l⟫ + k*η*p.H^2 := by
    have h := real_inner_le_norm (v.2-p.w) (p.z l)
    rw [inner_sub_left] at h
    have hbound := mul_le_mul (detail_displacement p hp hη k) (hp.detail l)
      (norm_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hη) hp.detailPos.le)
    nlinarith only [h,hbound]
  intro hf
  have hi := hf i
  have hj := hf j
  change 0 < (p.R*p.dc i)*v.1 + ⟪v.2,p.z i⟫ at hi
  change 0 < (p.R*p.dc j)*v.1 + ⟪v.2,p.z j⟫ at hj
  have hb' : 0 ≤ 1-a := by linarith
  have hpos : 0 < a*((p.R*p.dc i)*v.1+⟪v.2,p.z i⟫) +
      (1-a)*((p.R*p.dc j)*v.1+⟪v.2,p.z j⟫) := by
    rcases ha.eq_or_lt with he | hh
    · simpa [← he] using hj
    · exact add_pos_of_pos_of_nonneg (mul_pos hh hi) (mul_nonneg hb' hj.le)
  have he := congrArg (fun x : ℝ => x*p.R*v.1) hzero
  have hwi := mul_le_mul_of_nonneg_left (hinc i) ha
  have hwj := mul_le_mul_of_nonneg_left (hinc j) hb'
  nlinarith only [he,hwi,hwj,hdebt,hk,hpos]

noncomputable def hard (p : Params) (k : ℕ) : ℝ :=
  (fun x : ℝ => x + mean (fun i => if p.dc i*x < 0 then p.dc i else 0))^[k] p.b

lemma hard_lattice (p : Params) (hp : Valid p) (k : ℕ) :
    ∃ z : ℤ, hard p k = p.b + z*p.L := by
  induction k with
  | zero => exact ⟨0,by simp [hard]⟩
  | succ k ih =>
    obtain ⟨z,hz⟩ := ih
    have hg : p.δ ≤ |hard p k| := hz ▸ hp.clearance z
    have hn : hard p k ≠ 0 := by
      intro hh
      rw [hh,abs_zero] at hg
      linarith [hp.gapPos]
    have hi : ∃ j : ℤ, mean (fun i => if p.dc i*hard p k < 0 then p.dc i else 0) = j*p.L := by
      rcases lt_or_gt_of_ne hn with h | h
      · simpa only [mul_neg_iff,h,not_lt_of_gt h,and_true,and_false,false_or,or_false]
          using hp.positiveMass
      · simpa only [mul_neg_iff,h,not_lt_of_gt h,and_true,and_false,false_or,or_false]
          using hp.negativeMass
    obtain ⟨j,hj⟩ := hi
    refine ⟨z+j,?_⟩
    rw [show hard p (k+1) = hard p k +
      mean (fun i => if p.dc i*hard p k < 0 then p.dc i else 0) from
      Function.iterate_succ_apply' _ k _,hj,hz,Int.cast_add]
    ring

lemma hard_clearance (p : Params) (hp : Valid p) (k : ℕ) : p.δ ≤ |hard p k| := by
  obtain ⟨z,hz⟩ := hard_lattice p hp k
  rw [hz]
  exact hp.clearance z

private lemma vote_tail (x : ℝ) : vote x ≤ Real.exp (-x) := by
  rw [vote, Real.exp_neg, one_div]
  exact inv_anti₀ (Real.exp_pos _) (by linarith)

lemma soft_hard_gap {x y δ η : ℝ} (hη : 0 < η)
    (hg : δ ≤ |y|) (hd : |x - y| ≤ δ / 2) :
    |vote (η * x) - (if y < 0 then 1 else 0)| ≤ Real.exp (-(η * (δ / 2))) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hd
  split_ifs with h
  · rw [abs_of_neg h] at hg
    have hx : x ≤ -(δ / 2) := by linarith
    rw [abs_of_nonpos (by linarith [(confidence (η*x)).2] : vote (η*x) - 1 ≤ 0)]
    have hid : -(vote (η*x) - 1) = vote (-(η*x)) := by
      rw [vote, vote, Real.exp_neg]
      field_simp
      ring
    rw [hid]
    exact (vote_tail _).trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hx hη.le]))
  · rw [abs_of_nonneg (le_of_not_gt h)] at hg
    have hx : δ / 2 ≤ x := by linarith
    rw [sub_zero, abs_of_pos (show 0 < vote (η*x) by unfold vote; positivity)]
    exact (vote_tail _).trans (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hx hη.le]))

lemma relative_gap {d x u r α m δ : ℝ} (hα : 0 < α) (hδ : 0 ≤ δ)
    (hd : m ≤ |d|) (hg : δ ≤ |u|) (hx : |x-u| ≤ δ/4) (hr : |r| ≤ m*δ/4) :
    |vote (α*(d*x+r))-(if d*u < 0 then 1 else 0)| ≤ Real.exp (-(α*(m*δ/2))) := by
  have hi : |d| * δ ≤ |d*u| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hg (abs_nonneg _)
  have he : |d*x+r-d*u| ≤ |d| * δ/2 := by
    rw [show d*x+r-d*u = d*(x-u)+r by ring]
    apply (abs_add_le ..).trans
    rw [abs_mul]
    linarith [mul_le_mul_of_nonneg_left hx (abs_nonneg d),mul_le_mul_of_nonneg_right hd hδ]
  apply (soft_hard_gap hα hi he).trans
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hd hδ) hα.le]

lemma mean_abs_bound {n : ℕ+} (f : Fin n → ℝ) {a : ℝ} (h : ∀ i, |f i| ≤ a) :
    |mean f| ≤ a := by
  have hn : 0 < (n : ℝ) := by positivity
  rw [mean,abs_mul,abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, a := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => h i)
    _ = _ := by simp [Finset.sum_const,hn.ne']

lemma mean_sub {n : ℕ+} (f g : Fin n → ℝ) :
    mean f - mean g = mean (fun i => f i-g i) := by
  simp only [mean,Finset.sum_sub_distrib,mul_sub]

lemma shadow_step (p : Params) (hp : Valid p) (k : ℕ) (r : Fin p.n → ℝ)
    {x α : ℝ} (hα : 0 < α) (hx : |x-hard p k| ≤ p.δ/4)
    (hr : ∀ i, |r i| ≤ p.m*p.δ/4) :
    |x + mean (fun i => p.dc i*vote (α*(p.dc i*x+r i))) - hard p (k+1)| ≤
    |x-hard p k| + p.D*Real.exp (-(α*(p.m*p.δ/2))) := by
  rw [show hard p (k+1) = hard p k +
      mean (fun i => if p.dc i*hard p k < 0 then p.dc i else 0) from
      Function.iterate_succ_apply' _ k _,add_sub_add_comm,mean_sub]
  apply (abs_add_le ..).trans
  apply add_le_add_right
  apply mean_abs_bound
  intro i
  by_cases hz : p.dc i = 0
  · simp only [hz,zero_mul,lt_self_iff_false,↓reduceIte,sub_zero,abs_zero]
    exact mul_nonneg ((abs_nonneg _).trans (hp.maxDC i)) (Real.exp_pos _).le
  have he := relative_gap hα hp.gapPos.le (hp.minDC i hz) (hard_clearance p hp k) hx (hr i)
  rw [show (if p.dc i*hard p k < 0 then p.dc i else 0) =
    p.dc i*(if p.dc i*hard p k < 0 then 1 else 0) by split <;> simp, ← mul_sub,abs_mul]
  exact mul_le_mul (hp.maxDC i) he (abs_nonneg _) ((abs_nonneg _).trans (hp.maxDC i))

noncomputable def axial (p : Params) (η : ℝ) (k : ℕ) : ℝ := (iterate p η (k+1)).1/(η*p.R)

noncomputable def residual (p : Params) (η : ℝ) (k : ℕ) (i : Fin p.n) : ℝ :=
  ⟪(iterate p η (k+1)).2,p.z i⟫/(η*p.R^2)

lemma score_split (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) (k : ℕ) (i : Fin p.n) :
    score p.rows (iterate p η (k+1)) i = (η*p.R^2)*(p.dc i*axial p η k+residual p η k i) := by
  change p.R*p.dc i*(iterate p η (k+1)).1 + ⟪(iterate p η (k+1)).2,p.z i⟫ = _
  rw [axial,residual]
  field_simp [hη.ne',hp.positiveScale.ne']

lemma mean_scale {n : ℕ+} (r : ℝ) (f : Fin n → ℝ) :
    mean (fun i => r*f i) = r*mean f := by
  rw [mean,mean,← Finset.mul_sum]
  ring

lemma axial_update (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) (k : ℕ) :
    axial p η (k+1) = axial p η k +
      mean (fun i => p.dc i*vote ((η*p.R^2)*(p.dc i*axial p η k+residual p η k i))) := by
  simp_rw [← score_split p hp hη k]
  unfold axial
  nth_rw 1 [next]
  change ((iterate p η (k+1)).1 + η*mean (fun i =>
    (p.R*p.dc i)*vote (score p.rows (iterate p η (k+1)) i)))/(η*p.R) = _
  simp_rw [mul_assoc p.R,mean_scale]
  field_simp [hη.ne',hp.positiveScale.ne']

lemma axial_start (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) :
    axial p η 0 = p.t/(η*p.R^2)+p.b := by
  have hscore (i : Fin p.n) : score p.rows (iterate p η 0) i = p.t*p.dc i+⟪p.w,p.z i⟫ := by
    change p.R*p.dc i*(p.t/p.R) + ⟪p.w,p.z i⟫ = _
    field_simp [hp.positiveScale.ne']
  rw [axial,next]
  change (p.t/p.R+η*mean (fun i => (p.R*p.dc i)*vote (score p.rows (iterate p η 0) i)))/(η*p.R) = _
  simp_rw [hscore,mul_assoc p.R,mean_scale]
  unfold Params.b
  field_simp [hη.ne',hp.positiveScale.ne']

lemma shadow_prefix (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) (T : ℕ)
    (hr : ∀ k < T, ∀ i, |residual p η k i| ≤ p.m*p.δ/4)
    (hbudget : |p.t/(η*p.R^2)| +
      T*(p.D*Real.exp (-((η*p.R^2)*(p.m*p.δ/2)))) ≤ p.δ/4) :
    ∀ k ≤ T, |axial p η k-hard p k| ≤ |p.t/(η*p.R^2)| +
      k*(p.D*Real.exp (-((η*p.R^2)*(p.m*p.δ/2)))) := by
  have hD : 0 ≤ p.D := (abs_nonneg _).trans (hp.maxDC 0)
  let cost := p.D*Real.exp (-((η*p.R^2)*(p.m*p.δ/2)))
  have hc : 0 ≤ cost := mul_nonneg hD (Real.exp_pos _).le
  change ∀ k ≤ T, |axial p η k-hard p k| ≤ |p.t/(η*p.R^2)| + k*cost
  intro k
  induction k with
  | zero =>
    intro _
    rw [axial_start p hp hη]
    simp [hard]
  | succ k ih =>
    intro hk
    have hkt := Nat.le_of_succ_le hk
    have hprev := ih hkt
    have hgap : |axial p η k-hard p k| ≤ p.δ/4 := by
      apply hprev.trans
      exact (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkt) hc) _).trans hbudget
    rw [axial_update p hp hη]
    have hh := shadow_step p hp k (residual p η k) (mul_pos hη (sq_pos_of_pos hp.positiveScale))
      hgap (hr k hk)
    change _ ≤ |axial p η k-hard p k|+cost at hh
    rw [Nat.cast_succ]
    linarith

lemma scale_prices (p : Params) (hp : Valid p) {α : ℝ}
    (h : p.threshold*Real.log p.R ≤ α) :
    0 < α ∧ |p.t| ≤ α*p.δ/16 ∧ p.H*‖p.w‖ ≤ α*p.m*p.δ/16 ∧
      4*Real.log p.R ≤ α*(p.m*p.δ/2) := by
  obtain ⟨i,_,_,hi,_⟩ := hp.balanced
  have hmD := (hp.minDC i hi.ne').trans (hp.maxDC i)
  have hD := hp.minPos.le.trans hmD
  have hpos := mul_pos hp.minPos hp.gapPos
  have hH := hp.detailPos.le
  have hbase : 0 ≤ 16*(1+|p.t| * p.D+p.H*‖p.w‖) := by positivity
  have hL := hp.scale
  have h0 := mul_le_mul_of_nonneg_right h hpos.le
  rw [Params.threshold] at h0
  have he : 16*(1+|p.t| * p.D+p.H*‖p.w‖)/(p.m*p.δ)*Real.log p.R*(p.m*p.δ) =
      16*(1+|p.t| * p.D+p.H*‖p.w‖)*Real.log p.R := by field_simp [hp.minPos.ne',hp.gapPos.ne']
  rw [he] at h0
  have hstatic := mul_le_mul_of_nonneg_left hL hbase
  have htx := mul_le_mul_of_nonneg_left hmD (abs_nonneg p.t)
  have htw := mul_nonneg hp.detailPos.le (norm_nonneg p.w)
  have htD := mul_nonneg (abs_nonneg p.t) hD
  have ha : 0 < α := by
    by_contra! hh
    nlinarith only [h0,hstatic,htD,htw,mul_nonpos_of_nonpos_of_nonneg hh hpos.le]
  refine ⟨ha,?_,?_,?_⟩
  · apply (le_of_mul_le_mul_right _ hp.minPos : _)
    nlinarith only [h0,hstatic,htx,htw]
  · nlinarith only [h0,hstatic,htD]
  · have hlog : 0 ≤ Real.log p.R := by linarith
    nlinarith only [h0,mul_nonneg htD hlog,mul_nonneg htw hlog,hlog]

lemma soft_price (p : Params) (hp : Valid p) {α : ℝ}
    (h : p.threshold*Real.log p.R ≤ α) :
    Real.exp (-(α*(p.m*p.δ/2))) ≤ (p.R^4)⁻¹ := by
  have hlog := (scale_prices p hp h).2.2.2
  apply (Real.exp_le_exp.mpr (neg_le_neg hlog)).trans
  rw [Real.exp_neg,show 4*Real.log p.R=(4 : ℕ)*Real.log p.R by norm_num,
    Real.exp_nat_mul,Real.exp_log hp.positiveScale]

lemma residual_price (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) (k : ℕ)
    (hlarge : p.threshold*Real.log p.R ≤ η*p.R^2)
    (htime : (k+1 : ℕ)*p.H^2 ≤ p.R^2*(p.m*p.δ/8)) :
    ∀ i, |residual p η k i| ≤ p.m*p.δ/4 := by
  intro i
  have hα := (scale_prices p hp hlarge).1
  have hstart := (scale_prices p hp hlarge).2.2.1
  have hd := detail_displacement p hp hη.le (k+1)
  have hrad : ‖(iterate p η (k+1)).2‖ ≤ (k+1 : ℕ)*η*p.H+‖p.w‖ := by
    simpa using (norm_add_le ((iterate p η (k+1)).2-p.w) p.w).trans (add_le_add_left hd _)
  have hH0 := hp.detailPos.le
  have hs := (abs_real_inner_le_norm (iterate p η (k+1)).2 (p.z i)).trans
    (mul_le_mul hrad (hp.detail i) (norm_nonneg _) (by positivity : 0 ≤ (k+1 : ℕ)*η*p.H+‖p.w‖))
  rw [residual,abs_div,abs_of_pos hα,div_le_iff₀ hα]
  nlinarith only [hs,hstart,mul_le_mul_of_nonneg_left htime hη.le,
    mul_nonneg (mul_nonneg hα.le hp.minPos.le) hp.gapPos.le]

lemma total_price (p : Params) (hp : Valid p) {α : ℝ} (hlarge : p.threshold*Real.log p.R ≤ α)
    (T : ℕ) (htime : T*p.H^2 ≤ p.R^2*(p.m*p.δ/8)) :
    |p.t/α| + T*(p.D*Real.exp (-(α*(p.m*p.δ/2)))) ≤ p.δ/4 := by
  have hα := (scale_prices p hp hlarge).1
  have ht := (scale_prices p hp hlarge).2.1
  have hD := (abs_nonneg _).trans (hp.maxDC 0)
  have ht' : |p.t/α| ≤ p.δ/16 := by
    rw [abs_div,abs_of_pos hα,div_le_iff₀ hα]
    linarith
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (soft_price p hp hlarge) hD)
    (Nat.cast_nonneg T)
  have hH := sq_pos_of_pos hp.detailPos
  have hR := sq_pos_of_pos hp.positiveScale
  have hT : (T : ℝ) ≤ p.R^2*(p.m*p.δ/(8*p.H^2)) := by
    have htime := (le_div_iff₀ hH).mpr htime
    convert htime using 1
    field_simp
  have hs := hp.size
  have hc : T*(p.D*(p.R^4)⁻¹) ≤ p.δ/16 := by
    rw [← mul_assoc,← div_eq_mul_inv,div_le_iff₀ (pow_pos hp.positiveScale _)]
    have hbig := mul_le_mul_of_nonneg_right hs hR.le
    nlinarith only [hbig,mul_le_mul_of_nonneg_right hT hD,mul_nonneg hD hR.le]
  linarith [he.trans hc,hp.gapPos]

lemma shadow_fails (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) (k : ℕ)
    (ha : |axial p η k-hard p k| ≤ p.δ/4)
    (hr : ∀ i, |residual p η k i| ≤ p.m*p.δ/4) : ¬ fits p.rows (iterate p η (k+1)) := by
  obtain ⟨i,j,_,hi,hj,_⟩ := hp.balanced
  have hg := hard_clearance p hp k
  have hn : hard p k ≠ 0 := by
    intro h
    rw [h,abs_zero] at hg
    linarith [hp.gapPos]
  have hw : ∃ l, p.dc l*hard p k < 0 := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact ⟨i,mul_neg_of_pos_of_neg hi h⟩
    · exact ⟨j,mul_neg_of_neg_of_pos hj h⟩
  obtain ⟨l,hl⟩ := hw
  have hd : p.dc l ≠ 0 := by rintro hh; simp [hh] at hl
  have hm := hp.minDC l hd
  have hh := mul_le_mul_of_nonneg_left hg (abs_nonneg (p.dc l))
  rw [← abs_mul,abs_of_neg hl] at hh
  have he : p.dc l*(axial p η k-hard p k) ≤ |p.dc l| * (p.δ/4) :=
    (le_abs_self _).trans ((abs_mul ..).le.trans (mul_le_mul_of_nonneg_left ha (abs_nonneg _)))
  have hb := (le_abs_self _).trans (hr l)
  have hbad : p.dc l*axial p η k+residual p η k l ≤ 0 := by
    nlinarith only [he,hb,hh,mul_le_mul_of_nonneg_right hm hp.gapPos.le,
      mul_nonneg (abs_nonneg (p.dc l)) hp.gapPos.le]
  intro hf
  have hf' := hf l
  rw [score_split p hp hη] at hf'
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hη.le (sq_nonneg _)) hbad)) hf'

lemma all_steps_fail (p : Params) (hp : Valid p) {η : ℝ} (hη : 0 < η) (K : ℕ)
    (hK : K*p.H^2 ≤ p.R^2*(p.m*p.δ/8))
    (hslow : K*(p.threshold*Real.log p.R)*p.H^2 ≤ p.R^2*p.debt) :
    ¬ fits p.rows (iterate p η K) := by
  rcases le_or_gt (η*p.R^2) (p.threshold*Real.log p.R) with h | h
  · apply small_step_fails p hp hη.le
    apply le_of_mul_le_mul_right _ (sq_pos_of_pos hp.positiveScale)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg K)) (sq_nonneg p.H)
    nlinarith only [hh,hslow]
  · cases K with
    | zero =>
      apply small_step_fails p hp hη.le
      simpa using hp.debtPos.le
    | succ k =>
      have hkr (j : ℕ) (hj : j ≤ k) : (j+1 : ℕ)*p.H^2 ≤ p.R^2*(p.m*p.δ/8) :=
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_succ hj)) (sq_nonneg _)).trans hK
      have hk' : (k : ℝ)*p.H^2 ≤ p.R^2*(p.m*p.δ/8) :=
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_succ k)) (sq_nonneg _)).trans hK
      have hb := total_price p hp h.le k hk'
      have hr (j : ℕ) (hj : j ≤ k) := residual_price p hp hη j h.le (hkr j hj)
      have hs := shadow_prefix p hp hη k (fun j hj => hr j hj.le) hb k le_rfl
      exact shadow_fails p hp hη k (hs.trans hb) (hr k le_rfl)

end LongTails.Proofs.BrightnessLogisticRawDynamics
