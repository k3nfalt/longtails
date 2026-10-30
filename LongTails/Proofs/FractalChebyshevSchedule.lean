import LongTails.Proofs.FractalChebyshevChain
import LongTails.Proofs.ScheduleBlockGeneric

namespace OracleTemplate.FractalChebyshev

open Real Finset OracleTemplate.ScheduleBlock

noncomputable def etaOf (L μ : ℝ) (k : ℕ) (j : ℕ) : ℝ := (schedule L μ k).getD j 0

lemma schedule_length (L μ : ℝ) (k : ℕ) : (schedule L μ k).length = 2 ^ k := by
  simp [schedule, angles_length]

lemma root_bounds {L μ : ℝ} (hμL : μ < L) (θ : ℝ) :
    μ ≤ (L + μ) / 2 + (L - μ) / 2 * cos θ ∧ (L + μ) / 2 + (L - μ) / 2 * cos θ ≤ L := by
  have h1 := neg_one_le_cos θ
  have h2 := cos_le_one θ
  constructor <;> nlinarith

lemma stepOf_bounds {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (θ : ℝ) :
    1 / L ≤ stepOf L μ θ ∧ stepOf L μ θ ≤ 1 / μ := by
  obtain ⟨h1, h2⟩ := root_bounds hμL θ
  unfold stepOf
  exact ⟨one_div_le_one_div_of_le (by linarith) h2, one_div_le_one_div_of_le hμ h1⟩

lemma getD_map_of_lt {l : List ℝ} {f : ℝ → ℝ} {j : ℕ} (hj : j < l.length) :
    (l.map f).getD j 0 = f (l.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj]
  simp

lemma etaOf_eq {L μ : ℝ} {k j : ℕ} (hj : j < 2 ^ k) :
    etaOf L μ k j = stepOf L μ ((angles k).getD j 0) := by
  unfold etaOf schedule
  exact getD_map_of_lt (by rw [angles_length]; exact hj)

lemma etaOf_bounds {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) {k j : ℕ} (hj : j < 2 ^ k) :
    1 / L ≤ etaOf L μ k j ∧ etaOf L μ k j ≤ 1 / μ := by
  rw [etaOf_eq hj]; exact stepOf_bounds hμ hμL _

lemma etaOf_nonneg {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (k j : ℕ) : 0 ≤ etaOf L μ k j := by
  by_cases hj : j < 2 ^ k
  · have := (etaOf_bounds hμ hμL hj).1
    have : 0 < 1 / L := by apply div_pos one_pos; linarith
    linarith
  · unfold etaOf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [schedule_length]; omega)]
    simp

lemma one_sub_stepOf {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (lam θ : ℝ) :
    1 - stepOf L μ θ * lam = fac ((L + μ - 2 * lam) / (L - μ)) ((L + μ) / (L - μ)) θ := by
  have hr := (root_bounds hμL θ).1
  have hd : 0 < L - μ := by linarith
  have hr0 : (L + μ) / 2 + (L - μ) / 2 * cos θ ≠ 0 := by linarith
  have hnum : (L + μ - 2 * lam) / (L - μ) + cos θ =
      ((L + μ) / 2 + (L - μ) / 2 * cos θ - lam) * (2 / (L - μ)) := by
    field_simp
    ring
  have hden : (L + μ) / (L - μ) + cos θ =
      ((L + μ) / 2 + (L - μ) / 2 * cos θ) * (2 / (L - μ)) := by
    field_simp
  unfold stepOf fac
  rw [hnum, hden, mul_div_mul_right _ _ (by positivity)]
  have hD : L + μ + (L - μ) * cos θ ≠ 0 := by nlinarith
  field_simp

lemma prod_Ico_getD (l : List ℝ) (φ : ℝ → ℝ) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ l.length) :
    ∏ j ∈ Ico s t, φ (l.getD j 0) = (((l.drop s).take (t - s)).map φ).prod := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rw [Finset.prod_Ico_succ_top hst, ih (by omega), show t + 1 - s = (t - s) + 1 by omega,
      List.take_add_one, List.map_append, List.prod_append]
    congr 1
    rw [List.getElem?_drop, show s + (t - s) = t by omega, List.getElem?_eq_getElem (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < l.length by omega)]

lemma win_schedule {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (k : ℕ) (lam : ℝ) {s t : ℕ}
    (hst : s ≤ t) (ht : t ≤ 2 ^ k) :
    win (etaOf L μ k) lam s t = prodF ((L + μ - 2 * lam) / (L - μ)) ((L + μ) / (L - μ))
      (((angles k).drop s).take (t - s)) := by
  unfold win prodF
  rw [← prod_Ico_getD (angles k) _ hst (by rw [angles_length]; exact ht)]
  apply Finset.prod_congr rfl
  intro j hj
  rw [etaOf_eq (by have := (Finset.mem_Ico.mp hj).2; omega), one_sub_stepOf hμ hμL]

lemma prodF_mem_unit {x x0 : ℝ} (hx : 1 ≤ x) (hxx : x ≤ x0) (l : List ℝ)
    (hl : ∀ θ ∈ l, 0 < θ ∧ θ < π) : 0 ≤ prodF x x0 l ∧ prodF x x0 l ≤ 1 := by
  induction l with
  | nil => simp [prodF]
  | cons θ l ih =>
    rw [prodF_cons]
    obtain ⟨h1, h2⟩ := ih (fun θ' h' => hl θ' (by simp [h']))
    have hθ := hl θ (by simp)
    have hc : -1 < cos θ := by
      have := cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
      rw [cos_pi] at this; linarith
    have hpos : 0 < x0 + cos θ := by linarith
    have hf1 : 0 ≤ fac x x0 θ := by unfold fac; apply div_nonneg <;> linarith
    have hf2 : fac x x0 θ ≤ 1 := by unfold fac; rw [div_le_one hpos]; linarith
    constructor
    · exact mul_nonneg hf1 h1
    · nlinarith

lemma x_bounds {L μ lam : ℝ} (hμL : μ < L) (h0 : 0 ≤ lam) (hL : lam ≤ L) :
    -1 ≤ (L + μ - 2 * lam) / (L - μ) ∧ (L + μ - 2 * lam) / (L - μ) ≤ (L + μ) / (L - μ) := by
  have hd : 0 < L - μ := by linarith
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · exact div_le_div_of_nonneg_right (by linarith) hd.le

lemma x0_gt_one {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) : 1 < (L + μ) / (L - μ) := by
  rw [lt_div_iff₀ (by linarith)]; linarith

theorem window_bound {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam)
    (hL : lam ≤ L) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ 2 ^ k) :
    |win (etaOf L μ k) lam s t| ≤ L / μ := by
  rw [win_schedule hμ hμL k lam hst ht]
  have hx0 := x0_gt_one hμ hμL
  obtain ⟨hx1, hx2⟩ := x_bounds hμL h0 hL
  have hK : 1 ≤ L / μ := by rw [le_div_iff₀ hμ]; linarith
  rcases le_or_gt lam μ with hlm | hlm
  · have hx : 1 ≤ (L + μ - 2 * lam) / (L - μ) := by rw [le_div_iff₀ (by linarith)]; linarith
    obtain ⟨p1, p2⟩ := prodF_mem_unit hx hx2 (((angles k).drop s).take (t - s))
      (fun θ h => angles_mem (List.mem_of_mem_drop (List.mem_of_mem_take h)))
    rw [abs_of_nonneg p1]; linarith
  · have hx : (L + μ - 2 * lam) / (L - μ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    refine (window_le_kappa k s (t - s) (by omega) hx0 hx1 hx).trans ?_
    apply max_le hK
    have hd' : L - μ ≠ 0 := by linarith
    have e : (L + μ) / (L - μ) - 1 = 2 * μ / (L - μ) := by
      rw [div_sub_one hd']; congr 1; ring
    rw [e, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hμ]
    nlinarith

theorem prefix_bound {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (k : ℕ) {lam : ℝ} (h0 : 0 ≤ lam)
    (hL : lam ≤ L) {t : ℕ} (ht : t ≤ 2 ^ k) : |pr (etaOf L μ k) lam t| ≤ 1 := by
  unfold pr
  rw [win_schedule hμ hμL k lam (Nat.zero_le t) ht, List.drop_zero, Nat.sub_zero]
  exact prefix_le_one k t (x0_gt_one hμ hμL) (x_bounds hμL h0 hL)

lemma prodF_angles (k : ℕ) : ∀ {x x0 : ℝ}, 1 < x0 →
    prodF x x0 (angles k) = dbl^[k] x / dbl^[k] x0 := by
  induction k with
  | zero =>
    intro x x0 _
    simp [angles, prodF, fac]
  | succ k ih =>
    intro x x0 hx0
    rw [angles, prodF_flatMap x x0 hx0, ih (one_lt_dbl hx0), Function.iterate_succ_apply,
      Function.iterate_succ_apply]

lemma abs_dbl_iterate_le (k : ℕ) : ∀ {x : ℝ}, -1 ≤ x → x ≤ 1 →
    -1 ≤ dbl^[k] x ∧ dbl^[k] x ≤ 1 := by
  induction k with
  | zero => intro x h1 h2; exact ⟨h1, h2⟩
  | succ k ih =>
    intro x h1 h2
    rw [Function.iterate_succ_apply]
    have := abs_dbl_le ⟨h1, h2⟩
    exact ih this.1 this.2

lemma pr_le_exp {η : ℕ → ℝ} {lam : ℝ} (t : ℕ)
    (hη : ∀ j < t, 0 ≤ 1 - η j * lam) :
    0 ≤ pr η lam t ∧ pr η lam t ≤ Real.exp (-(lam * ssum η t)) := by
  induction t with
  | zero => simp [pr, win, ssum]
  | succ t ih =>
    obtain ⟨i1, i2⟩ := ih (fun j hj => hη j (by omega))
    rw [pr_succ, ssum_succ]
    have hf := hη t (by omega)
    have he : 1 - η t * lam ≤ Real.exp (-(lam * η t)) := by
      have := Real.add_one_le_exp (-(lam * η t)); linarith
    refine ⟨mul_nonneg i1 hf, ?_⟩
    rw [mul_add, neg_add, Real.exp_add]
    exact mul_le_mul i2 (by linarith) hf (Real.exp_pos _).le

theorem final_relation {L μ : ℝ} (hμ : 0 < μ) (hμL : μ < L) (k : ℕ)
    (hT : 1 + 2 * L * ssum (etaOf L μ k) (2 ^ k) ≤ (dbl^[k] ((L + μ) / (L - μ))) ^ 2)
    {lam : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L) :
    (1 + 2 * lam * ssum (etaOf L μ k) (2 ^ k)) * pr (etaOf L μ k) lam (2 ^ k) ^ 2 ≤ 1 := by
  set S := ssum (etaOf L μ k) (2 ^ k)
  set P := pr (etaOf L μ k) lam (2 ^ k)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => etaOf_nonneg hμ hμL k j
  rcases le_or_gt lam μ with hlm | hlm
  · have hfac : ∀ j < 2 ^ k, 0 ≤ 1 - etaOf L μ k j * lam := by
      intro j hj
      have := (etaOf_bounds hμ hμL hj).2
      have : etaOf L μ k j * lam ≤ 1 / μ * μ :=
        mul_le_mul this hlm h0 (by positivity)
      rw [one_div_mul_cancel hμ.ne'] at this; linarith
    obtain ⟨p1, p2⟩ := pr_le_exp (2 ^ k) hfac
    have hP2 : P ^ 2 ≤ Real.exp (-(2 * lam * S)) := by
      calc P ^ 2 ≤ Real.exp (-(lam * S)) ^ 2 := pow_le_pow_left₀ p1 p2 2
        _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
    have he := Real.add_one_le_exp (2 * lam * S)
    have hpos : 0 ≤ 1 + 2 * lam * S := by positivity
    calc (1 + 2 * lam * S) * P ^ 2 ≤ (1 + 2 * lam * S) * Real.exp (-(2 * lam * S)) :=
          mul_le_mul_of_nonneg_left hP2 hpos
      _ ≤ Real.exp (2 * lam * S) * Real.exp (-(2 * lam * S)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  · have hx0 := x0_gt_one hμ hμL
    obtain ⟨hx1, -⟩ := x_bounds hμL h0 hL
    have hx : (L + μ - 2 * lam) / (L - μ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hP : P = dbl^[k] ((L + μ - 2 * lam) / (L - μ)) / dbl^[k] ((L + μ) / (L - μ)) := by
      change win _ _ 0 _ = _
      rw [win_schedule hμ hμL k lam (Nat.zero_le _) le_rfl, List.drop_zero, Nat.sub_zero,
        ← angles_length k, List.take_length, prodF_angles k hx0]
    set T := dbl^[k] ((L + μ) / (L - μ))
    obtain ⟨d1, d2⟩ := abs_dbl_iterate_le k hx1 hx
    have hT1 : 1 ≤ T := by
      have := le_dbl_iterate hx0.le k
      linarith
    have hP2 : P ^ 2 ≤ 1 / T ^ 2 := by
      rw [hP, div_pow, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have : (dbl^[k] ((L + μ - 2 * lam) / (L - μ))) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg T]
    have hl : 1 + 2 * lam * S ≤ T ^ 2 := by nlinarith
    calc (1 + 2 * lam * S) * P ^ 2 ≤ T ^ 2 * (1 / T ^ 2) :=
          mul_le_mul hl hP2 (sq_nonneg _) (sq_nonneg _)
      _ = 1 := by field_simp

end OracleTemplate.FractalChebyshev
