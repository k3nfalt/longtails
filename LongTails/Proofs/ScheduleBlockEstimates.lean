import LongTails.Proofs.ScheduleBlockVector

namespace OracleTemplate.ScheduleBlock

open Finset Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def posPart {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (v : E) : ℝ :=
  ∑ i, if 0 ≤ hH.eigenvalues rfl i then (hH.eigenvectorBasis rfl).repr v i ^ 2 else 0

noncomputable def negPart {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (v : E) : ℝ :=
  ∑ i, if hH.eigenvalues rfl i < 0 then (hH.eigenvectorBasis rfl).repr v i ^ 2 else 0

lemma posPart_nonneg {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (v : E) :
    0 ≤ posPart hH v :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

lemma negPart_nonneg {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (v : E) :
    0 ≤ negPart hH v :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> positivity

lemma posPart_add_negPart {H : E →L[ℝ] E} (hH : H.toLinearMap.IsSymmetric) (v : E) :
    posPart hH v + negPart hH v = ‖v‖ ^ 2 := by
  rw [norm_sq_coord (hH.eigenvectorBasis rfl), posPart, negPart, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ hH.eigenvalues rfl i
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma frame_step {f : E → ℝ} (H : E →L[ℝ] E) (c0 z : E) (η : ℕ → ℝ) (X : ℕ → E)
    (hX : ∀ s, X (s + 1) = X s - η s • gradient f (X s)) (s : ℕ) :
    X (s + 1) = X s - η s • ((gradient f c0 + H (z - c0)) + H (X s - z) +
      (gradient f (X s) - gradient f c0 - H (X s - c0))) := by
  rw [hX s]
  congr 2
  have : H (X s - c0) = H (X s - z) + H (z - c0) := by rw [← map_add]; congr 1; abel
  rw [this]; abel

variable {f : E → ℝ} {L ρ K R : ℝ} {η : ℕ → ℝ} {n : ℕ}

lemma frame_err (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (c0 x : E) {r : ℝ} (hx : ‖x - c0‖ ≤ r) :
    ‖gradient f x - gradient f c0 - fderiv ℝ (gradient f) c0 (x - c0)‖ ≤ ρ * r ^ 2 := by
  have hgd : Differentiable ℝ (gradient f) :=
    (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hf).differentiable
      (by norm_num)
  refine (OracleTemplate.NonlinearTemporalDiscrepancy.gradient_linearization_bound
    hρ hgd hH c0 x).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) hρ

theorem block_completed (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (F : ScheduleFacts η n L K) (hn : 1 ≤ n) (X : ℕ → E) (y : E)
    (hX : ∀ s, X (s + 1) = X s - η s • gradient f (X s)) (hX0 : X 0 = y)
    (hR : ∀ s ≤ n, ‖X s - y‖ ≤ R) :
    f (X n) - f y + ssum η n / 4 *
        posPart (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf y)
          (gradient f y + fderiv ℝ (gradient f) y (X n - y)) ≤
      (K ^ 2 / 2 + 1181) * ssum η n * (ρ * R ^ 2) ^ 2 +
        (L * K ^ 2 / 2 + 16 * L) * ssum η n ^ 2 * (ρ * R ^ 2) ^ 2 +
        2 * ssum η n * K ^ 2 * (n : ℝ) ^ 2 * (ρ * R ^ 2) ^ 2 + ρ * R ^ 3 := by
  set H := fderiv ℝ (gradient f) y
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf y
  set b := hsym.eigenvectorBasis rfl
  set lam := hsym.eigenvalues rfl
  have hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i :=
    fun v i => hsym.eigenvectorBasis_apply_self_apply rfl v i
  have hS := ssum_pos F hn le_rfl
  set S := ssum η n
  set e := fun s => gradient f (X s) - gradient f y - H (X s - y)
  have hstep : ∀ s < n, X (s + 1) = X s - η s • (gradient f y + H (X s - y) + e s) := by
    intro s _
    rw [hX s]
    congr 2
    show _ = _ + _ + (gradient f (X s) - gradient f y - H (X s - y))
    abel
  have hcoord := coord_traj H b lam hb η X y (gradient f y) e n hX0 hstep n le_rfl
  have he : ∀ s < n, ‖e s‖ ≤ ρ * R ^ 2 := fun s hs =>
    frame_err hf hρ hH y (X s) (hR s hs.le)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 (Nat.zero_le _))
  set u := X n - y
  have htay := (abs_le.mp (taylor_cubic hf hρ hH y (X n))).2
  have hu : ‖u‖ ≤ R := hR n le_rfl
  have hcub : ρ * ‖u‖ ^ 3 ≤ ρ * R ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu 3) hρ
  have hmodel := model_coord H b lam hb (gradient f y) u
  have hpos : posPart hsym (gradient f y + H u) =
      ∑ i, if 0 ≤ lam i then (b.repr (gradient f y) i + lam i * b.repr u i) ^ 2 else 0 := by
    unfold posPart
    apply Finset.sum_congr rfl
    intro i _
    rw [grad_coord H b lam hb]
  set ξ := fun i s => b.repr (e s) i
  have hci : ∀ i, b.repr (gradient f y) i * b.repr u i + lam i * b.repr u i ^ 2 / 2 +
      (if 0 ≤ lam i then S * (b.repr (gradient f y) i + lam i * b.repr u i) ^ 2 / 4 else 0) ≤
      (K ^ 2 / 2 + 1181) * wsum η (ξ i) n ^ 2 / S + (L * K ^ 2 / 2 + 16 * L) * wsum η (ξ i) n ^ 2 +
        2 * S * K ^ 2 * usum (ξ i) n ^ 2 := by
    intro i
    have hl := eig_bounds F.hL.le hlip y hsym i
    rw [hcoord i]
    exact coord_completed F hn hl.1 hl.2 (ξ i)
  have hw := wsum_sq_sum b η F.eta_nonneg e n he
  have hv := usum_sq_sum b e n he
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hci i
  have hsum2 : ∑ i, (if 0 ≤ lam i then S * (b.repr (gradient f y) i + lam i * b.repr u i) ^ 2 / 4
      else 0) = S / 4 * posPart hsym (gradient f y + H u) := by
    rw [hpos, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have eL : ∑ i, (b.repr (gradient f y) i * b.repr u i + lam i * b.repr u i ^ 2 / 2 +
      (if 0 ≤ lam i then S * (b.repr (gradient f y) i + lam i * b.repr u i) ^ 2 / 4 else 0)) =
      ∑ i, (b.repr (gradient f y) i * b.repr u i + lam i * b.repr u i ^ 2 / 2) +
        S / 4 * posPart hsym (gradient f y + H u) := by
    rw [Finset.sum_add_distrib, hsum2]
  have eR : ∑ i, ((K ^ 2 / 2 + 1181) * wsum η (ξ i) n ^ 2 / S +
      (L * K ^ 2 / 2 + 16 * L) * wsum η (ξ i) n ^ 2 + 2 * S * K ^ 2 * usum (ξ i) n ^ 2) =
      (K ^ 2 / 2 + 1181) * (∑ i, wsum η (ξ i) n ^ 2) / S +
        (L * K ^ 2 / 2 + 16 * L) * ∑ i, wsum η (ξ i) n ^ 2 +
        2 * S * K ^ 2 * ∑ i, usum (ξ i) n ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
  rw [eL, eR] at hsum
  have c1 : (K ^ 2 / 2 + 1181) * (∑ i, wsum η (ξ i) n ^ 2) / S ≤
      (K ^ 2 / 2 + 1181) * S * (ρ * R ^ 2) ^ 2 := by
    rw [div_le_iff₀ hS]
    have : 0 ≤ K ^ 2 / 2 + 1181 := by positivity
    have := mul_le_mul_of_nonneg_left hw this
    nlinarith
  have c2 : (L * K ^ 2 / 2 + 16 * L) * ∑ i, wsum η (ξ i) n ^ 2 ≤
      (L * K ^ 2 / 2 + 16 * L) * S ^ 2 * (ρ * R ^ 2) ^ 2 := by
    have : 0 ≤ L * K ^ 2 / 2 + 16 * L := by have := F.hL; positivity
    have := mul_le_mul_of_nonneg_left hw this
    linarith
  have c3 : 2 * S * K ^ 2 * ∑ i, usum (ξ i) n ^ 2 ≤
      2 * S * K ^ 2 * (n : ℝ) ^ 2 * (ρ * R ^ 2) ^ 2 := by
    have : 0 ≤ 2 * S * K ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hv this
    linarith
  have hT : f (X n) - f y ≤ ⟪gradient f y, u⟫ + ⟪H u, u⟫ / 2 + ρ * ‖u‖ ^ 3 := by
    linarith
  rw [hmodel] at hT
  linarith

theorem block_pred (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (F : ScheduleFacts η n L K) (hn : 1 ≤ n) (X : ℕ → E) (y0 y : E)
    (hX : ∀ s, X (s + 1) = X s - η s • gradient f (X s)) (hX0 : X 0 = y)
    (hy : ‖y - y0‖ ≤ R) (hR : ∀ s ≤ n, ‖X s - y‖ ≤ R) {Gγ : ℝ}
    (hγ : ‖gradient f y0 + fderiv ℝ (gradient f) y0 (y - y0)‖ ≤ Gγ) :
    f (X n) - f y + ssum η n / 2 *
        negPart (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf y0)
          (gradient f y0 + fderiv ℝ (gradient f) y0 (y - y0)) ≤
      K * Gγ * (ssum η n * (ρ * (2 * R) ^ 2)) +
        L * K ^ 2 / 2 * ssum η n ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
        1188 * ssum η n * (ρ * (2 * R) ^ 2) ^ 2 + 15 * L * ssum η n ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 +
        15 * L ^ 2 * ssum η n ^ 3 * (ρ * (2 * R) ^ 2) ^ 2 + 9 * ρ * R ^ 3 := by
  set H := fderiv ℝ (gradient f) y0
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf y0
  set b := hsym.eigenvectorBasis rfl
  set lam := hsym.eigenvalues rfl
  have hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i :=
    fun v i => hsym.eigenvectorBasis_apply_self_apply rfl v i
  have hS := ssum_pos F hn le_rfl
  set S := ssum η n
  set γ := gradient f y0 + H (y - y0)
  set e := fun s => gradient f (X s) - gradient f y0 - H (X s - y0)
  have hstep : ∀ s < n, X (s + 1) = X s - η s • (γ + H (X s - y) + e s) :=
    fun s _ => frame_step (f := f) H y0 y η X hX s
  have hcoord := coord_traj H b lam hb η X y γ e n hX0 hstep n le_rfl
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hy
  have hdist : ∀ s ≤ n, ‖X s - y0‖ ≤ 2 * R := by
    intro s hs
    calc ‖X s - y0‖ = ‖(X s - y) + (y - y0)‖ := by congr 1; abel
      _ ≤ ‖X s - y‖ + ‖y - y0‖ := norm_add_le _ _
      _ ≤ 2 * R := by linarith [hR s hs]
  have he : ∀ s < n, ‖e s‖ ≤ ρ * (2 * R) ^ 2 := fun s hs =>
    frame_err hf hρ hH y0 (X s) (hdist s hs.le)
  set u := X n - y
  have ht1 := (abs_le.mp (taylor_cubic hf hρ hH y0 (X n))).2
  have ht0 := (abs_le.mp (taylor_cubic hf hρ hH y0 y)).1
  have hd1 : ρ * ‖X n - y0‖ ^ 3 ≤ ρ * (2 * R) ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdist n le_rfl) 3) hρ
  have hd0 : ρ * ‖y - y0‖ ^ 3 ≤ ρ * R ^ 3 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 3) hρ
  have hid : ⟪gradient f y0, X n - y0⟫ + ⟪H (X n - y0), X n - y0⟫ / 2 -
      (⟪gradient f y0, y - y0⟫ + ⟪H (y - y0), y - y0⟫ / 2) = ⟪γ, u⟫ + ⟪H u, u⟫ / 2 := by
    have e1 : X n - y0 = (y - y0) + u := by
      rw [show u = X n - y from rfl]; abel
    rw [e1, show γ = gradient f y0 + H (y - y0) from rfl]
    have hs : ⟪H u, y - y0⟫ = ⟪H (y - y0), u⟫ := by
      exact (hsym u (y - y0)).trans (real_inner_comm _ _)
    simp only [map_add, inner_add_left, inner_add_right]
    rw [hs]; ring
  have hmodel := model_coord H b lam hb γ u
  set ξ := fun i s => b.repr (e s) i
  have hci : ∀ i, b.repr γ i * b.repr u i + lam i * b.repr u i ^ 2 / 2 +
      (if lam i < 0 then S * b.repr γ i ^ 2 / 2 else 0) ≤
      K * |b.repr γ i| * wsum η (ξ i) n + L * K ^ 2 * wsum η (ξ i) n ^ 2 / 2 +
        1188 * wsum η (ξ i) n ^ 2 / S + 15 * L * wsum η (ξ i) n ^ 2 +
        15 * S * L ^ 2 * wsum η (ξ i) n ^ 2 := by
    intro i
    have hl := eig_bounds F.hL.le hlip y0 hsym i
    rw [hcoord i]
    exact coord_pred F hn hl.1 hl.2 (ξ i)
  have hw := wsum_sq_sum b η F.eta_nonneg e n he
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hci i
  have hneg : ∑ i, (if lam i < 0 then S * b.repr γ i ^ 2 / 2 else 0) = S / 2 * negPart hsym γ := by
    unfold negPart
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  have eL : ∑ i, (b.repr γ i * b.repr u i + lam i * b.repr u i ^ 2 / 2 +
      (if lam i < 0 then S * b.repr γ i ^ 2 / 2 else 0)) =
      ∑ i, (b.repr γ i * b.repr u i + lam i * b.repr u i ^ 2 / 2) + S / 2 * negPart hsym γ := by
    rw [Finset.sum_add_distrib, hneg]
  have eR : ∑ i, (K * |b.repr γ i| * wsum η (ξ i) n + L * K ^ 2 * wsum η (ξ i) n ^ 2 / 2 +
        1188 * wsum η (ξ i) n ^ 2 / S + 15 * L * wsum η (ξ i) n ^ 2 +
        15 * S * L ^ 2 * wsum η (ξ i) n ^ 2) =
      K * ∑ i, |b.repr γ i| * wsum η (ξ i) n + L * K ^ 2 * (∑ i, wsum η (ξ i) n ^ 2) / 2 +
        1188 * (∑ i, wsum η (ξ i) n ^ 2) / S + 15 * L * (∑ i, wsum η (ξ i) n ^ 2) +
        15 * S * L ^ 2 * ∑ i, wsum η (ξ i) n ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, mul_assoc]
  rw [eL, eR] at hsum
  have hGγ : 0 ≤ Gγ := (norm_nonneg _).trans hγ
  have hεe : 0 ≤ S * (ρ * (2 * R) ^ 2) := by positivity
  have hcs : ∑ i, |b.repr γ i| * wsum η (ξ i) n ≤ Gγ * (S * (ρ * (2 * R) ^ 2)) := by
    apply cross_sum _ _ (fun i => wsum_nonneg F (ξ i) n) hGγ hεe
    · rw [← norm_sq_coord b]; exact pow_le_pow_left₀ (norm_nonneg _) hγ 2
    · rw [mul_pow]; exact hw
  have hK0 : 0 ≤ K := by linarith [F.hK]
  have hL0 : 0 ≤ L := F.hL.le
  have c0 : K * ∑ i, |b.repr γ i| * wsum η (ξ i) n ≤ K * (Gγ * (S * (ρ * (2 * R) ^ 2))) :=
    mul_le_mul_of_nonneg_left hcs hK0
  have c1 : L * K ^ 2 * (∑ i, wsum η (ξ i) n ^ 2) / 2 ≤
      L * K ^ 2 / 2 * S ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ L * K ^ 2 / 2)
    linarith
  have c2 : 1188 * (∑ i, wsum η (ξ i) n ^ 2) / S ≤ 1188 * S * (ρ * (2 * R) ^ 2) ^ 2 := by
    rw [div_le_iff₀ hS]; nlinarith
  have c3 : 15 * L * (∑ i, wsum η (ξ i) n ^ 2) ≤ 15 * L * S ^ 2 * (ρ * (2 * R) ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 15 * L)
    linarith
  have c4 : 15 * S * L ^ 2 * (∑ i, wsum η (ξ i) n ^ 2) ≤
      15 * L ^ 2 * S ^ 3 * (ρ * (2 * R) ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 15 * S * L ^ 2)
    nlinarith
  have hT : f (X n) - f y ≤ ⟪γ, u⟫ + ⟪H u, u⟫ / 2 + ρ * ‖X n - y0‖ ^ 3 + ρ * ‖y - y0‖ ^ 3 := by
    linarith
  rw [hmodel] at hT
  have : ρ * (2 * R) ^ 3 + ρ * R ^ 3 = 9 * ρ * R ^ 3 := by ring
  linarith

theorem block_exit (hf : ContDiff ℝ 2 f) (hρ : 0 ≤ ρ)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (F : ScheduleFacts η n L K) (X : ℕ → E) (y : E)
    (hX : ∀ s, X (s + 1) = X s - η s • gradient f (X s)) (hX0 : X 0 = y) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t ≤ n) (hR : ∀ s < t, ‖X s - y‖ ≤ R) {G : ℝ}
    (hG : ‖gradient f y‖ ≤ G) :
    f (X t) - f y + ‖X t - y‖ ^ 2 / (21 * ssum η n) ≤
      K * G * (ssum η n * (ρ * R ^ 2)) + 2 * ssum η n * G ^ 2 / 21 +
        (2 * K ^ 2 / 21 + 1181) * ssum η n * (ρ * R ^ 2) ^ 2 +
        (L * K ^ 2 / 2 + 16 * L) * ssum η n ^ 2 * (ρ * R ^ 2) ^ 2 + ρ * ‖X t - y‖ ^ 3 := by
  set H := fderiv ℝ (gradient f) y
  have hsym := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hf y
  set b := hsym.eigenvectorBasis rfl
  set lam := hsym.eigenvalues rfl
  have hb : ∀ v i, b.repr (H v) i = lam i * b.repr v i :=
    fun v i => hsym.eigenvectorBasis_apply_self_apply rfl v i
  have hSt := ssum_pos F ht1 htn
  have hSS := ssum_mono F htn
  set St := ssum η t
  set S := ssum η n
  have hS : 0 < S := lt_of_lt_of_le hSt hSS
  set e := fun s => gradient f (X s) - gradient f y - H (X s - y)
  have hstep : ∀ s < t, X (s + 1) = X s - η s • (gradient f y + H (X s - y) + e s) := by
    intro s _
    rw [hX s]
    congr 2
    show _ = _ + _ + (gradient f (X s) - gradient f y - H (X s - y))
    abel
  have hcoord := coord_traj H b lam hb η X y (gradient f y) e t hX0 hstep t le_rfl
  have he : ∀ s < t, ‖e s‖ ≤ ρ * R ^ 2 := fun s hs => frame_err hf hρ hH y (X s) (hR s hs)
  set u := X t - y
  have htay := (abs_le.mp (taylor_cubic hf hρ hH y (X t))).2
  have hmodel := model_coord H b lam hb (gradient f y) u
  set ξ := fun i s => b.repr (e s) i
  have hci : ∀ i, b.repr (gradient f y) i * b.repr u i + lam i * b.repr u i ^ 2 / 2 +
      b.repr u i ^ 2 / (21 * S) ≤
      K * |b.repr (gradient f y) i| * wsum η (ξ i) t + 2 * S * b.repr (gradient f y) i ^ 2 / 21 +
        (2 * K ^ 2 / 21 + 1181) * wsum η (ξ i) t ^ 2 / St +
        (L * K ^ 2 / 2 + 16 * L) * wsum η (ξ i) t ^ 2 := by
    intro i
    have hl := eig_bounds F.hL.le hlip y hsym i
    rw [hcoord i]
    exact coord_exit F ht1 htn hl.1 hl.2 (ξ i)
  have hw := wsum_sq_sum b η F.eta_nonneg e t he
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hci i
  have eL : ∑ i, (b.repr (gradient f y) i * b.repr u i + lam i * b.repr u i ^ 2 / 2 +
      b.repr u i ^ 2 / (21 * S)) =
      ∑ i, (b.repr (gradient f y) i * b.repr u i + lam i * b.repr u i ^ 2 / 2) +
        ‖u‖ ^ 2 / (21 * S) := by
    rw [Finset.sum_add_distrib, norm_sq_coord b u, Finset.sum_div]
  have eR : ∑ i, (K * |b.repr (gradient f y) i| * wsum η (ξ i) t +
        2 * S * b.repr (gradient f y) i ^ 2 / 21 +
        (2 * K ^ 2 / 21 + 1181) * wsum η (ξ i) t ^ 2 / St +
        (L * K ^ 2 / 2 + 16 * L) * wsum η (ξ i) t ^ 2) =
      K * ∑ i, |b.repr (gradient f y) i| * wsum η (ξ i) t +
        2 * S * (∑ i, b.repr (gradient f y) i ^ 2) / 21 +
        (2 * K ^ 2 / 21 + 1181) * (∑ i, wsum η (ξ i) t ^ 2) / St +
        (L * K ^ 2 / 2 + 16 * L) * ∑ i, wsum η (ξ i) t ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum, mul_assoc]
  rw [eL, eR, ← norm_sq_coord b] at hsum
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hεe : 0 ≤ St * (ρ * R ^ 2) := by positivity
  have hcs : ∑ i, |b.repr (gradient f y) i| * wsum η (ξ i) t ≤ G * (St * (ρ * R ^ 2)) := by
    apply cross_sum _ _ (fun i => wsum_nonneg F (ξ i) t) hG0 hεe
    · rw [← norm_sq_coord b]; exact pow_le_pow_left₀ (norm_nonneg _) hG 2
    · rw [mul_pow]; exact hw
  have hK0 : 0 ≤ K := by linarith [F.hK]
  have hL0 : 0 ≤ L := F.hL.le
  have hρR : 0 ≤ ρ * R ^ 2 := by positivity
  have c0 : K * ∑ i, |b.repr (gradient f y) i| * wsum η (ξ i) t ≤
      K * G * (S * (ρ * R ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hcs hK0
    have h2 : G * (St * (ρ * R ^ 2)) ≤ G * (S * (ρ * R ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSS hρR) hG0
    have := mul_le_mul_of_nonneg_left h2 hK0
    linarith
  have c1 : 2 * S * ‖gradient f y‖ ^ 2 / 21 ≤ 2 * S * G ^ 2 / 21 := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hG 2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * S)
    linarith
  have hE0 : 0 ≤ (ρ * R ^ 2) ^ 2 := sq_nonneg _
  have hSt2 : St ^ 2 ≤ S * St := by rw [sq]; exact mul_le_mul_of_nonneg_right hSS hSt.le
  have hSS2 : S * St ≤ S ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_left hSS hS.le
  have hw' : ∑ i, wsum η (ξ i) t ^ 2 ≤ S * St * (ρ * R ^ 2) ^ 2 :=
    hw.trans (mul_le_mul_of_nonneg_right hSt2 hE0)
  have hw'' : ∑ i, wsum η (ξ i) t ^ 2 ≤ S ^ 2 * (ρ * R ^ 2) ^ 2 :=
    hw'.trans (mul_le_mul_of_nonneg_right hSS2 hE0)
  have hA0 : 0 ≤ 2 * K ^ 2 / 21 + 1181 := by positivity
  have c2 : (2 * K ^ 2 / 21 + 1181) * (∑ i, wsum η (ξ i) t ^ 2) / St ≤
      (2 * K ^ 2 / 21 + 1181) * S * (ρ * R ^ 2) ^ 2 := by
    rw [div_le_iff₀ hSt]
    calc (2 * K ^ 2 / 21 + 1181) * (∑ i, wsum η (ξ i) t ^ 2)
        ≤ (2 * K ^ 2 / 21 + 1181) * (S * St * (ρ * R ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hw' hA0
      _ = (2 * K ^ 2 / 21 + 1181) * S * (ρ * R ^ 2) ^ 2 * St := by ring
  have c3 : (L * K ^ 2 / 2 + 16 * L) * ∑ i, wsum η (ξ i) t ^ 2 ≤
      (L * K ^ 2 / 2 + 16 * L) * S ^ 2 * (ρ * R ^ 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hw'' (by positivity : 0 ≤ L * K ^ 2 / 2 + 16 * L)
    linarith
  have hT : f (X t) - f y ≤ ⟪gradient f y, u⟫ + ⟪H u, u⟫ / 2 + ρ * ‖u‖ ^ 3 := by linarith
  rw [hmodel] at hT
  linarith

end OracleTemplate.ScheduleBlock
