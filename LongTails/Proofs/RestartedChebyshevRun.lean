import LongTails.Proofs.GdConvex
import LongTails.Setups.HessianLipschitzGradientStationarity

namespace OracleTemplate.RestartedScheduleGD

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def stepS (f : E → ℝ) (L ε G1 R : ℝ) (steps : List ℝ) (x0 : E) (s : State E) :
    State E :=
  (algorithm L ε G1 R steps x0).update s (gradient f s.point)

noncomputable def gdTraj (f : E → ℝ) (η : ℕ → ℝ) (y : E) : ℕ → E
  | 0 => y
  | j + 1 => gdTraj f η y j - η j • gradient f (gdTraj f η y j)

variable {f : E → ℝ} {L ε G1 R : ℝ} {steps : List ℝ} {x0 : E}

lemma stepS_stop (s : State E) (h : s.done = true ∨ ‖gradient f s.point‖ ≤ ε) :
    (stepS f L ε G1 R steps x0 s).point = s.point ∧ (stepS f L ε G1 R steps x0 s).done = true := by
  unfold stepS algorithm
  simp only
  rw [ite_eq_left h]
  exact ⟨rfl, rfl⟩

lemma stepS_plain (x c : E) (hg : ε < ‖gradient f x‖) (hG : G1 < ‖gradient f x‖) :
    stepS f L ε G1 R steps x0 ⟨x, c, 0, false⟩ = ⟨x - L⁻¹ • gradient f x, c, 0, false⟩ := by
  unfold stepS algorithm
  simp only
  rw [ite_eq_right (by simp only [Bool.false_eq_true, false_or, not_le]; exact hg),
    ite_eq_left (by simp [hG])]

lemma stepS_block (x c : E) (i : ℕ) (hg : ε < ‖gradient f x‖)
    (hb : ¬(i = 0 ∧ G1 < ‖gradient f x‖)) :
    stepS f L ε G1 R steps x0 ⟨x, c, i, false⟩ =
      ⟨x - steps.getD i 0 • gradient f x, if i = 0 then x else c,
        if i + 1 < steps.length ∧
            ‖x - steps.getD i 0 • gradient f x - (if i = 0 then x else c)‖ ≤ R
          then i + 1 else 0, false⟩ := by
  unfold stepS algorithm
  simp only
  rw [ite_eq_right (by simp only [Bool.false_eq_true, false_or, not_le]; exact hg), ite_eq_right hb]

lemma iterate_stop (s : State E) (h : s.done = true ∨ ‖gradient f s.point‖ ≤ ε) :
    ∀ j, ((stepS f L ε G1 R steps x0)^[j] s).point = s.point := by
  intro j
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2⟩ := stepS_stop (f := f) (L := L) (G1 := G1) (R := R) (steps := steps)
      (x0 := x0) s h
    rw [ih _ (Or.inl h2), h1]

section Block

variable (hR0 : 0 ≤ R) {n : ℕ} (hlen : steps.length = n) (hn : 1 ≤ n)

include hn in
lemma exists_exit (y : E) :
    ∃ j, 1 ≤ j ∧ (n ≤ j ∨ R < ‖gdTraj f (fun j => steps.getD j 0) y j - y‖) :=
  ⟨n, hn, Or.inl le_rfl⟩

include hlen in
theorem block_states (y c : E) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ)
    (hspec : n ≤ ℓ ∨ R < ‖gdTraj f (fun j => steps.getD j 0) y ℓ - y‖)
    (hmin : ∀ j, 1 ≤ j → j < ℓ → j < n ∧ ‖gdTraj f (fun j => steps.getD j 0) y j - y‖ ≤ R)
    (hG : ‖gradient f y‖ ≤ G1)
    (hg : ∀ j < ℓ, ε < ‖gradient f ((stepS f L ε G1 R steps x0)^[j] ⟨y, c, 0, false⟩).point‖) :
    ∀ j, 1 ≤ j → j ≤ ℓ →
      (stepS f L ε G1 R steps x0)^[j] ⟨y, c, 0, false⟩ =
        ⟨gdTraj f (fun j => steps.getD j 0) y j, y, if j < ℓ then j else 0, false⟩ := by
  set X := gdTraj f (fun j => steps.getD j 0) y
  have hnext : ∀ j, 1 ≤ j → j ≤ ℓ →
      (if j < steps.length ∧ ‖X j - y‖ ≤ R then j else 0) = (if j < ℓ then j else 0) := by
    intro j hj1 hjℓ
    rw [hlen]
    by_cases h1 : j < ℓ
    · obtain ⟨a1, a2⟩ := hmin j hj1 h1
      rw [ite_eq_left ⟨a1, a2⟩, ite_eq_left h1]
    · have hl : j = ℓ := by omega
      subst hl
      rw [ite_eq_right h1, ite_eq_right]
      rintro ⟨h1', h2'⟩
      rcases hspec with h | h
      · omega
      · linarith
  intro j hj1 hjℓ
  induction j, hj1 using Nat.le_induction with
  | base =>
    rw [Function.iterate_one]
    have hg0 := hg 0 hℓ1
    simp only [Function.iterate_zero, id_eq] at hg0
    rw [stepS_block y c 0 hg0 (by intro h; linarith [h.2])]
    have hX1 : y - steps.getD 0 0 • gradient f y = X 1 := rfl
    simp only [↓reduceIte, zero_add]
    rw [hX1, hnext 1 le_rfl hjℓ]
  | succ j hj1 ih =>
    have ihj := ih (by omega)
    rw [Function.iterate_succ_apply', ihj]
    have hjℓ' : j < ℓ := by omega
    have hgj := hg j hjℓ'
    rw [ihj] at hgj
    simp only [ite_eq_left hjℓ'] at hgj ⊢
    rw [stepS_block (X j) y j hgj (by intro h; omega)]
    have hj0 : j ≠ 0 := by omega
    have hXs : X j - steps.getD j 0 • gradient f (X j) = X (j + 1) := rfl
    simp only [hj0, ↓reduceIte]
    rw [hXs, hnext (j + 1) (by omega) hjℓ]

include hR0 in
lemma block_inside (y : E) (ℓ : ℕ)
    (hmin : ∀ j, 1 ≤ j → j < ℓ → j < n ∧ ‖gdTraj f (fun j => steps.getD j 0) y j - y‖ ≤ R) :
    ∀ j < ℓ, ‖gdTraj f (fun j => steps.getD j 0) y j - y‖ ≤ R := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp [gdTraj, hR0]
  · exact (hmin j hpos hj).2

end Block

lemma plain_descent (hf : ContDiff ℝ 2 f) (hL : 0 < L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x : E) :
    f (x - L⁻¹ • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
  have hg : ∀ z, HasGradientAt f (gradient f z) z := fun z =>
    ((hf.differentiable (by norm_num)) z).hasGradientAt
  have h := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (x - L⁻¹ • gradient f x)
  have e1 : x - L⁻¹ • gradient f x - x = -(L⁻¹ • gradient f x) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul,
    real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h
  have : L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 = ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
  have : L⁻¹ * ‖gradient f x‖ ^ 2 = ‖gradient f x‖ ^ 2 / L := by field_simp
  have : ‖gradient f x‖ ^ 2 / L = 2 * (‖gradient f x‖ ^ 2 / (2 * L)) := by field_simp
  linarith

end OracleTemplate.RestartedScheduleGD
