import LongTails.Proofs.FractalChebyshevExchange
import LongTails.Proofs.FractalChebyshevTree

namespace OracleTemplate.FractalChebyshev

open Real

lemma cos_two_mul_sq (x : ℝ) : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
  rw [Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq x]

lemma exchange_poly {C S' su sw cu cw n d D : ℝ} (_hC : C + S' = 1) (_hu : su + cu = 1)
    (_hw : sw + cw = 1) (hcw : 0 ≤ cw) (hsu : 0 ≤ su) (hd : 0 ≤ d) (hD : n ^ 2 * d ≤ D)
    (hlin : C * cu - S' * cw ≤ n ^ 2 * (cw * su)) (hconst : C * cu * sw ≤ S' * cw * su) :
    (2 * C) * (2 * cu) * (d + 2 * sw) ≤ (2 * cw) * ((D + 2 * S') * (d + 2 * su)) := by
  have h1 : (2 * cw) * ((n ^ 2 * d + 2 * S') * (d + 2 * su)) ≤
      (2 * cw) * ((D + 2 * S') * (d + 2 * su)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    linarith
  have hq : 0 ≤ n ^ 2 * cw * d ^ 2 := by positivity
  have hl : 0 ≤ (n ^ 2 * (cw * su) - (C * cu - S' * cw)) * d := mul_nonneg (by linarith) hd
  have e : (2 * cw) * ((n ^ 2 * d + 2 * S') * (d + 2 * su)) - (2 * C) * (2 * cu) * (d + 2 * sw)
      = 2 * (n ^ 2 * cw * d ^ 2) + 4 * ((n ^ 2 * (cw * su) - (C * cu - S' * cw)) * d) +
        8 * (S' * cw * su - C * cu * sw) := by ring
  nlinarith

lemma exchange_lin {C S' su sw cu cw n cα : ℝ} (hC : C - S' = cα) (hu : su + cu = 1)
    (hw : sw + cw = 1) (hS' : 0 ≤ S') (hcα : 0 ≤ cα) (hcu : 0 ≤ cu) (hsw : 0 ≤ sw)
    (hswu : sw ≤ su) (hI : cα ≤ n ^ 2 * (su - sw)) :
    C * cu - S' * cw ≤ n ^ 2 * (cw * su) := by
  have e : C * cu - S' * cw = cα * cu - S' * (su - sw) := by
    have : cu = 1 - su := by linarith
    have : cw = 1 - sw := by linarith
    subst_vars; nlinarith
  have h3 : cα * cu ≤ cα := by
    have : cu ≤ 1 := by linarith
    exact mul_le_of_le_one_right hcα this
  have h4 : 0 ≤ S' * (su - sw) := mul_nonneg hS' (by linarith)
  have h5 : su - sw ≤ cw * su := by
    have : cw = 1 - sw := by linarith
    rw [this]
    have : su ≤ 1 := by linarith
    nlinarith
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have := mul_le_mul_of_nonneg_left h5 hn2
  linarith

theorem exchange_core {α n d D : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hn : 2 ≤ n)
    (hd : 0 ≤ d) (hD : n ^ 2 * d ≤ D) :
    bad (1 + D) α * bad (1 + d) ((π - α) / n) ≤ bad (1 + d) (α / n) := by
  have hpi := Real.pi_pos
  have hnpos : 0 < n := by linarith
  have hI := ineq_I hα hα' hn
  have hII := ineq_II hα hα' hn
  obtain ⟨A, hA⟩ : ∃ A, A = α / 2 := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = (π - α) / (2 * n) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = α / (2 * n) := ⟨_, rfl⟩
  rw [← hu, ← hw] at hI hII
  rw [← hA] at hII
  have e1 : α = 2 * A := by rw [hA]; ring
  have e2 : (π - α) / n = 2 * u := by rw [hu]; field_simp
  have e3 : α / n = 2 * w := by rw [hw]; field_simp
  have hw0 : 0 < w := by rw [hw]; positivity
  have hwu : w ≤ u := by
    rw [hu, hw]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hu2 : u ≤ π / 2 := by
    rw [hu, div_le_iff₀ (by positivity)]; nlinarith
  have hA0 : 0 < A := by rw [hA]; positivity
  have hA1 : A < π / 4 := by rw [hA]; linarith
  have hsw0 : 0 < sin w := Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith)
  have hw1 : w < π / 2 := by
    rw [hw, div_lt_iff₀ (by positivity)]; nlinarith
  have hcw0 : 0 < cos w := Real.cos_pos_of_mem_Ioo ⟨by linarith, hw1⟩
  have hswu : sin w ≤ sin u := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hu2 hwu
  have hcu0 : 0 ≤ cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hu2⟩
  have hsA0 : 0 < sin A := Real.sin_pos_of_pos_of_lt_pi hA0 (by linarith)
  have hcA0 : 0 < cos A := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcosα : 0 ≤ cos α := Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hII2 : (sin w * cos A * cos u) ^ 2 ≤ (sin A * sin u * cos w) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hII 2
  have hcA : cos α = cos A ^ 2 - sin A ^ 2 := by
    rw [e1, Real.cos_two_mul]; nlinarith [Real.sin_sq_add_cos_sq A]
  have hcu : cos ((π - α) / n) = 1 - 2 * sin u ^ 2 := by rw [e2, cos_two_mul_sq]
  have hcw : cos (α / n) = 1 - 2 * sin w ^ 2 := by rw [e3, cos_two_mul_sq]
  have hsuw : sin w ^ 2 ≤ sin u ^ 2 := pow_le_pow_left₀ hsw0.le hswu 2
  have hpoly := exchange_poly (C := cos A ^ 2) (S' := sin A ^ 2) (su := sin u ^ 2)
    (sw := sin w ^ 2) (cu := cos u ^ 2) (cw := cos w ^ 2) (n := n) (d := d) (D := D)
    (by nlinarith [Real.sin_sq_add_cos_sq A]) (Real.sin_sq_add_cos_sq u)
    (Real.sin_sq_add_cos_sq w) (sq_nonneg _) (sq_nonneg _) hd hD
    (exchange_lin hcA.symm (Real.sin_sq_add_cos_sq u) (Real.sin_sq_add_cos_sq w)
      (sq_nonneg _) hcosα (sq_nonneg _) (sq_nonneg _) hsuw hI)
    (by
      have q1 : (sin w * cos A * cos u) ^ 2 = cos A ^ 2 * cos u ^ 2 * sin w ^ 2 := by ring
      have q2 : (sin A * sin u * cos w) ^ 2 = sin A ^ 2 * cos w ^ 2 * sin u ^ 2 := by ring
      rw [q1, q2] at hII2; exact hII2)
  have hsA2 : 0 < sin A ^ 2 := by positivity
  have hsu2 : 0 < sin u ^ 2 := by have := lt_of_lt_of_le hsw0 hswu; positivity
  have hsw2 : 0 < sin w ^ 2 := by positivity
  have hnd : 0 ≤ n ^ 2 * d := by positivity
  have hden1 : 0 < 1 + D - cos α := by
    have := Real.sin_sq_add_cos_sq A
    linarith
  have hden2 : 0 < 1 + d - cos ((π - α) / n) := by rw [hcu]; linarith
  have hden3 : 0 < 1 + d - cos (α / n) := by rw [hcw]; linarith
  unfold bad
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hden1 hden2) hden3, hcA, hcu, hcw]
  have hsA := Real.sin_sq_add_cos_sq A
  have hsu' := Real.sin_sq_add_cos_sq u
  have hsw' := Real.sin_sq_add_cos_sq w
  have g1 : 1 + (cos A ^ 2 - sin A ^ 2) = 2 * cos A ^ 2 := by linarith
  have g2 : 1 + (1 - 2 * sin u ^ 2) = 2 * cos u ^ 2 := by linarith
  have g3 : 1 + d - (1 - 2 * sin w ^ 2) = d + 2 * sin w ^ 2 := by ring
  have g4 : 1 + (1 - 2 * sin w ^ 2) = 2 * cos w ^ 2 := by linarith
  have g5 : 1 + D - (cos A ^ 2 - sin A ^ 2) = D + 2 * sin A ^ 2 := by linarith
  have g6 : 1 + d - (1 - 2 * sin u ^ 2) = d + 2 * sin u ^ 2 := by ring
  rw [g1, g2, g3, g4, g5, g6]
  exact hpoly

lemma bad_mono_cos {X c c' : ℝ} (hX : 1 < X) (hcc : c ≤ c') (hc' : c' ≤ 1) :
    (1 + c) / (X - c) ≤ (1 + c') / (X - c') := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

lemma dbl_iterate_ge {X : ℝ} (hX : 1 ≤ X) (j : ℕ) : 1 + 4 ^ j * (X - 1) ≤ dbl^[j] X := by
  induction j generalizing X with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have h1 : 1 ≤ dbl X := by unfold dbl; nlinarith
    have h2 := ih h1
    have h3 : 1 + 4 * (X - 1) ≤ dbl X := by unfold dbl; nlinarith
    have h4 : (0:ℝ) ≤ 4 ^ j := by positivity
    calc 1 + 4 ^ (j + 1) * (X - 1) = 1 + 4 ^ j * (4 * (X - 1)) := by ring
      _ ≤ 1 + 4 ^ j * (dbl X - 1) := by nlinarith
      _ ≤ dbl^[j] (dbl X) := h2

lemma le_dbl_iterate {X : ℝ} (hX : 1 ≤ X) (j : ℕ) : X ≤ dbl^[j] X := by
  have h1 := dbl_iterate_ge hX j
  have h2 : (1:ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have h3 : X - 1 ≤ 4 ^ j * (X - 1) := le_mul_of_one_le_left (by linarith) h2
  linarith

theorem exchange_max {α n X Y : ℝ} (hα : 0 < α) (hα' : α < π / 2) (hn : 2 ≤ n)
    (hX : 1 < X) (hY : 1 + n ^ 2 * (X - 1) ≤ Y) :
    max 1 (bad X ((π - α) / n)) * max 1 (bad Y α) ≤ max 1 (bad X (α / n)) := by
  have hpi := Real.pi_pos
  have hnpos : 0 < n := by linarith
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hXY : X ≤ Y := by
    have : X - 1 ≤ n ^ 2 * (X - 1) := le_mul_of_one_le_left (by linarith) hn2
    linarith
  have hY1 : 1 < Y := by linarith
  have ha1 : α / n ≤ (π - α) / n := div_le_div_of_nonneg_right (by linarith) hnpos.le
  have ha2 : (π - α) / n ≤ π := by
    rw [div_le_iff₀ hnpos]; nlinarith
  have ha3 : α / n ≤ α := div_le_self hα.le (by linarith)
  have hc1 : cos ((π - α) / n) ≤ cos (α / n) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ha2 ha1
  have hc2 : cos α ≤ cos (α / n) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) ha3
  have hb1 : bad X ((π - α) / n) ≤ bad X (α / n) :=
    bad_mono_cos hX hc1 (Real.cos_le_one _)
  have hb2 : bad Y α ≤ bad X (α / n) := by
    unfold bad
    have hca : cos (α / n) ≤ 1 := Real.cos_le_one _
    have hca' : cos α ≤ 1 := Real.cos_le_one _
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h1 : 0 ≤ 1 + cos α := by linarith [Real.neg_one_le_cos α]
    nlinarith [Real.neg_one_le_cos α]
  by_cases h1 : 1 ≤ bad X ((π - α) / n)
  · by_cases h2 : 1 ≤ bad Y α
    · rw [max_eq_right h1, max_eq_right h2]
      have hcore := exchange_core (d := X - 1) (D := Y - 1) hα hα' hn (by linarith)
        (by linarith)
      rw [show 1 + (Y - 1) = Y by ring, show 1 + (X - 1) = X by ring] at hcore
      rw [mul_comm]; exact hcore.trans (le_max_right _ _)
    · push Not at h2
      rw [max_eq_right h1, max_eq_left h2.le, mul_one]
      exact hb1.trans (le_max_right _ _)
  · push Not at h1
    rw [max_eq_left h1.le, one_mul]
    exact max_le_max le_rfl hb2

end OracleTemplate.FractalChebyshev
