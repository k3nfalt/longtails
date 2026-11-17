import LongTails.Proofs.FiniteSumNondualLowerComponents
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MintyChainGeometry

open FiniteSumNondualLowerComponents

def clip (r t : ℝ) : ℝ := max (-r) (min r t)

noncomputable def ramp (κ r t : ℝ) : ℝ := κ * max 0 (min 1 (4 * t / r - 1))

lemma clip_abs_le (r t : ℝ) (hr : 0 ≤ r) : |clip r t| ≤ r := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clip_lipschitz (r s t : ℝ) : |clip r s - clip r t| ≤ |s - t| := by
  unfold clip
  have h1 := abs_max_sub_max_le_max (-r) (min r s) (-r) (min r t)
  have h2 := abs_min_sub_min_le_max r s r t
  simp only [sub_self, abs_zero] at h1 h2
  have h3 : max 0 |min r s - min r t| = |min r s - min r t| := max_eq_right (abs_nonneg _)
  have h4 : max 0 |s - t| = |s - t| := max_eq_right (abs_nonneg _)
  rw [h3] at h1
  rw [h4] at h2
  exact h1.trans h2

lemma clip_nonneg_of_nonneg (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) : 0 ≤ clip r t := by
  unfold clip
  exact le_max_of_le_right (le_min hr ht)

lemma clip_nonpos_of_nonpos (r t : ℝ) (hr : 0 ≤ r) (ht : t ≤ 0) : clip r t ≤ 0 := by
  unfold clip
  exact max_le (by linarith) ((min_le_right _ _).trans ht)

lemma clip_sq_le_mul (r t : ℝ) (hr : 0 ≤ r) : clip r t ^ 2 ≤ clip r t * t := by
  unfold clip
  rcases le_total t (-r) with h | h
  · have hm : min r t = t := min_eq_right (by linarith)
    rw [hm, max_eq_left h]
    nlinarith
  · rcases le_total t r with h' | h'
    · rw [min_eq_right h', max_eq_right h]
      nlinarith
    · rw [min_eq_left h', max_eq_right (by linarith)]
      nlinarith

lemma clip_abs_ge (r t : ℝ) (hr : 0 ≤ r) (ht : r / 2 ≤ |t|) : r / 2 ≤ |clip r t| := by
  unfold clip
  rcases le_total t (-r) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h, abs_neg, abs_of_nonneg hr]
    linarith
  · rcases le_total t r with h' | h'
    · rw [min_eq_right h', max_eq_right h]
      exact ht
    · rw [min_eq_left h', max_eq_right (by linarith), abs_of_nonneg hr]
      linarith

lemma ramp_nonneg (κ r t : ℝ) (hκ : 0 ≤ κ) : 0 ≤ ramp κ r t :=
  mul_nonneg hκ (le_max_left _ _)

lemma ramp_le (κ r t : ℝ) (hκ : 0 ≤ κ) : ramp κ r t ≤ κ := by
  unfold ramp
  have h : max 0 (min 1 (4 * t / r - 1)) ≤ 1 := max_le zero_le_one (min_le_left _ _)
  nlinarith [le_max_left 0 (min 1 (4 * t / r - 1))]

lemma ramp_of_le (κ r t : ℝ) (hr : 0 < r) (ht : t ≤ r / 4) : ramp κ r t = 0 := by
  unfold ramp
  have h : 4 * t / r - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hr]
    linarith
  rw [max_eq_left ((min_le_right _ _).trans h), mul_zero]

lemma ramp_of_ge (κ r t : ℝ) (hr : 0 < r) (ht : r / 2 ≤ t) : ramp κ r t = κ := by
  unfold ramp
  have h : 1 ≤ 4 * t / r - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hr]
    linarith
  rw [min_eq_left h, max_eq_right zero_le_one, mul_one]

lemma clamp_lipschitz (s t : ℝ) :
    |max 0 (min 1 s) - max 0 (min 1 t)| ≤ |s - t| := by
  have h1 := abs_max_sub_max_le_max 0 (min 1 s) 0 (min 1 t)
  have h2 := abs_min_sub_min_le_max 1 s 1 t
  simp only [sub_self, abs_zero] at h1 h2
  have h3 : max 0 |min 1 s - min 1 t| = |min 1 s - min 1 t| := max_eq_right (abs_nonneg _)
  have h4 : max 0 |s - t| = |s - t| := max_eq_right (abs_nonneg _)
  rw [h3] at h1
  rw [h4] at h2
  exact h1.trans h2

lemma ramp_lipschitz (κ r s t : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) :
    |ramp κ r s - ramp κ r t| ≤ 4 * κ / r * |s - t| := by
  unfold ramp
  have h3 : |4 * s / r - 1 - (4 * t / r - 1)| = 4 / r * |s - t| := by
    rw [show 4 * s / r - 1 - (4 * t / r - 1) = 4 / r * (s - t) by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 / r)]
  rw [← mul_sub, abs_mul, abs_of_nonneg hκ]
  calc
    κ * |max 0 (min 1 (4 * s / r - 1)) - max 0 (min 1 (4 * t / r - 1))|
        ≤ κ * (4 / r * |s - t|) := by
      apply mul_le_mul_of_nonneg_left _ hκ
      rw [← h3]
      exact clamp_lipschitz _ _
    _ = 4 * κ / r * |s - t| := by ring

lemma clip_term_lower (κ a r s t : ℝ) (ha : 0 ≤ a) (haκ : a ≤ κ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    -(κ * t ^ 2 * r ^ 2 / 4) ≤ a * clip r (s - r) * ((s - r) + t * s) := by
  have hc := clip_sq_le_mul r (s - r) hr
  rcases le_total r s with h | h
  · have hc0 : 0 ≤ clip r (s - r) := clip_nonneg_of_nonneg r (s - r) hr (by linarith)
    have hk : 0 ≤ κ := ha.trans haκ
    have hs : 0 ≤ (s - r) + t * s := by nlinarith
    have : 0 ≤ a * clip r (s - r) * ((s - r) + t * s) := by positivity
    have : 0 ≤ κ * t ^ 2 * r ^ 2 / 4 := by positivity
    linarith
  · set c := clip r (s - r)
    have hc0 : c ≤ 0 := clip_nonpos_of_nonpos r (s - r) hr (by linarith)
    have hcr : -r ≤ c := by
      have := clip_abs_le r (s - r) hr
      rw [abs_le] at this
      exact this.1
    have hq : -(t ^ 2 * r ^ 2 / 4) ≤ c * ((s - r) + t * s) := by
      have e : c * ((s - r) + t * s) = (1 + t) * (c * (s - r)) + t * r * c := by ring
      rw [e]
      nlinarith [sq_nonneg (c + t * r / 2), mul_nonneg ht (sq_nonneg c)]
    have hneg : -(t ^ 2 * r ^ 2 / 4) ≤ 0 := by
      have : 0 ≤ t ^ 2 * r ^ 2 / 4 := by positivity
      linarith
    calc
      -(κ * t ^ 2 * r ^ 2 / 4) = κ * (-(t ^ 2 * r ^ 2 / 4)) := by ring
      _ ≤ a * (-(t ^ 2 * r ^ 2 / 4)) := by nlinarith
      _ ≤ a * (c * ((s - r) + t * s)) := mul_le_mul_of_nonneg_left hq ha
      _ = a * c * ((s - r) + t * s) := by ring

variable {d k : ℕ}

noncomputable def lift (π : Fin (k + 1) ↪ Fin d) (c : Fin (k + 1) → ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ∑ j, if π j = i then c j else 0)

lemma lift_apply (π : Fin (k + 1) ↪ Fin d) (c : Fin (k + 1) → ℝ) (j : Fin (k + 1)) :
    lift π c (π j) = c j := by
  change (∑ j', if π j' = π j then c j' else 0) = c j
  simp [π.injective.eq_iff]

lemma inner_lift (π : Fin (k + 1) ↪ Fin d) (c : Fin (k + 1) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) : ⟪lift π c, w⟫ = ∑ j, c j * w (π j) := by
  have h : ⟪lift π c, w⟫ = ∑ i, lift π c i * w i := by
    rw [PiLp.inner_apply]
    simp [mul_comm]
  rw [h]
  change (∑ i, (∑ j, if π j = i then c j else 0) * w i) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma norm_lift_sq (π : Fin (k + 1) ↪ Fin d) (c : Fin (k + 1) → ℝ) :
    ‖lift π c‖ ^ 2 = ∑ j, c j ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_lift]
  simp [lift_apply, sq]

lemma lift_sub (π : Fin (k + 1) ↪ Fin d) (c e : Fin (k + 1) → ℝ) :
    lift π c - lift π e = lift π (fun j => c j - e j) := by
  ext i
  change (∑ j, if π j = i then c j else 0) - (∑ j, if π j = i then e j else 0) =
    ∑ j, if π j = i then c j - e j else 0
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma lift_congr (π ρ : Fin (k + 1) ↪ Fin d) (c : Fin (k + 1) → ℝ) (t : ℕ)
    (hc : ∀ j : Fin (k + 1), t < j.val → c j = 0)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) : lift π c = lift ρ c := by
  ext i
  change (∑ j, if π j = i then c j else 0) = ∑ j, if ρ j = i then c j else 0
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val ≤ t
  · rw [h j hj]
  · rw [hc j (by omega)]
    simp

noncomputable def act (κ r : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    Fin (k + 1) → ℝ :=
  Fin.cases κ (fun i => ramp κ r (u (π i.castSucc)))

noncomputable def coef (κ r : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d))
    (j : Fin (k + 1)) : ℝ :=
  act κ r π u j * clip r (u (π j) - r)

noncomputable def chain (κ r : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  lift π (coef κ r π u)

lemma act_nonneg (κ r : ℝ) (hκ : 0 ≤ κ) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) : 0 ≤ act κ r π u j := by
  cases j using Fin.cases with
  | zero => exact hκ
  | succ i => exact ramp_nonneg κ r _ hκ

lemma act_le (κ r : ℝ) (hκ : 0 ≤ κ) (π : Fin (k + 1) ↪ Fin d)
    (u : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) : act κ r π u j ≤ κ := by
  cases j using Fin.cases with
  | zero => exact le_rfl
  | succ i => exact ramp_le κ r _ hκ


lemma coordinate_sq_sum (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    ∑ j, u (π j) ^ 2 ≤ ‖u‖ ^ 2 := by
  have h := coordinateMap_norm π u
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [EuclideanSpace.real_norm_sq_eq] at h2
  exact h2

lemma act_diff (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (u v : EuclideanSpace ℝ (Fin d)) (i : Fin k) :
    |act κ r π u i.succ - act κ r π v i.succ| ≤
      4 * κ / r * |u (π i.castSucc) - v (π i.castSucc)| := by
  simp only [act, Fin.cases_succ]
  exact ramp_lipschitz κ r _ _ hκ hr

lemma coef_diff (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (u v : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) :
    |coef κ r π u j - coef κ r π v j| ≤
      |act κ r π u j - act κ r π v j| * r + κ * |u (π j) - v (π j)| := by
  unfold coef
  have e : act κ r π u j * clip r (u (π j) - r) - act κ r π v j * clip r (v (π j) - r) =
      (act κ r π u j - act κ r π v j) * clip r (u (π j) - r) +
        act κ r π v j * (clip r (u (π j) - r) - clip r (v (π j) - r)) := by ring
  rw [e]
  have h1 : |(act κ r π u j - act κ r π v j) * clip r (u (π j) - r)| ≤
      |act κ r π u j - act κ r π v j| * r := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (clip_abs_le r _ hr.le) (abs_nonneg _)
  have h2 : |act κ r π v j * (clip r (u (π j) - r) - clip r (v (π j) - r))| ≤
      κ * |u (π j) - v (π j)| := by
    rw [abs_mul, abs_of_nonneg (act_nonneg κ r hκ π v j)]
    have hc := clip_lipschitz r (u (π j) - r) (v (π j) - r)
    rw [show u (π j) - r - (v (π j) - r) = u (π j) - v (π j) by ring] at hc
    exact mul_le_mul (act_le κ r hκ π v j) hc (abs_nonneg _) hκ
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

lemma coef_sq_sum (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (u v : EuclideanSpace ℝ (Fin d)) :
    ∑ j, (coef κ r π u j - coef κ r π v j) ^ 2 ≤ 25 * κ ^ 2 * ‖u - v‖ ^ 2 := by
  let w := u - v
  have hw : ∀ i, u i - v i = w i := fun i => rfl
  have hzero : (coef κ r π u 0 - coef κ r π v 0) ^ 2 ≤ κ ^ 2 * w (π 0) ^ 2 := by
    have h := coef_diff κ r hκ hr π u v 0
    simp only [act, Fin.cases_zero, sub_self, abs_zero, zero_mul, zero_add, hw] at h
    have h' := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs, mul_pow, sq_abs] at h'
    exact h'
  have hsucc (i : Fin k) : (coef κ r π u i.succ - coef κ r π v i.succ) ^ 2 ≤
      20 * κ ^ 2 * w (π i.castSucc) ^ 2 + 5 * κ ^ 2 * w (π i.succ) ^ 2 := by
    have h := coef_diff κ r hκ hr π u v i.succ
    have ha := act_diff κ r hκ hr π u v i
    have hb : |act κ r π u i.succ - act κ r π v i.succ| * r ≤
        4 * κ * |w (π i.castSucc)| := by
      rw [← hw]
      calc
        _ ≤ 4 * κ / r * |u (π i.castSucc) - v (π i.castSucc)| * r :=
          mul_le_mul_of_nonneg_right ha hr.le
        _ = 4 * κ * |u (π i.castSucc) - v (π i.castSucc)| := by field_simp
    rw [hw] at h
    have hc := h.trans (add_le_add hb le_rfl)
    have hpos : 0 ≤ 4 * κ * |w (π i.castSucc)| + κ * |w (π i.succ)| := by positivity
    have h2 := pow_le_pow_left₀ (abs_nonneg _) hc 2
    rw [sq_abs] at h2
    have hsq : (4 * κ * |w (π i.castSucc)| + κ * |w (π i.succ)|) ^ 2 ≤
        20 * κ ^ 2 * w (π i.castSucc) ^ 2 + 5 * κ ^ 2 * w (π i.succ) ^ 2 := by
      have e1 : |w (π i.castSucc)| ^ 2 = w (π i.castSucc) ^ 2 := sq_abs _
      have e2 : |w (π i.succ)| ^ 2 = w (π i.succ) ^ 2 := sq_abs _
      nlinarith [mul_nonneg (sq_nonneg κ) (sq_nonneg (|w (π i.castSucc)| - |w (π i.succ)|))]
    exact h2.trans hsq
  rw [Fin.sum_univ_succ]
  have hs1 : ∑ i : Fin k, (coef κ r π u i.succ - coef κ r π v i.succ) ^ 2 ≤
      ∑ i : Fin k, (20 * κ ^ 2 * w (π i.castSucc) ^ 2 + 5 * κ ^ 2 * w (π i.succ) ^ 2) :=
    Finset.sum_le_sum (fun i _ => hsucc i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs1
  have hcast : ∑ i : Fin k, w (π i.castSucc) ^ 2 ≤ ∑ j, w (π j) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    linarith [sq_nonneg (w (π (Fin.last k)))]
  have hsuc : w (π 0) ^ 2 + ∑ i : Fin k, w (π i.succ) ^ 2 = ∑ j, w (π j) ^ 2 :=
    (Fin.sum_univ_succ (fun j => w (π j) ^ 2)).symm
  have hall := coordinate_sq_sum π w
  have hk2 : 0 ≤ κ ^ 2 := sq_nonneg κ
  nlinarith [mul_le_mul_of_nonneg_left hcast hk2, sq_nonneg (w (π 0))]

lemma chain_lipschitz (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (u v : EuclideanSpace ℝ (Fin d)) :
    ‖chain κ r π u - chain κ r π v‖ ≤ 5 * κ * ‖u - v‖ := by
  unfold chain
  rw [lift_sub]
  have h := norm_lift_sq π (fun j => coef κ r π u j - coef κ r π v j)
  have hb := coef_sq_sum κ r hκ hr π u v
  have hsq : ‖lift π (fun j => coef κ r π u j - coef κ r π v j)‖ ^ 2 ≤
      (5 * κ * ‖u - v‖) ^ 2 := by
    rw [h]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ball (B : ℝ) (u : E) : E := if ‖u‖ ≤ B then u else (B / ‖u‖) • u

lemma ball_norm_le (B : ℝ) (hB : 0 ≤ B) (u : E) : ‖ball B u‖ ≤ B := by
  unfold ball
  split_ifs with h
  · exact h
  · have hu : 0 < ‖u‖ := by linarith [not_le.mp h]
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hB, abs_norm,
      div_mul_cancel₀ _ hu.ne']

lemma ball_residual (B : ℝ) (hB : 0 < B) (u : E) :
    ∃ t : ℝ, 0 ≤ t ∧ u - ball B u = t • ball B u ∧ (t ≠ 0 → ‖ball B u‖ = B) := by
  unfold ball
  split_ifs with h
  · exact ⟨0, le_rfl, by simp, fun h0 => absurd rfl h0⟩
  · have hu : 0 < ‖u‖ := by linarith [not_le.mp h]
    refine ⟨‖u‖ / B - 1, ?_, ?_, ?_⟩
    · rw [sub_nonneg, le_div_iff₀ hB, one_mul]
      exact (not_le.mp h).le
    · rw [smul_smul]
      have e : (‖u‖ / B - 1) * (B / ‖u‖) = 1 - B / ‖u‖ := by
        field_simp
      rw [e, sub_smul, one_smul]
    · intro _
      rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hB.le, abs_norm,
        div_mul_cancel₀ _ hu.ne']

lemma ball_vi (B : ℝ) (hB : 0 < B) (u z : E) (hz : ‖z‖ ≤ B) :
    ⟪u - ball B u, z - ball B u⟫ ≤ 0 := by
  obtain ⟨t, ht, he, hn⟩ := ball_residual B hB u
  rw [he, real_inner_smul_left]
  by_cases h0 : t = 0
  · simp [h0]
  · have hp := hn h0
    have h1 : ⟪ball B u, z⟫ ≤ ‖ball B u‖ * ‖z‖ := real_inner_le_norm _ _
    have h2 : ⟪ball B u, z - ball B u⟫ = ⟪ball B u, z⟫ - ‖ball B u‖ ^ 2 := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    rw [h2, hp]
    rw [hp] at h1
    have : ⟪ball B u, z⟫ - B ^ 2 ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos ht this

lemma ball_firm (B : ℝ) (hB : 0 < B) (u v : E) :
    ‖ball B u - ball B v‖ ^ 2 ≤ ⟪u - v, ball B u - ball B v⟫ := by
  have h1 := ball_vi B hB u (ball B v) (ball_norm_le B hB.le v)
  have h2 := ball_vi B hB v (ball B u) (ball_norm_le B hB.le u)
  have e : ⟪u - v, ball B u - ball B v⟫ - ‖ball B u - ball B v‖ ^ 2 =
      -⟪u - ball B u, ball B v - ball B u⟫ - ⟪v - ball B v, ball B u - ball B v⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  linarith

lemma ball_lipschitz (B : ℝ) (hB : 0 < B) (u v : E) :
    ‖ball B u - ball B v‖ ≤ ‖u - v‖ := by
  have h := ball_firm B hB u v
  have h2 := real_inner_le_norm (u - v) (ball B u - ball B v)
  have ha := norm_nonneg (ball B u - ball B v)
  have hb := norm_nonneg (u - v)
  nlinarith

lemma ball_residual_lipschitz (B : ℝ) (hB : 0 < B) (u v : E) :
    ‖(u - ball B u) - (v - ball B v)‖ ≤ ‖u - v‖ := by
  have h := ball_firm B hB u v
  have e : (u - ball B u) - (v - ball B v) = (u - v) - (ball B u - ball B v) := by abel
  have hs : ‖(u - ball B u) - (v - ball B v)‖ ^ 2 ≤ ‖u - v‖ ^ 2 := by
    rw [e, norm_sub_sq_real]
    nlinarith [sq_nonneg ‖ball B u - ball B v‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hs

lemma ball_of_le (B : ℝ) (u : E) (hu : ‖u‖ ≤ B) : ball B u = u := by
  simp [ball, hu]

end Ball

noncomputable def field (κ r B : ℝ) (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  chain κ r π (ball B u) + κ • (u - ball B u)

lemma field_lipschitz (κ r B : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hB : 0 < B)
    (π : Fin (k + 1) ↪ Fin d) (u v : EuclideanSpace ℝ (Fin d)) :
    ‖field κ r B π u - field κ r B π v‖ ≤ 6 * κ * ‖u - v‖ := by
  unfold field
  have e : chain κ r π (ball B u) + κ • (u - ball B u) - (chain κ r π (ball B v) + κ • (v - ball B v)) =
      (chain κ r π (ball B u) - chain κ r π (ball B v)) + κ • ((u - ball B u) - (v - ball B v)) := by
    rw [smul_sub κ (u - ball B u) (v - ball B v)]
    abel
  rw [e]
  have h1 := chain_lipschitz κ r hκ hr π (ball B u) (ball B v)
  have h2 := ball_lipschitz B hB u v
  have h3 := ball_residual_lipschitz B hB u v
  calc
    _ ≤ ‖chain κ r π (ball B u) - chain κ r π (ball B v)‖ +
        ‖κ • ((u - ball B u) - (v - ball B v))‖ := norm_add_le _ _
    _ ≤ 5 * κ * ‖u - v‖ + κ * ‖u - v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ]
      gcongr
      exact h1.trans (by gcongr)
    _ = 6 * κ * ‖u - v‖ := by ring

noncomputable def target (r : ℝ) (π : Fin (k + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  lift π (fun _ => r)

lemma target_norm_sq (r : ℝ) (π : Fin (k + 1) ↪ Fin d) :
    ‖target r π‖ ^ 2 = ((k : ℝ) + 1) * r ^ 2 := by
  rw [target, norm_lift_sq]
  simp

lemma target_norm_le (r B : ℝ) (hB : 0 ≤ B) (π : Fin (k + 1) ↪ Fin d)
    (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2) : ‖target r π‖ ≤ B := by
  have h := target_norm_sq r π
  have hs : ‖target r π‖ ^ 2 ≤ B ^ 2 := by
    rw [h]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) (sq_nonneg r)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hB two_ne_zero).mp hs

lemma field_target (κ r B : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B) (π : Fin (k + 1) ↪ Fin d)
    (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2) : field κ r B π (target r π) = 0 := by
  unfold field
  rw [ball_of_le B _ (target_norm_le r B hB π hrad), sub_self, smul_zero, add_zero]
  ext i
  change (∑ j, if π j = i then coef κ r π (target r π) j else 0) = 0
  apply Finset.sum_eq_zero
  intro j _
  have hc : coef κ r π (target r π) j = 0 := by
    unfold coef
    rw [target, lift_apply, sub_self]
    simp [clip, hr]
  simp [hc]

lemma field_minty (κ r B : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) (hB : 0 < B)
    (π : Fin (k + 1) ↪ Fin d) (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2)
    (u : EuclideanSpace ℝ (Fin d)) : 0 ≤ ⟪field κ r B π u, u - target r π⟫ := by
  obtain ⟨t, ht, he, hn⟩ := ball_residual B hB u
  set p := ball B u with hp
  have hcoord (j : Fin (k + 1)) : u (π j) = p (π j) + t * p (π j) := by
    have h := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x (π j)) he
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
    linarith
  have hchain : ⟪chain κ r π p, u - target r π⟫ =
      ∑ j, act κ r π p j * clip r (p (π j) - r) * ((p (π j) - r) + t * p (π j)) := by
    rw [chain, inner_lift]
    apply Finset.sum_congr rfl
    intro j _
    rw [PiLp.sub_apply, target, lift_apply, hcoord j, coef]
    ring
  have hterm : ∑ j : Fin (k + 1), -(κ * t ^ 2 * r ^ 2 / 4) ≤
      ⟪chain κ r π p, u - target r π⟫ := by
    rw [hchain]
    exact Finset.sum_le_sum (fun j _ => clip_term_lower κ _ r _ t (act_nonneg κ r hκ π p j)
      (act_le κ r hκ π p j) hr.le ht)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hterm
  have hvi := ball_vi B hB u (target r π) (target_norm_le r B hB.le π hrad)
  have hwall : ‖u - p‖ ^ 2 ≤ ⟪u - p, u - target r π⟫ := by
    have e : ⟪u - p, u - target r π⟫ = ‖u - p‖ ^ 2 - ⟪u - p, target r π - p⟫ := by
      rw [← real_inner_self_eq_norm_sq, ← inner_sub_right]
      congr 1
      abel
    rw [e]
    linarith
  have hnorm : 4 * ((k : ℝ) + 1) * r ^ 2 * t ^ 2 ≤ ‖u - p‖ ^ 2 := by
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    by_cases h0 : t = 0
    · simp [h0]
    · rw [hn h0]
      nlinarith [sq_nonneg t]
  have hsplit : ⟪field κ r B π u, u - target r π⟫ =
      ⟪chain κ r π p, u - target r π⟫ + κ * ⟪u - p, u - target r π⟫ := by
    rw [field, inner_add_left, real_inner_smul_left]
  rw [hsplit]
  push_cast at hterm
  have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  have h1 := mul_le_mul_of_nonneg_left (hnorm.trans hwall) hκ
  have h2 : 0 ≤ ((k : ℝ) + 1) * κ * t ^ 2 * r ^ 2 := by positivity
  have e1 : ((k : ℝ) + 1) * -(κ * t ^ 2 * r ^ 2 / 4) = -(((k : ℝ) + 1) * κ * t ^ 2 * r ^ 2) / 4 := by
    ring
  have e2 : κ * (4 * ((k : ℝ) + 1) * r ^ 2 * t ^ 2) = 4 * (((k : ℝ) + 1) * κ * t ^ 2 * r ^ 2) := by
    ring
  rw [e1] at hterm
  rw [e2] at h1
  linarith

lemma chain_lower (κ r : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (p : EuclideanSpace ℝ (Fin d)) (hj : ∃ j, p (π j) ≤ r / 2) :
    κ ^ 2 * r ^ 2 / 4 ≤ ‖chain κ r π p‖ ^ 2 := by
  by_contra hlt
  push Not at hlt
  have hsum : ‖chain κ r π p‖ ^ 2 = ∑ j, coef κ r π p j ^ 2 := by
    rw [chain, norm_lift_sq]
  have hone (j : Fin (k + 1)) : coef κ r π p j ^ 2 < κ ^ 2 * r ^ 2 / 4 := by
    have h := Finset.single_le_sum (fun i _ => sq_nonneg (coef κ r π p i)) (Finset.mem_univ j)
    rw [← hsum] at h
    linarith
  have hgood (j : Fin (k + 1)) (hact : act κ r π p j = κ) : |p (π j) - r| < r / 2 := by
    by_contra hge
    push Not at hge
    have hc := clip_abs_ge r (p (π j) - r) hr.le hge
    have h := hone j
    unfold coef at h
    rw [hact, mul_pow, ← sq_abs (clip r (p (π j) - r))] at h
    have h2 : (r / 2) ^ 2 ≤ |clip r (p (π j) - r)| ^ 2 :=
      pow_le_pow_left₀ (by positivity) hc 2
    nlinarith [mul_nonneg (sq_nonneg κ) (sub_nonneg.mpr h2)]
  have hall : ∀ n (hn : n < k + 1), |p (π ⟨n, hn⟩) - r| < r / 2 := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact hgood ⟨0, hn⟩ (by simp [act])
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hpos : r / 2 ≤ p (π ⟨n, by omega⟩) := by
        rw [abs_lt] at hprev
        linarith
      apply hgood ⟨n + 1, hn⟩
      have e : (⟨n + 1, hn⟩ : Fin (k + 1)) = (⟨n, by omega⟩ : Fin k).succ := rfl
      rw [e]
      simp only [act, Fin.cases_succ]
      exact ramp_of_ge κ r _ hr hpos
  obtain ⟨j, hj⟩ := hj
  have h := hall j.val j.isLt
  rw [abs_lt] at h
  linarith

lemma field_lower (κ r B : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hB : 0 < B)
    (π : Fin (k + 1) ↪ Fin d) (hrad : 4 * ((k : ℝ) + 1) * r ^ 2 ≤ B ^ 2)
    (u : EuclideanSpace ℝ (Fin d)) (hj : ∃ j, ball B u (π j) ≤ r / 2) :
    3 * κ ^ 2 * r ^ 2 / 16 ≤ ‖field κ r B π u‖ ^ 2 := by
  obtain ⟨t, ht, he, hn⟩ := ball_residual B hB u
  set p := ball B u with hp
  set g := chain κ r π p with hg
  have hlow := chain_lower κ r hr π p hj
  rw [← hg] at hlow
  have hfield : field κ r B π u = g + (κ * t) • p := by
    rw [field, ← hp, he, smul_smul]
  have hinner : -(r * ∑ j, |coef κ r π p j|) ≤ ⟪g, p⟫ := by
    rw [hg, chain, inner_lift, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    unfold coef
    set a := act κ r π p j
    have ha := act_nonneg κ r hκ.le π p j
    rcases le_total r (p (π j)) with h | h
    · have hc := clip_nonneg_of_nonneg r (p (π j) - r) hr.le (by linarith)
      have : 0 ≤ a * clip r (p (π j) - r) * p (π j) := by
        have : 0 ≤ p (π j) := by linarith
        positivity
      have : 0 ≤ r * |a * clip r (p (π j) - r)| := by positivity
      linarith
    · have hc := clip_nonpos_of_nonpos r (p (π j) - r) hr.le (by linarith)
      have hac : a * clip r (p (π j) - r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha hc
      rw [abs_of_nonpos hac]
      nlinarith
  have hcs : (∑ j, |coef κ r π p j|) ^ 2 ≤ ((k : ℝ) + 1) * ‖g‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin (k + 1))))
      (f := fun j => |coef κ r π p j|)
    simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at h
    rw [hg, chain, norm_lift_sq]
    push_cast at h
    exact h
  have hpn : 4 * ((k : ℝ) + 1) * r ^ 2 * t ^ 2 ≤ t ^ 2 * ‖p‖ ^ 2 := by
    by_cases h0 : t = 0
    · simp [h0]
    · rw [hn h0]
      nlinarith [sq_nonneg t]
  have hexp : ‖field κ r B π u‖ ^ 2 = ‖g‖ ^ 2 + 2 * (κ * t) * ⟪g, p⟫ + (κ * t) ^ 2 * ‖p‖ ^ 2 := by
    rw [hfield, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  set S := ∑ j, |coef κ r π p j|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  set X := κ * t * r
  have hX : 0 ≤ X := by positivity
  have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmain : 3 / 4 * ‖g‖ ^ 2 ≤ ‖g‖ ^ 2 - 2 * X * S + 4 * ((k : ℝ) + 1) * X ^ 2 := by
    have h4 : 0 ≤ ((k : ℝ) + 1) * (‖g‖ ^ 2 / 4 - 2 * X * S + 4 * ((k : ℝ) + 1) * X ^ 2) := by
      nlinarith [sq_nonneg (4 * ((k : ℝ) + 1) * X - S)]
    have h5 := nonneg_of_mul_nonneg_right (by linarith : 0 ≤ ((k : ℝ) + 1) *
      (‖g‖ ^ 2 / 4 - 2 * X * S + 4 * ((k : ℝ) + 1) * X ^ 2)) hK
    linarith
  have hcross : -(2 * X * S) ≤ 2 * (κ * t) * ⟪g, p⟫ := by
    have hkt : 0 ≤ 2 * (κ * t) := by positivity
    have := mul_le_mul_of_nonneg_left hinner hkt
    have e : 2 * (κ * t) * -(r * S) = -(2 * X * S) := by ring
    linarith
  have hlast : 4 * ((k : ℝ) + 1) * X ^ 2 ≤ (κ * t) ^ 2 * ‖p‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hpn (sq_nonneg κ)
    have e1 : 4 * ((k : ℝ) + 1) * X ^ 2 = κ ^ 2 * (4 * ((k : ℝ) + 1) * r ^ 2 * t ^ 2) := by ring
    have e2 : (κ * t) ^ 2 * ‖p‖ ^ 2 = κ ^ 2 * (t ^ 2 * ‖p‖ ^ 2) := by ring
    linarith
  rw [hexp]
  nlinarith

noncomputable def partialChain (κ r : ℝ) (π : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  lift π (fun j => if j.val ≤ t then coef κ r π u j else 0)

lemma coef_prefix (κ r : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) (u : EuclideanSpace ℝ (Fin d))
    (j : Fin (k + 1)) (hj : j.val ≤ t) : coef κ r π u j = coef κ r ρ u j := by
  unfold coef act
  rw [h j hj]
  cases j using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Fin.cases_succ]
    rw [h i.castSucc (by simp only [Fin.val_castSucc, Fin.val_succ] at hj ⊢; omega)]

lemma partialChain_prefix (κ r : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) (u : EuclideanSpace ℝ (Fin d)) :
    partialChain κ r π t u = partialChain κ r ρ t u := by
  unfold partialChain
  have hc : (fun j : Fin (k + 1) => if j.val ≤ t then coef κ r π u j else 0) =
      fun j => if j.val ≤ t then coef κ r ρ u j else 0 := by
    funext j
    split_ifs with hj
    · exact coef_prefix κ r π ρ t h u j hj
    · rfl
  rw [hc]
  exact lift_congr π ρ _ t (fun j hj => by simp [show ¬ j.val ≤ t by omega]) h

lemma chain_eq_partial (κ r : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (u : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ r / 4) :
    chain κ r π u = partialChain κ r π t u := by
  unfold chain partialChain
  congr 1
  funext j
  split_ifs with hj
  · rfl
  · cases j using Fin.cases with
    | zero => simp at hj
    | succ i =>
      have hi := h i.castSucc (by simp only [Fin.val_castSucc, Fin.val_succ] at hj ⊢; omega)
      unfold coef act
      simp only [Fin.cases_succ]
      rw [ramp_of_le κ r _ hr ((le_abs_self _).trans hi), zero_mul]

noncomputable def partialField (κ r B : ℝ) (π : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  partialChain κ r π t (ball B u) + κ • (u - ball B u)

lemma partialField_prefix (κ r B : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) (u : EuclideanSpace ℝ (Fin d)) :
    partialField κ r B π t u = partialField κ r B ρ t u := by
  unfold partialField
  rw [partialChain_prefix κ r π ρ t h]

lemma field_eq_partial (κ r B : ℝ) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (u : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), t ≤ j.val → |ball B u (π j)| ≤ r / 4) :
    field κ r B π u = partialField κ r B π t u := by
  unfold field partialField
  rw [chain_eq_partial κ r hr π t _ h]

end LongTails.Proofs.MintyChainGeometry
