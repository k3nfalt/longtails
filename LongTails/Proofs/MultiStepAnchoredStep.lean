import LongTails.Algorithms.MultiStepAnchoredForwardBackward
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneInclusion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Hyp (F : E → E) (H : E → Set E) (J : ℝ → E → E) (L ρ : ℝ) : Prop where
  res : ∀ γ z, 0 < γ → γ⁻¹ • (z - J γ z) ∈ H (J γ z)
  mono : ∀ x y, ∀ a ∈ H x, ∀ b ∈ H y, 0 ≤ ⟪a - b, x - y⟫
  lip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖
  cohypo : ∀ x y, ∀ a ∈ H x, ∀ b ∈ H y,
    -ρ * ‖(F x + a) - (F y + b)‖ ^ 2 ≤ ⟪(F x + a) - (F y + b), x - y⟫

lemma Hyp.nonexpansive {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ γ : ℝ}
    (h : Hyp F H J L ρ) (hγ : 0 < γ) (z z' : E) : ‖J γ z - J γ z'‖ ≤ ‖z - z'‖ := by
  have hm := h.mono _ _ _ (h.res γ z hγ) _ (h.res γ z' hγ)
  rw [← smul_sub, real_inner_smul_left] at hm
  have h1 : 0 ≤ ⟪z - J γ z - (z' - J γ z'), J γ z - J γ z'⟫ := by
    by_contra hneg
    rw [not_le] at hneg
    have := mul_neg_of_pos_of_neg (inv_pos.mpr hγ) hneg
    linarith
  have e : z - J γ z - (z' - J γ z') = (z - z') - (J γ z - J γ z') := by abel
  rw [e, inner_sub_left, real_inner_self_eq_norm_sq] at h1
  have h2 := real_inner_le_norm (z - z') (J γ z - J γ z')
  nlinarith [norm_nonneg (J γ z - J γ z'), norm_nonneg (z - z')]

lemma Hyp.fixed {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}
    (h : Hyp F H J L ρ) (hη : 0 < η) {xs : E} (hxs : -F xs ∈ H xs) :
    J η (xs - η • F xs) = xs := by
  have hm := h.mono _ _ _ (h.res η (xs - η • F xs) hη) _ hxs
  have e : η⁻¹ • (xs - η • F xs - J η (xs - η • F xs)) - -F xs =
      η⁻¹ • (xs - J η (xs - η • F xs)) := by
    rw [sub_right_comm, smul_sub, smul_smul, inv_mul_cancel₀ hη.ne', one_smul]
    abel
  rw [e, real_inner_smul_left, ← neg_sub (J η (xs - η • F xs)) xs, inner_neg_left,
    real_inner_self_eq_norm_sq] at hm
  have h1 : ‖J η (xs - η • F xs) - xs‖ ^ 2 ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    have := mul_pos (inv_pos.mpr hη) hpos
    linarith
  have h2 : ‖J η (xs - η • F xs) - xs‖ = 0 := by
    nlinarith [norm_nonneg (J η (xs - η • F xs) - xs)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h2)

lemma fb_lipschitz {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}
    (h : Hyp F H J L ρ) (hη : 0 < η) (t a b : E) :
    ‖J η (t - η • F a) - J η (t - η • F b)‖ ≤ η * L * ‖a - b‖ := by
  refine (h.nonexpansive hη _ _).trans ?_
  have e : (t - η • F a) - (t - η • F b) = -(η • (F a - F b)) := by
    rw [smul_sub]; abel
  rw [e, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.lip a b) hη.le

omit [InnerProductSpace ℝ E] in
lemma iterate_lipschitz {Ψ : E → E} {q : ℝ} (hq : 0 ≤ q)
    (hΨ : ∀ a b, ‖Ψ a - Ψ b‖ ≤ q * ‖a - b‖) (m : ℕ) (a b : E) :
    ‖Ψ^[m] a - Ψ^[m] b‖ ≤ q ^ m * ‖a - b‖ := by
  induction m generalizing a b with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ, mul_assoc]
    exact (ih _ _).trans (mul_le_mul_of_nonneg_left (hΨ a b) (pow_nonneg hq m))

omit [InnerProductSpace ℝ E] in
lemma contraction_error {Ψ : E → E} {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hΨ : ∀ a b, ‖Ψ a - Ψ b‖ ≤ q * ‖a - b‖) (m : ℕ) (v : E) :
    (1 - q ^ (m + 1)) * ‖Ψ (Ψ^[m] v) - Ψ^[m] v‖ ≤ q ^ m * (1 + q) * ‖Ψ (Ψ^[m] v) - v‖ := by
  have hQ : 0 ≤ q ^ m := pow_nonneg hq m
  have hP : q ^ (m + 1) ≤ 1 := pow_le_one₀ hq hq1
  have hcomm : Ψ (Ψ^[m] v) = Ψ^[m] (Ψ v) :=
    (Function.iterate_succ_apply' Ψ m v).symm.trans (Function.iterate_succ_apply Ψ m v)
  have h1 : ‖Ψ (Ψ^[m] v) - Ψ^[m] v‖ ≤ q ^ m * ‖Ψ v - v‖ := by
    rw [hcomm]
    exact iterate_lipschitz hq hΨ m (Ψ v) v
  have h2 : ‖Ψ (Ψ (Ψ^[m] v)) - Ψ (Ψ^[m] v)‖ ≤ q ^ (m + 1) * ‖Ψ v - v‖ := by
    have e1 : Ψ (Ψ (Ψ^[m] v)) = Ψ^[m + 1] (Ψ v) := by
      rw [hcomm]; exact (Function.iterate_succ_apply' Ψ m (Ψ v)).symm
    have e2 : Ψ (Ψ^[m] v) = Ψ^[m + 1] v := (Function.iterate_succ_apply' Ψ m v).symm
    rw [e1, e2]
    exact iterate_lipschitz hq hΨ (m + 1) (Ψ v) v
  have h3 : ‖Ψ v - Ψ (Ψ (Ψ^[m] v))‖ ≤ q * ‖v - Ψ (Ψ^[m] v)‖ := hΨ _ _
  have h4 : ‖Ψ v - v‖ ≤ ‖Ψ v - Ψ (Ψ (Ψ^[m] v))‖ + ‖Ψ (Ψ (Ψ^[m] v)) - v‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h5 : ‖Ψ (Ψ (Ψ^[m] v)) - v‖ ≤
      ‖Ψ (Ψ (Ψ^[m] v)) - Ψ (Ψ^[m] v)‖ + ‖Ψ (Ψ^[m] v) - v‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [norm_sub_rev v (Ψ (Ψ^[m] v))] at h3
  have h6 : (1 - q ^ (m + 1)) * ‖Ψ v - v‖ ≤ (1 + q) * ‖Ψ (Ψ^[m] v) - v‖ := by linarith
  calc (1 - q ^ (m + 1)) * ‖Ψ (Ψ^[m] v) - Ψ^[m] v‖
      ≤ (1 - q ^ (m + 1)) * (q ^ m * ‖Ψ v - v‖) :=
        mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hP)
    _ = q ^ m * ((1 - q ^ (m + 1)) * ‖Ψ v - v‖) := by ring
    _ ≤ q ^ m * ((1 + q) * ‖Ψ (Ψ^[m] v) - v‖) := mul_le_mul_of_nonneg_left h6 hQ
    _ = q ^ m * (1 + q) * ‖Ψ (Ψ^[m] v) - v‖ := by ring

lemma potential_identity (g g' d e : E) (μ μ' k : ℝ) (hk : k + 1 ≠ 0) :
    k * (k * μ' - μ) * ‖g‖ ^ 2 + k * ⟪g, d⟫ -
        ((k + 1) * ((k + 1) * μ' - μ) * ‖g'‖ ^ 2 +
          (k + 1) * ⟪g', (1 - 1 / (k + 1)) • (d - (2 * μ') • g) + e⟫) =
      k * (k + 1) * (⟪g' - g, (1 - 1 / (k + 1)) • (d - (2 * μ') • g) + e - d⟫ -
          μ * ‖g' - g‖ ^ 2) +
        (k + 1) ^ 2 * ((μ - μ') * ‖g' - (1 - 1 / (k + 1)) • g‖ ^ 2 -
          ⟪g' - (1 - 1 / (k + 1)) • g, e⟫) := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm g' g,
    real_inner_comm d g, real_inner_comm e g, real_inner_comm d g', real_inner_comm e g']
  field_simp
  ring

noncomputable def gval (F : E → E) (η : ℝ) (p : E × E) : E := F p.2 + η⁻¹ • (p.1 - p.2)

noncomputable def yval (F : E → E) (η : ℝ) (p : E × E) : E := p.1 + η • F p.2

noncomputable def fb (F : E → E) (J : ℝ → E → E) (η : ℝ) (t v : E) : E × E :=
  (t - η • F v, J η (t - η • F v))

noncomputable def next (F : E → E) (J : ℝ → E → E) (η s : ℝ) (m : ℕ) (a : E) (n : ℕ)
    (p : E × E) : E × E :=
  fb F J η (target s n a (yval F η p) (gval F η p))
    ((fun v => (fb F J η (target s n a (yval F η p) (gval F η p)) v).2)^[m]
      (predictor η s n a (yval F η p) (gval F η p)))

noncomputable def pot (F : E → E) (η μ μ' : ℝ) (a : E) (n : ℕ) (p : E × E) : ℝ :=
  ((n : ℝ) + 1) * (((n : ℝ) + 1) * μ' - μ) * ‖gval F η p‖ ^ 2 +
    ((n : ℝ) + 1) * ⟪gval F η p, yval F η p - a⟫

lemma yval_eq (F : E → E) {η : ℝ} (hη : η ≠ 0) (p : E × E) :
    yval F η p = p.2 + η • gval F η p := by
  rw [yval, gval, smul_add, smul_smul, mul_inv_cancel₀ hη, one_smul]
  abel

lemma Hyp.mem {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}
    (h : Hyp F H J L ρ) (hη : 0 < η) {p : E × E} (hp : p.2 = J η p.1) :
    η⁻¹ • (p.1 - p.2) ∈ H p.2 := by
  have := h.res η p.1 hη
  rwa [← hp] at this

lemma Hyp.cocoercive {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}
    (h : Hyp F H J L ρ) (hη : 0 < η) {p p' : E × E} (hp : p.2 = J η p.1)
    (hp' : p'.2 = J η p'.1) :
    (η - ρ) * ‖gval F η p' - gval F η p‖ ^ 2 ≤
      ⟪gval F η p' - gval F η p, yval F η p' - yval F η p⟫ := by
  have hc := h.cohypo p'.2 p.2 _ (h.mem hη hp') _ (h.mem hη hp)
  rw [yval_eq F hη.ne' p', yval_eq F hη.ne' p]
  have e1 : p'.2 + η • gval F η p' - (p.2 + η • gval F η p) =
      (p'.2 - p.2) + η • (gval F η p' - gval F η p) := by
    rw [smul_sub]; abel
  rw [e1, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  change -ρ * ‖gval F η p' - gval F η p‖ ^ 2 ≤ ⟪gval F η p' - gval F η p, p'.2 - p.2⟫ at hc
  linarith

lemma pot_step {F : E → E} {H : E → Set E} {J : ℝ → E → E} {L ρ η s : ℝ} {m : ℕ}
    (h : Hyp F H J L ρ) (hL : 0 ≤ L) (hη : 0 < η) (hq : η * L ≤ 1)
    (hP : (η * L) ^ (m + 1) * (2 + η * L) < 1)
    (hσ : (η * L) ^ (m + 1) * (1 + η * L) * η ≤
      (η - ρ - s / 2) * (1 - (η * L) ^ (m + 1) * (2 + η * L)))
    (a : E) (n : ℕ) {p : E × E} (hp : p.2 = J η p.1) :
    pot F η (η - ρ) (s / 2) a (n + 1) (next F J η s m a n p) ≤
      pot F η (η - ρ) (s / 2) a n p := by
  set g := gval F η p with hg
  set y := yval F η p with hy
  set t := target s n a y g with ht
  set v0 := predictor η s n a y g with hv0
  set Ψ : E → E := fun v => (fb F J η t v).2 with hΨdef
  set vm := Ψ^[m] v0 with hvm
  have hnext : next F J η s m a n p = fb F J η t vm := rfl
  set p' := fb F J η t vm with hp'def
  have hp'1 : p'.1 = t - η • F vm := rfl
  have hp'2 : p'.2 = Ψ vm := rfl
  have hp' : p'.2 = J η p'.1 := rfl
  set g' := gval F η p' with hg'
  set y' := yval F η p' with hy'
  set k : ℝ := (n : ℝ) + 1 with hk
  have hk0 : 0 < k := by positivity
  have hk1 : k + 1 ≠ 0 := by positivity
  have hβ : 1 / ((n : ℝ) + 2) = 1 / (k + 1) := by rw [hk]; ring_nf
  set e := y' - t with he
  set w := g' - (1 - 1 / (k + 1)) • g with hw
  have hq0 : 0 ≤ η * L := mul_nonneg hη.le hL
  have hΨ : ∀ x z, ‖Ψ x - Ψ z‖ ≤ η * L * ‖x - z‖ := fun x z => fb_lipschitz h hη t x z
  have herr := contraction_error hq0 hq hΨ m v0
  rw [← hvm, ← hp'2] at herr
  have heq : e = η • (F p'.2 - F vm) := by
    rw [he, hy', yval, hp'1, smul_sub]; abel
  have hηg' : η • g' = η • F p'.2 + (p'.1 - p'.2) := by
    rw [hg', gval, smul_add, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
  have hD : p'.2 - v0 = e - η • w := by
    rw [hw, smul_sub, hηg', heq, hp'1, hv0, predictor, ← ht, hβ, smul_smul, smul_sub]
    abel
  have he_norm : ‖e‖ ≤ η * L * ‖p'.2 - vm‖ := by
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.lip _ _) hη.le
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have he0 : 0 ≤ ‖e‖ := norm_nonneg e
  have hD_norm : ‖p'.2 - v0‖ ≤ ‖e‖ + η * ‖w‖ := by
    rw [hD]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hQ0 : 0 ≤ (η * L) ^ m := pow_nonneg hq0 m
  have hP1 : (η * L) ^ (m + 1) ≤ 1 := pow_le_one₀ hq0 hq
  have hgap : 0 < 1 - (η * L) ^ (m + 1) * (2 + η * L) := by linarith
  have he_le : ‖e‖ ≤ (η - ρ - s / 2) * ‖w‖ := by
    have h1 : (1 - (η * L) ^ (m + 1)) * ‖e‖ ≤
        (η * L) ^ (m + 1) * (1 + η * L) * (‖e‖ + η * ‖w‖) := by
      calc (1 - (η * L) ^ (m + 1)) * ‖e‖
          ≤ (1 - (η * L) ^ (m + 1)) * (η * L * ‖p'.2 - vm‖) :=
            mul_le_mul_of_nonneg_left he_norm (sub_nonneg.mpr hP1)
        _ = η * L * ((1 - (η * L) ^ (m + 1)) * ‖p'.2 - vm‖) := by ring
        _ ≤ η * L * ((η * L) ^ m * (1 + η * L) * ‖p'.2 - v0‖) :=
            mul_le_mul_of_nonneg_left herr hq0
        _ = (η * L) ^ (m + 1) * (1 + η * L) * ‖p'.2 - v0‖ := by rw [pow_succ]; ring
        _ ≤ (η * L) ^ (m + 1) * (1 + η * L) * (‖e‖ + η * ‖w‖) :=
            mul_le_mul_of_nonneg_left hD_norm (by positivity)
    have h2 : (1 - (η * L) ^ (m + 1) * (2 + η * L)) * ‖e‖ ≤
        (η * L) ^ (m + 1) * (1 + η * L) * η * ‖w‖ := by linarith
    have h3 := mul_le_mul_of_nonneg_right hσ hw0
    have h4 : (1 - (η * L) ^ (m + 1) * (2 + η * L)) * ‖e‖ ≤
        (1 - (η * L) ^ (m + 1) * (2 + η * L)) * ((η - ρ - s / 2) * ‖w‖) := by linarith
    exact le_of_mul_le_mul_left h4 hgap
  have hwe : ⟪w, e⟫ ≤ (η - ρ - s / 2) * ‖w‖ ^ 2 := by
    have := real_inner_le_norm w e
    nlinarith [mul_le_mul_of_nonneg_left he_le hw0]
  have hd' : y' - a = (1 - 1 / (k + 1)) • (y - a - (2 * (s / 2)) • g) + e := by
    rw [he, ht, target, hβ]
    module
  have hco : (η - ρ) * ‖g' - g‖ ^ 2 ≤
      ⟪g' - g, (1 - 1 / (k + 1)) • (y - a - (2 * (s / 2)) • g) + e - (y - a)⟫ := by
    rw [← hd', sub_sub_sub_cancel_right]
    exact h.cocoercive hη hp hp'
  have hid := potential_identity g g' (y - a) e (η - ρ) (s / 2) k hk1
  have hcast : ((n + 1 : ℕ) : ℝ) + 1 = k + 1 := by rw [hk]; push_cast; ring
  rw [hnext]
  unfold pot
  rw [hcast, ← hg', ← hy', hd', ← hg, ← hy, ← hk]
  have hc : 0 ≤ k * (k + 1) := by positivity
  have hsq : 0 ≤ (k + 1) ^ 2 := by positivity
  have t1 := mul_nonneg hc (sub_nonneg.mpr hco)
  have t2 : 0 ≤ (k + 1) ^ 2 * ((η - ρ - s / 2) * ‖w‖ ^ 2 - ⟪w, e⟫) :=
    mul_nonneg hsq (sub_nonneg.mpr hwe)
  linarith

end OracleTemplate.CohypomonotoneInclusion
