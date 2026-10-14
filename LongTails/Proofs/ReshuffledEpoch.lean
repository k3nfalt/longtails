import LongTails.Setups.ReshuffledSmoothConvex
import LongTails.Proofs.LinearDecaySgdStep

open Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ReshuffledConvex

open LongTails.Setups.ReshuffledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {n : ℕ}

structure Hyp (f : Fin n → E → ℝ) (g : Fin n → E → E) (ℓ : Fin n → ℝ) (Lavg Lmax σ : ℝ)
    (xstar : E) : Prop where
  pos : 0 < Lavg
  le : Lavg ≤ Lmax
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  grad : ∀ i x, HasGradientAt (f i) (g i x) x
  nonneg : ∀ i, 0 ≤ ℓ i
  le_max : ∀ i, ℓ i ≤ Lmax
  avg : (n : ℝ)⁻¹ * ∑ i, ℓ i ≤ Lavg
  lip : ∀ i x y, ‖g i x - g i y‖ ≤ ℓ i * ‖x - y‖
  min : IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ xstar
  noise : (n : ℝ)⁻¹ * ∑ i, ‖g i xstar‖ ^ 2 ≤ σ ^ 2

def pre (v : Fin n → E) (j : ℕ) : E := ∑ m ∈ univ.filter (fun m : Fin n => m.val < j), v m

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma pre_zero (v : Fin n → E) : pre v 0 = 0 := by
  simp [pre]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma pre_succ (v : Fin n → E) {j : ℕ} (hj : j < n) : pre v (j + 1) = pre v j + v ⟨j, hj⟩ := by
  classical
  have hset : univ.filter (fun m : Fin n => m.val < j + 1) =
      insert ⟨j, hj⟩ (univ.filter (fun m : Fin n => m.val < j)) := by
    ext m
    rw [mem_insert, mem_filter, mem_filter]
    constructor
    · rintro ⟨-, hm⟩
      by_cases hmj : m.val = j
      · exact Or.inl (Fin.ext hmj)
      · exact Or.inr ⟨mem_univ _, by omega⟩
    · rintro (hm | ⟨-, hm⟩)
      · subst hm
        exact ⟨mem_univ _, Nat.lt_succ_self j⟩
      · exact ⟨mem_univ _, by omega⟩
  have hnot : (⟨j, hj⟩ : Fin n) ∉ univ.filter (fun m : Fin n => m.val < j) := by simp
  rw [pre, hset, sum_insert hnot, add_comm]
  rfl

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma pre_full (v : Fin n → E) : pre v n = ∑ m, v m := by
  rw [pre, filter_true_of_mem (fun m _ => m.isLt)]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma pre_add (u v : Fin n → E) (j : ℕ) : pre (fun m => u m + v m) j = pre u j + pre v j :=
  sum_add_distrib

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma norm_pre_le (v : Fin n → E) (j : ℕ) : ‖pre v j‖ ≤ ∑ m, ‖v m‖ :=
  (norm_sum_le _ _).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma norm_tail_le (v : Fin n → E) (j : ℕ) : ‖∑ m, v m - pre v j‖ ≤ ∑ m, ‖v m‖ := by
  classical
  have hsplit := sum_filter_add_sum_filter_not univ (fun m : Fin n => m.val < j) v
  have he : ∑ m, v m - pre v j = ∑ m ∈ univ.filter (fun m : Fin n => ¬ m.val < j), v m := by
    rw [pre, ← hsplit]
    abel
  rw [he]
  exact (norm_sum_le _ _).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => norm_nonneg _))

noncomputable def scatter (g : Fin n → E → E) (ℓ : Fin n → ℝ) (xstar : E)
    (π : Equiv.Perm (Fin n)) : ℝ :=
  ∑ j : Fin n, ℓ (π j) * ‖pre (fun m => g (π m) xstar) j‖ ^ 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma scatter_nonneg (g : Fin n → E → E) {ℓ : Fin n → ℝ} (hℓ : ∀ i, 0 ≤ ℓ i) (xstar : E)
    (π : Equiv.Perm (Fin n)) : 0 ≤ scatter g ℓ xstar π :=
  sum_nonneg (fun _ _ => mul_nonneg (hℓ _) (sq_nonneg _))

variable [NeZero n] {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
  {Lavg Lmax σ : ℝ} {xstar : E}

lemma card_pos' (n : ℕ) [NeZero n] : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
omit [NormedAddCommGroup E] in
lemma sum_objective (f : Fin n → E → ℝ) (x : E) :
    ∑ i, f i x = n * LongTails.Setups.FiniteSumSmoothAndConvex.objective f x := by
  have hn : (n : ℝ) ≠ 0 := (card_pos' n).ne'
  rw [LongTails.Setups.FiniteSumSmoothAndConvex.objective, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

namespace Hyp

omit [NeZero n] in
lemma lmax_pos (h : Hyp f g ℓ Lavg Lmax σ xstar) : 0 < Lmax := lt_of_lt_of_le h.pos h.le

omit [NeZero n] in
lemma lip_max (h : Hyp f g ℓ Lavg Lmax σ xstar) (i : Fin n) (x y : E) :
    ‖g i x - g i y‖ ≤ Lmax * ‖x - y‖ :=
  (h.lip i x y).trans (mul_le_mul_of_nonneg_right (h.le_max i) (norm_nonneg _))

lemma sum_ell_le (h : Hyp f g ℓ Lavg Lmax σ xstar) : ∑ i, ℓ i ≤ n * Lavg := by
  have hn := card_pos' n
  have := mul_le_mul_of_nonneg_left h.avg hn.le
  rwa [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at this

lemma sum_noise_le (h : Hyp f g ℓ Lavg Lmax σ xstar) : ∑ i, ‖g i xstar‖ ^ 2 ≤ n * σ ^ 2 := by
  have hn := card_pos' n
  have := mul_le_mul_of_nonneg_left h.noise hn.le
  rwa [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] at this

omit [NeZero n] in
lemma gap_nonneg (h : Hyp f g ℓ Lavg Lmax σ xstar) (x : E) :
    0 ≤ LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar := by
  have hm := h.min (Set.mem_univ x)
  change LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤ LongTails.Setups.FiniteSumSmoothAndConvex.objective f x at hm
  linarith

lemma sum_star (h : Hyp f g ℓ Lavg Lmax σ xstar) : ∑ i, g i xstar = 0 := by
  have hn := card_pos' n
  have hLm := h.lmax_pos
  set s := ∑ i, g i xstar with hs
  set t : ℝ := 1 / (n * Lmax) with ht
  have htpos : 0 < t := by positivity
  have hcomp : ∀ i, f i (xstar - t • s) ≤
      f i xstar - t * ⟪g i xstar, s⟫ + Lmax / 2 * (t ^ 2 * ‖s‖ ^ 2) := by
    intro i
    have hu := Gradient.smooth_upper_bound (h.grad i) (h.lip i) xstar (xstar - t • s)
    have he : xstar - t • s - xstar = -(t • s) := by abel
    rw [he, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos htpos, mul_pow] at hu
    have hle : ℓ i / 2 * (t ^ 2 * ‖s‖ ^ 2) ≤ Lmax / 2 * (t ^ 2 * ‖s‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith [h.le_max i]) (by positivity)
    linarith
  have hsum := sum_le_sum (fun i (_ : i ∈ univ) => hcomp i)
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_inner, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, sum_objective f (xstar - t • s), sum_objective f xstar, ← hs,
    real_inner_self_eq_norm_sq] at hsum
  have hm := h.min (Set.mem_univ (xstar - t • s))
  change LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤ LongTails.Setups.FiniteSumSmoothAndConvex.objective f (xstar - t • s) at hm
  have hm' := mul_le_mul_of_nonneg_left hm hn.le
  have hq : (n : ℝ) * (Lmax / 2 * (t ^ 2 * ‖s‖ ^ 2)) = t / 2 * ‖s‖ ^ 2 := by
    rw [ht]
    field_simp
  have hz : t / 2 * ‖s‖ ^ 2 ≤ 0 := by linarith
  have hsq : ‖s‖ ^ 2 ≤ 0 := by
    by_contra hc
    have : 0 < t / 2 * ‖s‖ ^ 2 := mul_pos (by positivity) (not_le.mp hc)
    linarith
  have : ‖s‖ = 0 := by nlinarith [norm_nonneg s]
  exact norm_eq_zero.mp this

lemma grad_diff_sq_sum (h : Hyp f g ℓ Lavg Lmax σ xstar) (x : E) :
    ∑ i, ‖g i x - g i xstar‖ ^ 2 ≤
      2 * Lmax * (n * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) := by
  have hb : ∀ i ∈ univ, ‖g i x - g i xstar‖ ^ 2 ≤
      2 * Lmax * (f i x - f i xstar - ⟪g i xstar, x - xstar⟫) := fun i _ =>
    SampledConvex.cocoercive h.lmax_pos (h.convex i) (h.grad i) (h.lip_max i) x xstar
  have hsum := sum_le_sum hb
  rw [← mul_sum, sum_sub_distrib, sum_sub_distrib, ← sum_inner, h.sum_star, inner_zero_left,
    sum_objective f x, sum_objective f xstar] at hsum
  linarith

lemma init_gap (h : Hyp f g ℓ Lavg Lmax σ xstar) (x : E) :
    LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤ Lavg / 2 * ‖x - xstar‖ ^ 2 := by
  have hn := card_pos' n
  have hb : ∀ i ∈ univ, f i x ≤ f i xstar + ⟪g i xstar, x - xstar⟫ + ℓ i / 2 * ‖x - xstar‖ ^ 2 :=
    fun i _ => Gradient.smooth_upper_bound (h.grad i) (h.lip i) xstar x
  have hsum := sum_le_sum hb
  have hre : ∑ i, ℓ i / 2 * ‖x - xstar‖ ^ 2 = (∑ i, ℓ i) * (‖x - xstar‖ ^ 2 / 2) := by
    rw [sum_mul]
    exact sum_congr rfl (fun i _ => by ring)
  rw [sum_add_distrib, sum_add_distrib, ← sum_inner, h.sum_star, inner_zero_left, hre,
    sum_objective f x, sum_objective f xstar] at hsum
  have hl := mul_le_mul_of_nonneg_right h.sum_ell_le
    (by positivity : (0 : ℝ) ≤ ‖x - xstar‖ ^ 2 / 2)
  have hfin : (n : ℝ) * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
      n * (Lavg / 2 * ‖x - xstar‖ ^ 2) := by linarith
  exact le_of_mul_le_mul_left hfin hn

lemma obj_convex (h : Hyp f g ℓ Lavg Lmax σ xstar) (a b : E) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) :
    LongTails.Setups.FiniteSumSmoothAndConvex.objective f (θ • a + (1 - θ) • b) ≤
      θ * LongTails.Setups.FiniteSumSmoothAndConvex.objective f a + (1 - θ) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f b := by
  have hn := card_pos' n
  have hb : ∀ i ∈ univ, f i (θ • a + (1 - θ) • b) ≤ θ * f i a + (1 - θ) * f i b := by
    intro i _
    have := (h.convex i).2 (Set.mem_univ a) (Set.mem_univ b) h0 (by linarith : 0 ≤ 1 - θ) (by ring)
    simpa [smul_eq_mul] using this
  have hsum := sum_le_sum hb
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_objective f (θ • a + (1 - θ) • b),
    sum_objective f a, sum_objective f b] at hsum
  have hfin : (n : ℝ) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (θ • a + (1 - θ) • b) ≤
      n * (θ * LongTails.Setups.FiniteSumSmoothAndConvex.objective f a + (1 - θ) * LongTails.Setups.FiniteSumSmoothAndConvex.objective f b) := by linarith
  exact le_of_mul_le_mul_left hfin hn

set_option maxHeartbeats 1000000 in
theorem epoch_inequality (h : Hyp f g ℓ Lavg Lmax σ xstar) (π : Equiv.Perm (Fin n)) {η : ℝ}
    (hη : 0 ≤ η) (hγ : n * η * Lavg ≤ 1 / 2) (y : ℕ → E)
    (hy : ∀ j (hj : j < n), y (j + 1) = y j - η • g (π ⟨j, hj⟩) (y j)) (z : E) :
    ‖y n - z‖ ^ 2 ≤ ‖y 0 - z‖ ^ 2 -
      2 * (n * η) * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (y n) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f z) +
      32 * (n * η) ^ 3 * Lavg * Lmax *
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (y 0) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) +
      2 * η ^ 3 * (1 + 8 * (n * η) ^ 2 * Lavg ^ 2) * scatter g ℓ xstar π := by
  classical
  have hn := card_pos' n
  have hLm := h.lmax_pos
  let s : Fin n → E := fun m => g (π m) xstar
  let G : Fin n → E := fun m => g (π m) (y m)
  let r : Fin n → E := fun m => G m - s m
  let q : Fin n → ℝ := fun m => ‖g (π m) (y 0) - g (π m) xstar‖
  let lw : Fin n → ℝ := fun m => ℓ (π m)
  let p : Fin n → ℝ := fun m => ‖pre s m‖
  let ρ : ℝ := ∑ m, ‖r m‖
  let Q : ℝ := ∑ m, q m
  let U : ℝ := ∑ m, lw m * p m
  let W : ℝ := ∑ m, lw m * p m ^ 2
  let a : ℝ := LongTails.Setups.FiniteSumSmoothAndConvex.objective f (y 0) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar
  let c : ℝ := n * Lavg
  have hW : scatter g ℓ xstar π = W := rfl
  have hc0 : 0 ≤ c := mul_nonneg hn.le h.pos.le
  have hlw0 : ∀ m, 0 ≤ lw m := fun m => h.nonneg _
  have hp0 : ∀ m, 0 ≤ p m := fun m => norm_nonneg _
  have hρ0 : 0 ≤ ρ := sum_nonneg (fun m _ => norm_nonneg _)
  have hQ0 : 0 ≤ Q := sum_nonneg (fun m _ => norm_nonneg _)
  have hU0 : 0 ≤ U := sum_nonneg (fun m _ => mul_nonneg (hlw0 m) (hp0 m))
  have hW0 : 0 ≤ W := sum_nonneg (fun m _ => mul_nonneg (hlw0 m) (sq_nonneg _))
  have ha0 : 0 ≤ a := h.gap_nonneg _
  have hpath : ∀ j, j ≤ n → y j = y 0 - η • pre G j := by
    intro j
    induction j with
    | zero => intro _; simp [pre_zero]
    | succ j ih =>
      intro hj
      have hj' : j < n := hj
      calc y (j + 1) = y j - η • G ⟨j, hj'⟩ := hy j hj'
        _ = (y 0 - η • pre G j) - η • G ⟨j, hj'⟩ := by rw [← ih hj'.le]
        _ = y 0 - η • pre G (j + 1) := by rw [pre_succ G hj', smul_add]; abel
  have hlw : ∑ m, lw m ≤ c := by
    have he : ∑ m, lw m = ∑ i, ℓ i := Equiv.sum_comp π ℓ
    rw [he]
    exact h.sum_ell_le
  have hsfull : pre s n = 0 := by
    rw [pre_full]
    have he : ∑ m, s m = ∑ i, g i xstar := Equiv.sum_comp π (fun i => g i xstar)
    rw [he, h.sum_star]
  have hGsr : G = fun m => s m + r m := by
    funext m
    simp only [r]
    abel
  have hr : ∀ m : Fin n, ‖r m‖ ≤ q m + lw m * (η * (p m + ρ)) := by
    intro m
    have h1 : r m = (g (π m) (y m) - g (π m) (y 0)) + (g (π m) (y 0) - g (π m) xstar) := by
      simp only [r, G, s]
      abel
    have h2 : ‖y m - y 0‖ ≤ η * (p m + ρ) := by
      have hpm := hpath m m.isLt.le
      have he : y m - y 0 = -(η • pre G m) := by rw [hpm]; abel
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      apply mul_le_mul_of_nonneg_left _ hη
      rw [hGsr, pre_add]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_pre_le r m))
    calc ‖r m‖ ≤ ‖g (π m) (y m) - g (π m) (y 0)‖ + ‖g (π m) (y 0) - g (π m) xstar‖ := by
          rw [h1]; exact norm_add_le _ _
      _ ≤ lw m * ‖y m - y 0‖ + q m := add_le_add (h.lip (π m) _ _) le_rfl
      _ ≤ lw m * (η * (p m + ρ)) + q m := by
          have := mul_le_mul_of_nonneg_left h2 (hlw0 m)
          linarith
      _ = q m + lw m * (η * (p m + ρ)) := add_comm _ _
  have hρ1 : ρ ≤ Q + η * U + η * ρ * c := by
    have hs := sum_le_sum (fun m (_ : m ∈ univ) => hr m)
    have he : ∑ m, (q m + lw m * (η * (p m + ρ))) = Q + η * U + η * ρ * ∑ m, lw m := by
      have h1 : ∀ m ∈ univ, q m + lw m * (η * (p m + ρ)) =
          q m + (η * (lw m * p m) + η * ρ * lw m) := fun m _ => by ring
      show ∑ m, (q m + lw m * (η * (p m + ρ))) =
        (∑ m, q m) + η * (∑ m, lw m * p m) + η * ρ * ∑ m, lw m
      rw [sum_congr rfl h1, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, add_assoc]
    rw [he] at hs
    have := mul_le_mul_of_nonneg_left hlw (mul_nonneg hη hρ0)
    exact hs.trans (by linarith)
  have hρ : ρ ≤ 2 * Q + 2 * η * U := by
    have hcr : η * ρ * c ≤ ρ / 2 := by
      have hh : c * η ≤ 1 / 2 := by
        have : c * η = n * η * Lavg := by simp only [c]; ring
        rw [this]; exact hγ
      have := mul_le_mul_of_nonneg_right hh hρ0
      nlinarith
    linarith
  have hCS : U ^ 2 ≤ c * W := by
    have hcs := sum_mul_sq_le_sq_mul_sq univ (fun m => Real.sqrt (lw m))
      (fun m => Real.sqrt (lw m) * p m)
    have e1 : ∑ m, Real.sqrt (lw m) * (Real.sqrt (lw m) * p m) = U :=
      sum_congr rfl (fun m _ => by
        rw [← mul_assoc, Real.mul_self_sqrt (hlw0 m)])
    have e2 : ∑ m, Real.sqrt (lw m) ^ 2 = ∑ m, lw m :=
      sum_congr rfl (fun m _ => Real.sq_sqrt (hlw0 m))
    have e3 : ∑ m, (Real.sqrt (lw m) * p m) ^ 2 = W :=
      sum_congr rfl (fun m _ => by rw [mul_pow, Real.sq_sqrt (hlw0 m)])
    rw [e1, e2, e3] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right hlw hW0)
  have hρ2 : ρ ^ 2 ≤ 8 * Q ^ 2 + 8 * η ^ 2 * (c * W) := by
    have h1 : ρ ^ 2 ≤ (2 * Q + 2 * η * U) ^ 2 := pow_le_pow_left₀ hρ0 hρ 2
    have h2 : (2 * Q + 2 * η * U) ^ 2 ≤ 8 * Q ^ 2 + 8 * η ^ 2 * U ^ 2 := by
      nlinarith [sq_nonneg (2 * Q - 2 * η * U)]
    have h3 := mul_le_mul_of_nonneg_left hCS (by positivity : (0 : ℝ) ≤ 8 * η ^ 2)
    linarith
  have hQ2 : Q ^ 2 ≤ 2 * Lmax * (n : ℝ) ^ 2 * a := by
    have h1 : Q ^ 2 ≤ (n : ℝ) * ∑ m, q m ^ 2 := by
      have := sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin n => (1 : ℝ)) q
      simpa [Q] using this
    have he : ∑ m, q m ^ 2 = ∑ i, ‖g i (y 0) - g i xstar‖ ^ 2 :=
      Equiv.sum_comp π (fun i => ‖g i (y 0) - g i xstar‖ ^ 2)
    have h2 := h.grad_diff_sq_sum (y 0)
    rw [← he] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hn.le
    calc Q ^ 2 ≤ (n : ℝ) * ∑ m, q m ^ 2 := h1
      _ ≤ n * (2 * Lmax * (n * a)) := h3
      _ = 2 * Lmax * (n : ℝ) ^ 2 * a := by ring
  have hdist : ∀ m : Fin n, ‖y n - y m‖ ^ 2 ≤ 2 * η ^ 2 * p m ^ 2 + 2 * η ^ 2 * ρ ^ 2 := by
    intro m
    have hpm := hpath m m.isLt.le
    have hpn := hpath n le_rfl
    have he : y n - y m = -(η • (-pre s m + (∑ k, r k - pre r m))) := by
      have hG1 : pre G n = pre s n + pre r n := by rw [hGsr, pre_add]
      have hG2 : pre G m = pre s m + pre r m := by rw [hGsr, pre_add]
      rw [hpn, hpm, hG1, hG2, hsfull, pre_full r]
      simp only [smul_add, smul_sub, smul_neg, zero_add]
      abel
    have hnorm : ‖y n - y m‖ ≤ η * (p m + ρ) := by
      rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      apply mul_le_mul_of_nonneg_left _ hη
      refine (norm_add_le _ _).trans (add_le_add ?_ (norm_tail_le r m))
      rw [norm_neg]
    have h1 : ‖y n - y m‖ ^ 2 ≤ (η * (p m + ρ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h2 : (η * (p m + ρ)) ^ 2 ≤ 2 * η ^ 2 * p m ^ 2 + 2 * η ^ 2 * ρ ^ 2 := by
      have := mul_nonneg (sq_nonneg η) (sq_nonneg (p m - ρ))
      nlinarith
    exact h1.trans h2
  have hinner : ∀ m : Fin n, f (π m) (y n) - f (π m) z - lw m / 2 * ‖y n - y m‖ ^ 2 ≤
      ⟪G m, y n - z⟫ := by
    intro m
    have hc := Gradient.convex_support (h.convex (π m)) (h.grad (π m)) (y m) z
    have hu := Gradient.smooth_upper_bound (h.grad (π m)) (h.lip (π m)) (y m) (y n)
    have he : y n - z = (y n - y m) - (z - y m) := by abel
    rw [he, inner_sub_right]
    simp only [G, lw]
    linarith
  have hsumI : (n : ℝ) * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (y n) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f z) -
      (∑ m, lw m * ‖y n - y m‖ ^ 2) / 2 ≤ ⟪pre G n, y n - z⟫ := by
    have hs := sum_le_sum (fun m (_ : m ∈ univ) => hinner m)
    rw [← sum_inner, ← pre_full G, sum_sub_distrib, sum_sub_distrib] at hs
    have e1 : ∑ m, f (π m) (y n) = n * LongTails.Setups.FiniteSumSmoothAndConvex.objective f (y n) := by
      rw [← sum_objective]; exact Equiv.sum_comp π (fun i => f i (y n))
    have e2 : ∑ m, f (π m) z = n * LongTails.Setups.FiniteSumSmoothAndConvex.objective f z := by
      rw [← sum_objective]; exact Equiv.sum_comp π (fun i => f i z)
    have e3 : ∑ m, lw m / 2 * ‖y n - y m‖ ^ 2 = (∑ m, lw m * ‖y n - y m‖ ^ 2) / 2 := by
      rw [sum_div]; exact sum_congr rfl (fun m _ => by ring)
    rw [e1, e2, e3] at hs
    linarith
  have hD : ∑ m, lw m * ‖y n - y m‖ ^ 2 ≤ 2 * η ^ 2 * W + 2 * η ^ 2 * ρ ^ 2 * c := by
    have hs := sum_le_sum (fun m (_ : m ∈ univ) => mul_le_mul_of_nonneg_left (hdist m) (hlw0 m))
    have he : ∑ m, lw m * (2 * η ^ 2 * p m ^ 2 + 2 * η ^ 2 * ρ ^ 2) =
        2 * η ^ 2 * W + 2 * η ^ 2 * ρ ^ 2 * ∑ m, lw m := by
      have h1 : ∀ m ∈ univ, lw m * (2 * η ^ 2 * p m ^ 2 + 2 * η ^ 2 * ρ ^ 2) =
          2 * η ^ 2 * (lw m * p m ^ 2) + 2 * η ^ 2 * ρ ^ 2 * lw m := fun m _ => by ring
      show ∑ m, lw m * (2 * η ^ 2 * p m ^ 2 + 2 * η ^ 2 * ρ ^ 2) =
        2 * η ^ 2 * (∑ m, lw m * p m ^ 2) + 2 * η ^ 2 * ρ ^ 2 * ∑ m, lw m
      rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum, ← mul_sum]
    rw [he] at hs
    have := mul_le_mul_of_nonneg_left hlw (by positivity : (0 : ℝ) ≤ 2 * η ^ 2 * ρ ^ 2)
    linarith
  have hexp : ‖y n - z‖ ^ 2 ≤ ‖y 0 - z‖ ^ 2 - 2 * η * ⟪pre G n, y n - z⟫ := by
    have hpn := hpath n le_rfl
    have he : y 0 - z = (y n - z) + η • pre G n := by rw [hpn]; abel
    have hx : ‖y 0 - z‖ ^ 2 = ‖y n - z‖ ^ 2 + 2 * (η * ⟪y n - z, pre G n⟫) +
        ‖η • pre G n‖ ^ 2 := by
      rw [he, norm_add_sq_real, real_inner_smul_right]
    rw [real_inner_comm] at hx
    have := sq_nonneg ‖η • pre G n‖
    linarith
  have hcρ : c * ρ ^ 2 ≤ c * (8 * (2 * Lmax * (n : ℝ) ^ 2 * a) + 8 * η ^ 2 * (c * W)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have hηD : η * ∑ m, lw m * ‖y n - y m‖ ^ 2 ≤
      2 * η ^ 3 * (1 + 8 * (n * η) ^ 2 * Lavg ^ 2) * W + 32 * (n * η) ^ 3 * Lavg * Lmax * a := by
    have h1 := mul_le_mul_of_nonneg_left hD hη
    have h2 := mul_le_mul_of_nonneg_left hcρ (by positivity : (0 : ℝ) ≤ 2 * η ^ 3)
    have e1 : η * (2 * η ^ 2 * W + 2 * η ^ 2 * ρ ^ 2 * c) =
        2 * η ^ 3 * W + 2 * η ^ 3 * (c * ρ ^ 2) := by ring
    have e2 : 2 * η ^ 3 * W + 2 * η ^ 3 * (c * (8 * (2 * Lmax * (n : ℝ) ^ 2 * a) +
        8 * η ^ 2 * (c * W))) =
        2 * η ^ 3 * (1 + 8 * (n * η) ^ 2 * Lavg ^ 2) * W + 32 * (n * η) ^ 3 * Lavg * Lmax * a := by
      simp only [c]
      ring
    linarith
  have hI := mul_le_mul_of_nonneg_left hsumI (by positivity : (0 : ℝ) ≤ 2 * η)
  rw [hW]
  simp only [a] at hηD
  linarith

end Hyp

end OracleTemplate.ReshuffledConvex
