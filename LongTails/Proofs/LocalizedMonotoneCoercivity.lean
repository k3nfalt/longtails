import LongTails.Proofs.LocalizedMonotoneConstruction
import LongTails.Proofs.KernelPerceptronBridge

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.LocalizedMonotoneCoercivity

open LocalizedMonotoneConstruction LocalizedMonotoneProfile LocalizedMonotoneChain
open LocalizedMonotoneRadial

lemma norm_bound_from_hidden {d m : ℕ} (π : Fin m ↪ Fin d)
    (x e : EuclideanSpace ℝ (Fin d)) (B : ℝ) (hB : 0 ≤ B)
    (hhidden : ∀ j, |x (π j)| ≤ B)
    (houtside : ∀ i, (∀ j, i ≠ π j) → x i = e i) :
    ‖x‖ ≤ Real.sqrt m * B + ‖e‖ := by
  classical
  let S := Finset.univ.map π
  have hS : S.card = m := by simp [S]
  have hpoint (i : Fin d) : x i ^ 2 ≤ (if i ∈ S then B ^ 2 else 0) + e i ^ 2 := by
    by_cases hi : i ∈ S
    · obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hi
      have hh := pow_le_pow_left₀ (abs_nonneg (x (π j))) (hhidden j) 2
      rw [sq_abs, hj] at hh
      rw [ite_eq_left hi]
      nlinarith [sq_nonneg (e i)]
    · have he : x i = e i := houtside i (by
        intro j hij
        apply hi
        exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hij.symm⟩)
      simp only [ite_eq_right hi, zero_add, he, le_refl]
  have hsum : (∑ i : Fin d, if i ∈ S then B ^ 2 else 0) = m * B ^ 2 := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
    rw [he]
    simp [hS]
  have hsq : ‖x‖ ^ 2 ≤ m * B ^ 2 + ‖e‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    rw [Finset.sum_add_distrib, hsum] at h
    exact h
  have hs : (Real.sqrt m * B) ^ 2 = m * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hn : 0 ≤ Real.sqrt m * B := mul_nonneg (Real.sqrt_nonneg _) hB
  nlinarith [norm_nonneg x, norm_nonneg e, mul_nonneg hn (norm_nonneg e)]

lemma coordinate_abs_sum_bound {d m : ℕ} (π : Fin m ↪ Fin d)
    (e : EuclideanSpace ℝ (Fin d)) :
    ∑ j : Fin m, |e (π j)| ≤ Real.sqrt m * ‖e‖ := by
  have h := LongTails.Proofs.KernelPerceptronGeometry.sum_abs_le_sqrt
    (FiniteSumNondualLowerComponents.coordinateMap π e)
  exact h.trans (mul_le_mul_of_nonneg_left
    (FiniteSumNondualLowerComponents.coordinateMap_norm π e) (Real.sqrt_nonneg _))

noncomputable def extendSequence {n : ℕ} (s : Fin (n + 1) → ℝ) (i : ℕ) : ℝ :=
  if h : i < n + 1 then s ⟨i, h⟩ else 0

lemma extendSequence_fin {n : ℕ} (s : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    extendSequence s j.val = s j := by simp [extendSequence, j.isLt]

lemma extendSequence_sum {n : ℕ} (H : ℝ → ℝ) (s : Fin (n + 1) → ℝ) :
    (∑ i ∈ Finset.range n, |extendSequence s (i + 1) - H (extendSequence s i)|) =
      ∑ j : Fin n, |s j.succ - H (s j.castSucc)| := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  change |extendSequence s j.succ.val - H (extendSequence s j.castSucc.val)| = _
  rw [extendSequence_fin, extendSequence_fin]

lemma finite_coordinate_bound {n : ℕ} (H : ℝ → ℝ) (hmono : Monotone H)
    (h0 : H 0 = 0) (hH : ∀ x y, |H x - H y| ≤ |x - y|)
    (s : Fin (n + 1) → ℝ) (c : ℝ) (hc : 0 ≤ c) (j : Fin (n + 1)) :
    |s j| ≤ c + 2 * (|s 0 + H (s (Fin.last n)) - c| +
      ∑ i : Fin n, |s i.succ - H (s i.castSucc)|) := by
  have h := negative_wrap_coordinate_bound H hmono h0 hH (extendSequence s) n c hc
    j.val (Nat.le_of_lt_succ j.isLt)
  change |extendSequence s j.val| ≤ c + 2 *
    (|extendSequence s (0 : Fin (n + 1)).val + H (extendSequence s (Fin.last n).val) - c| +
      ∑ i ∈ Finset.range n, |extendSequence s (i + 1) - H (extendSequence s i)|) at h
  simpa only [extendSequence_fin, extendSequence_sum] using h

lemma chain_radial_coercivity {d n : ℕ} (a c t : ℝ) (ha : 0 < a) (hc : 0 ≤ c)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (π : Fin (n + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ≤ Real.sqrt (n + 1) * c + (2 * (n + 1) + 1) * ‖x - chain a c π (t • x)‖ := by
  let H : ℝ → ℝ := fun u => profile a (t * u)
  let s : Fin (n + 1) → ℝ := fun j => x (π j)
  let e := x - chain a c π (t • x)
  have hmono : Monotone H := by
    intro u v huv
    exact profile_monotone a ha (mul_le_mul_of_nonneg_left huv ht)
  have h0 : H 0 = 0 := by
    simpa only [H, mul_zero] using (profile_flat a 0 ha (by simpa using ha.le)).1
  have hH (u v : ℝ) : |H u - H v| ≤ |u - v| := by
    have h := profile_difference a (t * u) (t * v) ha
    rw [← mul_sub, abs_mul, abs_of_nonneg ht] at h
    exact h.trans (by nlinarith [abs_nonneg (u - v)])
  have he : |s 0 + H (s (Fin.last n)) - c| +
      (∑ i : Fin n, |s i.succ - H (s i.castSucc)|) = ∑ j : Fin (n + 1), |e (π j)| := by
    rw [Fin.sum_univ_succ]
    congr 1
    · dsimp [s, H, e]
      rw [chain_zero]
      simp only [PiLp.smul_apply, smul_eq_mul]
      congr 1
      ring
    · apply Finset.sum_congr rfl
      intro j _
      dsimp [s, H, e]
      rw [chain_succ]
      simp only [PiLp.smul_apply, smul_eq_mul]
  have hsum := coordinate_abs_sum_bound π e
  push_cast at hsum
  have hcoord (j : Fin (n + 1)) : |x (π j)| ≤ c + 2 * (Real.sqrt (n + 1) * ‖e‖) := by
    have h := finite_coordinate_bound H hmono h0 hH s c hc j
    rw [he] at h
    change |x (π j)| ≤ _ at h
    linarith
  have h := norm_bound_from_hidden π x e (c + 2 * (Real.sqrt (n + 1) * ‖e‖))
    (by positivity) hcoord (by
      intro i hi
      dsimp [e]
      rw [chain_outside a c π (t • x) i hi, sub_zero])
  push_cast at h
  have hsq : (Real.sqrt (n + 1 : ℕ)) ^ 2 = (n + 1 : ℕ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp := congrArg (fun z : ℝ => z * ‖e‖) hsq
  change ‖x‖ ≤ Real.sqrt (n + 1) * c + (2 * (n + 1) + 1) * ‖e‖
  push_cast at hp
  nlinarith

lemma extendSequence_signed_sum {n : ℕ} (H : ℝ → ℝ) (s : Fin (n + 1) → ℝ) :
    (∑ i ∈ Finset.range n, (extendSequence s (i + 1) - H (extendSequence s i))) =
      ∑ j : Fin n, (s j.succ - H (s j.castSucc)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  change extendSequence s j.succ.val - H (extendSequence s j.castSucc.val) = _
  rw [extendSequence_fin, extendSequence_fin]

lemma chain_terminal_sum {d n : ℕ} (a c : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : |x (π (Fin.last n))| ≤ a) :
    (∑ j : Fin (n + 1), (x - chain a c π x) (π j)) ≤ a - c + n * (3 * a / 2) := by
  let s : Fin (n + 1) → ℝ := fun j => x (π j)
  have hgap (u : ℝ) : u - profile a u ≤ 3 * a / 2 := (abs_le.mp (profile_gap a u ha)).2
  have hf : profile a (extendSequence s n) = 0 := by
    change profile a (extendSequence s (Fin.last n).val) = 0
    rw [extendSequence_fin]
    exact (profile_flat a _ ha hx).1
  have hs : extendSequence s n ≤ a := by
    change extendSequence s (Fin.last n).val ≤ a
    rw [extendSequence_fin]
    exact (abs_le.mp hx).2
  have h := negative_wrap_terminal_bound (profile a) (extendSequence s) n a (3 * a / 2) c hgap hf hs
  change (extendSequence s (0 : Fin (n + 1)).val +
      profile a (extendSequence s (Fin.last n).val) - c) +
      (∑ i ∈ Finset.range n, (extendSequence s (i + 1) - profile a (extendSequence s i))) ≤ _ at h
  rw [extendSequence_fin, extendSequence_fin, extendSequence_signed_sum] at h
  rw [Fin.sum_univ_succ]
  simp only [PiLp.sub_apply, chain_zero, chain_succ]
  dsimp [s] at h
  linarith

lemma chain_terminal_residual {d n : ℕ} (a c : ℝ) (ha : 0 < a)
    (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hx : |x (π (Fin.last n))| ≤ a) :
    c - a - n * (3 * a / 2) ≤ Real.sqrt (n + 1) * ‖x - chain a c π x‖ := by
  have h := chain_terminal_sum a c ha π x hx
  have hs := coordinate_abs_sum_bound π (x - chain a c π x)
  have hn : -(∑ j : Fin (n + 1), (x - chain a c π x) (π j)) ≤
      ∑ j : Fin (n + 1), |(x - chain a c π x) (π j)| := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun j _ => neg_le_abs _)
  push_cast at hs
  linarith

lemma localized_residual_lower {d n : ℕ} (a b c η : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (π : Fin (n + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (hcoerce : Real.sqrt (n + 1) * c + (2 * (n + 1) + 1) * η ≤ b)
    (hgap : Real.sqrt (n + 1) * η ≤ c - a - n * (3 * a / 2))
    (hhidden : ‖x‖ ≤ b → |x (π (Fin.last n))| ≤ a) :
    η ≤ ‖x - chain a c π (radial b x)‖ := by
  by_contra h
  push Not at h
  obtain ⟨t, ht, ht1, he⟩ := radial_contraction_factor b hb x
  have hbound := chain_radial_coercivity a c t ha hc ht ht1 π x
  rw [← he] at hbound
  have hn : 0 ≤ (2 * ((n : ℝ) + 1) + 1) := by positivity
  have hsmall : ‖x‖ ≤ b := by
    have hm := mul_le_mul_of_nonneg_left h.le hn
    linarith
  have hid := radial_eq_self b x hsmall
  rw [hid] at h
  have hterm := chain_terminal_residual a c ha π x (hhidden hsmall)
  have hpos : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have hstrict := mul_lt_mul_of_pos_left h hpos
  linarith

end LongTails.Proofs.LocalizedMonotoneCoercivity
