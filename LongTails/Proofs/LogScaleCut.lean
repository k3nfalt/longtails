import LongTails.Algorithms.BlackBoxDiagonalAccelerated

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ}

lemma sqn_nonneg (v : Fin d → ℝ) : 0 ≤ sqn v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma Cut.val_convex (C : Cut d) (ha : ∀ k, 0 ≤ C.a k) (hb : ∀ k, 0 ≤ C.b k)
    (θ θ' : Fin d → ℝ) :
    C.val θ + ∑ k, C.grad θ k * (θ' k - θ k) ≤ C.val θ' := by
  unfold Cut.val Cut.grad
  have h1 : ∀ k, C.a k * Real.exp (-θ k) + (-(C.a k * Real.exp (-θ k))) * (θ' k - θ k) ≤
      C.a k * Real.exp (-θ' k) := by
    intro k
    have e : Real.exp (-θ' k) = Real.exp (-θ k) * Real.exp (-(θ' k - θ k)) := by
      rw [← Real.exp_add]; ring_nf
    have hx := Real.add_one_le_exp (-(θ' k - θ k))
    have hp := Real.exp_pos (-θ k)
    rw [e]
    have := mul_le_mul_of_nonneg_left hx (mul_nonneg (ha k) hp.le)
    nlinarith
  have h2 : ∀ k, C.b k * Real.exp (θ k) + (C.b k * Real.exp (θ k)) * (θ' k - θ k) ≤
      C.b k * Real.exp (θ' k) := by
    intro k
    have e : Real.exp (θ' k) = Real.exp (θ k) * Real.exp (θ' k - θ k) := by
      rw [← Real.exp_add]; ring_nf
    have hx := Real.add_one_le_exp (θ' k - θ k)
    have hp := Real.exp_pos (θ k)
    rw [e]
    have := mul_le_mul_of_nonneg_left hx (mul_nonneg (hb k) hp.le)
    nlinarith
  have s1 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => h1 k
  have s2 := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => h2 k
  simp only [Finset.sum_add_distrib] at s1 s2
  have e3 : ∑ k, (-(C.a k * Real.exp (-θ k)) + C.b k * Real.exp (θ k)) * (θ' k - θ k) =
      ∑ k, (-(C.a k * Real.exp (-θ k))) * (θ' k - θ k) +
        ∑ k, (C.b k * Real.exp (θ k)) * (θ' k - θ k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e3]
  linarith

lemma clamp_sq_le {lo hi c t : ℝ} (h1 : lo ≤ c) (h2 : c ≤ hi) :
    (max lo (min hi t) - c) ^ 2 ≤ (t - c) ^ 2 := by
  rcases le_total t hi with h | h
  · rw [min_eq_right h]
    rcases le_total lo t with h' | h'
    · rw [max_eq_right h']
    · rw [max_eq_left h']; nlinarith
  · rw [min_eq_left h]
    rw [max_eq_right (le_trans h1 h2)]
    nlinarith

lemma cut_progress (C : Cut d) (ha : ∀ k, 0 ≤ C.a k) (hb : ∀ k, 0 ≤ C.b k)
    {lo hi θ θc : Fin d → ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ θ', sqn (fun k => θ' k - θc k) ≤ r ^ 2 → C.val θ' ≤ 0)
    (hlo : ∀ k, lo k ≤ θc k) (hhi : ∀ k, θc k ≤ hi k)
    (hviol : 0 < C.val θ) :
    sqn (fun k => cutStep lo hi r C θ k - θc k) ≤ sqn (fun k => θ k - θc k) - r ^ 2 := by
  set g := C.grad θ
  have hg : 0 < sqn g := by
    rcases (sqn_nonneg g).lt_or_eq with h | h
    · exact h
    · exfalso
      have hc := hball θc (by
        have h0 : sqn (fun k => θc k - θc k) = 0 := by simp [sqn]
        rw [h0]; positivity)
      have hcv := C.val_convex ha hb θ θc
      have hz : ∀ k, g k = 0 := by
        intro k
        have : g k ^ 2 = 0 := by
          have hle : g k ^ 2 ≤ sqn g :=
            Finset.single_le_sum (f := fun k => g k ^ 2) (fun j _ => sq_nonneg _)
              (Finset.mem_univ k)
          linarith [sq_nonneg (g k)]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have : ∑ k, C.grad θ k * (θc k - θ k) = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [show C.grad θ k = g k from rfl, hz k, zero_mul]
      linarith
  set n := Real.sqrt (sqn g)
  have hn : 0 < n := Real.sqrt_pos.mpr hg
  have hn2 : n ^ 2 = sqn g := Real.sq_sqrt (sqn_nonneg g)
  set p : Fin d → ℝ := fun k => θc k + r * g k / n
  have hp : sqn (fun k => p k - θc k) ≤ r ^ 2 := by
    have : sqn (fun k => p k - θc k) = r ^ 2 / n ^ 2 * sqn g := by
      unfold sqn
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [p]
      field_simp
      ring
    rw [this, hn2, div_mul_cancel₀ _ hg.ne']
  have hpv := hball p hp
  have hcv := C.val_convex ha hb θ p
  have hlin : r * n < ∑ k, g k * (θ k - θc k) := by
    have h1 : ∑ k, g k * (p k - θ k) = r * n - ∑ k, g k * (θ k - θc k) := by
      have : ∑ k, g k * (p k - θ k) =
          r / n * sqn g - ∑ k, g k * (θ k - θc k) := by
        unfold sqn
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [p]
        field_simp
        ring
      rw [this, ← hn2]
      field_simp
    have : ∑ k, C.grad θ k * (p k - θ k) = ∑ k, g k * (p k - θ k) := rfl
    linarith
  have hunc : sqn (fun k => (θ k - r * g k / n) - θc k) ≤ sqn (fun k => θ k - θc k) - r ^ 2 := by
    have e : sqn (fun k => (θ k - r * g k / n) - θc k) =
        sqn (fun k => θ k - θc k) - 2 * r / n * ∑ k, g k * (θ k - θc k) +
          r ^ 2 / n ^ 2 * sqn g := by
      unfold sqn
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      field_simp
      ring
    rw [e, ← hn2, div_mul_cancel₀ _ (by positivity : n ^ 2 ≠ 0)]
    have : 2 * r / n * (r * n) ≤ 2 * r / n * ∑ k, g k * (θ k - θc k) :=
      mul_le_mul_of_nonneg_left hlin.le (by positivity)
    have e2 : 2 * r / n * (r * n) = 2 * r ^ 2 := by field_simp
    linarith
  refine le_trans ?_ hunc
  unfold sqn cutStep clampBox
  refine Finset.sum_le_sum fun k _ => ?_
  exact clamp_sq_le (hlo k) (hhi k)

end OracleTemplate.BlackBoxDiagonal
