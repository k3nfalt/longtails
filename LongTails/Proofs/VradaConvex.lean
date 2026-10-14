import LongTails.Algorithms.Vrada
import LongTails.Proofs.AcceleratedFiniteSumStep

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.FiniteSum

open LongTails.Setups.FiniteSumSmoothAndConvex

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]

omit [NeZero n] [CompleteSpace E] in
lemma vradaInner_length (g : Fin n × E → E) (A a m : ℝ) (snapshot z : E) (seed : List (Fin n)) :
    (vradaInner g A a m snapshot z seed).2.length = seed.length := by
  induction seed generalizing z with
  | nil => rfl
  | cons i tail ih => simp only [vradaInner, List.length_cons, ih]

lemma vradaInner_bound {f : Fin n → E → ℝ} {g : Fin n × E → E} {L A a m : ℝ}
    (hL : 0 < L) (hA : 0 ≤ A) (ha : 0 < a) (hm : 0 < m)
    (hstep : 2 * L * a ^ 2 ≤ m * A)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (snapshot z u : E) (j : ℕ) :
    (𝔼 seed : Fin j → Fin n,
      let result := vradaInner g A a m snapshot z (List.ofFn seed)
      (A + a) * (result.2.map (fun x => objective f x - objective f u)).sum +
        m / 2 * ‖result.1 - u‖ ^ 2) ≤
      (j : ℝ) * A * (objective f snapshot - objective f u) + m / 2 * ‖z - u‖ ^ 2 := by
  induction j generalizing z with
  | zero => simp [vradaInner]
  | succ j ih =>
    rw [expect_tape_succ (fun seed =>
      let result := vradaInner g A a m snapshot z seed
      (A + a) * (result.2.map (fun x => objective f x - objective f u)).sum +
        m / 2 * ‖result.1 - u‖ ^ 2)]
    simp only [vradaInner, List.map_cons, List.sum_cons]
    let y := vradaMix A a snapshot z
    let next := fun i => z - (a / m) • estimator g snapshot y i
    have h := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      add_le_add (le_refl ((A + a) * (objective f (vradaMix A a snapshot (next i)) - objective f u)))
        (ih (next i)))
    have hs := accelerated_variance_reduced_step hL hA ha hm hstep hc hg hlip snapshot z u
    simp only [mul_add, Finset.expect_add_distrib, ← Finset.mul_expect,
      Finset.expect_sub_distrib, Fintype.expect_const, Nat.cast_add, Nat.cast_one] at h hs ⊢
    dsimp [next, y, vradaMix] at h ⊢
    linarith

lemma vradaEpoch_bound {f : Fin n → E → ℝ} {g : Fin n × E → E} {L A a : ℝ} {m : ℕ}
    (hL : 0 < L) (hA : 0 ≤ A) (ha : 0 < a) (hm : 0 < m)
    (hstep : 2 * L * a ^ 2 ≤ (m : ℝ) * A)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (snapshot z u : E) :
    (𝔼 seed : Fin m → Fin n,
      let result := vradaInner g A a m snapshot z (List.ofFn seed)
      (A + a) * (objective f ((m : ℝ)⁻¹ • result.2.sum) - objective f u) +
        1 / 2 * ‖result.1 - u‖ ^ 2) ≤
      A * (objective f snapshot - objective f u) + 1 / 2 * ‖z - u‖ ^ 2 := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hi := vradaInner_bound hL hA ha hmr hstep hc hg hlip snapshot z u m
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun (seed : Fin m → Fin n) _ => by
    let result := vradaInner g A a (m : ℝ) snapshot z (List.ofFn seed)
    have hlen : result.2.length = m := by simp [result, vradaInner_length]
    have hj := objective_list_average hc hg u result.2 (by omega)
    rw [hlen] at hj
    exact add_le_add (mul_le_mul_of_nonneg_left hj (show 0 ≤ A + a by positivity))
      (le_refl ((m : ℝ) / 2 * ‖result.1 - u‖ ^ 2)))
  have h := hav.trans hi
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at h ⊢
  nlinarith only [h, hmr]

lemma vradaWeight_pos {m : ℕ} {L : ℝ} (hL : 0 < L) (k : ℕ) : 0 < vradaWeight m L k := by
  induction k with
  | zero => exact one_div_pos.mpr hL
  | succ k ih => exact add_pos_of_pos_of_nonneg ih (Real.sqrt_nonneg _)

lemma vradaIncrement_pos {m : ℕ} {L : ℝ} (hL : 0 < L) (hm : 0 < m) (k : ℕ) :
    0 < vradaIncrement m L k := by
  unfold vradaIncrement
  exact Real.sqrt_pos.mpr (by have := vradaWeight_pos (m := m) hL k; positivity)

lemma vradaIncrement_sq {m : ℕ} {L : ℝ} (hL : 0 < L) (k : ℕ) :
    2 * L * vradaIncrement m L k ^ 2 = (m : ℝ) * vradaWeight m L k := by
  have h := vradaWeight_pos (m := m) hL k
  rw [vradaIncrement, Real.sq_sqrt (by positivity)]
  field_simp

lemma vradaRun_bound {f : Fin n → E → ℝ} {g : Fin n × E → E} {L : ℝ} {m : ℕ}
    (hL : 0 < L) (hm : 0 < m)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (u : E) (S k : ℕ) (z snapshot : E) :
    (𝔼 seed : VradaSeeds n m S,
      let result := vradaRun g L m S k z snapshot seed
      vradaWeight m L (k + S) * (objective f result.2 - objective f u) +
        1 / 2 * ‖result.1 - u‖ ^ 2) ≤
      vradaWeight m L k * (objective f snapshot - objective f u) + 1 / 2 * ‖z - u‖ ^ 2 := by
  induction S generalizing k z snapshot with
  | zero => simp [vradaRun]
  | succ S ih =>
    change (𝔼 seed : (Fin m → Fin n) × VradaSeeds n m S,
      let inner := vradaInner g (vradaWeight m L k) (vradaIncrement m L k) m snapshot z (List.ofFn seed.1)
      let result := vradaRun g L m S (k + 1) inner.1 ((m : ℝ)⁻¹ • inner.2.sum) seed.2
      vradaWeight m L (k + (S + 1)) * (objective f result.2 - objective f u) +
        1 / 2 * ‖result.1 - u‖ ^ 2) ≤ _
    rw [← Finset.univ_product_univ, Finset.expect_product]
    have h := Finset.expect_le_expect (s := Finset.univ) (fun (seed : Fin m → Fin n) _ =>
      ih (k + 1)
        (vradaInner g (vradaWeight m L k) (vradaIncrement m L k) m snapshot z (List.ofFn seed)).1
        ((m : ℝ)⁻¹ • (vradaInner g (vradaWeight m L k) (vradaIncrement m L k) m snapshot z (List.ofFn seed)).2.sum))
    have he := vradaEpoch_bound hL (vradaWeight_pos (m := m) hL k).le
      (vradaIncrement_pos hL hm k) hm (vradaIncrement_sq (m := m) hL k).le hc hg hlip snapshot z u
    apply le_trans ?_ he
    simpa only [show k + 1 + S = k + (S + 1) by omega, vradaWeight, vradaIncrement] using h

lemma vradaRun_rate {f : Fin n → E → ℝ} {g : Fin n × E → E} {L R : ℝ} {m : ℕ}
    (hL : 0 < L) (hR : 0 ≤ R) (hm : 0 < m)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    {u x0 : E} (hmin : IsMinOn (objective f) univ u) (hdist : ‖x0 - u‖ ≤ R) (S : ℕ) :
    (𝔼 seed : VradaSeeds n m S, (objective f (vradaRun g L m S 0 x0 x0 seed).2 - objective f u)) ≤
      R ^ 2 / vradaWeight m L S := by
  have h := vradaRun_bound hL hm hc hg hlip u S 0 x0 x0
  simp only [Nat.zero_add, Finset.expect_add_distrib, ← Finset.mul_expect] at h
  have hn := Finset.expect_nonneg (s := Finset.univ) (fun seed : VradaSeeds n m S => fun _ =>
    sq_nonneg ‖(vradaRun g L m S 0 x0 x0 seed).1 - u‖)
  have hg0 := initial_gap_bound hL hR hg hlip hmin hdist
  have hd : ‖x0 - u‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg (x0 - u)]
  apply (le_div_iff₀ (vradaWeight_pos hL S)).mpr
  rw [mul_comm]
  have hi : vradaWeight m L 0 * (objective f x0 - objective f u) ≤ R ^ 2 / 2 := by
    change (1 / L) * _ ≤ _
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hL).mpr
    nlinarith only [hg0]
  linarith

end OracleTemplate.FiniteSum
