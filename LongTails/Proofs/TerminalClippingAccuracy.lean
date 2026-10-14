import LongTails.Proofs.TerminalClippingPathwise
import LongTails.Proofs.TerminalClippingSquare

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

lemma martingale_sum_bound {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (P : ProbabilityMeasure Ω) (u : Vector q.d) {D : ℝ}
    (hB : 0 < q.B) (hD : 0 < D) (hT : 0 < q.T)
    (s : ℕ → ℕ × (Vector q.d × Vector q.d)) (ξ : ℕ → Ω)
    (hevent : (∑ t ∈ Finset.range q.T, martingaleIncrement q g P u D (s t) (ξ t)) ≤ Real.log (8 / q.δ)) :
    (∑ t ∈ Finset.range q.T,
      (-⟪clippedSample q g (s t) (ξ t) - ∫ ω, clippedSample q g (s t) ω ∂(P : Measure Ω),
        residualInfluence q u (s t)⟫ - q.B * Real.sqrt q.T * ‖residualInfluence q u (s t)‖ ^ 2)) ≤
      400 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T := by
  let τ := Real.sqrt q.T / (400 * q.B * D)
  let Y := fun t => -⟪clippedSample q g (s t) (ξ t) - ∫ ω, clippedSample q g (s t) ω ∂(P : Measure Ω),
    residualInfluence q u (s t)⟫
  let V := fun t => ‖residualInfluence q u (s t)‖ ^ 2
  have ht : 0 < Real.sqrt q.T := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have he : (∑ t ∈ Finset.range q.T, martingaleIncrement q g P u D (s t) (ξ t)) =
      τ * (∑ t ∈ Finset.range q.T, Y t) - τ ^ 2 * (26 * q.B ^ 2 * D) * (∑ t ∈ Finset.range q.T, V t) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    dsimp [martingaleIncrement, τ, Y, V]
    ring
  rw [he] at hevent
  have hh : (∑ t ∈ Finset.range q.T, Y t) - τ * (26 * q.B ^ 2 * D) * (∑ t ∈ Finset.range q.T, V t) ≤
      Real.log (8 / q.δ) / τ := by
    apply (le_div_iff₀ hτ).mpr
    nlinarith
  have hv : 0 ≤ ∑ t ∈ Finset.range q.T, V t := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_right (martingale_compensation_bound (T := q.T) hB hD) hv
  have hr : Real.log (8 / q.δ) / τ = 400 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T := by
    dsimp [τ]
    field_simp

  rw [hr] at hh
  change (∑ t ∈ Finset.range q.T, (Y t - q.B * Real.sqrt q.T * V t)) ≤ _
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

lemma square_sum_bound {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) {D : ℝ}
    (hB : 0 < q.B) (hD : 0 < D) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    (s : ℕ → ℕ × (Vector q.d × Vector q.d)) (ξ : ℕ → Ω)
    (hevent : (∑ t ∈ Finset.range q.T, squareIncrement q g D (s t) (ξ t)) ≤ Real.log (8 / q.δ)) :
    (∑ t ∈ Finset.range q.T, squareWeight q (s t).1 * ‖clippedSample q g (s t) (ξ t)‖ ^ 2) ≤
      q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T := by
  have hH := squareScale_pos q D hB hD hδ hδ1 hT
  have ht : (q.T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hT)
  simp only [squareIncrement, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hevent
  have he : (q.T : ℝ) * 2 / q.T = 2 := by field_simp
  rw [he] at hevent
  have hh := (div_le_iff₀ hH).mp (show
      (∑ t ∈ Finset.range q.T, squareWeight q (s t).1 * ‖clippedSample q g (s t) (ξ t)‖ ^ 2) / squareScale q D ≤
        Real.log (8 / q.δ) + 2 by linarith)
  exact hh.trans (by simpa only [add_comm, mul_comm] using squareScale_accuracy_bound q hB hD.le hδ hδ1 hT)

lemma trajectory_accuracy_on_events {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure Ω) (ξ : ℕ → Ω) (hg : Measurable (Function.uncurry g))
    (hB : 0 < q.B) (hG : 0 < q.G) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} {f : Vector q.d → ℝ} (hf : ConvexOn ℝ X f)
    (hx0 : q.x0 ∈ X) (hpX : ∀ y, projection y ∈ X)
    (hp : ∀ y, ∀ v ∈ X, ⟪y - projection y, v - projection y⟫ ≤ 0)
    (hsub : ∀ x ∈ X, ∀ y ∈ X, f x - f y ≤ ⟪∫ ω, g x ω ∂(P : Measure Ω), x - y⟫)
    (hgi : ∀ x ∈ X, Integrable (g x) (P : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (P : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(P : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    {u : Vector q.d} (hu : u ∈ X) {D : ℝ} (hD : 0 < D)
    (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D)
    (hradius : ∀ t ≤ q.T, ‖(trajectory q g projection ξ t).2.1 - u‖ ^ 2 ≤ 16 * D)
    (hmart : (∑ t ∈ Finset.range q.T, martingaleIncrement q g P u D (trajectory q g projection ξ t) (ξ t)) ≤
      Real.log (8 / q.δ))
    (hsquare : (∑ t ∈ Finset.range q.T, squareIncrement q g D (trajectory q g projection ξ t) (ξ t)) ≤
      Real.log (8 / q.δ)) :
    f (trajectory q g projection ξ q.T).2.1 - f u ≤
      16384 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T := by
  let s := trajectory q g projection ξ
  let V := fun t => residualInfluence q u (s t)
  let c := fun t => clippedSample q g (s t) (ξ t)
  let m := fun t => ∫ ω, clippedSample q g (s t) ω ∂(P : Measure Ω)
  let h := fun t => ∫ ω, g (s t).2.1 ω ∂(P : Measure Ω)
  let b := fun t => ⟪h t - m t, V t⟫
  let Y := fun t => -⟪c t - m t, V t⟫
  let v := fun t => ‖V t‖ ^ 2
  let Z := fun t => squareWeight q t * ‖c t‖ ^ 2
  let K := fun t => squareWeight q t * (18 * q.B ^ 2 * D)
  let N := fun t => ‖(s t).2.1 - pathComparator q u (s t)‖ ^ 2 /
    (4 * q.T * tailWeight q.B q.δ q.T (t - 1))
  let I := weight q.T 0 * (‖q.x0 - u‖ ^ 2 / (2 * tailWeight q.B q.δ q.T 0))
  let F := q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T
  have hq := confidence_ge_one hδ hδ1
  have hqp := confidence_pos hδ hδ1
  have ht : 0 < (q.T : ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt q.T := Real.sqrt_pos.mpr ht
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hx (t : ℕ) : (s t).2.1 ∈ X := trajectory_feasible q g projection hx0 hpX ξ t
  have hr0 : ‖q.x0 - u‖ ≤ Real.sqrt D := by
    nlinarith [Real.sq_sqrt hD.le, Real.sqrt_nonneg D, norm_nonneg (q.x0 - u)]
  have hd : ‖u - q.x0‖ ≤ Real.sqrt D := by rw [norm_sub_rev]; exact hr0
  have hb (t : ℕ) (ht' : t < q.T) : b t ≤
      2 * q.B * Real.sqrt q.T * v t + 26 * q.B * D / ((q.T : ℝ) * Real.sqrt q.T) := by
    have hlocal := radius_geometry hD.le (Real.sqrt_nonneg D) (Real.sq_sqrt hD.le).le hr0 (hradius t ht'.le)
    have hc : 0 ≤ weight q.T t * stepSize q.B q.δ q.T t / tailWeight q.B q.δ q.T 0 := by
      have hw : 0 ≤ weight q.T t := by linarith [(weight_bounds ht').1]
      exact div_nonneg (mul_nonneg hw (stepSize_pos hB hδ hδ1 ht').le)
        (tailWeight_pos hB hδ hδ1 hT).le
    have hgs : Measurable (g (s t).2.1) := hg.comp (measurable_const.prodMk measurable_id)
    have hh := influence_bias_local hgs (hgi _ (hx t)) (hmi _ (hx t)) hB hG hD.le hT
      hc (optimizer_influence_bound hB hδ hδ1 ht') hGD ((s t).2.1 - q.x0)
      (observableInfluence q (s t)) (u - q.x0) hlocal hd (hm _ (hx t))
    simpa only [b, h, m, V, v, residualInfluence, clippedSample, s, trajectory_time] using hh
  have hbSum := Finset.sum_le_sum (s := Finset.range q.T) (fun t ht' => hb t (Finset.mem_range.mp ht'))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbSum
  have hbConst : (q.T : ℝ) * (26 * q.B * D / ((q.T : ℝ) * Real.sqrt q.T)) ≤ 26 * F := by
    have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ 26 * q.B * D / Real.sqrt q.T by positivity)
    dsimp [F]
    convert hh using 1 <;> field_simp
  have hM : (∑ t ∈ Finset.range q.T, (Y t - q.B * Real.sqrt q.T * v t)) ≤ 400 * F := by
    convert martingale_sum_bound q g P u hB hD hT s ξ hmart using 1; (try dsimp [F]); ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hM
  have hZ := square_sum_bound q g hB hD hδ hδ1 hT s ξ hsquare
  change (∑ t ∈ Finset.range q.T, squareWeight q (s t).1 * ‖c t‖ ^ 2) ≤ F at hZ
  simp only [s, trajectory_time] at hZ
  change (∑ t ∈ Finset.range q.T, Z t) ≤ F at hZ
  have hA : (∑ t ∈ Finset.range q.T, (3 * q.B * Real.sqrt q.T * v t - N (t + 1))) ≤ 48 * F := by
    convert trajectory_absorption q g projection ξ u hB hδ hδ1 hT hD.le hstart using 1
    · apply Finset.sum_congr rfl
      intro t _
      simp [N, s, v, V]
    · dsimp [F]
      ring
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hA
  have hI : I ≤ 8192 * F := by
    convert initial_energy_bound hB hδ hδ1 hT hD.le hstart using 1; (try dsimp [F]); ring
  have hK : (∑ t ∈ Finset.range q.T, K t) ≤ F := by
    have hh := Finset.sum_le_sum (s := Finset.range q.T) (fun t ht' =>
      deterministic_cost_step_bound hB hδ hδ1 (Finset.mem_range.mp ht') hD.le)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hh
    apply hh.trans_eq
    dsimp [F]
    field_simp
  have hraw := trajectory_descent q g projection P ξ hB hδ hδ1 hT hf hx0 hpX hp hsub hgi hmi hm
    hu hD.le hstart hGD hradius
  have he (t : ℕ) : ⟪h t - c t, V t⟫ = b t + Y t := by
    dsimp [b, Y]
    simp only [inner_sub_left]
    ring
  have hdes : f (s q.T).2.1 - f u ≤ I +
      ∑ t ∈ Finset.range q.T, (-N (t + 1) + K t + Z t + b t + Y t) := by
    convert hraw using 1
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    rw [show -N (t + 1) + K t + Z t + b t + Y t = -N (t + 1) + K t + Z t + (b t + Y t) by ring, ← he]
    dsimp [N, K, Z, squareWeight, c, V, h, I, s]
    ring
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at hdes
  have hfinal : f (s q.T).2.1 - f u ≤ 16384 * F := by linarith
  convert hfinal using 1; (try dsimp [F]); ring

end OracleTemplate.TerminalClipping
