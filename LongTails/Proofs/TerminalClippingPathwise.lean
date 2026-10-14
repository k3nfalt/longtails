import LongTails.Proofs.TerminalClippingMartingale
import LongTails.Proofs.TerminalClippingTelescope

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

noncomputable def pathComparator (q : Public) (u : Vector q.d)
    (s : ℕ × (Vector q.d × Vector q.d)) : Vector q.d :=
  q.x0 + s.2.2 + (tailWeight q.B q.δ q.T (s.1 - 1) / tailWeight q.B q.δ q.T 0) • (u - q.x0)

lemma trajectory_comparator_initial {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (u : Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T) :
    pathComparator q u (trajectory q g projection ξ 0) = u := by
  have hs := (tailWeight_pos hB hδ hδ1 hT).ne'
  simp [pathComparator, trajectory, hs]

lemma trajectory_comparator_update {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (u : Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) {t : ℕ} (ht : t < q.T) :
    pathComparator q u (trajectory q g projection ξ (t + 1)) =
      (tailWeight q.B q.δ q.T t / tailWeight q.B q.δ q.T (t - 1)) •
        pathComparator q u (trajectory q g projection ξ t) +
      (1 - tailWeight q.B q.δ q.T t / tailWeight q.B q.δ q.T (t - 1)) •
        (trajectory q g projection ξ t).2.1 := by
  simp only [pathComparator, trajectory_time]
  change q.x0 + nextAuxiliary q.B q.δ q.T (trajectory q g projection ξ t).1
    ((trajectory q g projection ξ t).2.1 - q.x0) (trajectory q g projection ξ t).2.2 + _ = _
  rw [trajectory_time]
  exact auxiliary_comparator_update hB hδ hδ1 ht _ _ _ _

lemma trajectory_descent {Ω : Type*} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure Ω) (ξ : ℕ → Ω)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {X : Set (Vector q.d)} {f : Vector q.d → ℝ} (hf : ConvexOn ℝ X f)
    (hx0 : q.x0 ∈ X) (hpX : ∀ y, projection y ∈ X)
    (hp : ∀ y, ∀ v ∈ X, ⟪y - projection y, v - projection y⟫ ≤ 0)
    (hsub : ∀ x ∈ X, ∀ y ∈ X, f x - f y ≤ ⟪∫ ω, g x ω ∂(P : Measure Ω), x - y⟫)
    (hgi : ∀ x ∈ X, Integrable (g x) (P : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖ ^ 2) (P : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖ ^ 2 ∂(P : Measure Ω)) ≤
      q.B ^ 2 * ‖x - q.x0‖ ^ 2 + q.G ^ 2)
    {u : Vector q.d} (hu : u ∈ X) {D : ℝ} (hD : 0 ≤ D)
    (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) (hGD : q.G ^ 2 ≤ q.B ^ 2 * D)
    (hradius : ∀ t ≤ q.T, ‖(trajectory q g projection ξ t).2.1 - u‖ ^ 2 ≤ 16 * D) :
    f (trajectory q g projection ξ q.T).2.1 - f u ≤
      weight q.T 0 * (‖q.x0 - u‖ ^ 2 / (2 * tailWeight q.B q.δ q.T 0)) +
      ∑ t ∈ Finset.range q.T,
        (-‖(trajectory q g projection ξ (t + 1)).2.1 -
            pathComparator q u (trajectory q g projection ξ (t + 1))‖ ^ 2 /
            (4 * q.T * tailWeight q.B q.δ q.T t) +
          (weight q.T t * (stepSize q.B q.δ q.T t) ^ 2 / tailWeight q.B q.δ q.T t) *
            (18 * q.B ^ 2 * D + ‖clippedSample q g (trajectory q g projection ξ t) (ξ t)‖ ^ 2) +
          ⟪(∫ ω, g (trajectory q g projection ξ t).2.1 ω ∂(P : Measure Ω)) -
              clippedSample q g (trajectory q g projection ξ t) (ξ t),
            residualInfluence q u (trajectory q g projection ξ t)⟫) := by
  let x := fun t => (trajectory q g projection ξ t).2.1
  let z := fun t => pathComparator q u (trajectory q g projection ξ t)
  let θ := fun t => tailWeight q.B q.δ q.T t / tailWeight q.B q.δ q.T (t - 1)
  let H : ℕ → ℝ := fun n => Nat.rec (f u) (fun t a => θ t * a + (1 - θ t) * f (x t)) n
  let c := fun t => clippedSample q g (trajectory q g projection ξ t) (ξ t)
  let h := fun t => ∫ ω, g (x t) ω ∂(P : Measure Ω)
  have hz0 : z 0 = u := trajectory_comparator_initial q g projection ξ u hB hδ hδ1 hT
  have hx (t : ℕ) : x t ∈ X := trajectory_feasible q g projection hx0 hpX ξ t
  have hz (t : ℕ) (ht : t < q.T) : z (t + 1) = θ t • z t + (1 - θ t) • x t :=
    trajectory_comparator_update q g projection ξ u hB hδ hδ1 ht
  have hH (t : ℕ) : H (t + 1) = θ t * H t + (1 - θ t) * f (x t) := rfl
  have hmajor (n : ℕ) (hn : n ≤ q.T) : z n ∈ X ∧ f (z n) ≤ H n := by
    apply convex_comparator_upper hf x z H θ n (fun t _ => hx t)
    · rwa [hz0]
    · simp only [hz0, H, Nat.rec_zero, le_refl]
    · intro t ht
      exact comparator_ratio_bounds hB hδ hδ1 (by omega)
    · intro t ht
      exact hz t (by omega)
    · intro t _
      exact hH t
  have hxupdate (t : ℕ) : x (t + 1) = projection (x t - stepSize q.B q.δ q.T t • c t) :=
    trajectory_clipped_update q g projection ξ t
  have hr0 : ‖q.x0 - u‖ ≤ Real.sqrt D := by
    nlinarith [Real.sq_sqrt hD, Real.sqrt_nonneg D, norm_nonneg (q.x0 - u)]
  have hlocal (t : ℕ) (ht : t ≤ q.T) : ‖x t - q.x0‖ ≤ 5 * Real.sqrt D :=
    radius_geometry hD (Real.sqrt_nonneg D) (Real.sq_sqrt hD).le hr0 (hradius t ht)
  have hbound (t : ℕ) (ht : t ≤ q.T) :
      (∫ ω, ‖g (x t) ω‖ ^ 2 ∂(P : Measure Ω)) ≤ (6 * q.B * Real.sqrt D) ^ 2 := by
    have hh := (hm _ (hx t)).trans (local_moment_bound hD hGD (hlocal t ht))
    rw [mul_pow, mul_pow, Real.sq_sqrt hD]
    nlinarith [mul_nonneg (sq_nonneg q.B) hD]
  have hh := schedule_terminal_descent hB hδ hδ1 hT x z h c H (fun _ => 6 * q.B * Real.sqrt D)
    (fun _ _ => by positivity) hz (fun t _ => hH t)
    (fun t ht => by
      rw [hxupdate]
      exact projection_distance (hp _ _ (hmajor (t + 1) (by omega)).1))
    (fun t ht => by
      rw [hxupdate]
      exact projection_step (stepSize_pos hB hδ hδ1 ht).le (hp _ _ (hx t)))
    (fun t ht => hsub _ (hx t) _ (hmajor (t + 1) (by omega)).1)
    (fun t ht => objective_difference_from_moment (hgi _ (hx (t + 1))) (hmi _ (hx (t + 1)))
      (by positivity) (hbound (t + 1) (by omega)) (hsub _ (hx (t + 1)) _ (hx t)))
    (fun t ht => (hmajor (t + 1) (by omega)).2)
  change f (x q.T) - f u ≤ _
  change f (x q.T) - f u ≤ _ at hh
  convert hh using 1
  rw [hz0, show x 0 = q.x0 by rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have he := comparator_influence_decomposition hB hδ hδ1 ht'
    (x t) q.x0 (trajectory q g projection ξ t).2.2 u
  dsimp [x, z, c, h, residualInfluence, observableInfluence, pathComparator] at *
  simp only [trajectory_time] at *
  rw [he]
  congr 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hD]
  ring

lemma trajectory_influence_identity {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (u : Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) {t : ℕ} (ht : t < q.T) :
    residualInfluence q u (trajectory q g projection ξ t) =
      influenceScale q.B q.δ q.T t •
        ((trajectory q g projection ξ t).2.1 - pathComparator q u (trajectory q g projection ξ t)) := by
  dsimp [residualInfluence, observableInfluence, pathComparator]
  simp only [trajectory_time]
  exact (comparator_influence_decomposition hB hδ hδ1 ht _ _ _ _).symm

lemma trajectory_negative_absorbs {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (u : Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) {t : ℕ} (ht : t < q.T) :
    3 * q.B * Real.sqrt q.T * ‖residualInfluence q u (trajectory q g projection ξ t)‖ ^ 2 ≤
      ‖(trajectory q g projection ξ t).2.1 - pathComparator q u (trajectory q g projection ξ t)‖ ^ 2 /
        (4 * q.T * tailWeight q.B q.δ q.T (t - 1)) := by
  have hq := confidence_ge_one hδ hδ1
  have hc : 3 * q.B * Real.sqrt q.T ≤ 4096 * q.B * Real.sqrt q.T * Real.log (8 / q.δ) / 16 := by
    have hh := mul_le_mul_of_nonneg_right (show (3 : ℝ) ≤ 256 * Real.log (8 / q.δ) by linarith)
      (show 0 ≤ q.B * Real.sqrt q.T by positivity)
    convert hh using 1 <;> ring
  have hn := mul_le_mul_of_nonneg_right (negative_potential_bound hB hδ hδ1 ht)
    (sq_nonneg ‖(trajectory q g projection ξ t).2.1 - pathComparator q u (trajectory q g projection ξ t)‖)
  have hh := mul_le_mul_of_nonneg_right hc
    (sq_nonneg ‖residualInfluence q u (trajectory q g projection ξ t)‖)
  apply hh.trans
  rw [trajectory_influence_identity q g projection ξ u hB hδ hδ1 ht, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  convert hn using 1 <;> ring

lemma trajectory_initial_influence {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (u : Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {D : ℝ} (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) :
    ‖residualInfluence q u (trajectory q g projection ξ 0)‖ ^ 2 ≤ 16 * D / (q.T : ℝ) ^ 2 := by
  have hc := optimizer_influence_bound hB hδ hδ1 hT
  have hnon : 0 ≤ weight q.T 0 * stepSize q.B q.δ q.T 0 / tailWeight q.B q.δ q.T 0 := by
    have hw : 0 ≤ weight q.T 0 := by linarith [(weight_bounds hT).1]
    exact div_nonneg (mul_nonneg hw (stepSize_pos hB hδ hδ1 hT).le)
      (tailWeight_pos hB hδ hδ1 hT).le
  simp only [trajectory, residualInfluence, observableInfluence, sub_self, smul_zero, zero_sub,
    norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_sub_rev u q.x0]
  have hh := mul_le_mul (pow_le_pow_left₀ hnon hc 2) hstart (sq_nonneg _) (sq_nonneg _)
  convert hh using 1; ring

lemma trajectory_absorption {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (u : Vector q.d)
    (hB : 0 < q.B) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) (hT : 0 < q.T)
    {D : ℝ} (hD : 0 ≤ D) (hstart : ‖q.x0 - u‖ ^ 2 ≤ D) :
    (∑ t ∈ Finset.range q.T,
      (3 * q.B * Real.sqrt q.T * ‖residualInfluence q u (trajectory q g projection ξ t)‖ ^ 2 -
        ‖(trajectory q g projection ξ (t + 1)).2.1 - pathComparator q u (trajectory q g projection ξ (t + 1))‖ ^ 2 /
          (4 * q.T * tailWeight q.B q.δ q.T t))) ≤
      48 * q.B * D * Real.log (8 / q.δ) / Real.sqrt q.T := by
  let A := fun t => 3 * q.B * Real.sqrt q.T * ‖residualInfluence q u (trajectory q g projection ξ t)‖ ^ 2
  let N := fun t => ‖(trajectory q g projection ξ t).2.1 - pathComparator q u (trajectory q g projection ξ t)‖ ^ 2 /
    (4 * q.T * tailWeight q.B q.δ q.T (t - 1))
  have ht : 0 < (q.T : ℝ) := by exact_mod_cast hT
  have ht1 : 1 ≤ (q.T : ℝ) := by exact_mod_cast hT
  have hs : 0 < Real.sqrt q.T := Real.sqrt_pos.mpr ht
  have hq := confidence_ge_one hδ hδ1
  have hN : 0 ≤ N q.T := by
    have hS := tailWeight_pos hB hδ hδ1 (show q.T - 1 < q.T by omega)
    dsimp [N]
    positivity
  have hh := shifted_absorption A N hT hN (fun t _ ht =>
    trajectory_negative_absorbs q g projection ξ u hB hδ hδ1 ht)
  change (∑ t ∈ Finset.range q.T, (A t - N (t + 1))) ≤ _
  apply hh.trans
  have hi := mul_le_mul_of_nonneg_left
    (trajectory_initial_influence q g projection ξ u hB hδ hδ1 hT hstart)
    (show 0 ≤ 3 * q.B * Real.sqrt q.T by positivity)
  have he : 3 * q.B * Real.sqrt q.T * (16 * D / (q.T : ℝ) ^ 2) =
      (48 * q.B * D / Real.sqrt q.T) * (1 / q.T) := by
    field_simp
    nlinarith [Real.sq_sqrt ht.le]
  rw [he] at hi
  have hiT : 1 / (q.T : ℝ) ≤ Real.log (8 / q.δ) :=
    ((div_le_one ht).mpr ht1).trans hq
  have hp := mul_le_mul_of_nonneg_left hiT (show 0 ≤ 48 * q.B * D / Real.sqrt q.T by positivity)
  exact hi.trans (by convert hp using 1; ring)

end OracleTemplate.TerminalClipping
