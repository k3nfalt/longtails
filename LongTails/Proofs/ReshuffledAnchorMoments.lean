import LongTails.Proofs.ReshuffledBias
import LongTails.Proofs.ReshuffledWeightedBounds

set_option autoImplicit false

open Finset

namespace OracleTemplate.ReshuffledAnchorMoments

open ReshuffledConvex ReshuffledWeighted
open LongTails.Setups.ReshuffledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma anchor_convex_step {φ : E → ℝ} (hc : ConvexOn ℝ Set.univ φ)
    (w : ℕ → ℝ) (X : ℕ → E) (z : E) (k : ℕ)
    (hw : 0 < w k) (hww : w k ≤ w (k + 1)) :
    w (k + 1) * φ (anchor w X z (k + 1)) ≤
      w k * φ (anchor w X z k) + (w (k + 1) - w k) * φ (X (k + 1)) := by
  have hw1 : 0 < w (k + 1) := hw.trans_le hww
  have hθ0 : 0 ≤ w k / w (k + 1) := div_nonneg hw.le hw1.le
  have hθ1 : w k / w (k + 1) ≤ 1 := (div_le_one hw1).mpr hww
  have hj := hc.2 (Set.mem_univ (anchor w X z k)) (Set.mem_univ (X (k + 1)))
    hθ0 (sub_nonneg.mpr hθ1) (by ring : w k / w (k + 1) + (1 - w k / w (k + 1)) = 1)
  change φ (anchor w X z (k + 1)) ≤
    w k / w (k + 1) * φ (anchor w X z k) + (1 - w k / w (k + 1)) * φ (X (k + 1)) at hj
  have hm := mul_le_mul_of_nonneg_left hj hw1.le
  have he : w (k + 1) * (w k / w (k + 1) * φ (anchor w X z k) +
      (1 - w k / w (k + 1)) * φ (X (k + 1))) =
      w k * φ (anchor w X z k) + (w (k + 1) - w k) * φ (X (k + 1)) := by
    field_simp [hw1.ne']

  exact he ▸ hm

omit [CompleteSpace E] in
lemma anchor_convex_sum {φ : E → ℝ} (hc : ConvexOn ℝ Set.univ φ)
    (w : ℕ → ℝ) (X : ℕ → E) (z : E) (hz : φ z = 0) (t : ℕ)
    (hw : ∀ s, s ≤ t → 0 < w s) (hmono : ∀ s, s < t → w s ≤ w (s + 1)) :
    w t * φ (anchor w X z t) ≤
      ∑ s ∈ range t, (w (s + 1) - w s) * φ (X (s + 1)) := by
  induction t with
  | zero => simp [anchor, hz]
  | succ t ih =>
    have hi := ih (fun s hs => hw s (by omega)) (fun s hs => hmono s (by omega))
    have hs := anchor_convex_step hc w X z t (hw t (by omega)) (hmono t (by omega))
    rw [sum_range_succ]
    linarith

lemma sum_prefixes (T : ℕ) (a : ℕ → ℝ) :
    (∑ t ∈ range T, ∑ s ∈ range t, a s) =
      ∑ s ∈ range T, (T - (s + 1) : ℕ) * a s := by
  have he := triangular_sum T (fun _ => (1 : ℝ)) a
  simpa only [one_mul, mul_one, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm] using he

omit [CompleteSpace E] in
lemma sum_anchor_convex {φ : E → ℝ} (hc : ConvexOn ℝ Set.univ φ)
    (w : ℕ → ℝ) (X : ℕ → E) (z : E) (hz : φ z = 0) (T : ℕ)
    (hw : ∀ s, s < T → 0 < w s) (hmono : ∀ s, s + 1 < T → w s ≤ w (s + 1)) :
    (∑ t ∈ range T, w t * φ (anchor w X z t)) ≤
      ∑ s ∈ range T, (T - (s + 1) : ℕ) * ((w (s + 1) - w s) * φ (X (s + 1))) := by
  rw [← sum_prefixes]
  apply sum_le_sum
  intro t ht
  exact anchor_convex_sum hc w X z hz t
    (fun s hs => hw s (by have := mem_range.mp ht; omega))
    (fun s hs => hmono s (by have := mem_range.mp ht; omega))

omit [CompleteSpace E] in
lemma anchor_sum_family {ι : Type*} [Fintype ι] (φ : ι → E → ℝ)
    (hc : ∀ s, ConvexOn ℝ Set.univ (φ s))
    (w : ℕ → ℝ) (X : ι → ℕ → E) (z : E) (hz : ∀ s, φ s z = 0) (t : ℕ)
    (hw : ∀ u, u ≤ t → 0 < w u) (hmono : ∀ u, u < t → w u ≤ w (u + 1))
    (C : ℕ → ℝ) (hC : ∀ u, u ≤ t → (∑ s, φ s (X s u)) ≤ C u) :
    w t * (∑ s, φ s (anchor w (X s) z t)) ≤
      ∑ u ∈ range t, (w (u + 1) - w u) * C (u + 1) := by
  calc
    _ = ∑ s, w t * φ s (anchor w (X s) z t) := mul_sum ..
    _ ≤ ∑ s, ∑ u ∈ range t, (w (u + 1) - w u) * φ s (X s (u + 1)) :=
      sum_le_sum fun s _ => anchor_convex_sum (hc s) w (X s) z (hz s) t hw hmono
    _ = ∑ u ∈ range t, (w (u + 1) - w u) * ∑ s, φ s (X s (u + 1)) := by
      rw [sum_comm]; simp only [mul_sum]
    _ ≤ _ := by
      apply sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (hC (u + 1) (by have := mem_range.mp hu; omega))
        (sub_nonneg.mpr (hmono u (mem_range.mp hu)))

variable {n K : ℕ} [NeZero n]

lemma sampled_anchor_loss {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℕ → ℝ) (x0 : E) (k : Fin K) (i : Fin n) (w : ℕ → ℝ)
    (hw : ∀ u, u ≤ n * k.val + i.val → 0 < w u)
    (hmono : ∀ u, u < n * k.val + i.val → w u ≤ w (u + 1)) :
    let X := fun (s : Orders n K) => iterate g (schedule s) η x0
    let A := fun u => ∑ s : Orders n K, ReshuffledCentered.loss
      (f (schedule s (u / n) ⟨u % n, Nat.mod_lt _ (NeZero.pos n)⟩))
      (g (schedule s (u / n) ⟨u % n, Nat.mod_lt _ (NeZero.pos n)⟩)) xstar (X s u)
    let R := fun u => ∑ s : Orders n K, (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (X s u) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
    w (n * k.val + i.val) * (∑ s : Orders n K,
      ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar
        (anchor w (X s) xstar (n * k.val + i.val))) ≤
      ∑ u ∈ range (n * k.val + i.val), (w (u + 1) - w u) * (A (u + 1) + R (u + 1)) := by
  dsimp only
  exact anchor_sum_family
    (fun s : Orders n K => ReshuffledCentered.loss (f (s k i)) (g (s k i)) xstar)
    (fun s => ReshuffledCentered.loss_convex (h.convex (s k i)) xstar)
    w (fun s => iterate g (schedule s) η x0) xstar
    (fun s => ReshuffledCentered.loss_self _ _ _) _ hw hmono _
    (fun u hu => ReshuffledBias.past_label_loss h η x0 k i u hu)

omit [CompleteSpace E] in
lemma distance_telescope (w : ℕ → ℝ) (X : ℕ → E) (z : E) {T : ℕ} (hT : 0 < T)
    (hw : ∀ t, t < T → 0 < w t) (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1)) :
    (∑ t ∈ range T, w t * (‖X t - anchor w X z t‖ ^ 2 -
      ‖X (t + 1) - anchor w X z t‖ ^ 2)) ≤ w 0 * ‖X 0 - z‖ ^ 2 := by
  let d := fun t => if t < T then w t * ‖X t - anchor w X z t‖ ^ 2 else 0
  have hd : ∀ t, t < T → w t * (‖X t - anchor w X z t‖ ^ 2 -
      ‖X (t + 1) - anchor w X z t‖ ^ 2) ≤ d t - d (t + 1) := by
    intro t ht
    by_cases ht1 : t + 1 < T
    · dsimp [d]
      rw [ite_eq_left ht, ite_eq_left ht1]
      have h := anchor_distance w X z t (hw t ht) (hmono t ht1)
      nlinarith
    · dsimp [d]
      rw [ite_eq_left ht, ite_eq_right ht1]
      have hp := mul_nonneg (hw t ht).le (sq_nonneg ‖X (t + 1) - anchor w X z t‖)
      nlinarith
  have hs : ∀ m, (∑ t ∈ range m, (d t - d (t + 1))) = d 0 - d m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [sum_range_succ, ih]; ring
  calc
    _ ≤ ∑ t ∈ range T, (d t - d (t + 1)) := sum_le_sum fun t ht => hd t (mem_range.mp ht)
    _ = _ := by rw [hs]; simp [d, hT, anchor]

omit [CompleteSpace E] in
lemma distance_sum_telescope {ι : Type*} [Fintype ι] (w : ℕ → ℝ) (X : ι → ℕ → E)
    (z : E) {T : ℕ} (hT : 0 < T)
    (hw : ∀ t, t < T → 0 < w t) (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1)) :
    (∑ t ∈ range T, w t * ((∑ s, ‖X s t - anchor w (X s) z t‖ ^ 2) -
      ∑ s, ‖X s (t + 1) - anchor w (X s) z t‖ ^ 2)) ≤
      w 0 * ∑ s, ‖X s 0 - z‖ ^ 2 := by
  calc
    _ = ∑ s, ∑ t ∈ range T, w t * (‖X s t - anchor w (X s) z t‖ ^ 2 -
        ‖X s (t + 1) - anchor w (X s) z t‖ ^ 2) := by
      simp only [← sum_sub_distrib, mul_sum]
      rw [sum_comm]
    _ ≤ ∑ s, w 0 * ‖X s 0 - z‖ ^ 2 :=
      sum_le_sum fun s _ => distance_telescope w (X s) z hT hw hmono
    _ = _ := (mul_sum ..).symm

omit [CompleteSpace E] in
lemma objective_sum_anchor {ι : Type*} [Fintype ι] {φ : E → ℝ}
    (hc : ConvexOn ℝ Set.univ φ) (w : ℕ → ℝ) (X : ι → ℕ → E) (z : E)
    (hz : φ z = 0) (T : ℕ) (hw : ∀ t, t < T → 0 < w t)
    (hmono : ∀ t, t + 1 < T → w t ≤ w (t + 1)) :
    (∑ t ∈ range T, w t * ∑ s, φ (anchor w (X s) z t)) ≤
      ∑ t ∈ range T, (T - (t + 1) : ℕ) * (w (t + 1) - w t) * ∑ s, φ (X s (t + 1)) := by
  calc
    _ = ∑ s, ∑ t ∈ range T, w t * φ (anchor w (X s) z t) := by
      simp_rw [mul_sum]
      rw [sum_comm]
    _ ≤ ∑ s, ∑ t ∈ range T,
        (T - (t + 1) : ℕ) * ((w (t + 1) - w t) * φ (X s (t + 1))) :=
      sum_le_sum fun s _ => sum_anchor_convex hc w (X s) z hz T hw hmono
    _ = _ := by
      rw [sum_comm]
      simp only [mul_sum, mul_assoc]

end OracleTemplate.ReshuffledAnchorMoments
