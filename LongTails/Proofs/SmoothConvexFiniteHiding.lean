import LongTails.Proofs.FiniteSumNondualLowerAveraging

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace LongTails.Proofs.SmoothConvexFiniteHiding

open FiniteSumNondualLowerHiding FiniteSumNondualLowerExposure
open FiniteSumNondualLowerAveraging

lemma large_coordinates_sq {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (hθ : 0 ≤ θ) :
    ((Finset.univ.filter (fun i => θ < |x i|)).card : ℝ) * θ ^ 2 ≤ ‖x‖ ^ 2 := by
  classical
  let s := Finset.univ.filter (fun i => θ < |x i|)
  calc
    (s.card : ℝ) * θ ^ 2 = ∑ _ ∈ s, θ ^ 2 := by simp
    _ ≤ ∑ i ∈ s, x i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := pow_le_pow_left₀ hθ (Finset.mem_filter.mp hi).2.le 2
      simpa only [sq_abs] using h
    _ ≤ ∑ i, x i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun i _ _ => sq_nonneg (x i))
    _ = _ := (EuclideanSpace.real_norm_sq_eq x).symm

noncomputable def boundedObservation {d : ℕ} (B : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := if ‖x‖ ≤ B then x else 0

lemma boundedObservation_norm {d : ℕ} (B : ℝ) (hB : 0 ≤ B)
    (x : EuclideanSpace ℝ (Fin d)) : ‖boundedObservation B x‖ ≤ B := by
  unfold boundedObservation
  split_ifs with h
  · exact h
  · simpa using hB

noncomputable def largeSet {d : ℕ} (B θ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Finset (Fin d) := Finset.univ.filter (fun i => θ < |boundedObservation B x i|)

lemma largeSet_bound {d : ℕ} (B θ : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ)
    (x : EuclideanSpace ℝ (Fin d)) : ((largeSet B θ x).card : ℝ) ≤ B ^ 2 / θ ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hθ)).mpr
  exact (large_coordinates_sq (boundedObservation B x) θ hθ.le).trans
    (pow_le_pow_left₀ (norm_nonneg _) (boundedObservation_norm B hB x) 2)

lemma not_largeSet_small {d : ℕ} (B θ : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ B) (i : Fin d) (hi : i ∉ largeSet B θ x) : |x i| ≤ θ := by
  simpa [largeSet, boundedObservation, hx] using hi

lemma bounded_prefix_bad_count {d K : ℕ} {J : Type*} [Fintype J]
    (B θ D : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (hD : 0 ≤ D) (hDs : D + K ≤ d)
    (r : J → ℕ) (hr : ∀ j, r j ≤ K)
    (observe : J → (Fin K ↪ Fin d) → EuclideanSpace ℝ (Fin d))
    (hp : ∀ j π ρ, (∀ z : Fin K, z.val < r j → π z = ρ z) → observe j π = observe j ρ) :
    D * (((distinctWords K (Finset.univ : Finset (Fin d))).filter
      (fun w => ∃ j : J, ∃ π : Fin K ↪ Fin d, List.ofFn π = w ∧
        0 < hits (largeSet B θ (observe j π)) (w.drop (r j)))).card : ℝ) ≤
      (Fintype.card J : ℝ) * K * (B ^ 2 / θ ^ 2) *
        (distinctWords K (Finset.univ : Finset (Fin d))).card := by
  let F : J → (Fin K ↪ Fin d) → ℕ × Finset (Fin d) :=
    fun j π => (r j, largeSet B θ (observe j π))
  have hb : ∀ j π, ((F j π).2.card : ℝ) ≤ B ^ 2 / θ ^ 2 :=
    fun j π => largeSet_bound B θ hB hθ (observe j π)
  have hk : ∀ j π, (F j π).1 ≤ K := fun j _ => hr j
  have hf : ∀ j π ρ, (∀ z : Fin K, z.val < (F j π).1 → π z = ρ z) → F j π = F j ρ := by
    intro j π ρ h
    dsimp only [F]
    rw [hp j π ρ h]
  have hd : D + K ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) := by simpa using hDs
  have bound := prefix_family_bad_count_bound F hb (by positivity) hk hf Finset.univ D hD hd
  simpa only [F] using bound


end LongTails.Proofs.SmoothConvexFiniteHiding
