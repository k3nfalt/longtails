import LongTails.Proofs.FrontierChainPrefix

namespace LongTails.Proofs.FrontierChainTruncation

open FrontierChain FrontierChainNoise FrontierChainPrefix
open Classical

variable {d k : ℕ}

noncomputable def truncate (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ i : Fin (k + 1), if i.val < r then x (π i) • EuclideanSpace.single (π i) (1 : ℝ) else 0

lemma truncate_coordinate (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) :
    truncate π r x (π j) = if j.val < r then x (π j) else 0 := by
  have he : truncate π r x (π j) =
      ∑ i : Fin (k + 1), (if i.val < r then x (π i) • EuclideanSpace.single (π i) (1 : ℝ) else 0) (π j) := by
    simp [truncate]
  rw [he, Finset.sum_eq_single j]
  · split_ifs <;> simp
  · intro i _ hij
    have hne : π j ≠ π i := fun h => hij (π.injective h.symm)
    split_ifs <;> simp [hne]
  · simp

lemma truncate_prefix (π π' : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (hπ : ∀ j : Fin (k + 1), j.val < r → π j = π' j) :
    truncate π r x = truncate π' r x := by
  unfold truncate
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rw [hπ i hi]
  · rfl

lemma truncate_small (π : Fin (k + 1) ↪ Fin d) (r n : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (j : Fin (k + 1)) (hj : r ≤ j.val) : |truncate π n x (π j)| ≤ 1 / 4 := by
  rw [truncate_coordinate]
  split_ifs
  · exact hx j hj
  · norm_num

lemma residual_truncate (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4) :
    field π x - noiseField π x = field π (truncate π r x) - noiseField π (truncate π r x) := by
  apply residual_point π x (truncate π r x) r
  · intro j hj
    rw [truncate_coordinate, ite_eq_left hj]
  · exact hx
  · exact truncate_small π r r x hx

lemma field_truncate (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4) :
    field π x = field π (truncate π (r + 1) x) := by
  apply field_point π x (truncate π (r + 1) x) r
  · intro j hj
    rw [truncate_coordinate, ite_eq_left (by omega)]
  · exact hx
  · exact truncate_small π r (r + 1) x hx

lemma noise_truncate (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4) :
    noiseField π x = noiseField π (truncate π (r + 1) x) := by
  apply noise_point π x (truncate π (r + 1) x) r
  · intro j hj
    rw [truncate_coordinate, ite_eq_left (by omega)]
  · exact hx
  · exact truncate_small π r (r + 1) x hx

noncomputable def lookahead (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  FrontierChainGeometry.scatter π (fun i => if i.val < r then x (π i)
    else if i.val = r then max (-(1 / 4)) (min (1 / 4) (x (π i))) else 0)

lemma lookahead_coordinate (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) :
    lookahead π r x (π j) = if j.val < r then x (π j)
      else if j.val = r then max (-(1 / 4)) (min (1 / 4) (x (π j))) else 0 :=
  FrontierChainGeometry.scatter_apply _ _ _

lemma lookahead_small (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) (hj : r ≤ j.val) :
    |lookahead π r x (π j)| ≤ 1 / 4 := by
  rw [lookahead_coordinate, ite_eq_right (by omega)]
  split_ifs
  · rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · norm_num

lemma lookahead_agree (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (j : Fin (k + 1)) (hj : j.val ≤ r) : x (π j) = lookahead π r x (π j) := by
  rw [lookahead_coordinate]
  split_ifs with hi he
  · rfl
  · have hb := abs_le.mp (hx j (by omega))
    rw [min_eq_right hb.2, max_eq_right hb.1]
  · omega

lemma lookahead_prefix (π π' : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j) :
    lookahead π r x = lookahead π' r x := by
  unfold lookahead FrontierChainGeometry.scatter
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  split_ifs with hi he
  · rw [hπ i (by omega)]
  · rw [hπ i (by omega)]
  · simp

lemma field_lookahead (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4) :
    field π x = field π (lookahead π r x) :=
  field_point π x (lookahead π r x) r (lookahead_agree π r x hx) hx (lookahead_small π r x)

lemma noise_lookahead (π : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4) :
    noiseField π x = noiseField π (lookahead π r x) :=
  noise_point π x (lookahead π r x) r (lookahead_agree π r x hx) hx (lookahead_small π r x)

end LongTails.Proofs.FrontierChainTruncation
