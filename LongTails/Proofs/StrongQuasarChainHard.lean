import LongTails.Proofs.StrongQuasarChainObjective
import LongTails.Proofs.StrongQuasarChainLocalized
import LongTails.Proofs.FiniteSumNondualLowerSimulation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open Finset

namespace LongTails.Proofs.StrongQuasarChainHard

open LongTails.Proofs.StrongQuasarChainBlock LongTails.Proofs.StrongQuasarChainScalar
open LongTails.Proofs.StrongQuasarChainObjective LongTails.Proofs.StrongQuasarChainLocalized
open LongTails.Proofs.FiniteSumNondualLowerComponents LongTails.Proofs.FiniteSumNondualLowerSimulation
open LongTails.Proofs.SmoothConvexFiniteWall (wall localized localizedField localized_outside
  localized_gradient localized_lipschitz localized_zero localized_ge)
open LongTails.Proofs.SmoothConvexFiniteGeometry (weight smoothMax_ge smoothMax_eq_left)

noncomputable def starValue (S : Shape) : ℝ :=
  S.μ / 2 * ∑ p : Fin (S.k + 1), S.scale p ^ 2 +
    ∑ c ∈ range (S.k + 1), deadEnergy S.θ (S.q ^ c - S.q ^ (c + 1)) +
    ∑ p : Fin (S.k + 1), coordProfile S p (S.scale p)

lemma xstar_norm_sq (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) :
    ‖xstar S π‖ ^ 2 = ∑ p, S.scale p ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, xstar_inner]
  apply sum_congr rfl
  intro p _
  rw [xstar_apply_pi]
  ring

lemma objective_xstar (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) :
    objective S π (xstar S π) = starValue S := by
  rw [objective_expand, xstar_norm_sq]
  have hlink : ∑ c, deadEnergy S.θ (linkVar π (xstar S π) c) =
      ∑ c ∈ range (S.k + 1), deadEnergy S.θ (S.q ^ c - S.q ^ (c + 1)) := by
    rw [sum_congr rfl (fun c (_ : c ∈ (univ : Finset (Fin (S.k + 1)))) => by
      rw [selectedChain_xstar_linkVar S π c])]
    exact Fin.sum_univ_eq_sum_range (fun c => deadEnergy S.θ (S.q ^ c - S.q ^ (c + 1))) _
  rw [hlink]
  simp only [xstar_apply_pi, starValue]

noncomputable def gapFun (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (objective S π x - starValue S) / 17

noncomputable def gapField (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (1 / 17 : ℝ) • field S π x

noncomputable def hard (S : Shape) (R : ℝ) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  localized R (gapFun S π) x

noncomputable def hardField (S : Shape) (R : ℝ) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  localizedField R (gapFun S π) (gapField S π) x

section

variable {S : Shape} (V : S.Valid)
include V

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.gapFun_gradient {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (gapFun S π) (gapField S π x) x := by
  have h := V.objective_gradient π x
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  have h2 := (h.sub_const (starValue S)).const_mul (1 / 17 : ℝ)
  convert h2 using 1
  · funext y
    simp only [gapFun]
    ring
  · unfold gapField
    rw [map_smul]

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.gapFun_nonneg {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ gapFun S π x := by
  have h := V.minimizer π (Set.mem_univ x)
  rw [objective_xstar] at h
  unfold gapFun
  have : starValue S ≤ objective S π x := h
  apply div_nonneg (by linarith) (by norm_num)

omit V in
lemma gapFun_xstar (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) :
    gapFun S π (xstar S π) = 0 := by
  unfold gapFun
  rw [objective_xstar, sub_self, zero_div]

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.field_xstar {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) :
    field S π (xstar S π) = 0 := by
  have hmin : IsLocalMin (objective S π) (xstar S π) :=
    (V.minimizer π).isLocalMin Filter.univ_mem
  have hg := (V.objective_gradient π (xstar S π)).hasFDerivAt
  have h0 := hmin.hasFDerivAt_eq_zero hg
  have h1 : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) (field S π (xstar S π)) =
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))) 0 := by
    rw [map_zero]; exact h0
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).injective h1

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.gapField_lipschitz {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) : ‖gapField S π x - gapField S π y‖ ≤ ‖x - y‖ := by
  unfold gapField
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by norm_num)]
  have := V.field_lipschitz π x y
  linarith

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.gapField_bound {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ}
    (hR : ‖xstar S π‖ ≤ R) (x : EuclideanSpace ℝ (Fin d)) :
    ‖gapField S π x‖ ≤ ‖x‖ + R := by
  have h := V.gapField_lipschitz π x (xstar S π)
  have h0 : gapField S π (xstar S π) = 0 := by
    unfold gapField; rw [V.field_xstar, smul_zero]
  rw [h0, sub_zero] at h
  have := norm_sub_le x (xstar S π)
  linarith

omit V in
lemma objective_model {S : Shape} (V : S.Valid) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d)
    (x y : EuclideanSpace ℝ (Fin d)) :
    objective S π y - objective S π x - ⟪field S π x, y - x⟫ ≤ 6 * ‖y - x‖ ^ 2 := by
  have hA := separable_model_abs (linkProfile S.θ) (linkSlope S.θ) 1
    (fun j u v => by
      have hm := V.link_model j u v
      rw [abs_of_nonneg hm.1]; linarith [hm.2]) (selectedChain π x) (selectedChain π y)
  have hB := separable_model_abs (coordProfile S) (coordSlope S) 1
    (fun j u v => by have := V.coord_model j u v; linarith) (coordinateMap π x) (coordinateMap π y)
  have hnA : ‖selectedChain π y - selectedChain π x‖ ≤ 2 * ‖y - x‖ := by
    rw [← map_sub]
    exact ((selectedChain π).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (selectedChain_opNorm π) (norm_nonneg _))
  have hnB : ‖coordinateMap π y - coordinateMap π x‖ ≤ ‖y - x‖ := by
    rw [← map_sub]; exact coordinateMap_norm π _
  have hA2 : ‖selectedChain π y - selectedChain π x‖ ^ 2 ≤ 4 * ‖y - x‖ ^ 2 := by
    nlinarith [norm_nonneg (selectedChain π y - selectedChain π x), norm_nonneg (y - x)]
  have hB2 : ‖coordinateMap π y - coordinateMap π x‖ ^ 2 ≤ ‖y - x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnB 2
  have hfi : ⟪field S π x, y - x⟫ = S.μ * ⟪x, y - x⟫ +
      ⟪separableSlope (linkSlope S.θ) (selectedChain π x), selectedChain π y - selectedChain π x⟫ +
      ⟪separableSlope (coordSlope S) (coordinateMap π x), coordinateMap π y - coordinateMap π x⟫ := by
    unfold field
    rw [inner_add_left, inner_add_left, real_inner_smul_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      map_sub, map_sub]
  have hq : S.μ / 2 * ‖y‖ ^ 2 - S.μ / 2 * ‖x‖ ^ 2 - S.μ * ⟪x, y - x⟫ = S.μ / 2 * ‖y - x‖ ^ 2 := by
    have h1 := norm_sub_sq_real y x
    rw [inner_sub_right, real_inner_self_eq_norm_sq, h1, real_inner_comm x y]
    ring
  unfold objective
  rw [hfi]
  have hμ := V.hμ
  have hμ0 := V.hμ0
  have habsA := (abs_le.mp hA).2
  have habsB := (abs_le.mp hB).2
  nlinarith [sq_nonneg ‖y - x‖]

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.gapFun_upper {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ}
    (hR : ‖xstar S π‖ ≤ R) (x : EuclideanSpace ℝ (Fin d)) :
    gapFun S π x ≤ ‖x‖ ^ 2 + R ^ 2 := by
  have h := objective_model V π (xstar S π) x
  rw [V.field_xstar, inner_zero_left, sub_zero, objective_xstar] at h
  unfold gapFun
  have h1 : ‖x - xstar S π‖ ≤ ‖x‖ + R := by
    have := norm_sub_le x (xstar S π); linarith
  have h2 : ‖x - xstar S π‖ ^ 2 ≤ (‖x‖ + R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (‖x‖ + R) ^ 2 ≤ 2 * (‖x‖ ^ 2 + R ^ 2) := by nlinarith [sq_nonneg (‖x‖ - R)]
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

end

noncomputable def partialGapFun (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (S.μ / 2 * ‖x‖ ^ 2 +
    ∑ c : Fin (S.k + 1), (if c.val ≤ r then linkProfile S.θ c (selectedChain π x c) else 0) +
    ∑ p : Fin (S.k + 1), (if p.val ≤ r then coordProfile S p (x (π p))
      else S.μ * S.scale p ^ 2 * bump 0) - starValue S) / 17

noncomputable def partialGapField (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (1 / 17 : ℝ) • (S.μ • x +
    (selectedChain π).adjoint (separableSlope
      (fun c t => if c.val ≤ r then linkSlope S.θ c t else 0) (selectedChain π x)) +
    (coordinateMap π).adjoint (separableSlope
      (fun p t => if p.val ≤ r then coordSlope S p t else 0) (coordinateMap π x)))

noncomputable def partialField (S : Shape) (R : ℝ) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if 3 * R ≤ ‖x‖ then (4 : ℝ) • x else
    weight (R ^ 2) (partialGapFun S π r x) (wall R x) • partialGapField S π r x +
      (1 - weight (R ^ 2) (partialGapFun S π r x) (wall R x)) • ((4 : ℝ) • x)

section

variable {S : Shape} (V : S.Valid)
include V

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.small_scale (p : Fin (S.k + 1)) {t : ℝ} (ht : |t| ≤ S.ρ / 2) :
    |t / S.scale p| ≤ 1 / 16 := by
  have ha := V.scale_pos p
  have hs := V.scale_ge p
  have hθ := V.theta_small
  have hρ := V.hρθ
  rw [abs_div, abs_of_pos ha, div_le_iff₀ ha]
  have hq := pow_pos V.q_pos S.k
  nlinarith

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.link_inactive {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (hsmall : ∀ p : Fin (S.k + 1), r ≤ p.val → |x (π p)| ≤ S.ρ / 2)
    (c : Fin (S.k + 1)) (hc : r < c.val) :
    linkProfile S.θ c (selectedChain π x c) = 0 ∧ linkSlope S.θ c (selectedChain π x c) = 0 := by
  have hc0 : c ≠ 0 := by intro h; subst h; simp at hc
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hc0
  have h1 := hsmall j.castSucc (by simp only [Fin.val_castSucc, Fin.val_succ] at hc ⊢; omega)
  have h2 := hsmall j.succ (by omega)
  have hd : |x (π j.castSucc) - x (π j.succ)| ≤ S.θ := by
    have := abs_sub (x (π j.castSucc)) (x (π j.succ))
    have := V.hρθ
    linarith
  have hi := dead_inactive V.hθ0.le hd
  simp only [linkProfile, linkSlope, Fin.val_succ, Nat.add_one_ne_zero, ↓reduceIte,
    selectedChain_apply_succ]
  exact hi

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.coord_inactive (p : Fin (S.k + 1)) {t : ℝ} (ht : |t| ≤ S.ρ / 2) :
    coordProfile S p t = S.μ * S.scale p ^ 2 * bump 0 ∧ coordSlope S p t = 0 := by
  have hρ : |t| ≤ S.ρ := by linarith [V.hρ0]
  have hd := dead_inactive V.hρ0.le hρ
  have hs := V.small_scale p ht
  unfold coordProfile coordSlope
  rw [hd.1, hd.2, bump_flat hs, bumpSlope_zero_of_small hs]
  constructor <;> ring

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.partial_eq {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (hsmall : ∀ p : Fin (S.k + 1), r ≤ p.val → |x (π p)| ≤ S.ρ / 2) :
    partialGapFun S π r x = gapFun S π x ∧ partialGapField S π r x = gapField S π x := by
  constructor
  · unfold partialGapFun gapFun objective
    rw [separableEnergy_apply, separableEnergy_apply]
    congr 2
    congr 1
    · congr 1
      apply sum_congr rfl
      intro c _
      by_cases hc : c.val ≤ r
      · simp [hc]
      · simp only [hc, ↓reduceIte]
        exact (V.link_inactive π r x hsmall c (by omega)).1.symm
    · apply sum_congr rfl
      intro p _
      by_cases hp : p.val ≤ r
      · simp [hp, coordinateMap_apply]
      · simp only [hp, ↓reduceIte, coordinateMap_apply]
        exact (V.coord_inactive p (hsmall p (by omega))).1.symm
  · unfold partialGapField gapField field
    congr 2
    · congr 2
      apply PiLp.ext
      intro c
      change (if c.val ≤ r then linkSlope S.θ c (selectedChain π x c) else 0) =
        linkSlope S.θ c (selectedChain π x c)
      by_cases hc : c.val ≤ r
      · simp [hc]
      · simp only [hc, ↓reduceIte]
        exact (V.link_inactive π r x hsmall c (by omega)).2.symm
    · congr 1
      apply PiLp.ext
      intro p
      change (if p.val ≤ r then coordSlope S p (coordinateMap π x p) else 0) =
        coordSlope S p (coordinateMap π x p)
      by_cases hp : p.val ≤ r
      · simp [hp]
      · simp only [hp, ↓reduceIte, coordinateMap_apply]
        exact (V.coord_inactive p (hsmall p (by omega))).2.symm

end

lemma partial_prefix (S : Shape) {d : ℕ} (π π' : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (hπ : ∀ j : Fin (S.k + 1), j.val ≤ r → π j = π' j) (x : EuclideanSpace ℝ (Fin d)) :
    partialGapFun S π r x = partialGapFun S π' r x ∧
      partialGapField S π r x = partialGapField S π' r x := by
  constructor
  · unfold partialGapFun
    congr 3
    · congr 1
      apply sum_congr rfl
      intro c _
      by_cases hc : c.val ≤ r
      · simp only [hc, ↓reduceIte, selectedChain_prefix π π' r hπ x c hc]
      · simp [hc]
    · apply sum_congr rfl
      intro p _
      by_cases hp : p.val ≤ r
      · simp only [hp, ↓reduceIte, hπ p hp]
      · simp [hp]
  · unfold partialGapField
    congr 2
    · congr 1
      apply ext_inner_right ℝ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply sum_congr rfl
      intro j _
      change selectedChain π v j * (if j.val ≤ r then _ else 0) =
        selectedChain π' v j * (if j.val ≤ r then _ else 0)
      by_cases hj : j.val ≤ r
      · simp only [hj, ↓reduceIte, selectedChain_prefix π π' r hπ x j hj,
          selectedChain_prefix π π' r hπ v j hj]
      · simp [hj]
    · apply ext_inner_right ℝ
      intro v
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      apply sum_congr rfl
      intro j _
      change coordinateMap π v j * (if j.val ≤ r then _ else 0) =
        coordinateMap π' v j * (if j.val ≤ r then _ else 0)
      by_cases hj : j.val ≤ r
      · simp only [hj, ↓reduceIte, coordinateMap_apply, hπ j hj]
      · simp [hj]

lemma partialField_prefix (S : Shape) (R : ℝ) {d : ℕ} (π π' : Fin (S.k + 1) ↪ Fin d) (r : ℕ)
    (hπ : ∀ j : Fin (S.k + 1), j.val ≤ r → π j = π' j) (x : EuclideanSpace ℝ (Fin d)) :
    partialField S R π r x = partialField S R π' r x := by
  have h := partial_prefix S π π' r hπ x
  unfold partialField
  rw [h.1, h.2]

section props

variable {S : Shape} (V : S.Valid)
include V

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_outside {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (hxs : ‖xstar S π‖ ≤ R) (x : EuclideanSpace ℝ (Fin d)) (hx : 3 * R ≤ ‖x‖) :
    hard S R π x = wall R x ∧ hardField S R π x = (4 : ℝ) • x :=
  localized_outside R hR (gapFun S π) (gapField S π) (V.gapFun_upper π hxs) x hx

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.partialField_eq {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (hxs : ‖xstar S π‖ ≤ R) (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (hsmall : ‖x‖ < 3 * R → ∀ p : Fin (S.k + 1), r ≤ p.val → |x (π p)| ≤ S.ρ / 2) :
    partialField S R π r x = hardField S R π x := by
  unfold partialField
  split_ifs with hx
  · exact (V.hard_outside π hR hxs x hx).2.symm
  · have h := V.partial_eq π r x (hsmall (lt_of_not_ge hx))
    rw [h.1, h.2]
    rfl

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_gradient {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (hard S R π) (hardField S R π x) x :=
  localized_gradient R hR (gapFun S π) (gapField S π) (V.gapFun_gradient π) x

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_lipschitz {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (hxs : ‖xstar S π‖ ≤ R) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖hardField S R π x - hardField S R π y‖ ≤ 512 * ‖x - y‖ :=
  localized_lipschitz R hR (gapFun S π) (gapField S π) (V.gapFun_gradient π)
    (V.gapField_lipschitz π) (V.gapFun_upper π hxs) (V.gapField_bound π hxs) x y

omit V in
lemma hard_xstar (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (hxs : ‖xstar S π‖ ≤ R) : hard S R π (xstar S π) = 0 :=
  localized_zero R hR (gapFun S π) (xstar S π) (gapFun_xstar S π) hxs

omit V in
lemma gap_le_hard (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin d)) : gapFun S π x ≤ hard S R π x :=
  localized_ge R hR (gapFun S π) x

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_nonneg {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ hard S R π x :=
  (V.gapFun_nonneg π x).trans (gap_le_hard S π hR x)

omit V in
lemma wall_le_hard (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin d)) : wall R x ≤ hard S R π x :=
  (le_max_right _ _).trans (smoothMax_ge _ _ _ (sq_pos_of_pos hR))

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_zero {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R) :
    hard S R π 0 = gapFun S π 0 := by
  have h0 := V.gapFun_nonneg π 0
  have hw : wall R (0 : EuclideanSpace ℝ (Fin d)) = -(4 * R ^ 2) := by simp [wall]
  exact (smoothMax_eq_left (R ^ 2) (gapFun S π 0) (wall R 0) (sq_pos_of_pos hR)
    (by rw [hw]; nlinarith)).1

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_sq {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R)
    (hxs : ‖xstar S π‖ ≤ R / 2) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 256)
    (hc : (42 * γ * S.m) ^ 2 * S.μ ≤ 1) (x : EuclideanSpace ℝ (Fin d)) :
    γ * hard S R π x + ⟪hardField S R π x, xstar S π - x⟫ +
        γ * (S.μ / 17) / 2 * ‖xstar S π - x‖ ^ 2 ≤ γ * hard S R π (xstar S π) := by
  have hμ := V.hμ
  have hμ0 := V.hμ0
  apply localized_strongQuasar R hR (gapFun S π) (gapField S π) (xstar S π) γ (S.μ / 17)
    hγ0 (by linarith) (by positivity) (by linarith) (V.gapFun_nonneg π) (gapFun_xstar S π) hxs
  intro y
  have h := V.strongQuasar π hγ0 hγ hc y
  rw [objective_xstar] at h
  unfold gapFun gapField
  rw [real_inner_smul_left]
  have : γ * ((objective S π y - starValue S) / 17) +
      1 / 17 * ⟪field S π y, xstar S π - y⟫ + γ * (S.μ / 17) / 2 * ‖xstar S π - y‖ ^ 2 =
      (γ * objective S π y + ⟪field S π y, xstar S π - y⟫ +
        γ * S.μ / 2 * ‖xstar S π - y‖ ^ 2 - γ * starValue S) / 17 := by ring
  rw [this]
  apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

lemma _root_.LongTails.Proofs.StrongQuasarChainObjective.Shape.Valid.hard_gap {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R) (b : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) (hs : ∀ p : Fin (S.k + 1), b ≤ p.val → |x (π p)| ≤ S.ρ / 2) :
    S.μ * bump 0 / 17 * ∑ p ∈ (univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val),
      S.scale p ^ 2 ≤ hard S R π x := by
  refine le_trans ?_ (gap_le_hard S π hR x)
  have hl := V.objective_lower π x
  rw [objective_xstar] at hl
  unfold gapFun
  rw [le_div_iff₀ (by norm_num)]
  have hμ0 := V.hμ0
  have hsplit : ∑ p ∈ (univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val),
      S.μ * S.scale p ^ 2 * bump (x (π p) / S.scale p) ≤
      ∑ p, S.μ * S.scale p ^ 2 * bump (x (π p) / S.scale p) :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun p _ _ => by
      have := (bump_bounds (x (π p) / S.scale p)).1
      positivity)
  have heq : ∑ p ∈ (univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val),
      S.μ * S.scale p ^ 2 * bump (x (π p) / S.scale p) =
      S.μ * bump 0 * ∑ p ∈ (univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val),
        S.scale p ^ 2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    rw [bump_flat (V.small_scale p (hs p (mem_filter.mp hp).2))]
    ring
  have : (S.μ * bump 0 / 17 * ∑ p ∈ (univ : Finset (Fin (S.k + 1))).filter (fun p => b ≤ p.val),
      S.scale p ^ 2) * 17 = S.μ * bump 0 * ∑ p ∈ (univ : Finset (Fin (S.k + 1))).filter
        (fun p => b ≤ p.val), S.scale p ^ 2 := by ring
  linarith

end props

noncomputable def objZero (S : Shape) : ℝ :=
  ∑ c : Fin (S.k + 1), (if c.val = 0 then deadEnergy S.θ 1 else 0) +
    ∑ p : Fin (S.k + 1), coordProfile S p 0

noncomputable def gapZero (S : Shape) : ℝ := (objZero S - starValue S) / 17

lemma objective_zero (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (hθ : 0 ≤ S.θ) :
    objective S π 0 = objZero S := by
  rw [objective_expand]
  have h0 : deadEnergy S.θ 0 = 0 := (dead_inactive hθ (by simpa using hθ)).1
  unfold objZero
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_add]
  congr 1
  · apply sum_congr rfl
    intro c _
    unfold linkVar
    split_ifs with hc
    · simp
    · simp [h0]

lemma gapFun_zero (S : Shape) {d : ℕ} (π : Fin (S.k + 1) ↪ Fin d) (hθ : 0 ≤ S.θ) :
    gapFun S π 0 = gapZero S := by
  unfold gapFun gapZero
  rw [objective_zero S π hθ]

end LongTails.Proofs.StrongQuasarChainHard
