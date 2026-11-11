import LongTails.Proofs.SmoothConvexFiniteWall
import LongTails.Proofs.FiniteSumNondualLowerSimulation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.SmoothConvexFiniteSimulation

open FiniteSumNondualLowerComponents FiniteSumNondualLowerGeometry
open FiniteSumNondualLowerSimulation SmoothConvexFiniteGeometry SmoothConvexFiniteWall

noncomputable def partialObjective {d k : ℕ} (δ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / 8 * ∑ j : Fin (k + 1), if j.val ≤ r then
    maskedProfile true (Fin.cases (0 : ℝ) (fun _ => δ) j) (Fin.cases a (fun _ => 0) j)
      (selectedChain π x j) else 0

lemma partialObjective_eq {d k : ℕ} (δ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin k, r < j.succ.val → |x (π j.castSucc) - x (π j.succ)| ≤ δ) :
    partialObjective δ a π r x = hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0 x := by
  unfold partialObjective hardComponent separableEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change (if j.val ≤ r then _ else 0) = maskedProfile true _ _ _
  by_cases hj : j.val ≤ r
  · simp only [hj, ↓reduceIte]
  · rw [ite_eq_right hj]
    have hpos : 0 < j.val := by omega
    obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (show j ≠ 0 from by intro he; subst j; simp at hpos)
    have hz := (deadZone_inactive δ _ (h i (by omega))).1
    simp [maskedProfile, selectedChain_apply_succ, hz]

lemma partialObjective_prefix {d k : ℕ} (δ a : ℝ) (π ρ : Fin (k + 1) ↪ Fin d)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), j.val ≤ r → π j = ρ j) :
    partialObjective δ a π r x = partialObjective δ a ρ r x := by
  unfold partialObjective
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val ≤ r
  · simp only [hj, ↓reduceIte, selectedChain_prefix π ρ r h x j hj]
  · simp only [hj, ↓reduceIte]

noncomputable def partialField {d k : ℕ} (L R δ a : ℝ) (π : Fin (k + 1) ↪ Fin d)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if 3 * R ≤ ‖x‖ then (L / 128) • x else
    (L / 512) • (weight (R ^ 2) (partialObjective δ a π r x) (wall R x) •
      partialGradient 1 δ a π (fun _ => (0 : Fin 1)) 0 r x +
      (1 - weight (R ^ 2) (partialObjective δ a π r x) (wall R x)) • ((4 : ℝ) • x))

lemma partialField_prefix {d k : ℕ} (L R δ a : ℝ) (π ρ : Fin (k + 1) ↪ Fin d)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), j.val ≤ r → π j = ρ j) :
    partialField L R δ a π r x = partialField L R δ a ρ r x := by
  unfold partialField
  rw [partialObjective_prefix δ a π ρ r x h,
    partialGradient_prefix 1 δ a π ρ (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1))
      0 r x h (by intros; rfl)]

lemma partialField_eq {d k : ℕ} (L R δ a : ℝ) (hR : 0 < R) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (hsmall : ‖x‖ < 3 * R → ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ δ / 4) :
    partialField L R δ a π r x = field L R δ a π x := by
  unfold partialField
  split_ifs with hx
  · exact (field_outside L R δ a hR hδ π ha x hx).symm
  · have hs (j : Fin k) (hj : r < j.succ.val) :
        |x (π j.castSucc) - x (π j.succ)| ≤ δ := by
      have h₁ := hsmall (lt_of_not_ge hx) j.castSucc (by simp only [Fin.val_castSucc, Fin.val_succ] at *; omega)
      have h₂ := hsmall (lt_of_not_ge hx) j.succ (by omega)
      have h := abs_sub (x (π j.castSucc)) (x (π j.succ))
      linarith
    rw [partialObjective_eq δ a π r x hs,
      partialGradient_eq 1 δ a π (fun _ => (0 : Fin 1)) 0 r x (fun j hj _ => hs j hj)]
    rfl

noncomputable def simulatedState {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (π : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) : ℕ → S
  | 0 => initial
  | t + 1 =>
    let s := simulatedState L R δ a π query update initial t
    update s (partialField L R δ a π t (query s))

lemma simulatedState_prefix {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (π ρ : Fin (k + 1) ↪ Fin d) (query : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val < t → π j = ρ j) :
    simulatedState L R δ a π query update initial t =
      simulatedState L R δ a ρ query update initial t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he := ih (fun j hj => h j (by omega))
    simp only [simulatedState, he]
    rw [partialField_prefix L R δ a π ρ t _ (fun j hj => h j (by omega))]

lemma simulatedState_coupling {d k : ℕ} {S : Type*} (L R δ a : ℝ)
    (hR : 0 < R) (hδ : 0 ≤ δ) (π : Fin (k + 1) ↪ Fin d)
    (ha : ((k : ℝ) + 1) * a ^ 2 ≤ R ^ 2) (query : S → EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S) (T : ℕ)
    (hgood : ∀ t < T,
      let x := query (simulatedState L R δ a π query update initial t)
      ‖x‖ < 3 * R → ∀ j : Fin (k + 1), t ≤ j.val → |x (π j)| ≤ δ / 4) :
    simulatedState L R δ a π query update initial T =
      (fun s => update s (field L R δ a π (query s)))^[T] initial := by
  induction T with
  | zero => rfl
  | succ T ih =>
    have he := ih (fun t ht => hgood t (by omega))
    rw [simulatedState, partialField_eq L R δ a hR hδ π ha T _ (hgood T (by omega)), he,
      Function.iterate_succ_apply']

end LongTails.Proofs.SmoothConvexFiniteSimulation
