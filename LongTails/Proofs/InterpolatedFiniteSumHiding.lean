import LongTails.Proofs.AdamFinitePaths
import LongTails.Proofs.SmoothConvexFiniteHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumHiding

lemma indicator_exists_le_sum {J : Type*} [Fintype J] (P : J → Prop) [DecidablePred P]
    [Decidable (∃ j, P j)] :
    (if ∃ j, P j then (1 : ℝ) else 0) ≤ ∑ j, if P j then (1 : ℝ) else 0 := by
  classical
  by_cases h : ∃ j, P j
  · obtain ⟨j, hj⟩ := h
    rw [ite_eq_left ⟨j, hj⟩]
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if P j then (1 : ℝ) else 0) (fun j _ => by positivity)
      (Finset.mem_univ j)
    simpa only [ite_eq_left hj] using hh
  · simp only [ite_eq_right h]
    exact Finset.sum_nonneg (fun j _ => by positivity)

lemma unseen_coordinate_bound {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (seen : (I → Ω) → Finset I) (large : (I → Ω) → Finset Ω) (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ π, ((large π).card : ℝ) ≤ C)
    (hstable : ∀ π ρ, (∀ i ∈ seen π, π i = ρ i) → seen π = seen ρ ∧ large π = large ρ)
    (j : I) :
    (Fintype.card Ω : ℝ) * (∑ π : I → Ω, if j ∉ seen π ∧ π j ∈ large π then (1 : ℝ) else 0) ≤
      C * Fintype.card (I → Ω) := by
  classical
  let F := fun π : I → Ω => if j ∉ seen π ∧ π j ∈ large π then (1 : ℝ) else 0
  have hfiber (π : I → Ω) : ∑ v : Ω, F (Function.update π j v) ≤ C := by
    by_cases hex : ∃ v, j ∉ seen (Function.update π j v)
    · obtain ⟨v₀, hv₀⟩ := hex
      have he (v : Ω) :
          seen (Function.update π j v₀) = seen (Function.update π j v) ∧
          large (Function.update π j v₀) = large (Function.update π j v) := by
        apply hstable
        intro i hi
        have hij : i ≠ j := by intro h; subst i; exact hv₀ hi
        simp only [Function.update_of_ne hij]
      calc
        _ = ∑ v : Ω, if v ∈ large (Function.update π j v₀) then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro v _
          dsimp [F]
          rw [← (he v).1, ← (he v).2]
          simp only [hv₀, Function.update_self, not_false_eq_true, true_and]
        _ = ((large (Function.update π j v₀)).card : ℝ) := by simp
        _ ≤ C := hlarge _
    · have he : ∀ v, j ∈ seen (Function.update π j v) := by simpa using hex
      simpa only [F, he, not_true_eq_false, false_and, ite_false, Finset.sum_const_zero] using hC
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun π _ => hfiber π)
  rw [AdamFinitePaths.sum_coordinate_updates] at hh
  simpa only [F, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using hh

lemma any_unseen_coordinate_bound {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (seen : (I → Ω) → Finset I) (large : (I → Ω) → Finset Ω) (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ π, ((large π).card : ℝ) ≤ C)
    (hstable : ∀ π ρ, (∀ i ∈ seen π, π i = ρ i) → seen π = seen ρ ∧ large π = large ρ) :
    (Fintype.card Ω : ℝ) *
        (∑ π : I → Ω, if ∃ j, j ∉ seen π ∧ π j ∈ large π then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) * C * Fintype.card (I → Ω) := by
  classical
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun π _ =>
    indicator_exists_le_sum (fun j => j ∉ seen π ∧ π j ∈ large π))
  have hh := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (Fintype.card Ω))
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    unseen_coordinate_bound seen large C hC hlarge hstable j)
  rw [Finset.sum_comm] at hh
  rw [← Finset.mul_sum] at hb
  have he : (∑ _ : I, C * (Fintype.card (I → Ω) : ℝ)) =
      (Fintype.card I : ℝ) * C * Fintype.card (I → Ω) := by simp [mul_assoc]
  rw [he] at hb
  exact hh.trans hb

lemma equal_coordinates_count {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (i j : I) (hij : i ≠ j) :
    (Fintype.card Ω : ℝ) * (∑ π : I → Ω, if π i = π j then (1 : ℝ) else 0) =
      Fintype.card (I → Ω) := by
  classical
  rw [← AdamFinitePaths.sum_coordinate_updates j
    (fun π : I → Ω => if π i = π j then (1 : ℝ) else 0)]
  have he (π : I → Ω) :
      (∑ v : Ω, if (Function.update π j v) i = (Function.update π j v) j then (1 : ℝ) else 0) = 1 := by
    simp [Function.update_of_ne hij]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

lemma finite_union_bound {A J : Type*} [Fintype A] [Fintype J]
    (D : ℝ) (hD : 0 ≤ D) (P : J → A → Prop) (B : J → ℝ)
    (h : ∀ j, D * (∑ a, if P j a then (1 : ℝ) else 0) ≤ B j) :
    D * (∑ a, if ∃ j, P j a then (1 : ℝ) else 0) ≤ ∑ j, B j := by
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    indicator_exists_le_sum (fun j => P j a))
  have hh := mul_le_mul_of_nonneg_left hp hD
  rw [Finset.sum_comm] at hh
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  rw [← Finset.mul_sum] at hb
  exact hh.trans hb

lemma collision_bound {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I] :
    (Fintype.card Ω : ℝ) * (∑ π : I → Ω, if ¬Function.Injective π then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) ^ 2 * Fintype.card (I → Ω) := by
  have he (π : I → Ω) : ¬Function.Injective π ↔ ∃ ij : I × I, ij.1 ≠ ij.2 ∧ π ij.1 = π ij.2 := by
    constructor
    · intro hn
      by_contra h
      apply hn
      intro i j hij
      by_contra hne
      exact h ⟨(i, j), hne, hij⟩
    · rintro ⟨⟨i, j⟩, hne, hij⟩ hinj
      exact hne (hinj hij)
  simp_rw [he]
  have h := finite_union_bound (A := I → Ω) (Fintype.card Ω : ℝ) (Nat.cast_nonneg _)
    (fun ij : I × I => fun π => ij.1 ≠ ij.2 ∧ π ij.1 = π ij.2)
    (fun _ => (Fintype.card (I → Ω) : ℝ)) (fun ij => by
      by_cases hij : ij.1 = ij.2
      · simp [hij]
      · simpa [hij] using
          (equal_coordinates_count (Ω := Ω) ij.1 ij.2 hij).le)
  simpa [Fintype.card_prod, pow_two, mul_assoc] using h

lemma equal_constant_count {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (j : I) (a : Ω) :
    (Fintype.card Ω : ℝ) * (∑ π : I → Ω, if π j = a then (1 : ℝ) else 0) =
      Fintype.card (I → Ω) := by
  rw [← AdamFinitePaths.sum_coordinate_updates j (fun π : I → Ω => if π j = a then (1 : ℝ) else 0)]
  simp

lemma carrier_bound {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq I] (a : Ω) :
    (Fintype.card Ω : ℝ) * (∑ π : I → Ω, if ∃ j, π j = a then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) * Fintype.card (I → Ω) := by
  have h := finite_union_bound (A := I → Ω) (Fintype.card Ω : ℝ) (Nat.cast_nonneg _)
    (fun j π => π j = a) (fun _ : I => (Fintype.card (I → Ω) : ℝ))
    (fun j => (equal_constant_count j a).le)
  simpa using h

noncomputable def run {I Ω S : Type*} [DecidableEq I]
    (step : (I → Ω) → S → S) (reveal : S → Finset I) (initial : S)
    (π : I → Ω) : ℕ → S × Finset I
  | 0 => (initial, ∅)
  | t + 1 => let st := run step reveal initial π t
    (step π st.1, st.2 ∪ reveal st.1)

lemma run_stable {I Ω S : Type*} [DecidableEq I]
    (step : (I → Ω) → S → S) (reveal : S → Finset I) (initial : S)
    (hlocal : ∀ π ρ s, (∀ i ∈ reveal s, π i = ρ i) → step π s = step ρ s)
    (π ρ : I → Ω) (t : ℕ)
    (h : ∀ i ∈ (run step reveal initial π t).2, π i = ρ i) :
    run step reveal initial π t = run step reveal initial ρ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hprev : ∀ i ∈ (run step reveal initial π t).2, π i = ρ i := by
      intro i hi
      exact h i (Finset.mem_union_left _ hi)
    have hnew : ∀ i ∈ reveal (run step reveal initial π t).1, π i = ρ i := by
      intro i hi
      exact h i (Finset.mem_union_right _ hi)
    have he := ih hprev
    simp only [run]
    rw [← he, hlocal π ρ _ hnew]

lemma run_observation_bound {I Ω S : Type*} [Fintype I] [Fintype Ω] [DecidableEq I]
    (step : (I → Ω) → S → S) (reveal : S → Finset I) (initial : S)
    (hlocal : ∀ π ρ s, (∀ i ∈ reveal s, π i = ρ i) → step π s = step ρ s)
    (large : S → Finset Ω) (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ s, ((large s).card : ℝ) ≤ C) (t : ℕ) :
    (Fintype.card Ω : ℝ) *
        (∑ π : I → Ω, if ∃ j, j ∉ (run step reveal initial π t).2 ∧
          π j ∈ large (run step reveal initial π t).1 then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) * C * Fintype.card (I → Ω) := by
  apply any_unseen_coordinate_bound _ _ C hC (fun π => hlarge _)
  intro π ρ h
  have he := run_stable step reveal initial hlocal π ρ t h
  exact ⟨congrArg Prod.snd he, congrArg (fun s => large s.1) he⟩

lemma run_family_observation_bound {I Ω S J : Type*} [Fintype I] [Fintype Ω] [Fintype J]
    [DecidableEq I] (step : (I → Ω) → S → S) (reveal : S → Finset I) (initial : S)
    (hlocal : ∀ π ρ s, (∀ i ∈ reveal s, π i = ρ i) → step π s = step ρ s)
    (time : J → ℕ) (large : J → S → Finset Ω) (C : ℝ) (hC : 0 ≤ C)
    (hlarge : ∀ j s, ((large j s).card : ℝ) ≤ C) :
    (Fintype.card Ω : ℝ) *
        (∑ π : I → Ω, if ∃ j, ∃ i, i ∉ (run step reveal initial π (time j)).2 ∧
          π i ∈ large j (run step reveal initial π (time j)).1 then (1 : ℝ) else 0) ≤
      (Fintype.card J : ℝ) * Fintype.card I * C * Fintype.card (I → Ω) := by
  have h := finite_union_bound (A := I → Ω) (Fintype.card Ω : ℝ) (Nat.cast_nonneg _)
    (fun j π => ∃ i, i ∉ (run step reveal initial π (time j)).2 ∧
      π i ∈ large j (run step reveal initial π (time j)).1)
    (fun _ : J => (Fintype.card I : ℝ) * C * Fintype.card (I → Ω))
    (fun j => by
      have hj := run_observation_bound step reveal initial hlocal (large j) C hC (hlarge j) (time j)
      convert hj using 1
      congr 1
      apply Finset.sum_congr rfl
      intro π _
      split_ifs <;> rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] at h ⊢
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro π _
  split_ifs <;> rfl

lemma indicator_or_le_add (P Q : Prop) :
    (if P ∨ Q then (1 : ℝ) else 0) ≤ (if P then 1 else 0) + (if Q then 1 else 0) := by
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]

set_option maxHeartbeats 800000 in
lemma combined_bad_bound {I S J : Type*} [Fintype I] [Fintype J] [DecidableEq I] {d : ℕ}
    (step : (I → Fin d) → S → S) (reveal : S → Finset I) (initial : S)
    (hlocal : ∀ π ρ s, (∀ i ∈ reveal s, π i = ρ i) → step π s = step ρ s)
    (time : J → ℕ) (observe : J → S → EuclideanSpace ℝ (Fin d))
    (B θ : ℝ) (hB : 0 ≤ B) (hθ : 0 < θ) (carrier : Fin d) :
    (d : ℝ) * (∑ π : I → Fin d, if ¬Function.Injective π ∨ (∃ i, π i = carrier) ∨
      (∃ j, ∃ i, i ∉ (run step reveal initial π (time j)).2 ∧
        π i ∈ SmoothConvexFiniteHiding.largeSet B θ
          (observe j (run step reveal initial π (time j)).1)) then (1 : ℝ) else 0) ≤
      ((Fintype.card I : ℝ) ^ 2 + Fintype.card I +
        Fintype.card J * Fintype.card I * (B ^ 2 / θ ^ 2)) * Fintype.card (I → Fin d) := by
  classical
  let bad₁ := fun π : I → Fin d => ¬Function.Injective π
  let bad₂ := fun π : I → Fin d => ∃ i, π i = carrier
  let bad₃ := fun π : I → Fin d => ∃ j, ∃ i,
    i ∉ (run step reveal initial π (time j)).2 ∧
      π i ∈ SmoothConvexFiniteHiding.largeSet B θ (observe j (run step reveal initial π (time j)).1)
  have h₁ := collision_bound (I := I) (Ω := Fin d)
  have h₂ := carrier_bound (I := I) carrier
  have h₃ := run_family_observation_bound step reveal initial hlocal time
    (fun j s => SmoothConvexFiniteHiding.largeSet B θ (observe j s)) (B ^ 2 / θ ^ 2)
    (by positivity) (fun _ s => SmoothConvexFiniteHiding.largeSet_bound B θ hB hθ _)
  simp only [Fintype.card_fin] at h₁ h₂ h₃
  have hp (π : I → Fin d) :
      (if bad₁ π ∨ bad₂ π ∨ bad₃ π then (1 : ℝ) else 0) ≤
        (if bad₁ π then 1 else 0) + (if bad₂ π then 1 else 0) + (if bad₃ π then 1 else 0) := by
    by_cases h₁ : bad₁ π <;> by_cases h₂ : bad₂ π <;> by_cases h₃ : bad₃ π <;>
      simp [h₁, h₂, h₃]
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun π _ => hp π)) (Nat.cast_nonneg d)
  simp only [Finset.sum_add_distrib, mul_add] at hh
  change (d : ℝ) * (∑ π, if bad₁ π ∨ bad₂ π ∨ bad₃ π then (1 : ℝ) else 0) ≤ _
  have hb₁ : (d : ℝ) * (∑ π, if bad₁ π then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) ^ 2 * Fintype.card (I → Fin d) := by
    convert h₁ using 1
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    split_ifs <;> rfl
  have hb₂ : (d : ℝ) * (∑ π, if bad₂ π then (1 : ℝ) else 0) ≤
      (Fintype.card I : ℝ) * Fintype.card (I → Fin d) := by
    convert h₂ using 1
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    split_ifs <;> rfl
  have hb₃ : (d : ℝ) * (∑ π, if bad₃ π then (1 : ℝ) else 0) ≤
      (Fintype.card J : ℝ) * Fintype.card I * (B ^ 2 / θ ^ 2) * Fintype.card (I → Fin d) := by
    convert h₃ using 1
    congr 1
    apply Finset.sum_congr rfl
    intro π _
    split_ifs <;> rfl
  nlinarith only [hh, hb₁, hb₂, hb₃]


lemma finite_loss_bound {I : Type*} [Fintype I] (bad : I → Prop) (loss cost : I → ℝ)
    (A C : ℝ) (hC : 0 ≤ C) (hc : ∀ i, 0 ≤ cost i) (hl : ∀ i, 0 ≤ loss i)
    (hgood : ∀ i, ¬bad i → A - C * cost i ≤ loss i) :
    A * Fintype.card I - A * (∑ i, if bad i then (1 : ℝ) else 0) - C * (∑ i, cost i) ≤
      ∑ i, loss i := by
  have hp (i : I) : A - A * (if bad i then (1 : ℝ) else 0) - C * cost i ≤ loss i := by
    by_cases h : bad i
    · simp only [ite_eq_left h, mul_one, sub_self, zero_sub]
      exact (neg_nonpos.mpr (mul_nonneg hC (hc i))).trans (hl i)
    · simpa only [ite_eq_right h, mul_zero, sub_zero] using hgood i h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_comm] using hs

lemma finite_average_loss {I : Type*} [Fintype I] (bad : I → Prop) (loss cost : I → ℝ)
    (A C D b : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 < D)
    (hc : ∀ i, 0 ≤ cost i) (hcb : ∀ i, cost i ≤ b) (hl : ∀ i, 0 ≤ loss i)
    (hgood : ∀ i, ¬bad i → A - C * cost i ≤ loss i)
    (hbad : D * (∑ i, if bad i then (1 : ℝ) else 0) ≤ D * Fintype.card I / 8) :
    (7 * A / 8 - C * b) * Fintype.card I ≤ ∑ i, loss i := by
  have hbase := finite_loss_bound bad loss cost A C hC hc hl hgood
  have hcount : (∑ i, if bad i then (1 : ℝ) else 0) ≤ (Fintype.card I : ℝ) / 8 := by
    apply (mul_le_mul_iff_right₀ hD).mp
    nlinarith only [hbad]
  have hbc := mul_le_mul_of_nonneg_left hcount hA
  have hcost := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcb i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hcost
  have hcc := mul_le_mul_of_nonneg_left hcost hC
  nlinarith only [hbase, hbc, hcc]

lemma finite_average_loss_sum {I : Type*} [Fintype I] (bad : I → Prop) (loss cost : I → ℝ)
    (A C b : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : ∀ i, 0 ≤ cost i) (hl : ∀ i, 0 ≤ loss i)
    (hgood : ∀ i, ¬bad i → A - C * cost i ≤ loss i)
    (hbad : (∑ i, if bad i then (1 : ℝ) else 0) ≤ Fintype.card I / 8)
    (hcost : (∑ i, cost i) ≤ b * Fintype.card I) :
    (7 * A / 8 - C * b) * Fintype.card I ≤ ∑ i, loss i := by
  have hbase := finite_loss_bound bad loss cost A C hC hc hl hgood
  have hb := mul_le_mul_of_nonneg_left hbad hA
  have hcc := mul_le_mul_of_nonneg_left hcost hC
  nlinarith only [hbase, hb, hcc]

end LongTails.Proofs.InterpolatedFiniteSumHiding
