import LongTails.Proofs.RegretMatchingGame

open Finset

namespace OracleTemplate.RegretMatchingPotential

variable {m n : ℕ}

def Good (A C : Fin m → Fin n → ℝ) (ε : ℝ) (t : ℕ) : Prop :=
  (∀ a, regret (traj A C t).1 (payoffX A (strategy (traj A C t).2)) a ≤ ε) ∧
    ∀ b, regret (traj A C t).2 (payoffY C (strategy (traj A C t).1)) b ≤ ε

lemma exists_good_round {A C P : Fin m → Fin n → ℝ} {B ε : ℝ} (G : Game A C P B) (hε : 0 < ε)
    {T : ℕ} (hT : 20000 * B ^ 2 * ((m : ℝ) + n) ^ 4 / ε ^ 2 < T) : ∃ t < T, Good A C ε t := by
  classical
  have hb := size_bound G T
  have ex : sqNorm (traj A C T).1 ≤ (100 * B * ((m : ℝ) + n) ^ 2) ^ 2 := by
    rw [← size_sq]; exact pow_le_pow_left₀ (size_nonneg _) hb.1 2
  have ey : sqNorm (traj A C T).2 ≤ (100 * B * ((m : ℝ) + n) ^ 2) ^ 2 := by
    rw [← size_sq]; exact pow_le_pow_left₀ (size_nonneg _) hb.2 2
  have h0x : sqNorm (traj A C 0).1 = 0 := by simp [traj, sqNorm]
  have h0y : sqNorm (traj A C 0).2 = 0 := by simp [traj, sqNorm]
  have hT' : 20000 * B ^ 2 * ((m : ℝ) + n) ^ 4 < ε ^ 2 * T := by
    rw [div_lt_iff₀ (by positivity)] at hT; linarith
  have e : (100 * B * ((m : ℝ) + n) ^ 2) ^ 2 = 10000 * B ^ 2 * ((m : ℝ) + n) ^ 4 := by ring
  obtain ⟨t, ht, h1, h2⟩ := exists_good (Nx := fun t => sqNorm (traj A C t).1)
    (Ny := fun t => sqNorm (traj A C t).2)
    (bx := fun t => ∃ a, ε < regret (traj A C t).1 (payoffX A (strategy (traj A C t).2)) a)
    (byy := fun t => ∃ b, ε < regret (traj A C t).2 (payoffY C (strategy (traj A C t).1)) b)
    (e := ε ^ 2) (by positivity)
    (fun t => by
      have := sqNorm_mono G.hm (traj_nonneg A C t).1 (payoffX A (strategy (traj A C t).2))
      rw [← trajX_succ] at this; exact this)
    (fun t => by
      have := sqNorm_mono G.hn (traj_nonneg A C t).2 (payoffY C (strategy (traj A C t).1))
      rw [← trajY_succ] at this; exact this)
    (fun t ⟨a, ha⟩ => by
      have := regret_sq_le G.hm (traj_nonneg A C t).1 (payoffX A (strategy (traj A C t).2))
        (a := a) (by linarith)
      rw [← trajX_succ] at this
      show ε ^ 2 ≤ sqNorm (traj A C (t + 1)).1 - sqNorm (traj A C t).1
      nlinarith)
    (fun t ⟨b, hb⟩ => by
      have := regret_sq_le G.hn (traj_nonneg A C t).2 (payoffY C (strategy (traj A C t).1))
        (a := b) (by linarith)
      rw [← trajY_succ] at this
      show ε ^ 2 ≤ sqNorm (traj A C (t + 1)).2 - sqNorm (traj A C t).2
      nlinarith)
    (T := T) (by
      show sqNorm (traj A C T).1 - sqNorm (traj A C 0).1 +
        (sqNorm (traj A C T).2 - sqNorm (traj A C 0).2) < ε ^ 2 * T
      linarith)
  exact ⟨t, ht, fun a => not_lt.mp fun h => h1 ⟨a, h⟩, fun b => not_lt.mp fun h => h2 ⟨b, h⟩⟩

noncomputable def upd (A C : Fin m → Fin n → ℝ) (ε : ℝ) :
    (rmPlusPotential m n ε).State → (rmPlusPotential m n ε).State := fun s =>
  (rmPlusPotential m n ε).update s
    ((fun z : (Fin m → ℝ) × (Fin n → ℝ) => (payoffX A z.2, payoffY C z.1))
      (((rmPlusPotential m n ε).query s).2))

lemma run_state (A C : Fin m → Fin n → ℝ) (ε : ℝ) (k : ℕ) :
    ((upd A C ε)^[k] ((rmPlusPotential m n ε).initial ())).1 = (traj A C k).1 ∧
    ((upd A C ε)^[k] ((rmPlusPotential m n ε).initial ())).2.1 = (traj A C k).2 ∧
    ((∃ t < k, Good A C ε t ∧ ((upd A C ε)^[k] ((rmPlusPotential m n ε).initial ())).2.2 =
      (strategy (traj A C t).1, strategy (traj A C t).2)) ∨ ∀ t < k, ¬ Good A C ε t) := by
  induction k with
  | zero => exact ⟨rfl, rfl, Or.inr fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3⟩ := ih
    generalize (upd A C ε)^[k] ((rmPlusPotential m n ε).initial ()) = s at h1 h2 h3 ⊢
    obtain ⟨Qx, Qy, out⟩ := s
    dsimp only at h1 h2 h3
    subst h1 h2
    refine ⟨rfl, rfl, ?_⟩
    dsimp only [upd, rmPlusPotential]
    by_cases hg : Good A C ε k
    · have hg' := hg
      unfold Good at hg'
      rw [ite_eq_left_of_eq_true _ _ (eq_true hg')]
      exact Or.inl ⟨k, Nat.lt_succ_self k, hg, rfl⟩
    · have hg' := hg
      unfold Good at hg'
      rw [ite_eq_right_of_eq_false _ _ (eq_false hg')]
      rcases h3 with ⟨t, ht, hgt, he⟩ | h
      · exact Or.inl ⟨t, Nat.lt_succ_of_lt ht, hgt, he⟩
      · exact Or.inr fun t ht => (Nat.lt_succ_iff_lt_or_eq.mp ht).elim (h t) (· ▸ hg)


lemma nash_of_good {A C P : Fin m → Fin n → ℝ} {B ε : ℝ} (G : Game A C P B) {t : ℕ}
    (h : Good A C ε t) :
    (∀ i, 0 ≤ strategy (traj A C t).1 i) ∧ ∑ i, strategy (traj A C t).1 i = 1 ∧
    (∀ j, 0 ≤ strategy (traj A C t).2 j) ∧ ∑ j, strategy (traj A C t).2 j = 1 ∧
    (∀ i, ∑ j, A i j * strategy (traj A C t).2 j ≤
      ∑ i', ∑ j, strategy (traj A C t).1 i' * A i' j * strategy (traj A C t).2 j + ε) ∧
    ∀ j, ∑ i, strategy (traj A C t).1 i * C i j ≤
      ∑ i, ∑ j', strategy (traj A C t).1 i * C i j' * strategy (traj A C t).2 j' + ε := by
  refine ⟨(stratX_simplex G t).1, (stratX_simplex G t).2, (stratY_simplex G t).1,
    (stratY_simplex G t).2, fun i => ?_, fun j => ?_⟩
  · have := h.1 i
    unfold regret value payoffX at this
    have e : ∑ a, strategy (traj A C t).1 a * ∑ j, A a j * strategy (traj A C t).2 j =
        ∑ i', ∑ j, strategy (traj A C t).1 i' * A i' j * strategy (traj A C t).2 j :=
      sum_congr rfl fun i' _ => by rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
    linarith
  · have := h.2 j
    unfold regret value payoffY at this
    have e1 : ∑ i, C i j * strategy (traj A C t).1 i = ∑ i, strategy (traj A C t).1 i * C i j :=
      sum_congr rfl fun i _ => mul_comm _ _
    have e2 : ∑ b, strategy (traj A C t).2 b * ∑ i, C i b * strategy (traj A C t).1 i =
        ∑ i, ∑ j', strategy (traj A C t).1 i * C i j' * strategy (traj A C t).2 j' := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun b _ => by ring
    linarith

lemma output_nash {A C P : Fin m → Fin n → ℝ} {B ε : ℝ} (G : Game A C P B) (hε : 0 < ε)
    {T : ℕ} (hT : 20000 * B ^ 2 * ((m : ℝ) + n) ^ 4 / ε ^ 2 < T) :
    let out := (rmPlusPotential m n ε).output ((upd A C ε)^[T] ((rmPlusPotential m n ε).initial ()))
    (∀ i, 0 ≤ out.1 i) ∧ ∑ i, out.1 i = 1 ∧ (∀ j, 0 ≤ out.2 j) ∧ ∑ j, out.2 j = 1 ∧
    (∀ i, ∑ j, A i j * out.2 j ≤ ∑ i', ∑ j, out.1 i' * A i' j * out.2 j + ε) ∧
    ∀ j, ∑ i, out.1 i * C i j ≤ ∑ i, ∑ j', out.1 i * C i j' * out.2 j' + ε := by
  intro out
  obtain ⟨t, ht, hg⟩ := exists_good_round G hε hT
  rcases (run_state A C ε T).2.2 with ⟨t', _, hg', he⟩ | h
  · have : out = (strategy (traj A C t').1, strategy (traj A C t').2) := he
    rw [this]
    exact nash_of_good G hg'
  · exact absurd hg (h t ht)

end OracleTemplate.RegretMatchingPotential
