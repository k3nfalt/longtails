import LongTails.Proofs.BlackBoxRun

open scoped BigOperators

namespace OracleTemplate.BlackBoxDiagonal

variable {d : ℕ} [NeZero d]

section Probe

variable (f : Vec d → ℝ) (x0 : Vec d)

noncomputable def sec (k : Fin d) : ℝ :=
  gradient f (x0 + EuclideanSpace.single k 1) k - gradient f x0 k

noncomputable def Jpart (p : ℕ) : Fin d → ℝ := fun k => if k.val < p then sec f x0 k else 1

noncomputable def probeSt (p : ℕ) : St d :=
  { initial x0 with g0 := gradient f x0, pidx := p, J := Jpart f x0 (p - 1) }

noncomputable def startSt : St d :=
  let J := sec f x0
  { probeSt f x0 d with probing := false, J := J, θ := th0 J 0, pidx := d + 1, s := 0 }

omit [NeZero d] in
lemma Jpart_zero : Jpart f x0 0 = fun _ => 1 := by
  funext k; simp [Jpart]

omit [NeZero d] in
lemma Jpart_succ (p : ℕ) (hp : p < d) :
    Function.update (Jpart f x0 p) ⟨p, hp⟩ (sec f x0 ⟨p, hp⟩) = Jpart f x0 (p + 1) := by
  funext k
  by_cases hk : k = ⟨p, hp⟩
  · subst hk; simp [Jpart]
  · rw [Function.update_of_ne hk]
    have : k.val ≠ p := fun h => hk (Fin.ext h)
    simp only [Jpart]
    by_cases h1 : k.val < p
    · simp [h1, show k.val < p + 1 by omega]
    · simp [h1, show ¬ k.val < p + 1 by omega]

omit [NeZero d] in
lemma Jpart_full : Jpart f x0 d = sec f x0 := by
  funext k; simp [Jpart, k.isLt]

omit [NeZero d] in
lemma probe_first : stepOf f x0 (initial x0) = probeSt f x0 1 := by
  unfold stepOf updateOf probeSt
  simp only [initial, ↓reduceIte]
  rw [show (1 : ℕ) - 1 = 0 from rfl, Jpart_zero]
  simp [queryOf, orc]

omit [NeZero d] in
lemma probe_step (p : ℕ) (h1 : 1 ≤ p) (hp : p < d) :
    stepOf f x0 (probeSt f x0 p) = probeSt f x0 (p + 1) := by
  have hq : p - 1 < d := by omega
  unfold stepOf updateOf
  have hne : p ≠ 0 := by omega
  have hnd : p ≠ d := by omega
  simp only [probeSt, initial, ↓reduceIte, hne, hq, ↓reduceDIte, hnd]
  have hquery : queryOf x0 (probeSt f x0 p) = x0 + EuclideanSpace.single ⟨p - 1, hq⟩ 1 := by
    simp [queryOf, probeSt, initial, hq, hne]
  simp only [probeSt, initial] at hquery
  rw [hquery]
  simp only [orc]
  have e := Jpart_succ f x0 (p - 1) hq
  rw [show p - 1 + 1 = p by omega] at e
  rw [show p + 1 - 1 = p by omega, ← e]
  rfl

lemma probe_last : stepOf f x0 (probeSt f x0 d) = startSt f x0 := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hq : d - 1 < d := by omega
  unfold stepOf updateOf
  have hne : d ≠ 0 := by omega
  simp only [probeSt, initial, ↓reduceIte, hne, hq, ↓reduceDIte]
  have hquery : queryOf x0 (probeSt f x0 d) = x0 + EuclideanSpace.single ⟨d - 1, hq⟩ 1 := by
    simp [queryOf, probeSt, initial, hq, hne]
  simp only [probeSt, initial] at hquery
  rw [hquery]
  simp only [orc]
  have e := Jpart_succ f x0 (d - 1) hq
  rw [show d - 1 + 1 = d by omega, Jpart_full] at e
  unfold startSt probeSt
  simp only [initial]
  rw [← e]
  rfl

omit [NeZero d] in
lemma probe_iterate : ∀ p, 1 ≤ p → p ≤ d → (stepOf f x0)^[p] (initial x0) = probeSt f x0 p
  | 0, h, _ => by omega
  | 1, _, _ => by simp [probe_first]
  | p + 2, _, hp => by
      rw [Function.iterate_succ_apply', probe_iterate (p + 1) (by omega) (by omega)]
      exact probe_step f x0 (p + 1) (by omega) (by omega)

lemma start_iterate : (stepOf f x0)^[d + 1] (initial x0) = startSt f x0 := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  rw [Function.iterate_succ_apply', probe_iterate f x0 d hd le_rfl, probe_last]

end Probe

end OracleTemplate.BlackBoxDiagonal
