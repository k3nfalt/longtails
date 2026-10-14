import LongTails.Proofs.ExtragradientStep
import LongTails.Proofs.Execution

open scoped BigOperators

namespace OracleTemplate.SaddlePoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable def extraBase (X : Set E) (Y : Set F) (η : ℝ)
    (g : E × F → E × F) : ℕ → E × F
  | 0 => (start X, start Y)
  | n + 1 => prox X Y η (extraBase X Y η g n)
      (g (prox X Y η (extraBase X Y η g n) (g (extraBase X Y η g n))))

noncomputable def extraPredict (X : Set E) (Y : Set F) (η : ℝ)
    (g : E × F → E × F) (n : ℕ) : E × F :=
  prox X Y η (extraBase X Y η g n) (g (extraBase X Y η g n))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma start_mem {X : Set E} (h : X.Nonempty) : start X ∈ X := by
  rw [start, dite_eq_left h]
  exact h.choose_spec

omit [CompleteSpace E] [CompleteSpace F] in
lemma extraBase_mem {X : Set E} {Y : Set F} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hxc : IsCompact X) (hyc : IsCompact Y) (hxv : Convex ℝ X) (hyv : Convex ℝ Y)
    (η : ℝ) (g : E × F → E × F) (n : ℕ) : extraBase X Y η g n ∈ X ×ˢ Y := by
  cases n with
  | zero => exact ⟨start_mem hx, start_mem hy⟩
  | succ n => exact prox_mem hx hy hxc hyc hxv hyv η _ _

omit [CompleteSpace E] [CompleteSpace F] in
lemma extraPredict_mem {X : Set E} {Y : Set F} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hxc : IsCompact X) (hyc : IsCompact Y) (hxv : Convex ℝ X) (hyv : Convex ℝ Y)
    (η : ℝ) (g : E × F → E × F) (n : ℕ) : extraPredict X Y η g n ∈ X ×ˢ Y :=
  prox_mem hx hy hxc hyc hxv hyv η _ _

omit [CompleteSpace E] [CompleteSpace F] in
lemma execute_extragradient (L D ε : ℝ) (X : Set E) (Y : Set F)
    (g : E × F → E × F) (N : ℕ) (hN : N ≠ 0) :
    execute { answer := fun _ (_, z) _ => g z } (extragradient (L, D, ε, X, Y)) (fun _ => (2 * N)) =
      (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, extraPredict X Y (1 / (2 * L)) g k := by
  let A := extragradient (L, D, ε, X, Y)
  let T := fun s => A.update s (g ((A.query s).2))
  have hi : ∀ n, ∃ old : E × F,
      T^[2 * n] (A.initial ()) =
        (false, n, extraBase X Y (1 / (2 * L)) g n, old,
          ∑ k ∈ Finset.range n, extraPredict X Y (1 / (2 * L)) g k) := by
    intro n
    induction n with
    | zero => exact ⟨0, rfl⟩
    | succ n ih =>
      obtain ⟨old, ih⟩ := ih
      refine ⟨extraPredict X Y (1 / (2 * L)) g n, ?_⟩
      rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [ih]
      simp [T, A, extragradient, extraBase, extraPredict, Finset.sum_range_succ]
  erw [execute_iterate]
  obtain ⟨old, hi⟩ := hi N
  change A.output (T^[2 * N] (A.initial ())) = _
  rw [hi]
  simp [A, extragradient, hN]

omit [CompleteSpace E] [CompleteSpace F] in
lemma extragradient_regret {X : Set E} {Y : Set F} (hx : X.Nonempty) (hy : Y.Nonempty)
    (hxc : IsCompact X) (hyc : IsCompact Y) (hxv : Convex ℝ X) (hyv : Convex ℝ Y)
    (g : E × F → E × F) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ z w, ‖g z - g w‖ ≤ L * ‖z - w‖)
    (u : E × F) (hu : u ∈ X ×ˢ Y) (N : ℕ) :
    (∑ k ∈ Finset.range N, pairing (g (extraPredict X Y (1 / (2 * L)) g k))
      (extraPredict X Y (1 / (2 * L)) g k - u)) ≤
        L * energy (start X, start Y) u := by
  have htel : ∀ n, (1 / L) *
      (∑ k ∈ Finset.range n, pairing (g (extraPredict X Y (1 / (2 * L)) g k))
        (extraPredict X Y (1 / (2 * L)) g k - u)) ≤
      energy (start X, start Y) u - energy (extraBase X Y (1 / (2 * L)) g n) u := by
    intro n
    induction n with
    | zero => simp [extraBase]
    | succ n ih =>
      have hs := extragradient_step hx hy hxc hyc hxv hyv g hL hlip
        (extraBase X Y (1 / (2 * L)) g n) u hu
      dsimp only at hs
      change 2 * (1 / (2 * L)) * pairing (g (extraPredict X Y (1 / (2 * L)) g n))
        (extraPredict X Y (1 / (2 * L)) g n - u) ≤
        energy (extraBase X Y (1 / (2 * L)) g n) u -
          energy (extraBase X Y (1 / (2 * L)) g (n + 1)) u at hs
      have hh : 2 * (1 / (2 * L)) = 1 / L := by ring
      rw [hh] at hs
      rw [Finset.sum_range_succ]
      linarith
  have h := htel N
  have hn := energy_nonneg (extraBase X Y (1 / (2 * L)) g N) u
  have hh := mul_le_mul_of_nonneg_left h hL.le
  have he : L * (1 / L) = 1 := by field_simp
  rw [← mul_assoc, he, one_mul] at hh
  nlinarith

end OracleTemplate.SaddlePoint
