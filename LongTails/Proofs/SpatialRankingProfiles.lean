import LongTails.Proofs.SpatialRankingGradients

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingProfiles

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.SpatialRankingGradients

structure Profile where
  a₀ : ℝ
  a₁ : ℝ
  a₂ : ℝ
  b₂ : ℝ
  b₁ : ℝ
  b₀ : ℝ

def core (n i : ℕ) (x : Profile) : ℝ :=
  (if i=1 then x.a₁ else 0) + (if i=2 then x.a₂ else 0) +
  (if i=n-2 then x.b₂ else 0) + (if i=n-1 then x.b₁ else 0)

def value (n i : ℕ) (x : Profile) : ℝ :=
  if i=0 then x.a₀ else if i=n then x.b₀ else core n i x

noncomputable def moment (n : ℕ) (g : Bool) (x : Profile) : ℝ :=
  traceValue n g 1 * x.a₁ + traceValue n g 2 * x.a₂ +
  traceValue n g (n-2) * x.b₂ + traceValue n g (n-1) * x.b₁

noncomputable def forward (n : ℕ) (g : Bool) (i : ℕ) (x : Profile) : ℝ :=
  if i=0 then (population g).anchorLag*x.a₀
  else if i=n then (population g).anchorLag*x.b₀ - moment n g x
  else (population g).itemLag*core n i x + traceValue n g i*x.a₀

noncomputable def backward (n : ℕ) (g : Bool) (i : ℕ) (x : Profile) : ℝ :=
  if i=0 then (population g).anchorLag*x.a₀ + moment n g x
  else if i=n then (population g).anchorLag*x.b₀
  else (population g).itemLag*core n i x - traceValue n g i*x.b₀

noncomputable def synth (p : Params) (D : Items p) (g : Bool) (x : Profile) : Features p.d :=
  let u := vertex p D g
  x.a₀ • u 0 + x.a₁ • u 1 + x.a₂ • u 2 + x.b₂ • u (p.n-2) + x.b₁ • u (p.n-1) + x.b₀ • u p.n

lemma synth_value {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g h : Bool) {i : ℕ} (hi : i ≤ p.n) (x : Profile) :
    ⟪vertex p D g i, synth p D h x⟫ = if g=h then value p.n i x else 0 := by
  simp only [synth, inner_add_right, real_inner_smul_right]
  simp (disch := omega) only [vertex_inner hD]
  by_cases H : g=h
  · simp only [H, true_and, ite_true, value, core]
    split_ifs <;> first | omega | ring
  · simp [H]

set_option maxHeartbeats 1200000 in
lemma synth_forward {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g h : Bool) {i : ℕ} (hi : i ≤ p.n) (x : Profile) :
    ⟪vertex p D g i, shift (synth p D h x)⟫ =
      if g=h then forward p.n g i x else 0 := by
  simp only [synth, shift_add, shift_smul, inner_add_right, real_inner_smul_right]
  simp (disch := omega) only [vertex_lag hD]
  by_cases H : g=h
  · subst h
    have h (j : ℕ) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = p.n-2 ∨ j = p.n-1 ∨ j = p.n ∨
        (j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2 ∧ j ≠ p.n-2 ∧ j ≠ p.n-1 ∧ j ≠ p.n) := by omega
    rcases h i with rfl|rfl|rfl|rfl|rfl|rfl|hi'
    all_goals simp (disch := omega) only [lagEntry, forward, moment, core, ite_eq_left, ite_eq_right,
      true_and, Nat.lt_irrefl]
    all_goals simp
    all_goals ring
  · simp [H]

set_option maxHeartbeats 1200000 in
lemma synth_backward {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g h : Bool) {i : ℕ} (hi : i ≤ p.n) (x : Profile) :
    ⟪shift (vertex p D g i), synth p D h x⟫ =
      if g=h then backward p.n g i x else 0 := by
  rw [real_inner_comm]
  simp only [synth, inner_add_left, real_inner_smul_left]
  simp (disch := omega) only [vertex_lag hD]
  by_cases H : g=h
  · subst h
    have h (j : ℕ) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = p.n-2 ∨ j = p.n-1 ∨ j = p.n ∨
        (j ≠ 0 ∧ j ≠ 1 ∧ j ≠ 2 ∧ j ≠ p.n-2 ∧ j ≠ p.n-1 ∧ j ≠ p.n) := by omega
    rcases h i with rfl|rfl|rfl|rfl|rfl|rfl|hi'
    all_goals simp (disch := omega) only [lagEntry, backward, moment, core, ite_eq_left, ite_eq_right,
      true_and, Nat.lt_irrefl]
    all_goals simp
    all_goals ring
  · simp [H, Ne.symm H]

end LongTails.Proofs.SpatialRankingProfiles
