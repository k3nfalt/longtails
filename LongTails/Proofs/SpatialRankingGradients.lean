import LongTails.Proofs.SpatialRankingExecution
import LongTails.Proofs.LogisticPathLocality
import LongTails.Proofs.LogisticPathBounds
import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingGradients

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features Space direction margin shift)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.LogisticPathLocality
open LongTails.Proofs.SpatialRankingExecution
open LongTails.Proofs.LogisticPathBounds

noncomputable def vertex (p : Params) (D : Items p) (g : Bool) (i : ℕ) : Features p.d :=
  if hi : i ≤ p.n then D g ⟨i,by omega⟩ else 0

lemma row_eq (p : Params) (D : Items p) (g : Bool) {i : ℕ} (hi : i < p.n) :
    signedRow p D g i = (population g).scale • (vertex p D g i - vertex p D g (i+1)) := by
  simp [signedRow, vertex, hi, hi.le, Nat.succ_le_of_lt hi]

noncomputable def adjoint {d : ℕ} (θ : Space .conv d) :
    Features d →ₗ[ℝ] Space .conv d where
  toFun x := direction .conv d x θ
  map_add' x y := by
    simp [direction, shift_add, inner_add_left, smul_add]
    abel
  map_smul' k x := by
    change ((⟪k • x, θ.2⟫, ⟪shift (k • x), θ.2⟫),
        θ.1.1 • (k • x) + θ.1.2 • shift (k • x)) =
      ((k * ⟪x,θ.2⟫, k * ⟪shift x,θ.2⟫), k • (θ.1.1 • x + θ.1.2 • shift x))
    rw [shift_smul, real_inner_smul_left, real_inner_smul_left, smul_add]
    congr 1
    module

noncomputable def mass (p : Params) (D : Items p) (θ : Point p) (g : Bool) (i : ℕ) : ℝ :=
  Real.sigmoid (-margin .conv p.d (signedRow p D g i) θ) * (population g).scale

noncomputable def force (p : Params) (D : Items p) (θ : Point p) (g : Bool) : Features p.d :=
  edgeForce p.n (vertex p D g) (mass p D θ g)

lemma group_answer (p : Params) (D : Items p) (θ : Point p) (g : Bool) :
    ∑ i ∈ Finset.range p.n, answer p D ((g,i),θ) = adjoint θ (force p D θ g) := by
  unfold force edgeForce
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul]
  change Real.sigmoid (-margin .conv p.d (signedRow p D g i) θ) •
    adjoint θ (signedRow p D g i) = mass p D θ g i •
      adjoint θ (vertex p D g i - vertex p D g (i+1))
  rw [mass, row_eq p D g (Finset.mem_range.mp hi), map_smul, smul_smul]

lemma batch_eq (p : Params) (D : Items p) (θ : Point p) :
    batch p D θ = θ + (2:ℝ) • adjoint θ (force p D θ false + force p D θ true) := by
  unfold batch
  rw [show 2*p.n=p.n+p.n by omega, Finset.sum_range_add, map_add,
    ← group_answer, ← group_answer]
  congr 2
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [term, Nat.not_le.mpr hi', Nat.mod_eq_of_lt hi']
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [term, Nat.mod_eq_of_lt hi']

lemma vertex_inner {p : Params} {D : Items p} (hD : Geometry p D)
    (g h : Bool) {i j : ℕ} (hi : i ≤ p.n) (hj : j ≤ p.n) :
    ⟪vertex p D g i, vertex p D h j⟫ = if g = h ∧ i = j then 1 else 0 := by
  simp [vertex, hi, hj, hD.1]

lemma vertex_lag {p : Params} {D : Items p} (hD : Geometry p D)
    (g h : Bool) {i j : ℕ} (hi : i ≤ p.n) (hj : j ≤ p.n) :
    ⟪vertex p D g i, shift (vertex p D h j)⟫ =
      if g = h then lagEntry p.n g i j else 0 := by
  simp [vertex, hi, hj, hD.2]

noncomputable def ends (p : Params) (D : Items p) (g : Bool) : Features p.d :=
  (population g).scale • (vertex p D g 0 - vertex p D g p.n)

lemma first_force (p : Params) (D : Items p) (g : Bool) :
    force p D ((1,0),0) g = (1/2:ℝ) • ends p D g := by
  unfold force edgeForce mass ends
  simp only [margin, inner_zero_right, mul_zero, add_zero, neg_zero, Real.sigmoid_zero]
  rw [← Finset.smul_sum, smul_smul]
  rw [show ∑ i ∈ Finset.range p.n, (vertex p D g i - vertex p D g (i+1)) = _ from
    (by simpa using chain_sum (vertex p D g) 0 p.n : _ = vertex p D g 0 - vertex p D g p.n)]
  norm_num

lemma first_batch (p : Params) (D : Items p) :
    batch p D ((1,0),0) = ((1,0), ends p D false + ends p D true) := by
  rw [batch_eq, first_force, first_force, ← smul_add, map_smul, smul_smul]
  norm_num [adjoint, direction]

lemma first_vertex {p : Params} {D : Items p} (hD : Geometry p D)
    (g : Bool) {i : ℕ} (hi : i ≤ p.n) :
    ⟪vertex p D g i, ends p D false + ends p D true⟫ =
      (population g).scale * ((if i=0 then 1 else 0) - (if i=p.n then 1 else 0)) := by
  simp only [ends, inner_add_right, real_inner_smul_right, inner_sub_right,
    vertex_inner hD _ _ hi (Nat.zero_le _), vertex_inner hD _ _ hi le_rfl]
  cases g <;> simp

lemma first_mass {p : Params} {D : Items p} (hD : Geometry p D) (hn : 2 ≤ p.n)
    (g : Bool) {i : ℕ} (hi : i < p.n) :
    mass p D (batch p D ((1,0),0)) g i =
      if i = 0 ∨ i+1 = p.n then Real.sigmoid (-((population g).scale^2)) * (population g).scale
      else (1/2) * (population g).scale := by
  rw [mass, first_batch, row_eq p D g hi]
  simp only [margin, one_mul, zero_mul, add_zero, real_inner_smul_left, inner_sub_left,
    first_vertex hD g hi.le, first_vertex hD g (Nat.succ_le_of_lt hi)]
  by_cases h : i = 0
  · subst i
    simp [show 0 ≠ p.n by omega, show 1 ≠ p.n by omega, pow_two]
  · by_cases he : i+1 = p.n
    · simp [h, he, show i ≠ p.n by omega, show p.n ≠ 0 by omega, pow_two]
    · simp [h, he, show i ≠ p.n by omega, Real.sigmoid_zero]

noncomputable def nearEnds (p : Params) (D : Items p) (g : Bool) (a b : ℝ) : Features p.d :=
  a • (vertex p D g 0 - vertex p D g p.n) +
    b • (vertex p D g 1 - vertex p D g (p.n-1))

lemma second_force {p : Params} {D : Items p} (hD : Geometry p D) (hn : 4 ≤ p.n) (g : Bool) :
    force p D (batch p D ((1,0),0)) g = nearEnds p D g (extremeWeight (population g))
      ((population g).scale / 2 - extremeWeight (population g)) := by
  let q := mass p D (batch p D ((1,0),0)) g
  let f := (population g).scale
  let e := extremeWeight (population g)
  have hq (i : ℕ) (hi : i < p.n) : q i = if i=0 ∨ i+1=p.n then e else f/2 := by
    rw [show q i = _ from first_mass hD (by omega) g hi]
    dsimp [e, f, extremeWeight]
    split_ifs <;> ring
  have he := boundary_force hn (vertex p D g) q e (f/2) (f/2) e
    (by rw [hq 0 (by omega)]; simp)
    (by rw [hq (p.n-1) (by omega), ite_eq_left (Or.inr (by omega))])
    (by rw [hq 1 (by omega), ite_eq_right (by omega)])
    (by rw [hq (p.n-2) (by omega), ite_eq_right (by omega)])
    (fun i hl hr => by rw [hq i (by omega), ite_eq_right (by omega)])
  change edgeForce p.n (vertex p D g) q = _
  rw [he]
  unfold nearEnds
  change _ = e • _ + (f/2-e) • _
  module

lemma trace_ends {n : ℕ} (hn : 4 ≤ n) (g : Bool) :
    traceValue n g 1 = (population g).left / Real.sqrt n ∧
    traceValue n g (n-1) = (population g).right / Real.sqrt n := by
  have hn' : (n-2 : ℕ) ≠ 0 := by omega
  have hd : ((n-2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn'
  simp only [traceValue, Nat.sub_self, Nat.cast_zero, mul_zero, zero_div, add_zero,
    show n-1-1=n-2 by omega, mul_div_cancel_right₀ _ hd, true_and]
  cases g <;> norm_num [population, first, second]

lemma ends_direct {p : Params} {D : Items p} (hD : Geometry p D) (hn : 4 ≤ p.n)
    (g h : Bool) (a b : ℝ) : ⟪nearEnds p D g a b, ends p D h⟫ =
      if g=h then 2*(population h).scale*a else 0 := by
  simp only [nearEnds, ends, inner_add_left, real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right]
  simp (disch := omega) only [vertex_inner hD]
  by_cases H : g=h <;> simp [H, show p.n ≠ 0 by omega, show 0 ≠ p.n by omega,
    show p.n-1 ≠ 0 by omega, show p.n-1 ≠ p.n by omega, show 1 ≠ p.n by omega]
  ring

lemma ends_lag {p : Params} {D : Items p} (hD : Geometry p D) (hn : 4 ≤ p.n)
    (g h : Bool) (a b : ℝ) : ⟪shift (nearEnds p D g a b), ends p D h⟫ =
      if g=h then (population h).scale *
        (2*(population h).anchorLag*a - (population h).slope / Real.sqrt p.n*b) else 0 := by
  rw [real_inner_comm]
  simp only [nearEnds, ends, shift_add, shift_smul, shift_sub, real_inner_smul_left,
    inner_sub_left, inner_add_right, real_inner_smul_right, inner_sub_right]
  simp (disch := omega) only [vertex_lag hD]
  by_cases H : g=h
  · subst h
    simp [lagEntry, trace_ends hn g, show 0 ≠ p.n by omega, show p.n ≠ 0 by omega,
      show p.n ≠ 1 by omega, show 0 ≠ p.n-1 by omega, show p.n ≠ p.n-1 by omega,
      show 0 < p.n-1 by omega, show p.n-1 ≠ 0 by omega]
    cases g <;> norm_num [population, first, second] <;> ring
  · simp [H, Ne.symm H]

noncomputable def secondReadout (p : Params) (D : Items p) (g : Bool) : Features p.d :=
  nearEnds p D g (anchorCoeff (population g)) (nearCoeff (population g))

lemma readout_update (p : Params) (D : Items p) (g : Bool) :
    ends p D g + (2:ℝ) • nearEnds p D g (extremeWeight (population g))
      ((population g).scale / 2 - extremeWeight (population g)) = secondReadout p D g := by
  unfold ends nearEnds secondReadout nearEnds anchorCoeff nearCoeff
  module

lemma second_batch {p : Params} {D : Items p} (hD : Geometry p D) (hn : 4 ≤ p.n) :
    batch p D (batch p D ((1,0),0)) =
      (secondTaps (Real.sqrt p.n)⁻¹, secondReadout p D false + secondReadout p D true) := by
  rw [batch_eq, second_force hD hn, second_force hD hn, first_batch]
  let F (g : Bool) := nearEnds p D g (extremeWeight (population g))
    ((population g).scale / 2 - extremeWeight (population g))
  apply Prod.ext
  · apply Prod.ext
    · change 1 + 2 * ⟪F false + F true, ends p D false + ends p D true⟫ = _
      simp [F, inner_add_left, inner_add_right, ends_direct hD hn, secondTaps, population]
      ring
    · change 0 + 2 * ⟪shift (F false + F true), ends p D false + ends p D true⟫ = _
      simp [F, shift_add, inner_add_left, inner_add_right, ends_lag hD hn, secondTaps, population,
        nearCoeff, div_eq_mul_inv]
      ring
  · change ends p D false + ends p D true + (2:ℝ) • ((1:ℝ) • (F false + F true) +
        (0:ℝ) • shift (F false + F true)) = _
    rw [one_smul, zero_smul, add_zero, smul_add, ← readout_update, ← readout_update]
    dsimp only [F]
    abel

end LongTails.Proofs.SpatialRankingGradients
