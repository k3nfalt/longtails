import LongTails.Proofs.SpatialRankingProfiles

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingMargins

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.LogisticPathBounds
open LongTails.Proofs.LogisticPathLocality
open LongTails.Proofs.SpatialRankingExecution
open LongTails.Proofs.SpatialRankingGradients
open LongTails.Proofs.SpatialRankingProfiles

noncomputable def u (n : ℕ) : ℝ := (Real.sqrt n)⁻¹
noncomputable def v (n : ℕ) : ℝ := ((n-2 : ℕ) : ℝ)⁻¹

lemma trace_step (n i : ℕ) (g : Bool) (hi : 0 < i) :
    traceValue n g (i+1) = traceValue n g i + (population g).slope * u n * v n := by
  have he : ((i+1-1 : ℕ) : ℝ) = ((i-1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show i+1-1 = i-1+1 by omega)
  simp only [traceValue, u, v, he, div_eq_mul_inv]
  ring

lemma right_eq (g : Bool) :
    (population g).right = (population g).left + (population g).slope := by
  cases g <;> norm_num [population, first, second]

noncomputable def head (g : Bool) : Profile :=
  let A := anchorCoeff (population g)
  let B := nearCoeff (population g)
  ⟨A,B,0,0,-B,-A⟩

def impulse (w : Weights) : Profile :=
  ⟨w.left,w.near-w.left,w.bulk-w.near,w.near-w.bulk,w.right-w.near,-w.right⟩

lemma head_eq (p : Params) (D : Items p) (g : Bool) :
    secondReadout p D g = synth p D g (head g) := by
  unfold secondReadout nearEnds synth head
  dsimp
  module

lemma head_moment (n : ℕ) (hn : 8 ≤ n) (g : Bool) :
    moment n g (head g) = -nearCoeff (population g) * (population g).slope * u n := by
  simp only [moment, head, trace_ends (by omega : 4 ≤ n) g, right_eq, u, div_eq_mul_inv]
  ring

lemma impulse_moment (n : ℕ) (hn : 8 ≤ n) (g : Bool) (w : Weights) :
    moment n g (impulse w) = contact (population g) (u n) (v n) w := by
  have hl := trace_step n 1 g (by omega)
  have hr := trace_step n (n-2) g (by omega)
  rw [show n-2+1=n-1 by omega] at hr
  have hh := trace_ends (by omega : 4 ≤ n) g
  change traceValue n g 1 = (population g).left * u n ∧
    traceValue n g (n-1) = (population g).right * u n at hh
  rw [hh.1] at hl
  rw [hh.2] at hr
  change traceValue n g 2 = _ at hl
  unfold moment impulse contact
  rw [hh.1, hh.2, hl, show traceValue n g (n-2) = _ from eq_sub_of_add_eq hr.symm]
  rw [right_eq]
  ring

noncomputable def theta₂ (p : Params) (D : Items p) : Point p :=
  (secondTaps (u p.n), synth p D false (head false) + synth p D true (head true))

lemma step₂ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n) :
    batch p D (batch p D ((1,0),0)) = theta₂ p D := by
  rw [second_batch hD (by omega), head_eq, head_eq]
  rfl

noncomputable def score (p : Params) (D : Items p) (g : Bool) (i : ℕ) (θ : Point p) : ℝ :=
  margin .conv p.d (vertex p D g i) θ

lemma margin_eq {p : Params} (D : Items p) (g : Bool) {i : ℕ} (hi : i < p.n) (θ : Point p) :
    margin .conv p.d (signedRow p D g i) θ =
      (population g).scale * (score p D g i θ - score p D g (i+1) θ) := by
  rw [row_eq p D g hi]
  simp only [score, margin, real_inner_smul_left, inner_sub_left, shift_smul, shift_sub]
  ring

lemma score₂ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g : Bool) {i : ℕ} (hi : i ≤ p.n) :
    score p D g i (theta₂ p D) =
      (secondTaps (u p.n)).1 * value p.n i (head g) +
      (secondTaps (u p.n)).2 * backward p.n g i (head g) := by
  cases g <;> simp [score, theta₂, margin, inner_add_right, synth_value hD hn _ _ hi,
    synth_backward hD hn _ _ hi]

noncomputable def edgeWeight (n : ℕ) (w : Weights) (i : ℕ) : ℝ :=
  if i=0 then w.left else if i+1=n then w.right
  else if i=1 ∨ i+2=n then w.near else w.bulk

noncomputable def trainingWeights (n : ℕ) (g : Bool) : Weights :=
  let c := secondTaps (u n)
  weights (population g) (u n) (v n) c.1 c.2

lemma mass₂ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g : Bool) {i : ℕ} (hi : i < p.n) :
    mass p D (theta₂ p D) g i = edgeWeight p.n (trainingWeights p.n g) i := by
  let c := secondTaps (u p.n)
  let P := population g
  let A := anchorCoeff P
  let B := nearCoeff P
  let E := c.1 + c.2*P.itemLag
  let E₀ := c.1 + c.2*P.anchorLag
  let s := c.2*A
  let τ := traceValue p.n g
  let δ := P.slope*u p.n*v p.n
  have hends := trace_ends (by omega : 4 ≤ p.n) g
  change τ 1 = P.left*u p.n ∧ τ (p.n-1) = P.right*u p.n at hends
  have hd (j : ℕ) (hj : 0 < j) : τ (j+1) = τ j + δ := trace_step _ _ _ hj
  let z (j : ℕ) := score p D g j (theta₂ p D)
  have zl : z 0 = E₀*A - c.2*B*P.slope*u p.n := by
    rw [show z 0 = _ from score₂ hD hn g (Nat.zero_le _)]
    simp only [value, backward, ite_true, head_moment _ hn]
    dsimp [head, E₀, c, A, B, P]
    ring
  have zr : z p.n = -E₀*A := by
    rw [show z p.n = _ from score₂ hD hn g le_rfl]
    simp [value, backward, show p.n ≠ 0 by omega, head, E₀, A, c, P]
    ring
  have zm (j : ℕ) (hj : 0 < j) (hk : j < p.n) :
      z j = E*((if j=1 then B else 0) - (if j=p.n-1 then B else 0)) + τ j*s := by
    rw [show z j = _ from score₂ hD hn g hk.le]
    simp [value, backward, core, head, hj.ne', hk.ne, E, A, B, c, P, τ, s]
    split_ifs <;> ring
  rw [mass, margin_eq D g hi]
  change Real.sigmoid (- (P.scale * (z i - z (i+1)))) * P.scale = _
  have H (m : ℝ) (hm : z i-z (i+1)=m) : Real.sigmoid (-(P.scale*(z i-z (i+1))))*P.scale =
      P.scale*Real.sigmoid (-(P.scale*m)) := by
    rw [hm, mul_comm]
  change _ = edgeWeight p.n (weights P (u p.n) (v p.n) c.1 c.2) i
  by_cases hl : i=0
  · subst i
    simp only [edgeWeight, ite_true, weights]
    apply H
    rw [zl, zm 1 (by omega) (by omega), hends.1]
    simp [show 1 ≠ p.n-1 by omega, E, E₀, A, B, s]
    ring
  by_cases hr : i+1=p.n
  · have he : i=p.n-1 := by omega
    conv_rhs => simp only [edgeWeight, hl, hr, ite_true, ite_false]
    apply H
    rw [hr, zr, zm i (by omega) hi, he, hends.2]
    simp [show p.n-1 ≠ 1 by omega, E, E₀, A, B, s]
    ring
  have zi := zm i (by omega) hi
  have zj := zm (i+1) (by omega) (by omega)
  rw [hd i (by omega)] at zj
  by_cases hn' : i=1 ∨ i+2=p.n
  · simp only [edgeWeight, hl, hr, hn', ite_true, ite_false]
    apply H
    rw [zi,zj]
    rcases hn' with h|h
    · subst i
      simp [show 1 ≠ p.n-1 by omega, show 2 ≠ p.n-1 by omega, E, B, s, δ]
      ring
    · simp [show i ≠ 1 by omega, show i ≠ p.n-1 by omega,
        show i+1=p.n-1 by omega, show p.n ≠ 2 by omega, E, B, s, δ, A]
      ring
  · simp only [edgeWeight, hl, hr, hn', ite_false]
    apply H
    rw [zi,zj]
    simp [show i ≠ 1 by omega, show i ≠ p.n-1 by omega,
        show i+1 ≠ p.n-1 by omega, hl, s, δ, A]
    ring

lemma force₂ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n) (g : Bool) :
    force p D (theta₂ p D) g = synth p D g (impulse (trainingWeights p.n g)) := by
  let w := trainingWeights p.n g
  let q := mass p D (theta₂ p D) g
  have hh (i : ℕ) (hi : i < p.n) : q i = edgeWeight p.n w i := mass₂ hD hn g hi
  have he := boundary_force (by omega : 4 ≤ p.n) (vertex p D g) q
    w.left w.near w.bulk w.right
    (by rw [hh 0 (by omega)]; simp [edgeWeight])
    (by rw [hh (p.n-1) (by omega)]; simp (disch := omega) only [edgeWeight, ite_eq_left, ite_eq_right])
    (by rw [hh 1 (by omega)]; simp [edgeWeight, show 2 ≠ p.n by omega])
    (by rw [hh (p.n-2) (by omega)]; simp (disch := omega) only [edgeWeight, ite_eq_left, ite_eq_right])
    (fun i hl hr => by rw [hh i (by omega)]; simp (disch := omega) only [edgeWeight, ite_eq_right])
  change edgeForce _ _ q = synth p D g (impulse w)
  rw [he]
  unfold synth impulse
  module

end LongTails.Proofs.SpatialRankingMargins
