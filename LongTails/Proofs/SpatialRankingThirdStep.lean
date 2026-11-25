import LongTails.Proofs.SpatialRankingMargins

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingThirdStep

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin direction)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.LogisticPathBounds
open LongTails.Proofs.SpatialRankingExecution
open LongTails.Proofs.SpatialRankingGradients
open LongTails.Proofs.SpatialRankingProfiles
open LongTails.Proofs.SpatialRankingMargins

noncomputable def gradGroup (p : Params) (D : Items p) (g : Bool) : Features p.d :=
  synth p D g (impulse (trainingWeights p.n g))

lemma correction {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g h : Bool) :
    (2*⟪gradGroup p D g, synth p D h (head h)⟫,
     2*⟪shift (gradGroup p D g), synth p D h (head h)⟫) =
      if g=h then tapCorrection (population g) (u p.n) (v p.n)
        (secondTaps (u p.n)).1 (secondTaps (u p.n)).2 else 0 := by
  let w := trainingWeights p.n g
  let P := population g
  let A := anchorCoeff P
  let B := nearCoeff P
  let R := synth p D h (head h)
  have H (i : ℕ) (hi : i ≤ p.n) : ⟪vertex p D g i, R⟫ = if g=h then value p.n i (head h) else 0 :=
    synth_value hD hn g h hi _
  have J (i : ℕ) (hi : i ≤ p.n) : ⟪shift (vertex p D g i), R⟫ =
      if g=h then backward p.n g i (head h) else 0 := by
    rw [synth_backward hD hn g h hi]
  change (2 * ⟪synth p D g (impulse w), R⟫, 2 * ⟪shift (synth p D g (impulse w)), R⟫) = _
  simp only [synth, impulse, shift_add, shift_smul, inner_add_left, real_inner_smul_left]
  simp (disch := omega) only [H, J]
  by_cases he : g=h
  · subst h
    simp only [ite_true]
    change _ = (2*(A*(w.left+w.right)+B*(2*w.near-w.left-w.right)),
      2*(P.anchorLag*(A*(w.left+w.right))+P.itemLag*(B*(2*w.near-w.left-w.right))-
        w.left*B*P.slope*u p.n+A*contact P (u p.n) (v p.n) w))
    rw [← impulse_moment p.n hn g w]
    simp (disch := omega) only [value, backward, core,
      ite_eq_right, head, moment, impulse]
    dsimp only [A, B, P]
    simp only [trace_ends (by omega : 4 ≤ p.n) g, right_eq, u, div_eq_mul_inv]
    apply Prod.ext <;> simp <;> ring
  · simp [he]

noncomputable def theta₃ (p : Params) (D : Items p) : Point p :=
  let c := secondTaps (u p.n)
  let f := gradGroup p D false + gradGroup p D true
  (thirdTaps (u p.n) (v p.n), (theta₂ p D).2 + (2:ℝ) • (c.1 • f + c.2 • shift f))

lemma step₃ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n) :
    batch p D (theta₂ p D) = theta₃ p D := by
  rw [batch_eq, force₂ hD hn, force₂ hD hn]
  let F := gradGroup p D
  let R (g : Bool) := synth p D g (head g)
  let c := secondTaps (u p.n)
  let delta (g : Bool) := tapCorrection (population g) (u p.n) (v p.n) c.1 c.2
  have hh (g h : Bool) : ((2*⟪F g,R h⟫,2*⟪shift (F g),R h⟫) : ℝ × ℝ) =
      if g=h then delta g else 0 := correction hD hn g h
  apply Prod.ext
  · change c + (2:ℝ) • (⟪F false + F true, R false + R true⟫,
       ⟪shift (F false + F true), R false + R true⟫) = c + delta false + delta true
    have hd (g h : Bool) := congrArg Prod.fst (hh g h)
    have hl (g h : Bool) := congrArg Prod.snd (hh g h)
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, inner_add_left, inner_add_right]
      have hff := hd false false
      have hft := hd false true
      have htf := hd true false
      have htt := hd true true
      simp at hff hft htf htt
      linarith
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, shift_add, inner_add_left, inner_add_right]
      have hff := hl false false
      have hft := hl false true
      have htf := hl true false
      have htt := hl true true
      simp at hff hft htf htt
      linarith
  · rfl

lemma score₃ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n) (g : Bool)
    {i : ℕ} (hi : i ≤ p.n) :
    let x := head g
    let y := impulse (trainingWeights p.n g)
    let c := secondTaps (u p.n)
    let d := thirdTaps (u p.n) (v p.n)
    score p D g i (theta₃ p D) =
      d.1*(value p.n i x + 2*(c.1*value p.n i y + c.2*forward p.n g i y)) +
      d.2*(backward p.n g i x + 2*(c.1*backward p.n g i y + c.2*value p.n i y)) := by
  cases g <;> simp [score, theta₃, theta₂, margin, gradGroup, shift_add, inner_add_right,
    real_inner_smul_right, inner_shift_shift, synth_value hD hn _ _ hi,
    synth_forward hD hn _ _ hi, synth_backward hD hn _ _ hi] <;> ring

noncomputable def lastScore (n : ℕ) (g : Bool) (i : ℕ) : ℝ :=
  let P := population g
  let c := secondTaps (u n)
  let d := thirdTaps (u n) (v n)
  let w := trainingWeights n g
  let A := anchorCoeff P
  let B := nearCoeff P
  let E := d.1 + d.2*P.itemLag
  let E₀ := d.1 + d.2*P.anchorLag
  let K := 2*(E*c.1 + (P.itemLag*d.1+d.2)*c.2)
  let K₀ := 2*(E₀*c.1 + (P.anchorLag*d.1+d.2)*c.2)
  let C := 2*d.1*c.2*w.left + d.2*(A + 2*c.1*w.right)
  let J := contact P (u n) (v n) w
  if i=0 then E₀*A + K₀*w.left + d.2*(-B*P.slope*u n + 2*c.1*J)
  else if i=n then -E₀*A - K₀*w.right - 2*d.1*c.2*J
  else E*core n i (head g) + K*core n i (impulse w) + traceValue n g i*C

lemma score₃_eq {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n) (g : Bool)
    {i : ℕ} (hi : i ≤ p.n) : score p D g i (theta₃ p D) = lastScore p.n g i := by
  rw [score₃ hD hn g hi]
  by_cases hl : i=0
  · subst i
    simp only [lastScore, value, backward, forward, ite_true, head_moment _ hn, impulse_moment _ hn]
    dsimp only [head, impulse]
    ring
  by_cases hr : i=p.n
  · subst i
    simp only [lastScore, value, backward, forward, hl, ite_false, ite_true, impulse_moment _ hn]
    dsimp only [head, impulse]
    ring
  simp only [lastScore, value, backward, forward, hl, hr, ite_false]
  dsimp only [head, impulse]
  ring

noncomputable def lastMargin (n : ℕ) (g : Bool) (i : ℕ) : ℝ :=
  let B := boundaryMargin (population g) (u n) (v n)
  if i=0 then B .leftAnchor else if i+1=n then B .rightAnchor
  else if i=1 then B .leftNear else if i+2=n then B .rightNear
  else if i=2 ∨ i+3=n then B .interior else bulkSlope (population g) (u n) (v n)*u n*v n

lemma last_margin_score (n : ℕ) (hn : 8 ≤ n) (g : Bool) (i : ℕ) (hi : i < n) :
    (population g).scale*(lastScore n g i-lastScore n g (i+1)) = lastMargin n g i := by
  have ht (j : ℕ) (hj : 0<j) : traceValue n g (j+1) =
      traceValue n g j + (population g).slope*u n*v n := trace_step n j g hj
  have hl := (trace_ends (by omega : 4 ≤ n) g).1
  have hr := (trace_ends (by omega : 4 ≤ n) g).2
  change traceValue n g 1 = (population g).left * u n at hl
  change traceValue n g (n-1) = (population g).right * u n at hr
  by_cases h₀ : i=0
  · subst i
    simp (disch := omega) only [lastScore, lastMargin, boundaryMargin, core, head, impulse,
      trainingWeights, ite_eq_right, ite_true, hl, Nat.zero_add]
    ring
  by_cases hₙ : i+1=n
  · have e : i=n-1 := by omega
    simp (disch := omega) only [lastScore, lastMargin, boundaryMargin, core, head, impulse,
      trainingWeights, ite_eq_left, ite_eq_right]
    rw [e, hr]
    ring
  have hd := ht i (by omega)
  have hi' : i=1 ∨ i+2=n ∨ i=2 ∨ i+3=n ∨ (i≠1 ∧ i+2≠n ∧ i≠2 ∧ i+3≠n) := by omega
  rcases hi' with H|H|H|H|H
  all_goals simp (disch := omega) only [lastScore, lastMargin, boundaryMargin, bulkSlope, core,
    head, impulse, trainingWeights, ite_eq_left, ite_eq_right, hd]
  all_goals ring

lemma certified_margin {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n)
    (g : Bool) {i : ℕ} (hi : i < p.n) : 0.001 * u p.n * v p.n <
      margin .conv p.d (signedRow p D g i) (theta₃ p D) := by
  have hn₀ : 0 < (p.n : ℝ) := by exact_mod_cast (show 0 < p.n by omega)
  have hn₈ : (8 : ℝ) ≤ p.n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hn₀.le
  have hu₀ : 0 < u p.n := by unfold u; positivity
  have hv₀ : 0 < v p.n := by
    unfold v
    positivity [show 0 < p.n-2 by omega]
  have hu : u p.n ∈ Set.Icc 0 0.375 := by
    refine ⟨hu₀.le, ?_⟩
    rw [u, inv_le_comm₀ (Real.sqrt_pos.mpr hn₀) (by norm_num)]
    norm_num
    nlinarith [Real.sqrt_nonneg (p.n:ℝ)]
  have hv : v p.n ∈ Set.Icc 0 0.17 := by
    refine ⟨hv₀.le, ?_⟩
    have he : (6:ℝ) ≤ (p.n-2:ℕ) := by exact_mod_cast (show 6 ≤ p.n-2 by omega)
    rw [v, inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    linarith
  rw [margin_eq D g hi, score₃_eq hD hn g hi.le, score₃_eq hD hn g (Nat.succ_le_of_lt hi),
    last_margin_score _ hn g i hi]
  have he (e : BoundaryEdge) : 0.05 < boundaryMargin (population g) (u p.n) (v p.n) e := by
    have hb := boundary_margin_bounds hu hv e
    cases g <;> simp only [population] <;> linarith [hb.1, hb.2]
  have hb : 0.001 < bulkSlope (population g) (u p.n) (v p.n) := by
    have hh := bulk_margin_bounds hu hv
    cases g <;> simp only [population] <;> linarith [hh.1, hh.2]
  have hbound : 0.001*u p.n*v p.n ≤ 0.05 := by
    have h := mul_le_mul hu.2 hv.2 hv₀.le (by norm_num : (0:ℝ) ≤ 0.375)
    linarith
  unfold lastMargin
  split_ifs <;> first | exact hbound.trans_lt (he _) |
    exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hb hu₀) hv₀

lemma separates₃ {p : Params} {D : Items p} (hD : Geometry p D) (hn : 8 ≤ p.n) :
    Separates p D (theta₃ p D) := by
  intro g i hi
  apply lt_of_le_of_lt _ (certified_margin hD hn g hi)
  unfold u v
  positivity

end LongTails.Proofs.SpatialRankingThirdStep
