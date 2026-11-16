import LongTails.Proofs.AsgoFixedRadiusMatrix
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic

open MeasureTheory Matrix OracleTemplate.Muon

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

noncomputable section

variable {m n : ℕ}

lemma gradient_minimizer (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) : I.H Wstar = 0 := by
  open Matrix in
  open scoped BigOperators in
  (
    have hm : IsLocalMin I.f Wstar := Filter.Eventually.of_forall hS.minimizer
    have hz := hm.hasFDerivAt_eq_zero (hS.objectiveGradient Wstar).hasFDerivAt
    have hh := congrArg
      (fun F : Mat m n →L[ℝ] ℝ => F (I.H Wstar)) hz
    change inner ℝ (I.H Wstar) (I.H Wstar) = 0 at hh
    rw [real_inner_self_eq_norm_sq] at hh
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (I.H Wstar)]
  )

lemma gradient_dual_bound (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) (X : Mat m n) :
    Core.weightedQuadratic I.L⁻¹ (I.H X) ≤ 2 * (I.f X - I.f Wstar) := by
  open Matrix in
  open scoped BigOperators in
  (
    let D : Mat m n := ofMatrix (I.L⁻¹ * toMatrix (I.H X))
    have hInv := inverse_posDef I.L hS.smoothPos
    have hsym : (I.L⁻¹)ᵀ = I.L⁻¹ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hInv.1.isHermitian.eq
    have hi : inner ℝ (I.H X) D = Core.weightedQuadratic I.L⁻¹ (I.H X) := by
      rw [inner_trace]
      change ((toMatrix (I.H X))ᵀ * (I.L⁻¹ * toMatrix (I.H X))).trace =
        (((toMatrix (I.H X))ᵀ * I.L⁻¹) * toMatrix (I.H X)).trace
      rw [Matrix.mul_assoc]
    have hq : Core.weightedQuadratic I.L D = Core.weightedQuadratic I.L⁻¹ (I.H X) := by
      change (((I.L⁻¹ * toMatrix (I.H X))ᵀ * I.L) *
        (I.L⁻¹ * toMatrix (I.H X))).trace =
        (((toMatrix (I.H X))ᵀ * I.L⁻¹) * toMatrix (I.H X)).trace
      rw [Matrix.transpose_mul, hsym]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc I.L I.L⁻¹ _, hInv.2.1, Matrix.one_mul]
    have hneg : Core.weightedQuadratic I.L (-D) = Core.weightedQuadratic I.L D := by
      change (((-toMatrix D)ᵀ * I.L) * (-toMatrix D)).trace =
        (((toMatrix D)ᵀ * I.L) * toMatrix D).trace
      simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    have hs := hS.smoothUpper X (X - D)
    have hm := hS.minimizer (X - D)
    have he : X - D - X = -D := by
      module
    rw [he, inner_neg_right, hi, hneg, hq] at hs
    linarith
  )

lemma weighted_convexity (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) (X : Mat m n) :
    I.f X - I.f Wstar + Core.weightedQuadratic I.L⁻¹ (I.H X) / 2 ≤
      inner ℝ (I.H X) (X - Wstar) := by
  open Matrix in
  open scoped BigOperators in
  (
    let D : Mat m n := ofMatrix (I.L⁻¹ * toMatrix (I.H X))
    have hInv := inverse_posDef I.L hS.smoothPos
    have hsym : (I.L⁻¹)ᵀ = I.L⁻¹ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hInv.1.isHermitian.eq
    have hi : inner ℝ (I.H X) D = Core.weightedQuadratic I.L⁻¹ (I.H X) := by
      rw [inner_trace]
      change ((toMatrix (I.H X))ᵀ * (I.L⁻¹ * toMatrix (I.H X))).trace =
        (((toMatrix (I.H X))ᵀ * I.L⁻¹) * toMatrix (I.H X)).trace
      rw [Matrix.mul_assoc]
    have hq : Core.weightedQuadratic I.L D = Core.weightedQuadratic I.L⁻¹ (I.H X) := by
      change (((I.L⁻¹ * toMatrix (I.H X))ᵀ * I.L) *
        (I.L⁻¹ * toMatrix (I.H X))).trace =
        (((toMatrix (I.H X))ᵀ * I.L⁻¹) * toMatrix (I.H X)).trace
      rw [Matrix.transpose_mul, hsym]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc I.L I.L⁻¹ _, hInv.2.1, Matrix.one_mul]
    have hs := hS.smoothUpper Wstar (Wstar + D)
    rw [gradient_minimizer I Wstar hS, inner_zero_left] at hs
    have he : Wstar + D - Wstar = D := by
      exact add_sub_cancel_left Wstar D
    rw [he, hq] at hs
    have hc := OracleTemplate.Gradient.convex_support hS.convex hS.objectiveGradient X (Wstar + D)
    have he' : Wstar + D - X = D - (X - Wstar) := by
      module
    rw [he', inner_sub_right, hi] at hc
    linarith
  )

lemma objective_continuous (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) : Continuous I.f := by
  open Matrix in
  open scoped BigOperators in
  (
    exact continuous_iff_continuousAt.mpr
      (fun X => (hS.objectiveGradient X).continuousAt)
  )

lemma gradient_continuous (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) : Continuous I.H := by
  open Matrix in
  open scoped BigOperators in
  (
    have hbridge (L : Matrix (Fin m) (Fin m) ℝ) (hL : L.PosDef)
        (X : Mat m n) :
        ‖X‖ ^ 2 ≤ spectralNorm (ofMatrix L) * Core.weightedQuadratic L⁻¹ X := by
      open scoped MatrixOrder Matrix.Norms.L2Operator in
      (
        classical
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst m
          have hX : X=0 := Subsingleton.elim _ _
          delta Core.weightedQuadratic
          simp [hX,Muon.toMatrix]
        have : NeZero m := ⟨by omega⟩
        let c := ‖L‖
        have hc : 0<c := norm_pos_iff.2 hL.isUnit.ne_zero
        have heq : c = Muon.spectralNorm (Muon.ofMatrix L) := by
          rw [show c=‖L‖ from rfl,Matrix.l2_opNorm_def]
          rfl
        have hOrder : Core.loewner L (c•(1 : Matrix (Fin m) (Fin m) ℝ)) := by
          change (c•(1 : Matrix (Fin m) (Fin m) ℝ)-L).PosSemidef
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
            ((Matrix.PosSemidef.one.smul hc.le).isHermitian.sub hL.isHermitian) (fun u => ?_)
          rw [star_trivial, Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,
            Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]
          apply sub_nonneg.mpr
          let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 u
          let F := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)
          have hinner := real_inner_le_norm v (F v)
          have hop := F.le_opNorm v
          have hd : inner ℝ v (F v) = u ⬝ᵥ (L*ᵥu) := by
            change inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m))
              (WithLp.toLp 2 (L*ᵥu)) = _
            rw [EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]
          have hf : ‖F‖ = c := by rw [show c=‖L‖ from rfl,Matrix.l2_opNorm_def]; rfl
          rw [hd] at hinner
          rw [hf] at hop
          have hu : ‖v‖^2 = u ⬝ᵥ u := Muon.norm_toLp_sq u
          nlinarith [mul_le_mul_of_nonneg_left hop (norm_nonneg v)]
        have h := inverse_quadratic_order (c•(1 : Matrix (Fin m) (Fin m) ℝ)) L X
          (Matrix.PosDef.one.smul hc) hL hOrder
        have hInv : (c•(1 : Matrix (Fin m) (Fin m) ℝ))⁻¹=c⁻¹•1 := by
          let := invertibleOfNonzero hc.ne'
          rw [Matrix.inv_smul _ c (by simp), invOf_eq_inv, inv_one]
        rw [hInv] at h
        delta Core.weightedQuadratic at h
        simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
          Matrix.trace_smul,smul_eq_mul] at h
        have hnorm : ((Muon.toMatrix X)ᵀ*Muon.toMatrix X).trace=‖X‖^2 := by
          rw [← inner_trace,real_inner_self_eq_norm_sq]
        rw [hnorm] at h
        have hmul := mul_le_mul_of_nonneg_left h hc.le
        rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at hmul
        rw [← heq]
        exact hmul
      )
    have htwo (X Y : Mat m n) :
        Core.weightedQuadratic I.L⁻¹ (I.H X - I.H Y) ≤
          2 * (I.f X - I.f Y - inner ℝ (I.H Y) (X - Y)) := by
      let D : Mat m n := ofMatrix (I.L⁻¹ * toMatrix (I.H X - I.H Y))
      have hInv := inverse_posDef I.L hS.smoothPos
      have hsym : (I.L⁻¹)ᵀ = I.L⁻¹ := by
        simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hInv.1.isHermitian.eq
      have hi : inner ℝ (I.H X - I.H Y) D = Core.weightedQuadratic I.L⁻¹ (I.H X - I.H Y) := by
        rw [inner_trace]
        change ((toMatrix (I.H X - I.H Y))ᵀ * (I.L⁻¹ * toMatrix (I.H X - I.H Y))).trace =
          (((toMatrix (I.H X - I.H Y))ᵀ * I.L⁻¹) * toMatrix (I.H X - I.H Y)).trace
        rw [Matrix.mul_assoc]
      have hq : Core.weightedQuadratic I.L D = Core.weightedQuadratic I.L⁻¹ (I.H X - I.H Y) := by
        change (((I.L⁻¹ * toMatrix (I.H X - I.H Y))ᵀ * I.L) *
          (I.L⁻¹ * toMatrix (I.H X - I.H Y))).trace =
          (((toMatrix (I.H X - I.H Y))ᵀ * I.L⁻¹) * toMatrix (I.H X - I.H Y)).trace
        rw [Matrix.transpose_mul, hsym]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc I.L I.L⁻¹ _, hInv.2.1, Matrix.one_mul]
      have hneg : Core.weightedQuadratic I.L (-D) = Core.weightedQuadratic I.L D := by
        change (((-toMatrix D)ᵀ * I.L) * (-toMatrix D)).trace =
          (((toMatrix D)ᵀ * I.L) * toMatrix D).trace
        simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      have hs := hS.smoothUpper X (X - D)
      have hl := OracleTemplate.Gradient.convex_support hS.convex hS.objectiveGradient Y (X - D)
      have he : X - D - X = -D := by module
      have hey : X - D - Y = (X - Y) - D := by module
      rw [he, inner_neg_right, hneg, hq] at hs
      rw [hey, inner_sub_right] at hl
      rw [inner_sub_left] at hi
      linarith
    have hco (X Y : Mat m n) :
        Core.weightedQuadratic I.L⁻¹ (I.H X - I.H Y) ≤
          inner ℝ (I.H X - I.H Y) (X - Y) := by
      have hxy := htwo X Y
      have hyx := htwo Y X
      have hg : I.H Y - I.H X = -(I.H X - I.H Y) := by module
      have hx : Y - X = -(X - Y) := by module
      have hq : Core.weightedQuadratic I.L⁻¹ (-(I.H X - I.H Y)) =
          Core.weightedQuadratic I.L⁻¹ (I.H X - I.H Y) := by
        change (((-toMatrix (I.H X - I.H Y))ᵀ * I.L⁻¹) *
          (-toMatrix (I.H X - I.H Y))).trace =
          (((toMatrix (I.H X - I.H Y))ᵀ * I.L⁻¹) * toMatrix (I.H X - I.H Y)).trace
        simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
      rw [hg, hq, hx, inner_neg_right] at hyx
      rw [inner_sub_left]
      linarith
    let c := spectralNorm (ofMatrix I.L)
    have hc : 0 ≤ c := spectralNorm_nonneg _
    have hLip (X Y : Mat m n) : ‖I.H X - I.H Y‖ ≤ c * ‖X - Y‖ := by
      have hb := hbridge I.L hS.smoothPos (I.H X - I.H Y)
      have hq := hco X Y
      have hi := real_inner_le_norm (I.H X - I.H Y) (X - Y)
      have hm := mul_le_mul_of_nonneg_left (hq.trans hi) hc
      change ‖I.H X - I.H Y‖ ^ 2 ≤ c * _ at hb
      rcases eq_or_lt_of_le (norm_nonneg (I.H X - I.H Y)) with hz | hp
      · rw [← hz]
        exact mul_nonneg hc (norm_nonneg _)
      · apply le_of_mul_le_mul_left (a0 := hp)
        calc
          ‖I.H X - I.H Y‖ * ‖I.H X - I.H Y‖ = ‖I.H X - I.H Y‖ ^ 2 := (pow_two _).symm
          _ ≤ c * (‖I.H X - I.H Y‖ * ‖X - Y‖) := hb.trans hm
          _ = ‖I.H X - I.H Y‖ * (c * ‖X - Y‖) := by ring
    have hl : LipschitzWith ⟨c, hc⟩ I.H := by
      apply LipschitzWith.of_dist_le_mul
      intro X Y
      change dist (I.H X) (I.H Y) ≤ c * dist X Y
      simpa only [dist_eq_norm] using hLip X Y
    exact hl.continuous
  )

lemma gradient_norm_bound (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) (X : Mat m n) :
    ‖I.H X‖ ≤ spectralNorm (ofMatrix I.L) * ‖X - Wstar‖ := by
  open Matrix in
  open scoped BigOperators in
  (
    have hbridge (L : Matrix (Fin m) (Fin m) ℝ) (hL : L.PosDef)
        (X : Mat m n) :
        ‖X‖ ^ 2 ≤ spectralNorm (ofMatrix L) * Core.weightedQuadratic L⁻¹ X := by
      open scoped MatrixOrder Matrix.Norms.L2Operator in
      (
        classical
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst m
          have hX : X=0 := Subsingleton.elim _ _
          delta Core.weightedQuadratic
          simp [hX,Muon.toMatrix]
        have : NeZero m := ⟨by omega⟩
        let c := ‖L‖
        have hc : 0<c := norm_pos_iff.2 hL.isUnit.ne_zero
        have heq : c = Muon.spectralNorm (Muon.ofMatrix L) := by
          rw [show c=‖L‖ from rfl,Matrix.l2_opNorm_def]
          rfl
        have hOrder : Core.loewner L (c•(1 : Matrix (Fin m) (Fin m) ℝ)) := by
          change (c•(1 : Matrix (Fin m) (Fin m) ℝ)-L).PosSemidef
          refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
            ((Matrix.PosSemidef.one.smul hc.le).isHermitian.sub hL.isHermitian) (fun u => ?_)
          rw [star_trivial, Matrix.sub_mulVec,dotProduct_sub,Matrix.smul_mulVec,
            Matrix.one_mulVec,dotProduct_smul,smul_eq_mul]
          apply sub_nonneg.mpr
          let v : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 u
          let F := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin L)
          have hinner := real_inner_le_norm v (F v)
          have hop := F.le_opNorm v
          have hd : inner ℝ v (F v) = u ⬝ᵥ (L*ᵥu) := by
            change inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin m))
              (WithLp.toLp 2 (L*ᵥu)) = _
            rw [EuclideanSpace.inner_toLp_toLp,star_trivial,dotProduct_comm]
          have hf : ‖F‖ = c := by rw [show c=‖L‖ from rfl,Matrix.l2_opNorm_def]; rfl
          rw [hd] at hinner
          rw [hf] at hop
          have hu : ‖v‖^2 = u ⬝ᵥ u := Muon.norm_toLp_sq u
          nlinarith [mul_le_mul_of_nonneg_left hop (norm_nonneg v)]
        have h := inverse_quadratic_order (c•(1 : Matrix (Fin m) (Fin m) ℝ)) L X
          (Matrix.PosDef.one.smul hc) hL hOrder
        have hInv : (c•(1 : Matrix (Fin m) (Fin m) ℝ))⁻¹=c⁻¹•1 := by
          let := invertibleOfNonzero hc.ne'
          rw [Matrix.inv_smul _ c (by simp), invOf_eq_inv, inv_one]
        rw [hInv] at h
        delta Core.weightedQuadratic at h
        simp only [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
          Matrix.trace_smul,smul_eq_mul] at h
        have hnorm : ((Muon.toMatrix X)ᵀ*Muon.toMatrix X).trace=‖X‖^2 := by
          rw [← inner_trace,real_inner_self_eq_norm_sq]
        rw [hnorm] at h
        have hmul := mul_le_mul_of_nonneg_left h hc.le
        rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at hmul
        rw [← heq]
        exact hmul
      )
    have hb := hbridge I.L hS.smoothPos (I.H X)
    have hd := gradient_dual_bound I Wstar hS X
    have hw := weighted_convexity I Wstar hS X
    have hq : Core.weightedQuadratic I.L⁻¹ (I.H X) ≤
        inner ℝ (I.H X) (X - Wstar) := by linarith
    have hi := real_inner_le_norm (I.H X) (X - Wstar)
    have hc := spectralNorm_nonneg (ofMatrix I.L)
    have hm := mul_le_mul_of_nonneg_left (hq.trans hi) hc
    rcases eq_or_lt_of_le (norm_nonneg (I.H X)) with hz | hp
    · rw [← hz]
      exact mul_nonneg hc (norm_nonneg _)
    · apply le_of_mul_le_mul_left (a0 := hp)
      calc
        ‖I.H X‖ * ‖I.H X‖ = ‖I.H X‖ ^ 2 := (pow_two _).symm
        _ ≤ spectralNorm (ofMatrix I.L) * (‖I.H X‖ * ‖X - Wstar‖) := hb.trans hm
        _ = ‖I.H X‖ * (spectralNorm (ofMatrix I.L) * ‖X - Wstar‖) := by ring
  )

lemma gap_upper (I : Core.Problem m n) (Wstar : Mat m n)
    (hS : Core.SourceAssumptions I Wstar) (X : Mat m n) :
    0 ≤ I.f X - I.f Wstar ∧
      I.f X - I.f Wstar ≤ Core.weightedQuadratic I.L (X - Wstar) / 2 := by
  open Matrix in
  open scoped BigOperators in
  (
    refine ⟨sub_nonneg.mpr (hS.minimizer X), ?_⟩
    have hh := hS.smoothUpper Wstar X
    rw [gradient_minimizer I Wstar hS, inner_zero_left] at hh
    linarith
  )

end

end OracleTemplate.AsgoFixedRadius
