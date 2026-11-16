import LongTails.Proofs.AsgoFixedRadiusMatrix
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

open MeasureTheory Matrix OracleTemplate.Muon
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma accumulator_psd (p : LongTails.Setups.AsgoFixedRadius.Public) {Ξ : Type*}
    (g : Mat p.m p.n → Ξ → Mat p.m p.n) (s : ℕ → Ξ) (t : ℕ) :
    (Core.accumulator p g s t).PosSemidef := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    induction t with
    | zero =>
        change (0 : Matrix (Fin p.m) (Fin p.m) ℝ).PosSemidef
        exact Matrix.PosSemidef.zero
    | succ t ih =>
        change (Core.accumulator p g s t +
          Core.gram (Core.batchGradient p g s t (Core.point p g s t))).PosSemidef
        apply ih.add
        change ((toMatrix (Core.batchGradient p g s t (Core.point p g s t))) *
          (toMatrix (Core.batchGradient p g s t (Core.point p g s t)))ᵀ).PosSemidef
        simpa using Matrix.posSemidef_self_mul_conjTranspose
          (toMatrix (Core.batchGradient p g s t (Core.point p g s t)))
  )

lemma damped_posDef (p : LongTails.Setups.AsgoFixedRadius.Public) {Ξ : Type*}
    (g : Mat p.m p.n → Ξ → Mat p.m p.n) (s : ℕ → Ξ) (t : ℕ) (hk : 0 < p.k) :
    (Core.matrixRoot (Core.accumulator p g s t) +
      p.k • (1 : Matrix (Fin p.m) (Fin p.m) ℝ)).PosDef := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    exact Matrix.PosDef.posSemidef_add (root_psd (Core.accumulator p g s t))
      (Matrix.PosDef.one.smul hk)
  )

lemma trajectory_measurable (p : LongTails.Setups.AsgoFixedRadius.Public) {Ξ Ω : Type*}
    [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (g : Mat p.m p.n → Ξ → Mat p.m p.n) (hg : Measurable (Function.uncurry g))
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ j, Measurable (ξ j)) (t : ℕ) :
    Measurable (fun ω => Core.trajectory p g (fun j => ξ j ω) t) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    have hto : Continuous (toMatrix (m := p.m) (n := p.n)) := by
      change Continuous (fun X : Mat p.m p.n => fun i j => X (i, j))
      fun_prop
    have hof : Continuous (ofMatrix (m := p.m) (n := p.n)) := by
      change Continuous (fun A : Matrix (Fin p.m) (Fin p.n) ℝ =>
        WithLp.toLp 2 (fun ij : Fin p.m × Fin p.n => A ij.1 ij.2))
      fun_prop
    have hmul {a b c : ℕ}
        (A : Ω → Matrix (Fin a) (Fin b) ℝ) (B : Ω → Matrix (Fin b) (Fin c) ℝ)
        (hA : Measurable A) (hB : Measurable B) :
        Measurable (fun ω => A ω * B ω) := by
      apply Measurable.of_eval_matrix
      intro i j
      change Measurable (fun ω => ∑ k : Fin b, A ω i k * B ω k j)
      exact Finset.measurable_fun_sum Finset.univ (fun k _ => hA.eval_matrix.mul hB.eval_matrix)
    have hstep (k : ℕ)
        (Y : Ω → Mat p.m p.n × Matrix (Fin p.m) (Fin p.m) ℝ) (hY : Measurable Y)
        (hsamples : ∀ j < p.M, Measurable (ξ (k * p.M + j))) :
        Measurable (fun ω => Core.iterationStep p g (fun j => ξ j ω) k (Y ω)) := by
      let G : Ω → Mat p.m p.n :=
        fun ω => Core.batchGradient p g (fun j => ξ j ω) k (Y ω).1
      have hG : Measurable G := by
        change Measurable (fun ω => (1 / (p.M : ℝ)) •
          ∑ j ∈ Finset.range p.M, g (Y ω).1 (ξ (k * p.M + j) ω))
        exact (Finset.measurable_fun_sum (Finset.range p.M)
          (fun j hj => hg.comp (hY.fst.prodMk (hsamples j (Finset.mem_range.mp hj))))).const_smul (1 / (p.M : ℝ))
      have hTG : Measurable (fun ω => toMatrix (G ω)) := hto.measurable.comp hG
      have hTGT : Measurable (fun ω => (toMatrix (G ω))ᵀ) :=
        Measurable.of_eval_matrix _ (fun _ _ => hTG.eval_matrix)
      let S : Ω → Matrix (Fin p.m) (Fin p.m) ℝ :=
        fun ω => (Y ω).2 + Core.gram (G ω)
      have hS : Measurable S := by
        exact hY.snd.fun_add (hmul _ _ hTG hTGT)
      let A : Ω → Matrix (Fin p.m) (Fin p.m) ℝ :=
        fun ω => Core.matrixRoot (S ω) + p.k • 1
      have hA : Measurable A :=
        ((root_measurable (m := p.m)).2.comp hS).fun_add measurable_const
      have hAI : Measurable (fun ω => (A ω)⁻¹) :=
        (inverse_measurable (m := p.m)).2.comp hA
      have hAG := hmul _ _ hAI hTG
      have hnew : Measurable (fun ω => (Y ω).1 -
          p.R • ofMatrix ((A ω)⁻¹ * toMatrix (G ω))) :=
        hY.fst.sub ((hof.measurable.comp hAG).const_smul p.R)
      exact hnew.prodMk hS
    induction t with
    | zero =>
        change Measurable (fun _ : Ω => (p.W0, (0 : Matrix (Fin p.m) (Fin p.m) ℝ)))
        exact measurable_const
    | succ t ih =>
        exact hstep t (fun ω => Core.trajectory p g (fun j => ξ j ω) t) ih
          (fun j _ => hξ (t * p.M + j))
  )

lemma trajectory_adapted (p : LongTails.Setups.AsgoFixedRadius.Public) {Ξ Ω : Type*}
    [MeasurableSpace Ξ]
    (g : Mat p.m p.n → Ξ → Mat p.m p.n) (hg : Measurable (Function.uncurry g))
    (ξ : ℕ → Ω → Ξ) (t : ℕ) :
    @Measurable Ω (Mat p.m p.n)
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      inferInstance (fun ω => Core.point p g (fun j => ξ j ω) t) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    let : MeasurableSpace Ω :=
      MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance
    have hprefix : Measurable (fun ω (i : Fin (t * p.M)) => ξ i ω) :=
      measurable_iff_comap_le.mpr le_rfl
    have hto : Continuous (toMatrix (m := p.m) (n := p.n)) := by
      change Continuous (fun X : Mat p.m p.n => fun i j => X (i, j))
      fun_prop
    have hof : Continuous (ofMatrix (m := p.m) (n := p.n)) := by
      change Continuous (fun A : Matrix (Fin p.m) (Fin p.n) ℝ =>
        WithLp.toLp 2 (fun ij : Fin p.m × Fin p.n => A ij.1 ij.2))
      fun_prop
    have hmul {a b c : ℕ}
        (A : Ω → Matrix (Fin a) (Fin b) ℝ) (B : Ω → Matrix (Fin b) (Fin c) ℝ)
        (hA : Measurable A) (hB : Measurable B) :
        Measurable (fun ω => A ω * B ω) := by
      apply Measurable.of_eval_matrix
      intro i j
      change Measurable (fun ω => ∑ k : Fin b, A ω i k * B ω k j)
      exact Finset.measurable_fun_sum Finset.univ (fun k _ => hA.eval_matrix.mul hB.eval_matrix)
    have hstep (k : ℕ)
        (Y : Ω → Mat p.m p.n × Matrix (Fin p.m) (Fin p.m) ℝ) (hY : Measurable Y)
        (hsamples : ∀ j < p.M, Measurable (ξ (k * p.M + j))) :
        Measurable (fun ω => Core.iterationStep p g (fun j => ξ j ω) k (Y ω)) := by
      let G : Ω → Mat p.m p.n :=
        fun ω => Core.batchGradient p g (fun j => ξ j ω) k (Y ω).1
      have hG : Measurable G := by
        change Measurable (fun ω => (1 / (p.M : ℝ)) •
          ∑ j ∈ Finset.range p.M, g (Y ω).1 (ξ (k * p.M + j) ω))
        exact (Finset.measurable_fun_sum (Finset.range p.M)
          (fun j hj => hg.comp (hY.fst.prodMk (hsamples j (Finset.mem_range.mp hj))))).const_smul (1 / (p.M : ℝ))
      have hTG : Measurable (fun ω => toMatrix (G ω)) := hto.measurable.comp hG
      have hTGT : Measurable (fun ω => (toMatrix (G ω))ᵀ) :=
        Measurable.of_eval_matrix _ (fun _ _ => hTG.eval_matrix)
      let S : Ω → Matrix (Fin p.m) (Fin p.m) ℝ :=
        fun ω => (Y ω).2 + Core.gram (G ω)
      have hS : Measurable S := by
        exact hY.snd.fun_add (hmul _ _ hTG hTGT)
      let A : Ω → Matrix (Fin p.m) (Fin p.m) ℝ :=
        fun ω => Core.matrixRoot (S ω) + p.k • 1
      have hA : Measurable A :=
        ((root_measurable (m := p.m)).2.comp hS).fun_add measurable_const
      have hAI : Measurable (fun ω => (A ω)⁻¹) :=
        (inverse_measurable (m := p.m)).2.comp hA
      have hAG := hmul _ _ hAI hTG
      have hnew : Measurable (fun ω => (Y ω).1 -
          p.R • ofMatrix ((A ω)⁻¹ * toMatrix (G ω))) :=
        hY.fst.sub ((hof.measurable.comp hAG).const_smul p.R)
      exact hnew.prodMk hS
    have hstate : ∀ k ≤ t,
        Measurable (fun ω => Core.trajectory p g (fun j => ξ j ω) k) := by
      intro k
      induction k with
      | zero =>
          intro _
          change Measurable (fun _ : Ω => (p.W0, (0 : Matrix (Fin p.m) (Fin p.m) ℝ)))
          exact measurable_const
      | succ k ih =>
          intro hk
          apply hstep k _ (ih (by omega))
          intro j hj
          have hidx : k * p.M + j < t * p.M := by
            calc
              _ < k * p.M + p.M := Nat.add_lt_add_left hj _
              _ = (k + 1) * p.M := by simp only [Nat.add_mul, Nat.one_mul]
              _ ≤ t * p.M := Nat.mul_le_mul_right p.M hk
          exact (measurable_pi_apply (⟨k * p.M + j, hidx⟩ : Fin (t * p.M))).comp hprefix
    exact (hstate t le_rfl).fst
  )

end OracleTemplate.AsgoFixedRadius
