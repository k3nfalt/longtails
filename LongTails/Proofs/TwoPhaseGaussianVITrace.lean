import LongTails.Proofs.GaussianVariationalGuarantee
import LongTails.Algorithms.TwoPhaseGaussianVI

open MeasureTheory
namespace OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
open LongTails.Setups.GaussianVariationalInference
variable {d : ℕ} {μ L : ℝ} {V : Point d → ℝ}

noncomputable def averaged (V : Point d → ℝ) (μ a : ℝ) (K : ℕ) :
    (t : ℕ) → Location d × Scale d → (Fin (K+t) → Fin d → ℝ) → Location d × Scale d
  | 0, z, ξ => (wmass a 0 K)⁻¹ • wsum V μ a 0 K z ξ
  | t+1, z, ξ => averaged V μ a K t (stepAt V μ a 0 z (ξ 0)) (fun i => ξ i.succ)

lemma measurable_averaged (h : Potential L μ V) (a : ℝ) (K t : ℕ) :
    Measurable (fun w : (Location d × Scale d) × (Fin (K+t) → Fin d → ℝ) =>
      averaged V μ a K t w.1 w.2) := by
  induction t with
  | zero =>
    have hw := measurable_wsum h a K 0
    exact (hw.fst.const_smul (wmass a 0 K)⁻¹).prodMk (hw.snd.const_smul (wmass a 0 K)⁻¹)
  | succ t ih =>
    exact ih.comp (((measurable_stepAt h a 0).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).prodMk
        (by fun_prop : Measurable (fun w : (Location d × Scale d) × (Fin (K+(t+1)) → Fin d → ℝ) =>
          fun i : Fin (K+t) => w.2 i.succ)))

lemma averaged_cholesky (h : Potential L μ V) {a : ℝ} (ha : 2 ≤ a) {K : ℕ} (hK : 0 < K)
    (t : ℕ) (z : Location d × Scale d) (hz : IsCholesky z.2) (ξ) :
    IsCholesky (averaged V μ a K t z ξ).2 := by
  induction t generalizing z with
  | zero => exact (avg_bound h z.1 z.2 ha K hK 0 z ξ hz).1
  | succ t ih => exact ih _ (stepAt_cholesky h.pos ha 0 hz _) _

lemma trace (V : Point d → ℝ) (μ a : ℝ) (ha : 2 ≤ a) (K : ℕ) (hK : 0 < K)
    (T : ℕ) (z : Location d × Scale d) (ω : ℕ → Fin d → ℝ) :
    let A := twoPhaseSgd μ a T z
    A.output ((fun s => A.update s (gradient V (A.query s).2))^[K+T] (A.initial ω)) =
      averaged V μ a K T z (fun i => ω i) := by
  intro A
  let base := reparameterizedProxSgd μ a z.1 z.2
  let f : (ℕ × SgdState d) → ℕ × SgdState d := fun s => A.update s (gradient V (A.query s).2)
  let g : SgdState d → SgdState d := fun s => base.update s (gradient V (base.query s).2)
  have second (n : ℕ) (s : SgdState d) : f^[n] (0,s) = (0,g^[n] s) := by
    induction n generalizing s with
    | zero => rfl
    | succ n ih =>
      exact ih (g s)
  have both (t : ℕ) (y : Location d × Scale d) (v : ℕ → Fin d → ℝ) :
      A.output (f^[K+t] (t,⟨v,0,y,0,0⟩)) = averaged V μ a K t y (fun i => v i) := by
    induction t generalizing y v with
    | zero =>
      change base.output (f^[K] (0,⟨v,0,y,0,0⟩)).2 = _
      rw [second]
      change sgdOutput V μ a y.1 y.2 K v = _
      exact sgdOutput_eq V μ ha _ _ hK v
    | succ t ih =>
      exact ih (stepAt V μ a 0 y (v 0)) (fun i => v (i+1))
  exact both T z ω

end OracleTemplate.GaussianVariational.TwoPhaseGaussianVI
