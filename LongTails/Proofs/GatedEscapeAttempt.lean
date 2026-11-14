import LongTails.Proofs.GatedEscapeTrajProb
import LongTails.Proofs.GatedEscapeAccept
import LongTails.Proofs.GatedEscapeMajority
import LongTails.Proofs.GatedEscapeMeasurable

namespace LongTails.Proofs.GatedEscapeAttempt

open MeasureTheory ProbabilityTheory LongTails.Algorithms.GatedPerturbedEscape
  LongTails.Proofs.GatedEscapeProcess LongTails.Proofs.GatedEscapeMoments
  LongTails.Proofs.GatedEscapePhases LongTails.Proofs.GatedEscapeTrajProb
  LongTails.Proofs.GatedEscapeAccept LongTails.Proofs.GatedEscapeMajority
  LongTails.Proofs.GatedEscapeMeasurable LongTails.Proofs.GatedEscapeDescent
  LongTails.Proofs.StrongGrowthAgdBlocks LongTails.Proofs.ComparisonTrustTaylor
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {Ω : Type} [MeasurableSpace Ω]
variable (cfg : Config) (d : ℕ) (g : E → Ω → E) (f : E → ℝ)

noncomputable def qhS (s : State E) : ℝ := select cfg.M cfg.τq (fun c => ⟪s.w, s.store c - s.g0⟫ / cfg.r)

def accS (s : State E) : Prop := cfg.r / 2 ≤ ‖s.v‖ ∧ qhS cfg s ≤ -2 * cfg.θ

noncomputable def dxS (s : State E) : E :=
  -(((if 0 ≤ ⟪s.g0, s.w⟫ then (1 : ℝ) else -1) * cfg.r) • s.w)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
noncomputable instance instAccSDecidable (s : State E) : Decidable (accS cfg s) := Classical.dec _

def A0S (x : E) (s : State E) : Prop := ‖s.g0 - gradient f x‖ ≤ 3 * cfg.τ0

def AqS (x : E) (s : State E) : Prop :=
  |qhS cfg s - ⟪s.w, gradient f (x + cfg.r • s.w) - s.g0⟫ / cfg.r| ≤ 3 * cfg.τq

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
noncomputable instance instA0SDecidable (x : E) (s : State E) : Decidable (A0S cfg f x s) :=
  Classical.dec _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
noncomputable instance instAqSDecidable (x : E) (s : State E) : Decidable (AqS cfg f x s) :=
  Classical.dec _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] in
lemma attempt_split (s : State E) (hd : s.done = false) (hph : s.ph = .grad0) (hj : s.j = 0)
    (hM : 0 < cfg.M) (hT : 0 < cfg.T) (β : ℕ → (Fin cfg.b → Ω) × E) :
    let s1 := run (astep cfg d g) s β cfg.M
    let s3 := run (astep cfg d g) s β (cfg.M + 1 + cfg.T)
    s1.g0 = select cfg.M cfg.τ0 (fill cfg g s.store s.x β cfg.M) ∧ s1.x = s.x ∧
    s3.x = s.x ∧ s3.g0 = s1.g0 ∧ s3.ph = .ray ∧ s3.j = 0 ∧ s3.done = false ∧
    s3.found = s.found ∧ s3.att = s.att ∧ s3.dx = s.dx ∧
    s3.v = vrun cfg g s.x s1.g0 (clip cfg.r ((cfg.s0 / Real.sqrt d) • (β cfg.M).2))
      (fun n => (β (cfg.M + 1 + n)).1) cfg.T ∧
    s3.w = (1 / ‖s3.v‖) • s3.v := by
  intro s1 s3
  have h1 : s1 = _ := run_grad0_end cfg d g s hd hph hj hM β
  have h2 : run (astep cfg d g) s β (cfg.M + 1) = astep cfg d g s1 (β cfg.M) := run_succ _ _ _ _
  have h2' := run_init cfg d g s1 (by rw [h1]; exact hd) (by rw [h1]) (β cfg.M)
  set s2 := run (astep cfg d g) s β (cfg.M + 1) with hs2
  have hs3 : s3 = run (astep cfg d g) s2 (shift (cfg.M + 1) β) cfg.T := run_add _ _ _ _ _
  have h3 := run_traj_end cfg d g s2 (by rw [h2, h2', h1]; exact hd) (by rw [h2, h2']) (by rw [h2, h2', h1])
    hT (shift (cfg.M + 1) β)
  rw [← hs3] at h3
  have e2 : s2 =
      { s1 with
        ph := .traj
        v := clip cfg.r ((cfg.s0 / Real.sqrt d) • (β cfg.M).2)
        t := s1.t + 1 } := by rw [h2, h2']
  refine ⟨by rw [h1], by rw [h1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [h3, e2, h1, shift, hd]

end LongTails.Proofs.GatedEscapeAttempt
