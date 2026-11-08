import LongTails.Proofs.BirchResourceHardOracle
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.BirchResourceHardInstance

open MeasureTheory ProbabilityTheory Set
open OracleTemplate.Rennala (Point Instance)
open LongTails.Proofs.BirchResourceChain
open LongTails.Proofs.BirchResourceGeometry
open LongTails.Setups.BirchNonEuclidean
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

structure Distortion {d : ℕ} (N : Seminorm ℝ (Point d)) : Prop where
  primal : ∀ v, ‖v‖ ≤ N v
  dual : ∀ v, ‖v‖ / 2 ≤ dualNorm N v ∧ dualNorm N v ≤ ‖v‖

lemma axial_distorted {d : ℕ} (i : Fin d) : Distortion (axial i) :=
  ⟨fun v => (axial_distortion i v).1, axial_dual i⟩

lemma euclidean_distorted (d : ℕ) : Distortion (normSeminorm ℝ (Point d)) := by
  refine ⟨fun _ => le_rfl, fun v => ?_⟩
  have hR (x : Point d) (hx : normSeminorm ℝ (Point d) x ≤ 1) : ‖x‖ ≤ 1 := hx
  refine ⟨?_, by simpa using OracleTemplate.NormBallLMO.dualNorm_le_norm hR v⟩
  by_cases hz : v = 0
  · subst v
    simpa using OracleTemplate.NormBallLMO.dualNorm_nonneg hR (0 : Point d)
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
  let u : Point d := ‖v‖⁻¹ • v
  have hu : normSeminorm ℝ (Point d) u ≤ 1 := by
    change ‖u‖ ≤ 1
    simp [u, norm_smul, inv_mul_cancel₀ hn.ne']
  have he : inner ℝ v u = ‖v‖ := by
    rw [show u = ‖v‖⁻¹ • v from rfl, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have h := OracleTemplate.NormBallLMO.inner_le_dualNorm hR v hu
  rw [he] at h
  linarith [norm_nonneg v]

noncomputable def amplitude (p : Params) : ℝ := 64 * Real.sqrt p.ε

noncomputable def width (p : Params) : ℝ := 30 * amplitude p / p.L

noncomputable def chance (p : Params) : ℝ := amplitude p ^ 2 / (amplitude p ^ 2 + p.σ ^ 2)

lemma amplitude_pos (p : Params) (hε : 0 < p.ε) : 0 < amplitude p := by
  unfold amplitude
  positivity

lemma width_pos (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) : 0 < width p := by
  have h := amplitude_pos p hε
  unfold width
  positivity

lemma chance_pos (p : Params) (hε : 0 < p.ε) : 0 < chance p := by
  have h := amplitude_pos p hε
  unfold chance
  positivity

lemma chance_le (p : Params) (hε : 0 < p.ε) : chance p ≤ 1 := by
  have h := amplitude_pos p hε
  unfold chance
  exact (div_le_one (by positivity)).2 (le_add_of_nonneg_right (sq_nonneg _))

noncomputable def sampleLaw (p : Params) (hε : 0 < p.ε) : ProbabilityMeasure Bool :=
  bernoulliLaw (chance p) (chance_pos p hε).le (chance_le p hε)

noncomputable def streamLaw (p : Params) (hε : 0 < p.ε) : ProbabilityMeasure (ℕ → Bool) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (sampleLaw p hε : Measure Bool)), inferInstance⟩

lemma stream_iid (p : Params) (hε : 0 < p.ε) :
    IID (fun i (ξ : ℕ → Bool) => ξ i) (sampleLaw p hε : Measure Bool)
      (streamLaw p hε : Measure (ℕ → Bool)) :=
  OracleTemplate.StochasticGeneralized.infinitePi_iid _

lemma chance_real (p : Params) (hε : 0 < p.ε) :
    (sampleLaw p hε : Measure Bool).real ({true} : Set Bool) = chance p := by
  simp [sampleLaw, bernoulliLaw, Measure.real, bernoulliMeasure_def]

noncomputable def objectiveInstance (p : Params) : Instance p.d :=
  ⟨scaledObjective (width p) (amplitude p),
    scaledObjective (width p) (amplitude p) (0 : Point p.d) -
      width p * amplitude p * (4 * p.d)⟩

lemma hard_objective (p : Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hD : 0 < p.d) (hx : p.x0 = 0) (hgap : width p * amplitude p * (4 * p.d) ≤ p.Δ) :
    Objective p (objectiveInstance p) := by
  have ha := width_pos p hL hε
  have hs := amplitude_pos p hε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact (scaled_grad_value ha (amplitude p) x).symm ▸ scaled_gradient ha (amplitude p) x
  · intro x y
    exact ((hn.dual _).2.trans (scaled_smooth hL hs x y)).trans
      (mul_le_mul_of_nonneg_left (hn.primal _) hL.le)
  · intro x
    have h := scaled_gap ha.le hs.le hD x
    dsimp [objectiveInstance]
    linarith
  · rw [hx]
    dsimp [objectiveInstance]
    linarith

lemma oracle_valid (p : Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε) :
    StochasticGradient p (sampleLaw p hε : Measure Bool) (objectiveInstance p).f
      (scaledOracle (width p) (amplitude p) (chance p)) :=
  hard_oracle hn.dual (width_pos p hL hε) (amplitude_pos p hε)

lemma missing_coordinate (p : Params) (hn : Distortion p.N) (hL : 0 < p.L) (hε : 0 < p.ε)
    (x : Point p.d) (k : ℕ) (hk : k < p.d) (hx : Supported x k) :
    4 * p.ε ≤ dualNorm p.N (gradient (objectiveInstance p).f x) ^ 2 :=
  scaled_unrevealed (width_pos p hL hε) hε p.N (fun v => (hn.dual v).1) x hk hx

end LongTails.Proofs.BirchResourceHardInstance
