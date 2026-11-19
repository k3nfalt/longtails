import LongTails.Algorithms.LocalizedClippedSubgradient
import LongTails.Proofs.TerminalClippingConcentration

open MeasureTheory OracleTemplate OracleTemplate.TerminalClipping
open LongTails.Setups.TerminalClippingConvex
open LongTails.Algorithms.LocalizedClippedSubgradient
open scoped RealInnerProductSpace

namespace LongTails.Proofs.LocalizedClippedSubgradient

lemma localize_distance (p : Public) (hR : 0 ≤ p.R) {u : Vector p.d}
    (hu : ‖p.x0 - u‖ ≤ p.R) (y : Vector p.d) :
    ‖localize p y - u‖ ≤ ‖y - u‖ := by
  rw [norm_sub_rev] at hu
  have h := norm_clip_sub_le hR hu (y - p.x0)
  convert h using 2 <;> (try unfold localize) <;> abel

lemma localize_radius (p : Public) (hR : 0 ≤ p.R) (y : Vector p.d) :
    ‖localize p y - p.x0‖ ≤ p.R := by simpa [localize] using norm_clip_le hR (y - p.x0)

lemma drift_constants {R v ε D : ℝ} (hR : 0 < R) (hv : 0 < v) (hε : 0 < ε)
    (hD : 0 ≤ D) (hD' : D ≤ 2 * R) :
    let η := ε / (64 * v)
    let C := 16 * R * v / ε
    let τ := 1 / (8 * R ^ 2)
    τ * (2 * η * C * D + η ^ 2 * C ^ 2) ≤ 1 ∧
    τ * (2 * η * (2 * R * v / C) + η ^ 2 * v) +
      τ ^ 2 * (8 * η ^ 2 * D ^ 2 + 2 * η ^ 4 * C ^ 2) * v ≤ τ * η * ε := by
  dsimp only
  constructor
  · field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hD') hR.le]
  · have hd := pow_le_pow_left₀ hD hD' 2
    field_simp
    nlinarith [mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg ε)]

lemma clipped_drift {Ω : Type*} [MeasurableSpace Ω] (p : Public)
    (hR : 0 < p.R) (hε : 0 < p.ε) (hv : 0 < p.G ^ 2 + p.B ^ 2 * p.R ^ 2)
    {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → Vector p.d} (hg : Measurable g)
    (hgi : Integrable g P) (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ p.G ^ 2 + p.B ^ 2 * p.R ^ 2)
    {proj : Vector p.d → Vector p.d} (hp : Measurable proj)
    {x u : Vector p.d} (hu : ‖p.x0 - u‖ ≤ p.R) (hx : ‖x - p.x0‖ ≤ p.R)
    (hproj : ∀ y, ‖proj y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2)
    {gap : ℝ} (hsub : gap ≤ ⟪∫ ω, g ω ∂P, x - u⟫) :
    let τ := 1 / (8 * p.R ^ 2)
    let Z := fun ω => Real.exp (τ * ‖proj (proposal p x (g ω)) - u‖ ^ 2)
    Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤
      Real.exp (τ * ‖x - u‖ ^ 2 + τ * step p * p.ε - 2 * τ * step p * gap) := by
  let v := p.G ^ 2 + p.B ^ 2 * p.R ^ 2
  let τ := 1 / (8 * p.R ^ 2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hη : 0 < step p := div_pos hε (mul_pos (by norm_num) hv)
  have hC : 0 < threshold p := div_pos (mul_pos (mul_pos (by norm_num) hR) hv) hε
  have hdist : ‖x - u‖ ≤ 2 * p.R := by linarith [norm_sub_le_norm_sub_add_norm_sub x p.x0 u]
  have hc := drift_constants hR hv hε (norm_nonneg (x-u)) hdist
  have hi := full_moment_clip_bias hg hgi hmi hC hm
  have hb : -⟪x - u, ∫ ω, clip (threshold p) (g ω) ∂P⟫ ≤ 2 * p.R * v / threshold p - gap := by
    have hh := (real_inner_le_norm ((∫ ω, g ω ∂P) - ∫ ω, clip (threshold p) (g ω) ∂P)
      (x - u)).trans (mul_le_mul hi hdist (norm_nonneg _) (div_nonneg hv.le hC.le))
    rw [inner_sub_left] at hh
    rw [real_inner_comm]
    change _ ≤ v / threshold p * (2 * p.R) at hh
    rw [show v / threshold p * (2 * p.R) = 2 * p.R * v / threshold p by ring] at hh
    linarith only [hh, hsub]
  have hs := full_moment_clip_second hg hmi hC.le
  have hmproj : Measurable (fun y => proj (localize p y)) :=
    hp.comp (measurable_const.add ((measurable_clip _).comp (measurable_id.sub_const _)))
  have hj := projected_energy_mgf ((measurable_clip _).comp hg)
    (integrable_clip (P := P) hg hC.le) hs.1 hmproj x u
    (fun y => (hproj _).trans (pow_le_pow_left₀ (norm_nonneg _) (localize_distance p hR.le hu y) 2))
    hη.le hτ.le (fun z => norm_clip_le hC.le _) hb (hs.2.trans hm) hc.1
  refine ⟨hj.1, hj.2.trans (Real.exp_le_exp.mpr ?_)⟩
  change τ * ‖x-u‖^2 + τ * (2 * step p * (2*p.R*v/threshold p-gap) + step p^2*v) +
    τ^2*(8*step p^2*‖x-u‖^2+2*step p^4*threshold p^2)*v ≤ _
  change _ ≤ τ * ‖x-u‖^2 + τ * step p * p.ε - 2 * τ * step p * gap
  have hc2 := hc.2
  change τ * (2 * step p * (2 * p.R * v / threshold p) + step p ^ 2 * v) +
    τ ^ 2 * (8 * step p ^ 2 * ‖x-u‖ ^ 2 + 2 * step p ^ 4 * threshold p ^ 2) * v ≤
    τ * step p * p.ε at hc2
  linarith only [hc2]

end LongTails.Proofs.LocalizedClippedSubgradient
