import LongTails.Proofs.MarkovNonconvexBurnInBatchesParameters
import LongTails.Proofs.MarkovNonconvexBurnInBatchesTrajectory
import LongTails.Proofs.MixedNoiseSelectors

open MeasureTheory ProbabilityTheory OracleTemplate
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Setups.MarkovSmoothNonconvex
open Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw)
open Algorithms.MarkovNonconvexBurnInBatches

noncomputable def algorithm (p : Params) : Algorithm (Space p) (Space p) (Space p) :=
  method (p.ε/(2*p.L)) (blocks p-1) (discard p) (keep p-1+1) (Nat.succ_pos _) p.x0

lemma accuracy (p : Params) (hp : spec.valid p) (f : Space p → ℝ) (O : Oracle (Space p) (Space p))
    (ha : spec.admissible p f O) :
    spec.successful p f (fun z : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm p) (fun _ => blocks p*(discard p+keep p)) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨hf,hl,hlow,Z,mZ,κ,hκ,π,g,rfl,hinv,hd,hg,hi,hz,hq,hv⟩ := ha
  let k := blocks p-1
  let r := keep p-1
  let n := r+1
  let b := discard p
  let η := p.ε/(2*p.L)
  have pos := counts_pos p hp
  have ek : k+1 = blocks p := Nat.sub_add_cancel pos.1
  have en : n = keep p := Nat.sub_add_cancel pos.2
  have ηpos : 0 < η := div_pos hp.2.1 (mul_pos (by norm_num) hp.1)
  have hη : p.L*η = p.ε/2 := by dsimp [η]; field_simp [hp.1.ne']
  have gap : p.Δ ≤ ((k+1:ℕ):ℝ)*η*(p.ε/4) := by
    rw [ek]
    have hh := Nat.le_ceil (8*(p.L*p.Δ/p.ε^2))
    have hdiv : 8*(p.L*p.Δ)/p.ε^2 ≤ (blocks p:ℝ) := by
      simpa only [blocks, mul_div_assoc] using hh
    have e := (div_le_iff₀ (sq_pos_of_pos hp.2.1)).mp hdiv
    dsimp [η]
    field_simp [hp.1]
    nlinarith
  have size : 1024*p.τ*p.σ^2 ≤ (n:ℝ)*p.ε^2 := by rw [en]; exact keep_size p hp
  let P : Measure (ℕ → Z) := pathLaw κ π
  let X := fun j (ξ : ℕ → Z) => iterate g η b n p.x0 ξ j
  let G := fun j ξ => ‖gradient f (X j ξ)‖
  have gm := OracleTemplate.HeavyTailedMarkovGradient.measurable_gradient_of_lipschitz hp.1.le hl
  have total := trajectory_budget κ π hinv hp.2.2.1 hp.2.1 hp.1.le ηpos hη hd hg hf gm hl
    hi hz hq hv p.x0 hlow (k+1) b r size (discard_decay p hp) gap
  change (∑ j ∈ Finset.range (k+1), ∫ ξ, G j ξ ∂P) ≤ _ at total
  let U := (PMF.uniformOfFintype (Fin (k+1))).toMeasure
  let Q := U.prod P
  let Y := fun z : Fin (k+1) × (ℕ → Z) => G z.1.val z.2
  have mx : Measurable (fun z : Fin (k+1) × (ℕ → Z) => X z.1.val z.2) :=
    measurable_from_prod_countable_right fun i =>
      (MarkovNormalizedExecution.measurable_output hg η n 1 p.x0 i.val).comp (measurable_retained b n)
  have iy : Integrable Y Q := by
    refine Integrable.of_bound (gm.comp mx).norm.aestronglyMeasurable
      (‖gradient f p.x0‖ + k*(p.L*η)) (.of_forall fun z => ?_)
    change |‖gradient f (X z.1.val z.2)‖| ≤ _
    rw [abs_norm]
    apply (MarkovNormalizedExecution.norm_bound hp.1.le ηpos.le _ hl g n 1 p.x0 z.1.val
      (retained b n z.2)).trans
    exact add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_of_lt_succ z.1.isLt))
      (mul_nonneg hp.1.le ηpos.le)) _
  have ey : (∫ z, Y z ∂Q) ≤ p.ε := by
    rw [integral_prod _ iy, OracleTemplate.MixedNoise.integral_uniform_finite, Fintype.card_fin,
      Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, G j ξ ∂P), inv_mul_le_iff₀ (by positivity)]
    exact total
  let O : Oracle (Space p) (Space p) :=
    { Seed := fun _ => Z, law := pathLaw κ π, answer := fun _ (_, x) z => g x z }
  change spec.successful p f (fun z : Fin (k+1) × (ℕ → Z) => execute O
    (method η k b n (Nat.succ_pos _) p.x0) (fun _ => blocks p*(discard p+keep p)) z.1 z.2) _
  have budget_eq : blocks p*(discard p+keep p) = (k+1)*(b+n) := by rw [ek,en]
  simp only [budget_eq, O, execute_method]
  exact ⟨mx,iy,ey⟩

end LongTails.Proofs.MarkovNonconvexBurnInBatches
