import LongTails.Proofs.TerminalClippingSingleLogConfidence
import LongTails.Proofs.ClippedSubgradientStep
import LongTails.Proofs.TerminalClippingSchedule
import LongTails.Proofs.FixedBatchConfidenceProbability

open MeasureTheory LongTails.Setups.TerminalClippingConvex
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClippingSingleLog

lemma iid_accuracy {Ω : Type} [MeasurableSpace Ω] (p : Public) (T : ℕ)
    (hT : 0 < T) (hR : 0 ≤ p.R) (hG : 0 < p.G) (hδ : 0 < p.δ) (hδ' : p.δ < 1)
    {X : Set (Vector p.d)} (hc : Convex ℝ X) (hclosed : IsClosed X) (hx : p.x0 ∈ X)
    {f : Vector p.d → ℝ} (hf : ConvexOn ℝ X f) {u : Vector p.d} (hu : u ∈ X)
    (hmin : ∀ x ∈ X, f u ≤ f x) (hd : ‖p.x0-u‖ ≤ p.R)
    (proj : Vector p.d → Vector p.d) (hpm : ∀ w, proj w ∈ X)
    (hpv : ∀ w, ∀ a ∈ X, ⟪w-proj w,a-proj w⟫ ≤ 0)
    (g : Vector p.d → Ω → Vector p.d) (hg : Measurable (Function.uncurry g))
    (ν : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k)
      (ν : Measure Ω) (P : Measure (ℕ → Ω)))
    (hgi : ∀ x ∈ X, Integrable (g x) (ν : Measure Ω))
    (hmi : ∀ x ∈ X, Integrable (fun ω => ‖g x ω‖^2) (ν : Measure Ω))
    (hm : ∀ x ∈ X, (∫ ω, ‖g x ω‖^2 ∂(ν : Measure Ω)) ≤ p.B^2*‖x-p.x0‖^2+p.G^2)
    (hsub : ∀ x ∈ X, ∀ y ∈ X, f x-f y ≤ ⟪∫ ω, g x ω ∂(ν : Measure Ω), x-y⟫) :
    (P : Measure (ℕ → Ω)) {a | 24*p.R*momentScale p*Real.sqrt (Real.log (8/p.δ)/T) <
      f (path g proj (slope p T) (level p T) T p.x0 (fun i => a (2*i)) T)-f u} ≤
      ENNReal.ofReal (p.δ/4) := by
  rcases eq_or_lt_of_le hR with hzero | hR
  · have hx₀ : p.x0 = u := sub_eq_zero.mp (norm_eq_zero.mp
      (le_antisymm (hd.trans hzero.ge) (norm_nonneg _)))
    have hk : slope p T = 0 := by simp [slope, ← hzero]
    have hy (a : ℕ → Ω) (j : ℕ) :
        path g proj (slope p T) (level p T) T p.x0 (fun i => a (2*i)) j = p.x0 := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [path, ih, hk, zero_mul, zero_smul, sub_zero]
        exact WeaklyConvexHeavyTailed.projection_fixed hpv hx
    simp_rw [hy]
    simp [hx₀, ← hzero]
  let q := Real.log (8/p.δ)
  let M := momentScale p
  let r := p.R/(T:ℝ)
  let k := slope p T
  let C := level p T
  let b := 3*k*r
  let τ := 1/(2*b*C)
  have ht : 0 < (T:ℝ) := by exact_mod_cast hT
  have hM : 0 < M := by dsimp [M,momentScale]; positivity
  have hq := TerminalClipping.confidence_ge_one hδ hδ'
  have hrT : r*T=p.R := div_mul_cancel₀ _ ht.ne'
  have hk : k = r/(12*M*Real.sqrt (T*q)) := by
    dsimp only [k,slope,r,M,q]; rw [max_eq_right hR.le]; ring
  have tune : Tuning T q M r k C b τ := by
    simp only [τ,b,hk]
    exact tuning ht hq hM (div_pos hR ht)
  let K := region X p.x0 p.R
  obtain ⟨hne,hcomp,hconv⟩ := region_spec hx hR.le hc hclosed
  have hxK : p.x0 ∈ K := ⟨hx, Metric.mem_closedBall_self (by positivity)⟩
  have huK : u ∈ K := by
    refine ⟨hu, ?_⟩
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
    linarith
  have hp := SaddlePoint.project_spec hne hcomp hconv
  have law := FixedBatchConfidence.iid_finite_block_law (TerminalClipping.even_samples_iid hIID) 0 T
  have tail := compact_accuracy tune (hf.subset (show K ⊆ X from fun _ h => h.1) hconv)
    huK (fun x hx => hmin x hx.1) hxK (hrT.symm ▸ hd)
    (LongTails.Proofs.NondualProjection.project_lipschitz hne hcomp hconv).continuous.measurable
    (fun w => (hp w).1) (fun w => (hp w).2) hg ν
    (fun x hx => hgi x hx.1) (fun x hx => hmi x hx.1)
    (fun x hx => region_moment hx (hm x hx.1))
    (fun x hx y hy => hsub x hx.1 y hy.1) (fun i (a : ℕ → Ω) => a (2*i))
    (by simpa only [Nat.zero_add] using law)
  have he : Real.exp (-q) = p.δ/8 := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 8/p.δ)]
    field_simp
  apply ((measure_mono ?_).trans tail).trans
  · rw [he, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  · intro a ha good
    let y := path g (SaddlePoint.project K) k C T p.x0 (fun i => a (2*i))
    change (∀ j ≤ T, ‖y j-p.x0‖ < 4*(r*T)) ∧ f (y T)-f u ≤ 24*(r*T)*M*Real.sqrt (q/T) at good
    rw [hrT] at good
    have heq := path_coupled hx hR.le hc hclosed proj hpm hpv g k C T (fun i => a (2*i)) T
      (fun i hi => good.1 (i+1) hi)
    have hh := good.2
    change path g proj k C T p.x0 (fun i => a (2*i)) T = y T at heq
    rw [← heq] at hh
    exact (not_lt_of_ge hh) ha

end OracleTemplate.TerminalClippingSingleLog
