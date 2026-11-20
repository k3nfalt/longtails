import LongTails.Proofs.MultirateVariance

namespace LongTails.Proofs.MultirateAccuracy

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (objective)
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms
open MultirateSchedule MultirateCausality MultiratePackets MultirateStaleness MultirateTrajectory

variable {p : Params} {g : Fin p.n → Point p → p.Ω → Point p} {f : Functions p}

lemma objective_diff (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (y : Point p) :
    HasGradientAt (objective (network p) f) (gradient (objective (network p) f) y) y := by
  rw [gradient_average hf]
  exact OracleTemplate.FiniteSum.objective_gradient (f := f)
    (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hf y

lemma measurable_v (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable fun s => v g s k :=
  estimate_measurable g id hg k
    (fun _ => point_measurable g id hg _ fun _ _ _ => coord_measurable _)
    (fun _ => coord_measurable _)

lemma estimator_moment {P : Measure (Samples p)} [IsProbabilityMeasure P]
    {μ : Fin p.n → ProbabilityMeasure p.Ω}
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε)
    (hL : 0 < smoothness p) (hcomp : ∀ i, 0 ≤ p.L i)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (lower : ℝ) (hlo : ∀ x, lower ≤ objective (network p) f x)
    (hΔ : objective (network p) f p.x0 - lower ≤ p.Δ) (k : Fin (K p)) :
    let e := fun s => ‖v g s k - gradient (objective (network p) f) (x g s k)‖^2
    Integrable e P ∧ (∫ s, e s ∂P) ≤ 7142 * δ p ^ 2 := by
  let F := objective (network p) f
  let D := fun s => ‖average p (replies g s k) - stale g s f k‖
  let E := fun s => ‖v g s k - gradient F (x g s k)‖^2
  have hδ : 0 < δ p := LeonBatchTuning.resolution_pos (network p) hε
  have hgrad (i) : LipschitzWith ⟨p.L i,hcomp i⟩ (gradient (f i)) :=
    LipschitzWith.of_dist_le_mul (fun z w => by rw [dist_eq_norm,dist_eq_norm]; exact hl i z w)
  have hF : LipschitzWith ⟨smoothness p,hL.le⟩ (gradient F) :=
    LipschitzWith.of_dist_le_mul (fun z w => by rw [dist_eq_norm,dist_eq_norm]; exact gradient_lipschitz hf hl z w)
  have hD := MultirateVariance.adaptive_variance hw hi hsg (fun i => (hgrad i).continuous.measurable) hh hσ hε k
  change Integrable (fun s => D s ^ 2) P ∧ (∫ s, D s ^ 2 ∂P) ≤ δ p ^ 2 at hD
  have hg := fun i => (hsg i).measurable
  have hE : Measurable E := ((measurable_v hg k).sub (hF.continuous.measurable.comp
    (point_measurable g id hg k (fun _ _ _ => coord_measurable _)))).norm.pow_const 2
  have hbound (s) : E s ≤ 125 * δ p ^ 2 + 5 * D s ^ 2 := by
    have hr := gradient_range g s hε hL (objective_diff hf) (gradient_lipschitz hf hl) lower hlo hΔ k k.isLt.le
    have he := packet_error hε (replies g s k) (gradient F (x g s k)) hr
    rw [← show packets g s k = _ from funext (packet_eq g s k)] at he
    have ht := norm_sub_le_norm_sub_add_norm_sub (average p (replies g s k)) (stale g s f k) (gradient F (x g s k))
    have hs := stale_error g s hh hε hL hcomp hf hl k
    have h : ‖v g s k - gradient F (x g s k)‖ ≤ 3 / 2 * (5*δ p + D s) := by
      change ‖v g s k - gradient F (x g s k)‖ ≤ _ at he
      change ‖stale g s f k - gradient F (x g s k)‖ ≤ _ at hs
      dsimp only [D]; linarith
    have he2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    dsimp only [E]
    nlinarith [sq_nonneg (5*δ p-D s), sq_nonneg (δ p), sq_nonneg (D s)]
  have hB : Integrable (fun s => 125 * δ p ^ 2 + 5 * D s ^ 2) P := (integrable_const _).add (hD.1.const_mul _)
  have hI := hB.mono' hE.aestronglyMeasurable (Filter.Eventually.of_forall fun s => by
    change ‖E s‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound s)
  refine ⟨hI,(integral_mono hI hB hbound).trans ?_⟩
  rw [integral_add (integrable_const _) (hD.1.const_mul _),integral_const_mul,integral_const]
  simp only [probReal_univ,one_smul]
  rw [integral_const_mul]
  linarith [hD.2,sq_nonneg (δ p)]

lemma estimated_sum (hε : 0 < p.ε) (hL : 0 < smoothness p)
    {F : Point p → ℝ} (hf : ∀ z, HasGradientAt F (gradient F z) z)
    (hl : ∀ z w, ‖gradient F z - gradient F w‖ ≤ smoothness p * ‖z-w‖)
    (hgap : ∀ z, F p.x0 - F z ≤ p.Δ) (s : Samples p) :
    (∑ i : Fin (K p), ‖v g s i‖) ≤ K p * δ p + 3 * ∑ i : Fin (K p), ‖v g s i - gradient F (x g s i)‖ := by
  let η := δ p / smoothness p
  have hδ : 0 < δ p := LeonBatchTuning.resolution_pos (network p) hε
  have hη : 0 < η := div_pos hδ hL
  have hd (k : ℕ) : η * (∑ i ∈ Finset.range k, ‖v g s i‖) ≤ F p.x0 - F (x g s k) +
      3 * η * (∑ i ∈ Finset.range k, ‖v g s i - gradient F (x g s i)‖) + k * (smoothness p / 2 * η^2) := by
    induction k with
    | zero => simp [x,modelAt,trajectory,LeonTrajectory.initial]
    | succ k ih =>
      have hs := ParameterFreeNsgdmRun.descent_step hf hl hL.le η hη.le (x g s k) (v g s k)
      rw [← x_step] at hs
      have ht := mul_le_mul_of_nonneg_left (norm_sub_norm_le (v g s k) (gradient F (x g s k))) hη.le
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_succ]
      linarith
  have h := hd (K p)
  simp_rw [← Fin.sum_univ_eq_sum_range] at h
  have hηL : η * smoothness p = δ p := div_mul_cancel₀ _ hL.ne'
  have hk := (div_le_iff₀ (sq_pos_of_pos hδ)).mp (LeonBatchTuning.iterations_lower (network p))
  have hb : p.Δ ≤ (K p : ℝ) * (η * δ p) / 2 := by
    apply le_of_mul_le_mul_left (a := smoothness p) _ hL
    change 2 * smoothness p * p.Δ ≤ (K p : ℝ) * δ p ^ 2 at hk
    nlinarith [congrArg (fun u => (K p : ℝ)*u*δ p) hηL]
  have hc : smoothness p / 2 * η^2 = η*δ p/2 := by nlinarith [congrArg (fun u => η*u) hηL]
  rw [hc] at h
  apply le_of_mul_le_mul_left (a := η) _ hη
  linarith only [h,hgap (x g s (K p)),hb]


lemma history_lookup (s : Samples p) (k i : ℕ) (hi : i < k) :
    (modelAt g s k).history[k - 1 - i]? = some (x g s i, ‖v g s i‖) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hist : (modelAt g s (k+1)).history = (x g s k, ‖v g s k‖) :: (modelAt g s k).history := rfl
    rw [hist]
    by_cases he : i = k
    · subst i
      simp
    · rw [show k+1-1-i = (k-1-i)+1 by omega, List.getElem?_cons_succ]
      exact ih (by omega)

lemma output_eq (s : Samples p) (ij : Fin (K p) × Fin (K p)) :
    output p (modelAt g s (K p)) ij =
      if ‖v g s ij.1.rev‖ ≤ ‖v g s ij.2.rev‖ then x g s ij.1.rev else x g s ij.2.rev := by
  have lookup (i : Fin (K p)) : (modelAt g s (K p)).history[i.val]? = some (x g s i.rev, ‖v g s i.rev‖) := by
    have h := history_lookup (g := g) s (K p) i.rev i.rev.isLt
    have he : K p - 1 - i.rev.val = i.val := by
      change K p - 1 - (K p - (i.val+1)) = i.val
      omega
    rwa [he] at h
  unfold output LeonTrajectory.output
  rw [lookup,lookup]
  rfl

lemma successful (P : ProbabilityMeasure (Samples p)) (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) (P : Measure _))
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) (P : Measure _))
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε)
    (hL : 0 < smoothness p) (hcomp : ∀ i, 0 ≤ p.L i)
    (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hl : ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖)
    (lower : ℝ) (hlo : ∀ x, lower ≤ objective (network p) f x)
    (hΔ : objective (network p) f p.x0 - lower ≤ p.Δ) (T : DistributedTemplate.Time) :
    spec.successful p f (fun z : (Fin (K p) × Fin (K p)) × Samples p =>
      output p (modelAt g z.2 (K p)) z.1)
      (DistributedTemplate.law (Setups.BandwidthHeterogeneousSmoothNonconvex.system (network p) g P) (algorithm p T)) := by
  let F := gradient (objective (network p) f)
  let y := fun (i : Fin (K p)) (s : Samples p) => x g s i.rev
  let V := fun (i : Fin (K p)) (s : Samples p) => v g s i.rev
  let G := fun i s => F (y i s)
  let out := fun (ij : Fin (K p) × Fin (K p)) (s : Samples p) =>
    if ‖V ij.1 s‖ ≤ ‖V ij.2 s‖ then y ij.1 s else y ij.2 s
  have hg := fun i => (hsg i).measurable
  have hy (i) : Measurable (y i) := point_measurable g id hg _ (fun _ _ _ => coord_measurable _)
  have hv (i) : Measurable (V i) := measurable_v hg _
  have hF : LipschitzWith ⟨smoothness p,hL.le⟩ F := LipschitzWith.of_dist_le_mul
    (fun z w => by rw [dist_eq_norm,dist_eq_norm]; exact gradient_lipschitz hf hl z w)
  have hG (i) : Measurable (G i) := hF.continuous.measurable.comp (hy i)
  have hb (i : Fin (K p)) := estimator_moment hw hi hsg hh hσ hε hL hcomp hf hl lower hlo hΔ i.rev
  have hs (s : Samples p) : ∑ i, ‖V i s‖ ≤ K p * δ p + 3 * ∑ i, ‖V i s - G i s‖ := by
    have he (z : Fin (K p) → ℝ) : ∑ i : Fin (K p), z i.rev = ∑ i, z i := Equiv.sum_comp Fin.revPerm z
    change (∑ i : Fin (K p), ‖v g s i.rev‖) ≤ _ + 3 * ∑ i : Fin (K p), ‖v g s i.rev - F (x g s i.rev)‖
    rw [he (fun i => ‖v g s i‖), he (fun i => ‖v g s i - F (x g s i)‖)]
    exact estimated_sum hε hL (objective_diff hf) (gradient_lipschitz hf hl) (fun z => by linarith [hlo z]) s
  let : NeZero (K p) := ⟨by change 4 ^ _ ≠ (0 : ℕ); positivity⟩
  have hpair := LeonPairAccuracy.expected (P : Measure _) V G (δ p) hv hG
    (fun i => (hb i).1) (fun i => (hb i).2) hs
  have hm (ij) : Measurable (out ij) :=
    Measurable.ite (measurableSet_le (hv _).norm (hv _).norm) (hy _) (hy _)
  have hval (z : (Fin (K p) × Fin (K p)) × Samples p) : F (out z.1 z.2) =
      if ‖V z.1.1 z.2‖ ≤ ‖V z.1.2 z.2‖ then G z.1.1 z.2 else G z.1.2 z.2 := by
    by_cases h : ‖V z.1.1 z.2‖ ≤ ‖V z.1.2 z.2‖ <;> simp [out,G,h]
  let Q := (PMF.uniformOfFintype (Fin (K p) × Fin (K p))).toMeasure.prod (P : Measure (Samples p))
  let Y := fun z : (Fin (K p) × Fin (K p)) × Samples p => output p (modelAt g z.2 (K p)) z.1
  change Measurable Y ∧ Integrable (fun z => ‖F (Y z)‖^2) Q ∧ (∫ z, ‖F (Y z)‖^2 ∂Q) ≤ p.ε^2
  rw [show Y = fun z => out z.1 z.2 from funext fun z => output_eq z.2 z.1]
  refine ⟨measurable_from_prod_countable_right hm, ?_⟩
  simp_rw [hval]
  exact ⟨hpair.1,hpair.2.trans_eq (by unfold δ LeonTuning.resolution; ring)⟩


lemma zero_curvature {F : Point p → ℝ} (hf : ∀ z, HasGradientAt F (gradient F z) z)
    (hl : ∀ z w, ‖gradient F z - gradient F w‖ ≤ smoothness p * ‖z-w‖) (hL : smoothness p = 0)
    (hΔ : 0 ≤ p.Δ) (a : ℝ) (ha : ∀ z, a ≤ F z) (hb : F p.x0 - a ≤ p.Δ) :
    gradient F p.x0 = 0 := by
  by_contra hn
  let L := ‖gradient F p.x0‖^2 / (4 * (p.Δ + 1))
  have hden : 0 < 4 * (p.Δ + 1) := by linarith
  have hnorm := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hpos : 0 < L := div_pos hnorm hden
  have hgrad (z w) : ‖gradient F z - gradient F w‖ ≤ L * ‖z-w‖ := by
    have h := hl z w
    rw [hL,zero_mul] at h
    exact h.trans (mul_nonneg hpos.le (norm_nonneg _))
  have hd := OracleTemplate.Gradient.descent hpos hf hgrad p.x0
  have he : ‖gradient F p.x0‖^2 / (2*L) = 2*(p.Δ+1) := by dsimp [L]; field_simp; ring
  rw [he] at hd
  linarith [ha (p.x0 - (1 / L) • gradient F p.x0)]

end LongTails.Proofs.MultirateAccuracy
