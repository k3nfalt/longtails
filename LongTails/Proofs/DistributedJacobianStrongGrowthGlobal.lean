import LongTails.Proofs.DistributedJacobianStrongGrowthBounds

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthGlobal

lemma bounded_good_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f)
    {D : ℝ} (h0 : ∀ ω, 0 ≤ f ω) (hD : ∀ ω, f ω ≤ D)
    (E : Set Ω) (hE : MeasurableSet E) :
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤ (∫ ω, E.indicator f ω ∂P) + D * P.real Eᶜ := by
  have hi : Integrable f P := (integrable_const D).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (h0 ω)]; exact hD ω)
  have hb := integral_mono (hi.indicator hE.compl) ((integrable_const D).indicator hE.compl)
    (fun ω => by
      by_cases hω : ω ∈ Eᶜ
      · simpa only [Set.indicator_of_mem hω] using hD ω
      · simp only [Set.indicator_of_notMem hω, le_refl])
  rw [integral_indicator_const D hE.compl, smul_eq_mul] at hb
  have he := integral_add_compl hE hi
  rw [← integral_indicator hE, ← integral_indicator hE.compl] at he
  refine ⟨hi, ?_⟩
  rw [← he]
  exact add_le_add le_rfl (by simpa only [mul_comm] using hb)

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProcess

lemma random_warm_center_bound (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (s T : ℕ) {r : ℝ} (hr : 0 < r)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T ≤ (p.n : ℝ))
    (hguard : p.M * r ≤ p.L /
      (16 * (p.L / p.μ) * p.ρ * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T))
    (width : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (hrange : 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T ≤
      spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (center : (Fin (p.n * s) → p.Ω) → Point p) (hm : Measurable center)
    (hcR : ∀ z, ‖center z - p.x0‖ ≤ p.R)
    (E : Set (Fin (p.n * s) → p.Ω)) (hE : MeasurableSet E)
    (hcenter : ∀ z ∈ E, ‖center z - I.solution‖ ≤ 3 * r / 8) (k : ℕ) :
    let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
    let c := (T : ℝ) / (64 * (p.L / p.μ))
    let past := fun ω (i : Fin (p.n * s)) => S.sample i.val ω
    let output := fun ω => refineRun p s T H width spacing r g (center (past ω))
      (fun t => S.sample t ω) k
    Measurable output ∧ Integrable (fun ω => ‖output ω - I.solution‖ ^ 2) (S.law : Measure S.Seed) ∧
      (∫ ω, ‖output ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)) ≤
        (1 - c / 2) ^ k * r ^ 2 + (2 / c) * (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2 +
          4 * p.R ^ 2 * (S.law : Measure S.Seed).real {ω | past ω ∉ E} := by
  classical
  let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
  let c := (T : ℝ) / (64 * (p.L / p.μ))
  let V := (1 - c / 2) ^ k * r ^ 2 + (2 / c) * (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2
  let past := fun ω (i : Fin (p.n * s)) => S.sample i.val ω
  let good := past ⁻¹' E
  let output := fun ω => refineRun p s T H width spacing r g (center (past ω))
    (fun t => S.sample t ω) k
  let P0 : Measure (Fin (p.n * s) → p.Ω) := Measure.pi fun _ => (S.marginal : Measure p.Ω)
  let Q0 : Measure (ℕ → p.Ω) := Measure.infinitePi fun _ : ℕ => (S.marginal : Measure p.Ω)
  let S0 : Sampling p := {
    Seed := ℕ → p.Ω
    measurableSeed := inferInstance
    law := ⟨Q0, inferInstance⟩
    marginal := S.marginal
    sample := fun j ω => ω j
    iid := by simpa [Q0] using OracleTemplate.StochasticGeneralized.infinitePi_iid (S.marginal : Measure p.Ω) }
  have hg0 : oracleAssumptions p I g S0 := hg
  let K : (Fin (p.n * s) → p.Ω) → (ℕ → p.Ω) → ℝ :=
    fun z ω => ‖refineRun p 0 T H width spacing r g (center z) ω k - I.solution‖ ^ 2
  have hK : Measurable (Function.uncurry K) :=
    (((DistributedJacobianStrongGrowthProcess.measurable_refineRun p 0 T H width spacing r g hg.1 k).comp
      ((hm.comp measurable_fst).prodMk measurable_snd)).sub_const I.solution).norm.pow_const 2
  have hmup : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hL : 0 < p.L := lt_of_lt_of_le hmup hp.2.2.2.2.2.2.2.1
  have hκ : 0 < p.L / p.μ := div_pos hL hmup
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 64 * (p.L / p.μ))).mpr
    nlinarith
  have hq : 0 ≤ 1 - c / 2 := by linarith
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hb (z : Fin (p.n * s) → p.Ω) (hz : z ∈ E) :=
    DistributedJacobianStrongGrowthBounds.refineRun_bound p hp I hI g S0 hg0 0 T hr hT hTκ hn hguard
      width spacing hs hrange (center z) (hcR z) (hcenter z hz) k
  have hKb (z : Fin (p.n * s) → p.Ω) (hz : z ∈ E) : (∫ ω, K z ω ∂Q0) ≤ V := by
    have hnorm : ‖center z - I.solution‖ ≤ r := (hcenter z hz).trans (by linarith)
    have hsquare := (sq_le_sq₀ (norm_nonneg _) hr.le).mpr hnorm
    exact (hb z hz).2.trans (add_le_add
      (mul_le_mul_of_nonneg_left hsquare (pow_nonneg hq k)) le_rfl)
  have hW : Integrable (E.indicator (fun _ => V)) P0 := (integrable_const V).indicator hE
  have hpbound := DistributedJacobianStrongGrowthHistory.product_event_bound P0 Q0 K (fun _ => V) E hE hK
    (fun _ _ => sq_nonneg _) (fun z hz => (hb z hz).1) hKb hW
  have hmean : (∫ z, E.indicator (fun _ => V) z ∂P0) ≤ V := by
    calc
      _ ≤ ∫ _z, V ∂P0 := integral_mono hW (integrable_const V) (fun z => by
        by_cases hz : z ∈ E
        · simp only [Set.indicator_of_mem hz, le_refl]
        · simpa only [Set.indicator_of_notMem hz] using hV)
      _ = V := by simp
  have hpair := S.iid.prefix_tail_law (p.n * s)
  have hlaw : ProbabilityTheory.HasLaw
      (fun ω => (past ω, fun j => S.sample (p.n * s + j) ω)) (P0.prod Q0)
      (S.law : Measure S.Seed) := ⟨hpair.measurable.aemeasurable, hpair.map_eq⟩
  have hv := hlaw.integral_comp hpbound.1.aestronglyMeasurable
  have hshift (ω : S.Seed) : K (past ω) (fun j => S.sample (p.n * s + j) ω) =
      ‖output ω - I.solution‖ ^ 2 :=
    congrArg (fun x => ‖x - I.solution‖ ^ 2)
      (DistributedJacobianStrongGrowthProcess.refineRun_shift p s T H width spacing r g
        (center (past ω)) (fun j => S.sample j ω) k).symm
  have hind (ω : S.Seed) : E.indicator (fun z => K z (fun j => S.sample (p.n * s + j) ω)) (past ω) =
      good.indicator (fun ω => ‖output ω - I.solution‖ ^ 2) ω := by
    by_cases hω : past ω ∈ E
    · simpa only [Set.indicator_of_mem hω,
        Set.indicator_of_mem (show ω ∈ good from hω)] using hshift ω
    · simp only [Set.indicator_of_notMem hω, Set.indicator_of_notMem (show ω ∉ good from hω)]
  change (∫ ω, E.indicator (fun z => K z (fun j => S.sample (p.n * s + j) ω)) (past ω)
    ∂(S.law : Measure S.Seed)) = _ at hv
  simp_rw [hind] at hv
  have hgoodbound : (∫ ω, good.indicator (fun ω => ‖output ω - I.solution‖ ^ 2) ω
      ∂(S.law : Measure S.Seed)) ≤ V := by
    rw [hv]
    exact hpbound.2.trans hmean
  have hpast : Measurable past := Measurable.of_eval fun i => S.iid.measurable i.val
  have hstream : Measurable (fun ω => fun j => S.sample j ω) := Measurable.of_eval S.iid.measurable
  have hout : Measurable output := by
    convert! (DistributedJacobianStrongGrowthProcess.measurable_refineRun p s T H width spacing r g hg.1 k).comp
      ((hm.comp hpast).prodMk hstream) using 1
  have hR : 0 ≤ p.R := le_of_lt hp.2.2.2.2.2.2.2.2.2.2.1
  have hglobal (ω : S.Seed) : ‖output ω - I.solution‖ ^ 2 ≤ (2 * p.R) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      (DistributedJacobianStrongGrowthProcess.refineRun_global_root_bound p s T H width spacing r g
        (center (past ω)) I.solution (fun j => S.sample j ω) k hR (hcR _) hI.2.2.2.2.1)
  have hsplit := bounded_good_event (S.law : Measure S.Seed)
    (fun ω => ‖output ω - I.solution‖ ^ 2) ((hout.sub_const I.solution).norm.pow_const 2)
    (fun _ => sq_nonneg _) hglobal good (hE.preimage hpast)
  refine ⟨hout, hsplit.1, ?_⟩
  change (∫ ω, ‖output ω - I.solution‖ ^ 2 ∂(S.law : Measure S.Seed)) ≤
    V + 4 * p.R ^ 2 * (S.law : Measure S.Seed).real goodᶜ
  nlinarith [hsplit.2]

end LongTails.Proofs.DistributedJacobianStrongGrowthGlobal
