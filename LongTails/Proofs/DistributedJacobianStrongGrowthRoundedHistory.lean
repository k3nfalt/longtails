import LongTails.Proofs.DistributedJacobianStrongGrowthRounding

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRoundedHistory

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

lemma history_projected_block_contraction (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (T N : ℕ) {r : ℝ} (hr : 0 < r)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T ≤ (p.n : ℝ))
    (hguard : p.M * r ≤ p.L /
      (16 * (p.L / p.μ) * p.ρ * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T))
    (width : ℕ) (spacing : ℝ) (hs : 0 < spacing)
    (hrange : 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T ≤
      spacing * ((2 ^ width - 1 : ℕ) : ℝ) / 2)
    (current anchor : (Fin N → p.Ω) → Point p) (hx : Measurable current) (ha : Measurable anchor)
    (E : Set (Fin N → p.Ω)) (hE : MeasurableSet E)
    (hlocal : ∀ z ∈ E, ‖current z - I.solution‖ ≤ r)
    (hanchor : ∀ z ∈ E, ‖I.solution - anchor z‖ ≤ r / 2) :
    let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
    let c := (T : ℝ) / (64 * (p.L / p.μ))
    let past := fun ω (i : Fin N) => S.sample i.val ω
    let good := past ⁻¹' E
    let output := fun ω => projectedBlockOutput p T N H width spacing (anchor (past ω)) r g
      (current (past ω)) (fun k => S.sample k ω)
    Integrable (good.indicator (fun ω => ‖output ω - I.solution‖ ^ 2)) (S.law : Measure S.Seed) ∧
      (∫ ω, good.indicator (fun ω => ‖output ω - I.solution‖ ^ 2) ω ∂(S.law : Measure S.Seed)) ≤
        (1 - c / 2) *
          (∫ ω, good.indicator (fun ω => ‖current (past ω) - I.solution‖ ^ 2) ω ∂(S.law : Measure S.Seed)) +
            (1 + 2 / c) * (Real.sqrt p.d * spacing) ^ 2 := by
  classical
  let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
  let c := (T : ℝ) / (64 * (p.L / p.μ))
  let past := fun ω (i : Fin N) => S.sample i.val ω
  let good := past ⁻¹' E
  let Z := fun ω => blockOutput p T N H g (current (past ω)) (fun k => S.sample k ω)
  let X := fun ω => roundedBlockOutput p T N H width spacing g (current (past ω))
    (fun k => S.sample k ω)
  have hmup : 0 < p.μ := hp.2.2.2.2.2.2.1
  have hL : 0 < p.L := lt_of_lt_of_le hmup hp.2.2.2.2.2.2.2.1
  have hrho : 0 ≤ p.ρ := le_trans (by norm_num) hp.2.2.2.2.2.2.2.2.1
  have hRp : 0 < p.R := hp.2.2.2.2.2.2.2.2.2.2.1
  have ht : 0 < (T : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  have hc : 0 < c := by dsimp [c]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hpast : Measurable past := Measurable.of_eval fun i => S.iid.measurable (i.val)
  have hstream : Measurable (fun ω => fun k => S.sample k ω) :=
    Measurable.of_eval fun k => S.iid.measurable k
  have hX : Measurable X :=
    (DistributedJacobianStrongGrowthRounding.measurable_roundedBlockOutput
      p T N H width spacing g hg.1).comp ((hx.comp hpast).prodMk hstream)
  have hgood : MeasurableSet good := hE.preimage hpast
  have hb := DistributedJacobianStrongGrowthHistory.history_block_contraction
    p hp I hI g S hg T N hr hT hTκ hn hguard current hx E hE hlocal
  have hZi : Integrable (good.indicator (fun ω => ‖Z ω - I.solution‖ ^ 2))
      (S.law : Measure S.Seed) := by
    change Integrable (fun ω => good.indicator (fun ω => ‖Z ω - I.solution‖ ^ 2) ω)
      (S.law : Measure S.Seed)
    simpa only [good, Z, past, H, Set.indicator, Set.mem_preimage] using hb.1
  have hZb : (∫ ω, good.indicator (fun ω => ‖Z ω - I.solution‖ ^ 2) ω ∂(S.law : Measure S.Seed)) ≤
      (1 - c) * ∫ ω, good.indicator (fun ω => ‖current (past ω) - I.solution‖ ^ 2) ω
        ∂(S.law : Measure S.Seed) := by
    simpa only [good, Z, past, H, c, Set.indicator, Set.mem_preimage] using hb.2
  have hdist : ‖I.solution - p.x0‖ ≤ p.R := by
    simpa only [norm_sub_rev] using hI.2.2.2.2.1
  have hrnd := DistributedJacobianStrongGrowthProjection.localized_rounded_event_bound
    (S.law : Measure S.Seed) p (anchor ∘ past) X Z I.solution good hgood (ha.comp hpast) hX
    hRp.le hr.le hdist (fun ω hω => hanchor (past ω) hω)
    (by positivity : 0 ≤ Real.sqrt p.d * spacing) (half_pos hc)
    (fun ω _ => DistributedJacobianStrongGrowthRounding.roundedBlockOutput_error
      p T N H hH width spacing hs hrange g (current (past ω)) (fun k => S.sample k ω)) hZi
  have hcoef : 1 + 1 / (c / 2) = 1 + 2 / c := by field_simp
  rw [hcoef] at hrnd
  refine ⟨hrnd.1, ?_⟩
  apply DistributedJacobianStrongGrowthProjection.rounded_contraction_algebra
    (integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => sq_nonneg _) ω)
  exact hrnd.2.trans (add_le_add
    (mul_le_mul_of_nonneg_left hZb (by positivity : 0 ≤ 1 + c / 2)) le_rfl)

end LongTails.Proofs.DistributedJacobianStrongGrowthRoundedHistory
