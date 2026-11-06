import LongTails.Proofs.AffineSoftmaxOuterCost
import LongTails.Proofs.AffineSoftmaxCostParameters

namespace LongTails.Proofs.AffineSoftmaxCostMoments

open MeasureTheory
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxOuter
open LongTails.Algorithms.AffineSoftmaxBudget
open LongTails.Algorithms.AffineSoftmaxAcceleration

lemma referenceFinalCost_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L : ℝ) {G r floor : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hf : 0 < floor) (H J : ℕ) (hH : 0 < H) :
    let δp := floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)
    let δm := floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))
    let A := 16 * Real.sqrt ((L + 2 * G ^ 2 / τ + floor) / floor) + 4
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    Integrable (fun seed => (referenceFinalCost m initial τ L G r floor H J seed : ℝ))
      (finalLaw : Measure FinalSeed) ∧
    (∫ seed, (referenceFinalCost m initial τ L G r floor H J seed : ℝ) ∂(finalLaw : Measure FinalSeed)) ≤
      m + (A * (restartRounds (G * r) δp : ℝ) + 1024 * V / (floor * δp)) +
        (A * (3 * (restartRounds (G * r) δm : ℝ) + 4) +
          (1024 * V / (floor * δm)) * (1 + 3 * (J : ℝ) / 2)) := by
  dsimp only
  let δp := floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)
  let δm := floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))
  let s : Snapshot (Fin m) E := ⟨initial, (fun _ => 0), (fun _ => 0)⟩
  let reply := fun _ : Fin m × E => ((0 : ℝ), (0 : E))
  let project := fun _ : E => initial
  let p := fun seed : ProxSeed => (Program.cost reply (cachedProxPlan s τ L G r floor δp project seed) : ℝ)
  let q := fun seed : MultilevelSeed => (Program.cost reply (multilevelPlan s τ L G r floor δm project J seed) : ℝ)
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hδp : 0 < δp := by dsimp [δp]; positivity
  have hδm : 0 < δm := by dsimp [δm]; positivity
  have hp := AffineSoftmaxMultilevelCost.levelPlan_cost_bound s τ L hG hr hf hδp project reply 0
  simp only [levelPlan, pow_zero, div_one, Nat.cast_zero, add_zero, mul_one] at hp
  have hq := AffineSoftmaxMultilevelCost.multilevelPlan_cost_moments s τ L G r floor δm project J reply
    (fun j => (AffineSoftmaxMultilevelCost.levelPlan_cost_bound s τ L hG hr hf hδm project reply j).1)
  have hqb := AffineSoftmaxMultilevelCost.multilevelPlan_cost_le s τ L hG hr hf hδm project reply J
  have hpi : Integrable (fun seed : FinalSeed => p seed.1) (finalLaw : Measure FinalSeed) :=
    measurePreserving_fst.integrable_comp_of_integrable hp.1
  have hqi : Integrable (fun seed : FinalSeed => q seed.2) (finalLaw : Measure FinalSeed) :=
    measurePreserving_snd.integrable_comp_of_integrable hq.1
  have he : (fun seed : FinalSeed => (referenceFinalCost m initial τ L G r floor H J seed : ℝ)) =
      (fun seed => (m : ℝ) + p seed.1 + q seed.2) := by
    funext seed
    simp only [referenceFinalCost, Nat.cast_add, p, q, s, reply, project, δp, δm]
  have hmeanp : (∫ seed : FinalSeed, p seed.1 ∂(finalLaw : Measure FinalSeed)) = ∫ seed, p seed ∂(proxLaw : Measure ProxSeed) := by
    simp only [finalLaw, ProbabilityMeasure.coe_mk, integral_fun_fst, probReal_univ, one_smul]
  have hmeanq : (∫ seed : FinalSeed, q seed.2 ∂(finalLaw : Measure FinalSeed)) = ∫ seed, q seed ∂(multilevelLaw : Measure MultilevelSeed) := by
    simp only [finalLaw, ProbabilityMeasure.coe_mk, integral_fun_snd, probReal_univ, one_smul]
  have hmpi : Integrable (fun seed : FinalSeed => (m : ℝ) + p seed.1) (finalLaw : Measure FinalSeed) :=
    (integrable_const (m : ℝ)).add hpi
  rw [he]
  refine ⟨hmpi.add hqi, ?_⟩
  rw [integral_add hmpi hqi,
    integral_add (integrable_const (m : ℝ)) hpi, hmeanp, hmeanq]
  simp only [integral_const, probReal_univ, one_smul]
  exact add_le_add (add_le_add (le_refl (m : ℝ)) hp.2) hqb

lemma iid_sum_cost_moments {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (c : Ω → ℝ) (hc : Integrable c (P : Measure Ω)) (N : ℕ) :
    Integrable (fun seeds : ℕ → Ω => ∑ k ∈ Finset.range N, c (seeds k))
      (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω))) ∧
    (∫ seeds : ℕ → Ω, (∑ k ∈ Finset.range N, c (seeds k))
      ∂(Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))) = (N : ℝ) * ∫ seed, c seed ∂(P : Measure Ω) := by
  have hp k := measurePreserving_eval_infinitePi (fun _ : ℕ => (P : Measure Ω)) k
  have hi k : Integrable (fun seeds : ℕ → Ω => c (seeds k))
      (Measure.infinitePi (fun _ : ℕ => (P : Measure Ω))) := (hp k).integrable_comp_of_integrable hc
  have he k : (∫ seeds : ℕ → Ω, c (seeds k) ∂(Measure.infinitePi (fun _ : ℕ => (P : Measure Ω)))) =
      ∫ seed, c seed ∂(P : Measure Ω) := by
    rw [← integral_map (hp k).measurable.aemeasurable (by rw [(hp k).map_eq]; exact hc.aestronglyMeasurable), (hp k).map_eq]
  refine ⟨integrable_finsetSum _ (fun k _ => hi k), ?_⟩
  rw [integral_finsetSum _ (fun k _ => hi k)]
  simp only [he, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma referenceOuterCost_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L : ℝ) {G r floor : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hf : 0 < floor) (H b J : ℕ) (hH : 0 < H) :
    let p := fun seed : LongTails.Algorithms.AffineSoftmaxSearch.ProbeSeed =>
      (Program.cost (fun _ : Fin m × E => ((0 : ℝ), (0 : E)))
        (LongTails.Algorithms.AffineSoftmaxSearch.probePlan m initial τ L G r floor (fun _ => initial) seed b) : ℝ)
    Integrable (fun seed => (referenceOuterCost m initial τ L G r floor H b J seed : ℝ))
      (outerLaw : Measure OuterSeed) ∧
    (∫ seed, (referenceOuterCost m initial τ L G r floor H b J seed : ℝ) ∂(outerLaw : Measure OuterSeed)) =
      ((2 * H + 9 : ℕ) : ℝ) * (∫ seed, p seed ∂(LongTails.Algorithms.AffineSoftmaxSearch.probeLaw : Measure _)) +
        (∫ seed, (referenceFinalCost m initial τ L G r floor H J seed : ℝ) ∂(finalLaw : Measure FinalSeed)) := by
  dsimp only
  let p := fun seed : LongTails.Algorithms.AffineSoftmaxSearch.ProbeSeed =>
    (Program.cost (fun _ : Fin m × E => ((0 : ℝ), (0 : E)))
      (LongTails.Algorithms.AffineSoftmaxSearch.probePlan m initial τ L G r floor (fun _ => initial) seed b) : ℝ)
  let f := fun seed : FinalSeed => (referenceFinalCost m initial τ L G r floor H J seed : ℝ)
  let c := fun seeds : ℕ → LongTails.Algorithms.AffineSoftmaxSearch.ProbeSeed =>
    ∑ k ∈ Finset.range (2 * H + 9), p (seeds k)
  have hp := AffineSoftmaxSearchCost.probePlan_cost_moments m initial τ L hG hr hf
    (fun _ => initial) (fun _ => (0, 0)) b
  have hs := iid_sum_cost_moments LongTails.Algorithms.AffineSoftmaxSearch.probeLaw p hp.1 (2 * H + 9)
  have hfint := (referenceFinalCost_moments m initial τ L hG hr hf H J hH).1
  have hci : Integrable (fun seed : OuterSeed => c seed.1) (outerLaw : Measure OuterSeed) :=
    measurePreserving_fst.integrable_comp_of_integrable hs.1
  have hfi : Integrable (fun seed : OuterSeed => f seed.2) (outerLaw : Measure OuterSeed) :=
    measurePreserving_snd.integrable_comp_of_integrable hfint
  have he : (fun seed : OuterSeed => (referenceOuterCost m initial τ L G r floor H b J seed : ℝ)) =
      (fun seed => c seed.1 + f seed.2) := by
    funext seed
    simp only [referenceOuterCost, Nat.cast_add, Nat.cast_sum, c, p, f]
  rw [he]
  refine ⟨hci.add hfi, ?_⟩
  rw [integral_add hci hfi]
  simp only [outerLaw, ProbabilityMeasure.coe_mk, integral_fun_fst, integral_fun_snd, probReal_univ, one_smul]
  exact congrArg (fun a => a + ∫ seed, f seed ∂(finalLaw : Measure FinalSeed)) hs.2

lemma referenceRunCost_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L : ℝ) {G r floor : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hf : 0 < floor) (H b N J : ℕ) (hH : 0 < H) :
    Integrable (fun seeds => (referenceRunCost m initial τ L G r floor H b N J seeds : ℝ))
      (Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed))) ∧
    (∫ seeds, (referenceRunCost m initial τ L G r floor H b N J seeds : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))) =
      (N : ℝ) * ∫ seed, (referenceOuterCost m initial τ L G r floor H b J seed : ℝ) ∂(outerLaw : Measure OuterSeed) := by
  have hi := (referenceOuterCost_moments m initial τ L hG hr hf H b J hH).1
  simpa only [referenceRunCost, Nat.cast_sum] using
    iid_sum_cost_moments outerLaw (fun seed => (referenceOuterCost m initial τ L G r floor H b J seed : ℝ)) hi N

lemma referenceOuterCost_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) {τ L G r D ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    let H := compilerDepth G D r ε
    let floor := compilerFloor G D r ε
    let U := Real.sqrt ((L + 2 * G ^ 2 / τ) / floor)
    let T := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2) / (floor ^ 2 * r ^ 2)
    (∫ seed, (referenceOuterCost m initial τ L G r floor H (compilerBoost G D r ε) (5 * H) seed : ℝ)
      ∂(outerLaw : Measure OuterSeed)) ≤ 200000000000 * (H : ℝ) ^ 5 * ((m : ℝ) + U + T) := by
  let H := compilerDepth G D r ε
  let floor := compilerFloor G D r ε
  let b := compilerBoost G D r ε
  let J := 5 * H
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  let A := 16 * Real.sqrt ((L + 2 * G ^ 2 / τ + floor) / floor) + 4
  let U := Real.sqrt ((L + 2 * G ^ 2 / τ) / floor)
  let T := V / (floor ^ 2 * r ^ 2)
  let δs := floor * r ^ 2 / 32768
  let δp := floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)
  let δm := floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)))
  have hf : 0 < floor := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε
  have hH : 3 ≤ H := AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε
  have hHp : 0 < H := by omega
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hHp
  have hs := AffineSoftmaxCostParameters.compiler_search_depth hG hr hrD hε
  have hsr : (restartRounds (G * r) δs : ℝ) ≤ 10 * (H : ℝ) := by
    have hh : (restartRounds (G * r) δs : ℝ) ≤ 6 * (H : ℝ) := by exact_mod_cast hs
    linarith
  have hpr : (restartRounds (G * r) δp : ℝ) ≤ 8 * (H : ℝ) := by
    have hh : (restartRounds (G * r) δp : ℝ) ≤ ((8 * H : ℕ) : ℝ) :=
      Nat.cast_le.mpr (AffineSoftmaxCostParameters.compiler_final_prox_depth hG hr hrD hε)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hmr : (restartRounds (G * r) δm : ℝ) ≤ 10 * (H : ℝ) := by
    have hh : (restartRounds (G * r) δm : ℝ) ≤ ((10 * H : ℕ) : ℝ) :=
      Nat.cast_le.mpr (AffineSoftmaxCostParameters.compiler_multilevel_base_depth hG hr hrD hε)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
  have hbr : (b : ℝ) ≤ 10 * (H : ℝ) := by
    have hh : (b : ℝ) ≤ 7 * (H : ℝ) := by
      exact_mod_cast AffineSoftmaxOuterParameters.compilerBoost_bound hr hrD hε hsmall
    linarith
  have hAU : A ≤ 20 * (1 + U) := AffineSoftmaxCostParameters.regularized_coefficient_bound (by positivity) hf
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast NeZero.pos m
  have hJr : (J : ℝ) = 5 * (H : ℝ) := by simp only [J, Nat.cast_mul, Nat.cast_ofNat]
  have hns : 1024 * V / (floor * δs) = 33554432 * T := by dsimp [δs, T]; field_simp; ring
  have hnp : 1024 * V / (floor * δp) = 102400000 * (H : ℝ) ^ 3 * T := by dsimp [δp, T]; field_simp; ring
  have hnm : (1024 * V / (floor * δm)) * (1 + 3 * (J : ℝ) / 2) =
      204800000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ)) * (1 + 3 * (J : ℝ) / 2) * T := by
    dsimp [δm, T]
    field_simp
    ring
  have ho := (referenceOuterCost_moments m initial τ L hG hr hf H b J hHp).2
  have hp := (AffineSoftmaxSearchCost.probePlan_cost_moments m initial τ L hG hr hf
    (fun _ => initial) (fun _ : Fin m × E => ((0 : ℝ), (0 : E))) b).2
  have hfin := (referenceFinalCost_moments m initial τ L hG hr hf H J hHp).2
  dsimp only at ho hp hfin
  change _ ≤ (m : ℝ) + (b : ℝ) * m + b * (A * (restartRounds (G * r) δs : ℝ) + 1024 * V / (floor * δs)) at hp
  change _ ≤ (m : ℝ) + (A * (restartRounds (G * r) δp : ℝ) + 1024 * V / (floor * δp)) +
    (A * (3 * (restartRounds (G * r) δm : ℝ) + 4) + (1024 * V / (floor * δm)) * (1 + 3 * (J : ℝ) / 2)) at hfin
  rw [hns] at hp
  rw [hnp, hnm] at hfin
  change (∫ seed, (referenceOuterCost m initial τ L G r floor H b J seed : ℝ) ∂(outerLaw : Measure OuterSeed)) ≤ _
  rw [ho]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (2 * H + 9))) hfin
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hh
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  exact hh.trans (AffineSoftmaxCostParameters.outer_cost_scalar_bound hm hHr (Nat.cast_nonneg b) hbr hJr
    (by dsimp [A]; positivity) hAU (Real.sqrt_nonneg _) (by dsimp [T, V]; positivity)
    (Nat.cast_nonneg _) hsr (Nat.cast_nonneg _) hpr (Nat.cast_nonneg _) hmr)

lemma referenceRunCost_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) {τ L G r D ε : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hrD : r ≤ D)
    (hε : 0 < ε) (hsmall : ε < G * D) :
    let H := compilerDepth G D r ε
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    (∫ seeds, (referenceRunCost m initial τ L G r (compilerFloor G D r ε) H
      (compilerBoost G D r ε) (compilerHorizon G D r ε) (5 * H) seeds : ℝ)
      ∂(Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))) ≤
      50000000000000 * (H : ℝ) ^ 6 *
        ((m : ℝ) * compilerScale D r + D * Real.sqrt ((L + 2 * G ^ 2 / τ) / ε) + V * D ^ 2 / ε ^ 2) := by
  let H := compilerDepth G D r ε
  let floor := compilerFloor G D r ε
  let b := compilerBoost G D r ε
  let N := compilerHorizon G D r ε
  let t := compilerScale D r
  let S := L + 2 * G ^ 2 / τ
  let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
  let U := Real.sqrt (S / floor)
  let T := V / (floor ^ 2 * r ^ 2)
  have hf : 0 < floor := AffineSoftmaxOuterParameters.compilerFloor_pos hr hrD hε
  have hHp : 0 < H := lt_of_lt_of_le (by norm_num : 0 < 3)
    (AffineSoftmaxOuterParameters.compilerDepth_ge_three G D r ε)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hD : 0 < D := hr.trans_le hrD
  have ht : 0 ≤ t := zero_le_one.trans (AffineSoftmaxOuterParameters.compilerScale_bounds hr hrD).1
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hN : (N : ℝ) ≤ 201 * (H : ℝ) * t := (AffineSoftmaxOuterParameters.compilerHorizon_bounds hr hrD).2
  have ho := referenceOuterCost_bound m initial hτ hL hG hr hrD hε hsmall
  have hcancel := AffineSoftmaxCostParameters.compiler_cost_cancellation_bounds hr hrD hε hS hV (G := G)
  have hsum : t * ((m : ℝ) + U + T) ≤ (m : ℝ) * t + D * Real.sqrt (S / ε) + V * D ^ 2 / ε ^ 2 := by
    nlinarith only [hcancel.1, hcancel.2]
  have he := (referenceRunCost_moments m initial τ L hG hr hf H b N (5 * H) hHp).2
  change (∫ seeds, (referenceRunCost m initial τ L G r floor H b N (5 * H) seeds : ℝ)
    ∂(Measure.infinitePi (fun _ : ℕ => (outerLaw : Measure OuterSeed)))) ≤ _
  rw [he]
  calc
    _ ≤ (N : ℝ) * (200000000000 * (H : ℝ) ^ 5 * ((m : ℝ) + U + T)) :=
      mul_le_mul_of_nonneg_left ho (Nat.cast_nonneg N)
    _ ≤ (201 * (H : ℝ) * t) * (200000000000 * (H : ℝ) ^ 5 * ((m : ℝ) + U + T)) := by gcongr
    _ = 40200000000000 * (H : ℝ) ^ 6 * (t * ((m : ℝ) + U + T)) := by ring
    _ ≤ 50000000000000 * (H : ℝ) ^ 6 * ((m : ℝ) * t + D * Real.sqrt (S / ε) + V * D ^ 2 / ε ^ 2) := by
      gcongr
      norm_num

lemma referenceFinalCost_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (H J : ℕ) :
    Measurable (referenceFinalCost m initial τ L G r floor H J) := by
  let s : Snapshot (Fin m) E := ⟨initial, (fun _ => 0), (fun _ => 0)⟩
  let reply := fun _ : Fin m × E => ((0 : ℝ), (0 : E))
  let project := fun _ : E => initial
  have hp := AffineSoftmaxMultilevelCost.cachedProxPlan_cost_measurable
    (fun _ : FinalSeed => s) τ L G r (fun _ => floor)
    (fun _ => floor * r ^ 2 / (100000 * (H : ℝ) ^ 3)) measurable_const measurable_const
    (fun _ => project) reply (fun seed : FinalSeed => seed.1)
    (fun j k => (measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_fst))
  have hq := AffineSoftmaxMultilevelCost.multilevelPlan_cost_measurable
    (fun _ : FinalSeed => s) τ L G r (fun _ => floor)
    (fun _ => floor * r ^ 2 / (2 * 100000 * (H : ℝ) ^ 3 * (2 + 12 * (J : ℝ))))
    measurable_const measurable_const (fun _ => project) (fun _ => J) measurable_const
    reply (fun seed : FinalSeed => seed.2) measurable_snd
  exact (measurable_const.add hp).add hq

lemma probe_cost_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (b : ℕ)
    (project : E → E) (reply : Fin m × E → ℝ × E) :
    Measurable (fun seeds : LongTails.Algorithms.AffineSoftmaxSearch.ProbeSeed =>
      Program.cost reply (LongTails.Algorithms.AffineSoftmaxSearch.probePlan m initial τ L G r floor project seeds b)) := by
  simp only [AffineSoftmaxSearchOracle.probePlan_cost, AffineSoftmaxSearch.boostedCachedPlan_cost]
  apply measurable_const.add
  apply Measurable.add_const
  apply Finset.measurable_sum
  intro j _
  exact AffineSoftmaxMultilevelCost.cachedProxPlan_cost_measurable _ τ L G r
    (fun _ => floor) (fun _ => floor * r ^ 2 / 32768) measurable_const measurable_const
    (fun _ => project) reply (fun seeds : LongTails.Algorithms.AffineSoftmaxSearch.ProbeSeed => seeds j)
    (fun k l => (measurable_pi_apply l).comp ((measurable_pi_apply k).comp (measurable_pi_apply j)))

lemma referenceOuterCost_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (H b J : ℕ) :
    Measurable (referenceOuterCost m initial τ L G r floor H b J) := by
  have hp := probe_cost_measurable m initial τ L G r floor b (fun _ => initial) (fun _ => (0, 0))
  have hf := referenceFinalCost_measurable m initial τ L G r floor H J
  exact (Finset.measurable_sum _ (fun i _ => hp.comp ((measurable_pi_apply i).comp measurable_fst))).add
    (hf.comp measurable_snd)

lemma referenceRunCost_measurable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (initial : E) (τ L G r floor : ℝ) (H b N J : ℕ) :
    Measurable (referenceRunCost m initial τ L G r floor H b N J) := by
  exact Finset.measurable_sum _ (fun i _ =>
    (referenceOuterCost_measurable m initial τ L G r floor H b J).comp (measurable_pi_apply i))

end LongTails.Proofs.AffineSoftmaxCostMoments
