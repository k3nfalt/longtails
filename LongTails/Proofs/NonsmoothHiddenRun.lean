import LongTails.Proofs.NonsmoothHiddenExpectation
import LongTails.Proofs.HiddenConvexRun
import LongTails.Proofs.MomentumLastIterateRecursion
import LongTails.Proofs.NonsmoothHiddenTuning

open Set Metric InnerProductSpace MeasureTheory Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.NonsmoothHidden

open LocalHiddenConvex

noncomputable def localCost (G D M r : ℝ) (k : ℕ) : ℝ :=
  G ^ 2 / (2 * D) + (96 * D * M * r ^ 3 + 16 * G * M * r ^ 2) / ((k : ℝ) + 1)

lemma harmonic_sum_bound (N : ℕ) :
    ∑ j ∈ range N, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log ((N : ℝ) + 1) := by
  cases N with
  | zero => simp
  | succ N =>
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_add, div_one, Nat.cast_add, Nat.cast_one]
    have hs := MomentumConvex.sum_inv_le_log N
    have he : ∀ j : ℕ, (j : ℝ) + 1 + 1 = (j : ℝ) + 2 := fun j => by ring
    simp only [he]
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) + 1)
      (by linarith : (N : ℝ) + 1 ≤ (N : ℝ) + 1 + 1)
    have he2 : (N : ℝ) + 1 + 1 = (N : ℝ) + 2 := by ring
    rw [he2] at hl
    linarith

lemma localCost_sum_bound {G D M r : ℝ} (hG : 0 ≤ G) (hD : 0 ≤ D)
    (hM : 0 ≤ M) (hr : 0 ≤ r) (N : ℕ) :
    ∑ j ∈ range N, localCost G D M r j ≤ (N : ℝ) * G ^ 2 / (2 * D) +
      (96 * D * M * r ^ 3 + 16 * G * M * r ^ 2) * (1 + Real.log ((N : ℝ) + 1)) := by
  simp only [localCost, div_eq_mul_inv, sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul, ← mul_sum]
  have hh := mul_le_mul_of_nonneg_left (harmonic_sum_bound N)
    (by positivity : 0 ≤ 96 * D * M * r ^ 3 + 16 * G * M * r ^ 2)
  simp only [one_div] at hh
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F H : E → ℝ} {c : E → E} {J : E → E →L[ℝ] E}
  {g : E → E} {oracle : E → Ω → E} {μ LJ r D G : ℝ}
  (hμ : 0 < μ) (hLJ : 0 ≤ LJ) (hr : 0 ≤ r) (hD : 0 < D) (hG : 0 ≤ G)
  (hreg : 64 * LJ * r ≤ μ) (hJ : ∀ x v, μ * ‖v‖ ≤ ‖J x v‖)
  (hTaylor : ∀ x y, ‖c y - c x - J x (y - x)‖ ≤ LJ * ‖y - x‖ ^ 2)
  (hlip : ∀ x y, ‖J x - J y‖ ≤ LJ * ‖x - y‖)
  (heq : ∀ x, F x = H (c x)) (hF : Measurable F)
  (hg : ∀ x, LongTails.Setups.NonsmoothHiddenConvex.IsPulledSubgradient H c J g x)
  (hom : Measurable (Function.uncurry oracle)) (hoi : ∀ x, Integrable (oracle x) P)
  (hoi2 : ∀ x, Integrable (fun ω => ‖oracle x ω‖ ^ 2) P)
  (homean : ∀ x, ∫ ω, oracle x ω ∂P = g x)
  (hoG : ∀ x, ∫ ω, ‖oracle x ω‖ ^ 2 ∂P ≤ G ^ 2)

include hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hF hg hom hoi hoi2 homean hoG

omit [CompleteSpace E] in
lemma run_energy_integrable (N k : ℕ) {b u x z : E} (hu : u ∈ closedBall b r)
    (hx : x ∈ closedBall b (2 * r)) (hz : z ∈ closedBall b (2 * r)) :
    Integrable (fun ξ => localEnergy F c J b r D u (k + N)
      (localRun oracle r D b N k x z ξ)) (Measure.pi fun _ : Fin N => P) := by
  have hpG : ∀ v, ‖g v‖ ≤ G := fun v =>
    mean_norm_le hG (hoi v) (hoi2 v) (homean v) (hoG v)
  have hqm := local_correction_measurable hμ hLJ hr hreg hJ hTaylor hlip hu
  have hgap : ∀ v ∈ closedBall b (2 * r), |F v - F u| ≤ 4 * G * r :=
    fun v hv => local_gap_abs_le hμ hLJ hG hr hreg hJ hTaylor heq hg hpG hv hu
  have hq : ∀ v ∈ closedBall b (2 * r), ‖qField c J b r u v‖ ≤ r := by
    intro v hv
    rw [qField_eq hv]
    exact (correction_small hμ hLJ hr hreg hJ hTaylor hv hu).2
  have hm : Measurable (fun ξ : Fin N → Ω => localRun oracle r D b N k x z ξ) :=
    (localRun_measurable hom r D N k).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin N → Ω => ((b, x, z), ξ)))
  exact localEnergy_integrable hr hD.le (k + N) hu hF hqm hgap hq hm
    (fun ξ => localRun_mem oracle hr N k hx hz ξ)

lemma expected_energy_bound (N k : ℕ) {b u x z : E} (hu : u ∈ closedBall b r)
    (hx : x ∈ closedBall b (2 * r)) (hz : z ∈ closedBall b (2 * r)) :
    (∫ ξ, localEnergy F c J b r D u (k + N) (localRun oracle r D b N k x z ξ)
      ∂Measure.pi (fun _ : Fin N => P)) ≤
      localEnergy F c J b r D u k (x, z) +
        ∑ j ∈ range N, localCost G D (LJ / μ) r (k + j) := by
  have hqm := local_correction_measurable hμ hLJ hr hreg hJ hTaylor hlip hu
  induction N generalizing k x z with
  | zero => simp [localRun]
  | succ N ih =>
    let Q := Measure.pi (fun _ : Fin N => P)
    let y := averageQuery k x z
    let step := fun ω => (y, ballProj b (2 * r) (z - D⁻¹ • oracle y ω))
    let C := ∑ j ∈ range N, localCost G D (LJ / μ) r (k + 1 + j)
    let B := fun ω => localEnergy F c J b r D u (k + 1) (step ω) + C
    let Φ := fun v : Ω × (Fin N → Ω) => localEnergy F c J b r D u (k + (N + 1))
      (localRun oracle r D b (N + 1) k x z (Fin.cons v.1 v.2))
    have hRunM : Measurable (fun ξ : Fin (N + 1) → Ω =>
        localRun oracle r D b (N + 1) k x z ξ) :=
      (localRun_measurable hom r D (N + 1) k).comp
        (measurable_const.prodMk measurable_id :
          Measurable (fun ξ : Fin (N + 1) → Ω => ((b, x, z), ξ)))
    have hm : Measurable (fun ξ : Fin (N + 1) → Ω =>
        localEnergy F c J b r D u (k + (N + 1)) (localRun oracle r D b (N + 1) k x z ξ)) :=
      (localEnergy_measurable (D := D) hF hqm (k + (N + 1))).comp hRunM
    have hcons := StochasticGradient.cons_measurePreserving P N
    have hi := run_energy_integrable hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hF hg
      hom hoi hoi2 homean hoG (N + 1) k hu hx hz
    have hΦi : Integrable Φ (P.prod Q) := (hcons.integrable_comp hm.aestronglyMeasurable).mpr hi
    have hy : y ∈ closedBall b (2 * r) := averageQuery_mem k hx hz
    have hz' : ∀ ω, (step ω).2 ∈ closedBall b (2 * r) :=
      fun ω => ballProj_mem b _ (by positivity)
    have hEq (ω : Ω) : (fun ξ => Φ (ω, ξ)) =
        fun ξ => localEnergy F c J b r D u (k + 1 + N)
          (localRun oracle r D b N (k + 1) (step ω).1 (step ω).2 ξ) := by
      funext ξ
      simp only [Φ, localRun, Fin.cons_zero, Fin.cons_succ, step, y]
      congr 1
      omega
    have hStep := local_energy_step hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hF hg
      hom hoi hoi2 homean hoG k hu hx hz
    have hBi : Integrable B P := hStep.1.add (integrable_const C)
    have hb : ∀ ω, (∫ ξ, Φ (ω, ξ) ∂Q) ≤ B ω := by
      intro ω
      rw [hEq]
      exact ih (k + 1) hy (hz' ω)
    calc
      _ = ∫ v, Φ v ∂P.prod Q := by
        rw [← hcons.map_eq, integral_map hcons.measurable.aemeasurable hm.aestronglyMeasurable]
      _ = ∫ ω, ∫ ξ, Φ (ω, ξ) ∂Q ∂P := integral_prod Φ hΦi
      _ ≤ ∫ ω, B ω ∂P := integral_mono hΦi.integral_prod_left hBi hb
      _ = (∫ ω, localEnergy F c J b r D u (k + 1) (step ω) ∂P) + C := by
        rw [integral_add hStep.1 (integrable_const C)]
        simp only [integral_const, probReal_univ, one_smul]
        rfl
      _ ≤ localEnergy F c J b r D u k (x, z) + localCost G D (LJ / μ) r k + C := by
        have hh := hStep.2
        change (∫ ω, localEnergy F c J b r D u (k + 1) (step ω) ∂P) ≤
          localEnergy F c J b r D u k (x, z) + G ^ 2 / (2 * D) +
            (96 * D * (LJ / μ) * r ^ 3 + 16 * G * (LJ / μ) * r ^ 2) / ((k : ℝ) + 1) at hh
        unfold localCost
        linarith
      _ = _ := by
        rw [sum_range_succ', add_zero]
        simp only [C]
        have he : ∀ j, k + 1 + j = k + (j + 1) := fun j => by omega
        simp only [he]
        ring

omit [CompleteSpace E] hD hlip in
lemma localOutput_integrable (N : ℕ) {b u : E} (hu : u ∈ closedBall b r) :
    Integrable (fun ξ => F (localOutput oracle r D N b ξ) - F u)
      (Measure.pi (fun _ : Fin N => P)) := by
  have hb : b ∈ closedBall b (2 * r) := mem_closedBall_self (by positivity)
  have hm : Measurable (fun ξ : Fin N → Ω => localRun oracle r D b N 0 b b ξ) :=
    (localRun_measurable hom r D N 0).comp
      (measurable_const.prodMk measurable_id : Measurable (fun ξ : Fin N → Ω => ((b, b, b), ξ)))
  have hpG : ∀ v, ‖g v‖ ≤ G := fun v =>
    mean_norm_le hG (hoi v) (hoi2 v) (homean v) (hoG v)
  apply Integrable.of_bound ((hF.comp hm.fst).sub measurable_const).aestronglyMeasurable (4 * G * r)
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs]
  exact local_gap_abs_le hμ hLJ hG hr hreg hJ hTaylor heq hg hpG
    (localRun_mem oracle hr N 0 hb hb ξ).1 hu

lemma expected_gap_sum_bound (N : ℕ) {b u : E} (hu : u ∈ closedBall b r) :
    (N : ℝ) * (∫ ξ, F (localOutput oracle r D N b ξ) - F u
      ∂Measure.pi (fun _ : Fin N => P)) ≤ D * r ^ 2 / 2 + 28 * D * (LJ / μ) * r ^ 3 +
        ∑ j ∈ range N, localCost G D (LJ / μ) r j := by
  have hb : b ∈ closedBall b (2 * r) := mem_closedBall_self (by positivity)
  have hei := run_energy_integrable hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hF hg
    hom hoi hoi2 homean hoG N 0 hu hb hb
  have hgi := localOutput_integrable (D := D) hμ hLJ hr hG hreg hJ hTaylor heq hF hg
    hom hoi hoi2 homean hoG N hu
  have he := expected_energy_bound hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hF hg
    hom hoi hoi2 homean hoG N 0 hu hb hb
  have hinit := localEnergy_initial (F := F) hμ hLJ hr hD.le hJ hTaylor hu
  simp only [zero_add] at hei he
  have hp : (∫ ξ, (N : ℝ) * (F (localOutput oracle r D N b ξ) - F u)
      ∂Measure.pi (fun _ : Fin N => P)) ≤
      ∫ ξ, localEnergy F c J b r D u N (localRun oracle r D b N 0 b b ξ) +
        27 * D * (LJ / μ) * r ^ 3 ∂Measure.pi (fun _ : Fin N => P) := by
    apply integral_mono (hgi.const_mul _) (hei.add (integrable_const _))
    intro ξ
    have hm := localRun_mem (D := D) oracle hr N 0 hb hb ξ
    exact localEnergy_endpoint hμ hLJ hr hD.le hreg hJ hTaylor hu hm.1 hm.2 N
  rw [integral_const_mul, integral_add hei (integrable_const _)] at hp
  simp only [integral_const, probReal_univ, one_smul] at hp
  linarith

lemma expected_gap_bound (N : ℕ) (hN : 1 ≤ N) (hrpos : 0 < r) (hGpos : 0 < G)
    (hDvalue : D = G * Real.sqrt (N : ℝ) / r) {b u : E} (hu : u ∈ closedBall b r) :
    (∫ ξ, F (localOutput oracle r D N b ξ) - F u ∂Measure.pi (fun _ : Fin N => P)) ≤
      16 * G * r * (1 + Real.log ((N : ℝ) + 1)) / Real.sqrt (N : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt (N : ℝ) := by
    simpa using Real.sqrt_le_sqrt hNreal
  have hspos : 0 < Real.sqrt (N : ℝ) := by linarith
  have hM : 0 ≤ LJ / μ := div_nonneg hLJ hμ.le
  have hsmall : 64 * (LJ / μ) * r ≤ 1 := by
    calc 64 * (LJ / μ) * r = (64 * LJ * r) / μ := by ring
         _ ≤ 1 := (div_le_one hμ).2 hreg
  have hL : 1 ≤ 1 + Real.log ((N : ℝ) + 1) := by
    have hl := Real.log_nonneg (by linarith : (1 : ℝ) ≤ (N : ℝ) + 1)
    linarith
  have hn := local_numerator_bound hGpos hrpos hM hs hL hsmall
  rw [Real.sq_sqrt (Nat.cast_nonneg N), ← hDvalue] at hn
  have hc := localCost_sum_bound hG hD.le hM hr N
  have he := expected_gap_sum_bound hμ hLJ hr hD hG hreg hJ hTaylor hlip heq hF hg
    hom hoi hoi2 homean hoG N hu
  have hh : (N : ℝ) * (∫ ξ, F (localOutput oracle r D N b ξ) - F u
      ∂Measure.pi (fun _ : Fin N => P)) ≤
      16 * G * r * Real.sqrt (N : ℝ) * (1 + Real.log ((N : ℝ) + 1)) := by
    linarith
  apply (le_div_iff₀ hspos).2
  apply (mul_le_mul_iff_left₀ hspos).mp
  calc
    _ = (N : ℝ) * (∫ ξ, F (localOutput oracle r D N b ξ) - F u
        ∂Measure.pi (fun _ : Fin N => P)) := by
      calc
        _ = (Real.sqrt (N : ℝ)) ^ 2 * (∫ ξ, F (localOutput oracle r D N b ξ) - F u
            ∂Measure.pi (fun _ : Fin N => P)) := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    _ ≤ _ := hh
    _ = _ := by ring

end OracleTemplate.NonsmoothHidden
