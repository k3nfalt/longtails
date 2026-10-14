import LongTails.Proofs.NearZeroSumFoamConvergence
import LongTails.Proofs.NearZeroSumRegularization
import LongTails.Proofs.NearZeroSumOrientation
import LongTails.Proofs.NearZeroSumTuning

open scoped RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace OracleTemplate.NearZeroSum

open LongTails.Setups.NearZeroSumGames

lemma minimum_game_monotonicity {p : Public} {I : Problem p} {H G : Space p → Space p}
    (geom : GameGeometry p I H G) (hνμ : p.ν ≤ p.μ)
    {u v : Space p} (hu : u ∈ domain p) (hv : v ∈ domain p) :
    p.ν * ‖u - v‖ ^ 2 ≤ ⟪ownGradient H G u - ownGradient H G v, u - v⟫ := by
  have h := game_monotonicity geom.strongX geom.strongY geom.convexG
    geom.gradientH geom.gradientG hu hv
  have hμ := mul_le_mul_of_nonneg_right hνμ (sq_nonneg ‖u.fst - v.fst‖)
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.sub_fst, WithLp.sub_snd]
  nlinarith

set_option maxHeartbeats 800000 in
lemma ordered_proximal_accuracy {p : Public} {I : Problem p} {H G P : Space p → Space p}
    (geom : GameGeometry p I H G) (hC : IsComplete (domain p))
    (hP : ConstrainedMonotone.Proj (domain p) P)
    (hν : 0 < p.ν) (hνμ : p.ν ≤ p.μ) (hμL : p.μ ≤ p.L)
    (hδ : 0 ≤ p.δ) (hδL : p.δ ≤ p.L) (hD : 0 ≤ p.D) (hε : 0 < p.ε)
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p,
      ‖ownGradient H G u - ownGradient H G v‖ ≤ 2 * p.L * ‖u - v‖)
    (hdiam : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖u - v‖ ≤ p.D)
    (u0 s : Space p) (hu0 : u0 ∈ domain p) (hs : s ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) s (-ownGradient H G s)) :
    let β := p.ν + 16 * p.δ
    let cfg := tunedFoamConfig p.L p.μ p.ν p.δ p.D p.ε
    let N := ⌈2 * (p.ν + β) / p.ν * Real.log (2 + p.D ^ 2 / p.ε)⌉₊
    let out := QueryPlan.eval (Sum.elim (ownGradient H G) P) (proximalFoamPlan cfg β N u0)
    out ∈ domain p ∧ ‖out - s‖ ^ 2 ≤ p.ε := by
  let β := p.ν + 16 * p.δ
  let cfg := tunedFoamConfig p.L p.μ p.ν p.δ p.D p.ε
  let N := ⌈2 * (p.ν + β) / p.ν * Real.log (2 + p.D ^ 2 / p.ε)⌉₊
  let step := fun u => QueryPlan.eval (Sum.elim (ownGradient H G) P) (foamPlan cfg β u u)
  let e := p.ν * Real.sqrt p.ε / (4 * (p.ν + β))
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hL : 0 < p.L := (hν.trans_le hνμ).trans_le hμL
  have hmr : 0 < p.ν + β := by linarith
  have hf := tuned_foam_facts hν hνμ hμL hδ hδL p.D p.ε
  have hmono := fun u hu v hv => minimum_game_monotonicity geom hνμ (u := u) (v := v) hu hv
  have hstep : ∀ u ∈ domain p, step u ∈ domain p ∧
      ‖step u - s‖ ≤ β / (p.ν + β) * ‖u - s‖ + e := by
    intro u hu
    obtain ⟨r, hr, hnr⟩ := regularized_vi_exists hC ⟨u0, hu0⟩ hP hν
      (by linarith : p.ν ≤ 2 * p.L) hβ hmono hlip u
    have gr := regularized_geometry geom β u
    have hfield : ∀ v ∈ domain (regularizedPublic p β),
        ownGradient H G v + β • (v - u) =
          ownGradient (p := regularizedPublic p β) (regularizedH H β u) G v := by
      intro v _
      exact (regularized_own_gradient H G β u v).symm
    have hLip : ∀ v ∈ domain (regularizedPublic p β), ∀ w ∈ domain (regularizedPublic p β),
        ‖(ownGradient H G v + β • (v - u)) -
          (ownGradient H G w + β • (w - u))‖ ≤ cfg.L * ‖v - w‖ := by
      intro v hv w hw
      exact regularized_lipschitz hβ hlip u hv hw
    have hpair : WithLp.toLp 2 (r.fst, r.snd) = r := WithLp.toLp_ofLp 2 r
    have hnr' : ConstrainedMonotone.Normal (domain (regularizedPublic p β))
        (WithLp.toLp 2 (r.fst, r.snd))
        (-ownGradient (p := regularizedPublic p β) (regularizedH H β u) G
          (WithLp.toLp 2 (r.fst, r.snd))) := by
      rw [hpair, regularized_own_gradient]
      exact hnr
    have hh := foam_convergence gr hC hP cfg u u hu hf.a_pos hf.b_pos hf.c_pos hf.b_le_a
      hf.alpha_pos hf.alpha_le_one hf.alpha_sq hf.small hf.large_curvature
      (show p.ν + β - p.δ - cfg.b = cfg.b - p.δ by have h := hf.small_curvature; linarith)
      hf.small_curvature hf.a_le_L hf.eta_pos hf.eta_L hf.inner_pos hf.inner_accuracy
      hD hδ hf.delta_le_L hfield hLip hdiam (by change WithLp.toLp 2 (r.fst, r.snd) ∈ domain p; rw [hpair]; exact hr) hnr'
    rw [hpair] at hh
    have herr := hh.2.trans (tuned_foam_accuracy hν hνμ hμL hδ hδL hε)
    have hnorm := tolerance_from_square (norm_nonneg (step u - r)) hν hβ hε herr
    refine ⟨hh.1, ?_⟩
    exact approximate_resolvent_distance hν hβ hr hs (hmono r hr s hs) hnr hns hnorm
  have hq : 0 ≤ β / (p.ν + β) := div_nonneg hβ hmr.le
  have hq₁ : β / (p.ν + β) < 1 := (div_lt_one hmr).mpr (by linarith)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hout := inexact_contraction_iterates hq hq₁ he hu0 (hdiam u0 hu0 s hs) hstep N
  have hdecay := outer_geometric_accuracy hν hβ hD hε
  have htol := outer_tolerance_sum (ε := p.ε) hν hβ
  have hnorm : ‖step^[N] u0 - s‖ ≤ Real.sqrt p.ε / 2 := by
    have hh := hout.2
    change _ ≤ _ + (p.ν * Real.sqrt p.ε / (4 * (p.ν + β))) / (1 - β / (p.ν + β)) at hh
    rw [htol] at hh
    change (β / (p.ν + β)) ^ N * p.D ≤ Real.sqrt p.ε / 4 at hdecay
    linarith
  dsimp only
  unfold proximalFoamPlan
  rw [eval_repeatQueries]
  refine ⟨hout.1, ?_⟩
  have hsqrt := Real.sq_sqrt hε.le
  have hn0 := norm_nonneg (step^[N] u0 - s)
  have hs0 := Real.sqrt_nonneg p.ε
  nlinarith


set_option maxHeartbeats 600000 in
lemma oriented_game_accuracy {p : Public} {I : Problem p} {H G P : Space p → Space p}
    (geom : GameGeometry p I H G) (hC : IsComplete (domain p))
    (hP : ConstrainedMonotone.Proj (domain p) P)
    (hμ : 0 < p.μ) (hν : 0 < p.ν) (hμL : p.μ ≤ p.L) (hνL : p.ν ≤ p.L)
    (hδ : 0 ≤ p.δ) (hδL : p.δ ≤ p.L) (hD : 0 ≤ p.D) (hε : 0 < p.ε)
    (hlip : ∀ u ∈ domain p, ∀ v ∈ domain p,
      ‖ownGradient H G u - ownGradient H G v‖ ≤ 2 * p.L * ‖u - v‖)
    (hdiam : ∀ u ∈ domain p, ∀ v ∈ domain p, ‖u - v‖ ≤ p.D)
    (u0 s : Space p) (hu0 : u0 ∈ domain p) (hs : s ∈ domain p)
    (hns : ConstrainedMonotone.Normal (domain p) s (-ownGradient H G s)) :
    let m := min p.μ p.ν
    let M := max p.μ p.ν
    let β := m + 16 * p.δ
    let cfg := tunedFoamConfig p.L M m p.δ p.D p.ε
    let N := ⌈2 * (m + β) / m * Real.log (2 + p.D ^ 2 / p.ε)⌉₊
    let out := QueryPlan.eval (Sum.elim (ownGradient H G) P)
      (orientedProximalFoamPlan cfg β N u0 (decide (p.μ < p.ν)))
    out ∈ domain p ∧ ‖out - s‖ ^ 2 ≤ p.ε := by
  by_cases h : p.μ < p.ν
  · have hg := swapped_geometry geom
    have hl : ∀ u ∈ domain (swappedPublic p), ∀ v ∈ domain (swappedPublic p),
        ‖ownGradient (p := swappedPublic p) (fun w => -swapPoint (H (swapPoint w)))
            (fun w => swapPoint (G (swapPoint w))) u -
          ownGradient (p := swappedPublic p) (fun w => -swapPoint (H (swapPoint w)))
            (fun w => swapPoint (G (swapPoint w))) v‖ ≤ 2 * p.L * ‖u - v‖ := by
      intro u hu v hv
      rw [swapped_own_gradient, swapped_own_gradient]
      exact swap_field_lipschitz hlip u hu v hv
    have hn := swap_normal hns
    have hn' : ConstrainedMonotone.Normal (domain (swappedPublic p)) (swapPoint s)
        (-ownGradient (p := swappedPublic p) (fun w => -swapPoint (H (swapPoint w)))
          (fun w => swapPoint (G (swapPoint w))) (swapPoint s)) := by
      rw [swapped_own_gradient, swap_swap]
      convert hn using 1
      exact ((LinearIsometryEquiv.withLpProdComm 2 ℝ p.E p.F).map_neg (ownGradient H G s)).symm
    have hh := ordered_proximal_accuracy hg (swap_complete hC) (swap_projection hP)
      hμ h.le hνL hδ hδL hD hε hl (swap_diameter hdiam) (swapPoint u0) (swapPoint s)
      ((swap_mem u0).mpr hu0) ((swap_mem s).mpr hs) hn'
    have hbfun : ownGradient (p := swappedPublic p) (fun w => -swapPoint (H (swapPoint w)))
        (fun w => swapPoint (G (swapPoint w))) = fun u => swapPoint (ownGradient H G (swapPoint u)) :=
      funext (swapped_own_gradient H G)
    rw [hbfun] at hh
    have hout := swap_accuracy hh
    dsimp only at hout ⊢
    rw [min_eq_left h.le, max_eq_right h.le]
    simp only [h, decide_true,
      orientedProximalFoamPlan, ↓reduceIte, eval_transportPlan, swapped_oracle_eval]
    simpa only [min_eq_left h.le, max_eq_right h.le, swapped_own_gradient] using hout
  · have hh := ordered_proximal_accuracy geom hC hP hν (le_of_not_gt h) hμL
      hδ hδL hD hε hlip hdiam u0 s hu0 hs hns
    dsimp only
    rw [min_eq_right (le_of_not_gt h), max_eq_left (le_of_not_gt h)]
    simp only [h, decide_false,
      orientedProximalFoamPlan, Bool.false_eq_true, ↓reduceIte]
    simpa only [min_eq_right (le_of_not_gt h), max_eq_left (le_of_not_gt h)] using hh

end OracleTemplate.NearZeroSum
