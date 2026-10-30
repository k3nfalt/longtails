import LongTails.Proofs.NonsmoothHiddenParameters
import LongTails.Proofs.NonsmoothHiddenRun
import LongTails.Proofs.NonsmoothHiddenEpoch
import LongTails.Proofs.NonsmoothHiddenExecution

open Set Metric MeasureTheory

namespace OracleTemplate.NonsmoothHidden

open LongTails.Setups.NonsmoothHiddenConvex

lemma execution_success (p : Params) (hp : spec.valid p) (I : Instance p) (O : Oracle p.E p.E)
    (had : spec.admissible p I O) (B : ℕ) (hB : outerIterations p * localIterations p ≤ B) :
    spec.successful p I
      (fun seed : (tunedAlgorithm p).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (tunedAlgorithm p) (fun _ => B) seed.1 seed.2)
      ⟨((tunedAlgorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have hgeo := parameter_geometry p hp
  have hcount := parameter_counts p hp
  have houter := parameter_outer_accuracy p hp
  rcases hp with ⟨hμ, hLc, hLJ, hG, hR, hε⟩
  dsimp only [spec, id_eq] at had
  rcases had with ⟨oracle, ν, P, rfl, hIID, hom, hoi, hoi2, homean, hoG,
    heq, hH, hd, hlower, hupper, hlip, hg, hbarrier, hmin⟩
  obtain ⟨xstar, hxs, hstar⟩ := minimizer_inside_barrier hR heq hH hbarrier hmin
  have hF := (hidden_continuous heq hH).measurable
  have hJ : ∀ x v, p.μ * ‖v‖ ≤ ‖I.J x v‖ := derivative_lower_bound hLJ hd hlip hlower
  have hTaylor : ∀ x y, ‖I.c y - I.c x - I.J x (y - x)‖ ≤ p.LJ * ‖y - x‖ ^ 2 := by
    intro x y
    exact LocalHiddenConvex.taylor_bound hLJ convex_univ (fun x _ => hd x)
      (fun x _ y _ => hlip x y) (mem_univ _) (mem_univ _)
  have hpG : ∀ x, ‖I.g x‖ ≤ p.G := fun x => mean_norm_le hG.le (hoi x) (hoi2 x) (homean x) (hoG x)
  let r := radius p
  let D := dualScale p
  let t := epochFraction p
  let N := localIterations p
  let K := outerIterations p
  let Q := Measure.infinitePi (fun _ : ℕ => (ν : Measure p.Ω))
  have hr : 0 < r := hgeo.2.2.1
  have hD : 0 < D := hcount.2.1
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨hgeo.2.2.2.2.2.1.le, hgeo.2.2.2.2.2.2.1⟩
  have hreg : 64 * p.LJ * r ≤ p.μ := hgeo.2.2.2.2.1
  let C := p.G * (2 * p.R + (p.LJ / p.μ) * (2 * p.R) ^ 2) + p.ε / 2
  have hbound : ∀ x, ‖x‖ ≤ p.R → |I.F x - I.F xstar - p.ε / 2| ≤ C := by
    intro x hx
    have hn : ‖xstar - x‖ ≤ 2 * p.R := by linarith [norm_sub_le xstar x]
    have hu := objective_gap_bound hμ hLJ hG.le hJ hTaylor heq (hg x) (hpG x) hn
    have hl : 0 ≤ I.F x - I.F xstar := sub_nonneg.mpr (hstar (mem_univ x))
    have ha := abs_sub (I.F x - I.F xstar) (p.ε / 2)
    rw [abs_of_nonneg hl, abs_of_nonneg (by positivity : 0 ≤ p.ε / 2)] at ha
    dsimp [C]
    linarith
  have hinit : I.F 0 - I.F xstar ≤ initialBound p := by
    have hn : ‖xstar - (0 : p.E)‖ ≤ p.R := by simpa using hxs
    have hh := objective_gap_bound hμ hLJ hG.le hJ hTaylor heq (hg 0) (hpG 0) hn
    convert hh using 1
    unfold initialBound
    ring
  have hstep : ∀ b, ‖b‖ ≤ p.R →
      (∫ ξ, I.F (restartOutside p.R (localOutput oracle r D N b ξ)) - I.F xstar - p.ε / 2
        ∂Measure.pi (fun _ : Fin N => (ν : Measure p.Ω))) ≤
        (1 - t) * (I.F b - I.F xstar - p.ε / 2) := by
    intro b hb
    let u := hiddenSegment I.c b xstar t
    have hu : u ∈ closedBall b r := by
      rw [mem_closedBall, dist_eq_norm]
      have hh := hiddenSegment_distance hμ (lt_of_lt_of_le hμ hLc).le ht.1 hlower hupper hb hxs
      exact hh.trans_eq hgeo.2.2.2.2.2.2.2
    have hi := localOutput_integrable (D := D) hμ hLJ hr.le hG.le hreg hJ hTaylor heq hF hg
      hom hoi hoi2 homean hoG N hu
    have hh := expected_gap_bound hμ hLJ hr.le hD hG.le hreg hJ hTaylor hlip heq hF hg
      hom hoi hoi2 homean hoG N hcount.1 hr hG rfl hu
    have hacc : (∫ ξ, I.F (localOutput oracle r D N b ξ) - I.F u
        ∂Measure.pi (fun _ : Fin N => (ν : Measure p.Ω))) ≤ t * (p.ε / 2) := by
      have hhh := hh.trans hcount.2.2
      convert hhh using 1
      ring
    exact restart_local_contraction hom r D hR.le N hF heq hH hbarrier hstar hxs ht hbound ν hi hacc
  have hm := (epochRun_measurable hom r D p.R N K).comp
    (measurable_const.prodMk measurable_id : Measurable (fun ξ : ℕ → p.Ω => ((0 : p.E), ξ)))
  have hiShift := epochRun_integrable hom r D hR.le N K hF hbound
    (by simpa using hR.le : ‖(0 : p.E)‖ ≤ p.R) (ν : Measure p.Ω)
  have hi : Integrable (fun ξ => I.F (epochRun oracle r D p.R N K 0 ξ) - I.F xstar) Q := by
    convert hiShift.add (integrable_const (p.ε / 2)) using 1
    ext ξ
    simp
  have hq : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hrec := epochRun_contraction hom r D hR.le N K hF hq hbound (ν : Measure p.Ω)
    hstep (by simpa using hR.le : ‖(0 : p.E)‖ ≤ p.R)
  have hrecBound : (1 - t) ^ K * (I.F 0 - I.F xstar - p.ε / 2) ≤ p.ε / 2 := by
    exact (mul_le_mul_of_nonneg_left (by linarith : I.F 0 - I.F xstar - p.ε / 2 ≤ initialBound p)
      (pow_nonneg hq K)).trans houter
  have hacc : (∫ ξ, I.F (epochRun oracle r D p.R N K 0 ξ) - I.F xstar ∂Q) ≤ p.ε := by
    have hh := hrec.trans hrecBound
    change (∫ ξ, (I.F (epochRun oracle r D p.R N K 0 ξ) - I.F xstar) - p.ε / 2 ∂Q) ≤ _ at hh
    rw [integral_sub hi (integrable_const _)] at hh
    simp only [integral_const, probReal_univ, one_smul] at hh
    linarith
  have hP : (P : Measure (ℕ → p.Ω)) = Q := by
    have hh := hIID.stream_law.map_eq
    simpa only [show (fun ξ : ℕ → p.Ω => fun k => ξ k) = id from rfl, Measure.map_id] using hh
  let output := fun ξ : ℕ → p.Ω => epochRun oracle r D p.R N K 0 ξ
  let result := fun seed : Unit × (ℕ → p.Ω) => execute
    { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => oracle x ω }
    (tunedAlgorithm p) (fun _ => B) seed.1 seed.2
  change Measurable result ∧ ∃ xstar, IsMinOn I.F univ xstar ∧
    Integrable (fun seed => I.F (result seed) - I.F xstar) ((Measure.dirac ()).prod (P : Measure _)) ∧
    (∫ seed, I.F (result seed) - I.F xstar ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.ε
  have hexec : result = fun seed => output seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact execute_epochRun P oracle r D p.R N K B (by omega) hB ξ
  rw [hexec, hP]
  refine ⟨hm.comp measurable_snd, xstar, hstar, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := Q)).integrable_comp_of_integrable hi
  · rw [integral_fun_snd (fun ξ => I.F (output ξ) - I.F xstar)]
    simpa using hacc

end OracleTemplate.NonsmoothHidden
