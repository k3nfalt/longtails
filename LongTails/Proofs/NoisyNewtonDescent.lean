import LongTails.Proofs.NoisyNewtonConcentration

namespace LongTails.Proofs.NoisyNewtonDescent

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Proofs.NoisyNewtonProcess
open LongTails.Proofs.NoisyNewtonConcentration
open LongTails.Proofs.NoisyNewtonTuning
open OracleTemplate.GeneralizedAccelerated (tentativeWeight coupling)

noncomputable def ghostDissipation (p : Params) (s : Ghost p) : ℝ := by
  classical
  exact if stopped p s then 0 else match s.1 with
  | .correction t _ _ => actualWeight t ^ 2 * (t.curvature * ‖t.displacement‖) ^ 2
  | _ => 0

lemma ghostDissipation_nonneg (p : Params) (s : Ghost p) : 0 ≤ ghostDissipation p s := by
  rcases s with ⟨state, error, flags⟩
  cases state <;> simp only [ghostDissipation]
  all_goals split_ifs <;> positivity

lemma model_charge_bound (p : Params) (hp : spec.valid p) (a proposal error : ℝ)
    (ha : 0 ≤ a) (hproposal : 0 < proposal) (hap : a ≤ proposal) (he : 0 ≤ error)
    (hmodel : error ≤ modelRadius p proposal / 2) :
    4 * a ^ 2 * error ^ 2 ≤ (4 * p.ε / (1073741824 * confidence p ^ 2)) * a := by
  have he2 := pow_le_pow_left₀ he hmodel 2
  rw [modelRadius_half_square p hp proposal hproposal] at he2
  have hscale := mul_le_mul_of_nonneg_left he2 hproposal.le
  have hb : proposal * error ^ 2 ≤ p.ε / (1073741824 * confidence p ^ 2) := by
    exact hscale.trans_eq (by field_simp)
  calc
    4 * a ^ 2 * error ^ 2 = (4 * a) * (a * error ^ 2) := by ring
    _ ≤ (4 * a) * (proposal * error ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hap (sq_nonneg error)) (by positivity)
    _ ≤ (4 * a) * (p.ε / (1073741824 * confidence p ^ 2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (4 * p.ε / (1073741824 * confidence p ^ 2)) * a := by ring

lemma ghostNext_descent (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (A H : Point p.d → Point p.d →L[ℝ] Point p.d) (u : Point p.d)
    (hc : ConvexOn ℝ Set.univ f) (hgrad : ∀ x, HasGradientAt f (grad x) x)
    (hderiv : ∀ x, HasFDerivAt grad (A x) x)
    (hA : ∀ x v, 0 ≤ ⟪A x v, v⟫) (hmin : ∀ x, f u ≤ f x)
    (hLip : ∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖A y - A x‖ ≤ (p.M₀ + p.M₁ * ‖grad x‖) * ‖y - x‖)
    (hH : ∀ x, ‖H x - A x‖ ≤ p.δ)
    (g : Point p.d → p.Ω → Point p.d) (n : ℕ) (s : Ghost p) (ξ : Fin n → p.Ω)
    (hb : StateBounds p s.1)
    (hm : ¬ stopped p s → ModelConsistent p grad H s)
    (he : ¬ stopped p s → stateEnergy p f u s.1 ≤ 8 * p.R ^ 2) :
    stateEnergy p f u (ghostNext p f u grad g H n s ξ).1 + 3 / 8 * ghostDissipation p s ≤
      stateEnergy p f u s.1 + (4 * p.ε / (1073741824 * confidence p ^ 2)) * ghostWeight p s +
        ghostNoise p grad u g n s ξ := by
  by_cases hs : stopped p s
  · simp [ghostNext_of_stopped p f u grad g H n s ξ hs, ghostDissipation, ghostWeight, ghostNoise, hs]
  · have hmc := hm hs
    have henergy := he hs
    rw [ghostNext_state p f u grad g H n s ξ hs]
    rcases s with ⟨state, error, flags⟩
    cases state with
    | model it k v =>
      simp [phaseNext, stateEnergy, baseIterate, ghostDissipation, ghostWeight, phaseWeight, ghostNoise, hs]
    | hessian it v =>
      simp [phaseNext, stateEnergy, baseIterate, prepare, ghostDissipation, ghostWeight, phaseWeight, ghostNoise, hs]
    | done it =>
      simp [phaseNext, stateEnergy, baseIterate, ghostDissipation, ghostWeight, phaseWeight, ghostNoise, hs]
    | correction t k v =>
      have hr := correctionReady_of_invariants p hp f grad A H u hc hgrad hderiv hA hmin hLip hH
        (.correction t k v, error, flags) t k v rfl hb hmc henergy
      obtain ⟨model, ht, herr, hmodel⟩ := hmc
      change error = ‖model - grad (coupling t.previous)‖ at herr
      have hfloor : 0 < curvatureFloor p := by
        unfold curvatureFloor
        exact div_pos (by norm_num) (target_pos p hp)
      have hη := hfloor.trans_le hb.1.2.2
      have hα := tolerance_bounds p hp
      have hres := LongTails.Proofs.NoisyNewtonModel.prepare_residual hderiv hA
        p.M₀ p.M₁ p.ρ p.δ (tolerance p) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1
        hα.1 (by linarith [hα.2]) hLip t.previous hη (H (coupling t.previous))
        (hH (coupling t.previous)) (model - grad (coupling t.previous))
      simp only [add_sub_cancel] at hres
      rw [← ht, ← herr] at hres
      have ha := actualWeight_bounds t hη hb.2.2
      have hcharge := model_charge_bound p hp (actualWeight t) (tentativeWeight t.previous) error
        ha.1.le (OracleTemplate.GeneralizedAccelerated.tentativeWeight_pos _ hη) ha.2
        (herr.symm ▸ norm_nonneg _) hmodel
      have hd := LongTails.Proofs.NoisyMsEnergy.finish_dissipation hc hgrad t hb.1.1.le hη hb.2.2
        (curvatureFloor p) u
        (updateEstimate p t (sampleReplies p n g (trialPoint t) ξ) - grad (trialPoint t))
        (tolerance p) error hα.2 (by simpa only [mul_assoc] using hres)
      dsimp only [phaseNext]
      unfold stateEnergy
      rw [baseIterate_resume]
      simp only [ghostDissipation, ghostWeight, phaseWeight,
        ghostNoise, ite_eq_right hs, ite_eq_left hr, baseIterate, correctionNoise]
      simp only [add_sub_cancel, real_inner_comm] at hd
      nlinarith only [hd, hcharge]

open OracleTemplate.StochasticGeneralized (blockTrace blockTrace_succ blockAdvance accumulated
  accumulated_eq_sum)

lemma ghostTrace_descent (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (A H : Point p.d → Point p.d →L[ℝ] Point p.d) (u : Point p.d)
    (hc : ConvexOn ℝ Set.univ f) (hgrad : ∀ x, HasGradientAt f (grad x) x)
    (hderiv : ∀ x, HasFDerivAt grad (A x) x)
    (hA : ∀ x v, 0 ≤ ⟪A x v, v⟫) (hmin : ∀ x, f u ≤ f x)
    (hLip : ∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖A y - A x‖ ≤ (p.M₀ + p.M₁ * ‖grad x‖) * ‖y - x‖)
    (hH : ∀ x, ‖H x - A x‖ ≤ p.δ)
    (g : Point p.d → p.Ω → Point p.d) (s : Ghost p) (ξ : ℕ → p.Ω)
    (hb : StateBounds p s.1) (hm : ModelConsistent p grad H s)
    (he : stateEnergy p f u s.1 ≤ 8 * p.R ^ 2) (n : ℕ) :
    let T := blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ
    stateEnergy p f u (T n).1.1 + 3 / 8 * ∑ i ∈ Finset.range n, ghostDissipation p (T i).1 ≤
      stateEnergy p f u s.1 + (4 * p.ε / (1073741824 * confidence p ^ 2)) *
        (∑ i ∈ Finset.range n, ghostWeight p (T i).1) +
      accumulated (ghostCost p) (ghostNext p f u grad g H) (ghostNoise p grad u g) n s ξ := by
  dsimp only
  induction n with
  | zero => simp [OracleTemplate.StochasticGeneralized.blockTrace_zero, accumulated]
  | succ n ih =>
    have hb' := ghostTrace_bounds p hp f u grad g H s ξ n hb
    have hm' := fun hlive => ghostTrace_modelConsistent p f u grad g H s ξ n hm hlive
    have he' := fun hlive => ghostTrace_live_energy p f u grad g H s ξ n he hlive
    have hd := ghostNext_descent p hp f grad A H u hc hgrad hderiv hA hmin hLip hH g
      (ghostCost p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1)
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).1
      (fun j => (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ n).2 j) hb' hm' he'
    rw [accumulated_eq_sum] at ih ⊢
    simp only [Finset.sum_range_succ]
    rw [blockTrace_succ]
    dsimp only [blockAdvance]
    nlinarith only [ih, hd]

lemma model_charge_sum_bound (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (s : Ghost p) (ξ : ℕ → p.Ω) (n : ℕ) (hs : StateBounds p s.1) :
    (4 * p.ε / (1073741824 * confidence p ^ 2)) *
      (∑ i ∈ Finset.range n, ghostWeight p (blockTrace (ghostCost p) (ghostNext p f u grad g H) s ξ i).1) ≤
      p.R ^ 2 := by
  have hR := hp.2.2.2.2.2.1
  have hε := hp.2.2.2.2.2.2.2.1
  have hl := confidence_lower p hp
  have hlp : 0 < confidence p := by linarith
  have hh := mul_le_mul_of_nonneg_left (ghostWeight_sum_bound p hp f u grad g H s ξ n hs)
    (by positivity : 0 ≤ 4 * p.ε / (1073741824 * confidence p ^ 2))
  apply hh.trans
  have he : (4 * p.ε / (1073741824 * confidence p ^ 2)) * (3 * target p / 2) =
      192 * p.R ^ 2 / (1073741824 * confidence p ^ 2) := by
    unfold target
    field_simp
    ring
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 1073741824 * confidence p ^ 2)).mpr
  have hd : 192 ≤ 1073741824 * confidence p ^ 2 := by nlinarith only [hl, sq_nonneg (confidence p - 100)]
  nlinarith only [mul_le_mul_of_nonneg_right hd (sq_nonneg p.R)]

lemma stateEnergy_nonneg (p : Params) (f : Point p.d → ℝ) (u : Point p.d)
    (hmin : ∀ x, f u ≤ f x) (s : State (Point p.d)) (hs : StateBounds p s) :
    0 ≤ stateEnergy p f u s :=
  add_nonneg (mul_nonneg hs.1.1.le (sub_nonneg.mpr (hmin _)))
    (div_nonneg (sq_nonneg _) (by norm_num))

lemma initialTrace_energy_bound (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d)
    (A H : Point p.d → Point p.d →L[ℝ] Point p.d) (u : Point p.d)
    (hc : ConvexOn ℝ Set.univ f) (hgrad : ∀ x, HasGradientAt f (grad x) x)
    (hderiv : ∀ x, HasFDerivAt grad (A x) x)
    (hA : ∀ x v, 0 ≤ ⟪A x v, v⟫) (hmin : ∀ x, f u ≤ f x)
    (hLip : ∀ x y, ‖y - x‖ ≤ p.ρ →
      ‖A y - A x‖ ≤ (p.M₀ + p.M₁ * ‖grad x‖) * ‖y - x‖)
    (hH : ∀ x, ‖H x - A x‖ ≤ p.δ)
    (hdist : ‖p.x0 - u‖ ≤ p.R) (hgap : f p.x0 - f u ≤ p.Δ)
    (g : Point p.d → p.Ω → Point p.d) (ξ : ℕ → p.Ω) (n : ℕ)
    (hnoise : accumulated (ghostCost p) (ghostNext p f u grad g H)
      (ghostNoise p grad u g) n (initialGhost p) ξ ≤ 2 * p.R ^ 2) :
    let T := blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ
    stateEnergy p f u (T n).1.1 + 3 / 8 * ∑ i ∈ Finset.range n, ghostDissipation p (T i).1 ≤
      4 * p.R ^ 2 := by
  have hi := initial_energy p hp f u hdist hgap
  have hb := initial_bounds p hp
  have hd := ghostTrace_descent p hp f grad A H u hc hgrad hderiv hA hmin hLip hH g
    (initialGhost p) ξ hb (initial_modelConsistent p grad H)
    (by nlinarith only [hi, sq_nonneg p.R]) n
  have hm := model_charge_sum_bound p hp f grad u g H (initialGhost p) ξ n hb
  dsimp only at hd ⊢
  linarith

lemma energy_bound_consequences (p : Params) (hp : spec.valid p)
    (f : Point p.d → ℝ) (grad : Point p.d → Point p.d) (u : Point p.d)
    (g : Point p.d → p.Ω → Point p.d) (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hmin : ∀ x, f u ≤ f x) (ξ : ℕ → p.Ω) (n : ℕ)
    (he : stateEnergy p f u (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ n).1.1 +
      3 / 8 * ∑ i ∈ Finset.range n, ghostDissipation p
        (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ i).1 ≤ 4 * p.R ^ 2) :
    (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ n).1.2.2.2 = false ∧
    (∑ i ∈ Finset.range n, ghostDissipation p
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ i).1) ≤ 24 * p.R ^ 2 ∧
    stateEnergy p f u (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ n).1.1 ≤
      4 * p.R ^ 2 := by
  have hb := ghostTrace_bounds p hp f u grad g H (initialGhost p) ξ n (initial_bounds p hp)
  have hE := stateEnergy_nonneg p f u hmin _ hb
  have hD : 0 ≤ ∑ i ∈ Finset.range n, ghostDissipation p
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ i).1 :=
    Finset.sum_nonneg (fun _ _ => ghostDissipation_nonneg p _)
  have hcap : stateEnergy p f u
      (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ n).1.1 ≤ 4 * p.R ^ 2 := by
    linarith
  refine ⟨?_, ?_, hcap⟩
  · by_contra hflag
    have ht : (blockTrace (ghostCost p) (ghostNext p f u grad g H) (initialGhost p) ξ n).1.2.2.2 = true := by
      simpa using hflag
    have hc := ghostTrace_energyFailure p f u grad g H (initialGhost p) ξ n
      (by intro h; simp [initialGhost] at h) ht
    have hR := hp.2.2.2.2.2.1
    nlinarith only [hc, hcap, sq_pos_of_pos hR]
  · nlinarith only [he, hE, sq_nonneg p.R]

end LongTails.Proofs.NoisyNewtonDescent
