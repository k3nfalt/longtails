import LongTails.Algorithms.StochasticGeneralizedAccelerated
import LongTails.Proofs.StochasticGeneralizedEnergy
import LongTails.Proofs.StochasticGeneralizedWeights

open Set InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling energy)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma prepare_curvature_pos {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (v : E) : 0 < (prepare L0 L1 s v).curvature := by
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

omit [CompleteSpace E] in
lemma prepare_damping {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (s : Iterate E) (v : E) (hG : 0 < s.guess) :
    0 < s.guess/(prepare L0 L1 s v).curvature ∧
      s.guess/(prepare L0 L1 s v).curvature ≤ 1 := by
  have hM := prepare_curvature_pos hL0 hL1 s v
  exact ⟨div_pos hG hM, (div_le_one hM).mpr (le_max_left _ _)⟩

omit [CompleteSpace E] in
lemma step_weights {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : E → E) (s : Iterate E) (hG : 0 < s.guess) :
    s.A < (step L0 L1 v h s).A ∧
      (step L0 L1 v h s).A ≤ s.A+tentativeWeight s ∧
      0 < (step L0 L1 v h s).guess := by
  have ha := GeneralizedAccelerated.tentativeWeight_pos s hG
  have hd := prepare_damping hL0 hL1 s (v (coupling s)) hG
  dsimp [step, finish, prepare]
  refine ⟨lt_add_of_pos_right _ (mul_pos hd.1 ha), ?_, ?_⟩
  · exact add_le_add le_rfl (mul_le_of_le_one_left ha.le hd.2)
  · split_ifs <;> positivity

noncomputable def dissipation (L0 L1 : ℝ) (v : E → E) (s : Iterate E) : ℝ :=
  let p := prepare L0 L1 s (v (coupling s))
  (s.guess/p.curvature)*(s.A+tentativeWeight s)*(3*p.curvature/8)*‖p.point-p.y‖^2

noncomputable def noiseIncrement (L0 L1 : ℝ) (g v h : E → E) (u : E) (s : Iterate E) : ℝ :=
  let p := prepare L0 L1 s (v (coupling s))
  let b := (s.guess/p.curvature)*tentativeWeight s
  let e₁ := g p.y-v p.y
  let e₂ := h p.point-g p.point
  (-b)*⟪e₂, s.z-u⟫+b^2*(8*‖e₁‖^2+6*‖e₂‖^2)

lemma step_energy {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (hdiff : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0+L1*‖g x‖)
    (v h : E → E) (u : E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    energy f u (step L0 L1 v h s)+dissipation L0 L1 v s ≤
      energy f u s+noiseIncrement L0 L1 g v h u s := by
  let p := prepare L0 L1 s (v (coupling s))
  have hM := prepare_curvature_pos hL0 hL1 s (v (coupling s))
  have ha := GeneralizedAccelerated.tentativeWeight_pos s hG
  have he := GeneralizedAccelerated.tentativeWeight_equation s hA hG
  have hd := prepare_damping hL0 hL1 s (v (coupling s)) hG
  have hweight : (s.guess/p.curvature)*(tentativeWeight s)^2*p.curvature = s.A+tentativeWeight s := by
    rw [← he]
    field_simp [show p.curvature ≠ 0 from hM.ne']
  have hr := local_step_residual hL0 hL1 hdiff hH (coupling s) (v (coupling s))
    (show 16*(L0+L1*‖v (coupling s)‖) ≤ p.curvature from le_max_right _ _)
  have hh := damped_step_error hM hc hg s.x s.z u p.point
    (g (coupling s)-v (coupling s)) (h p.point-g p.point) hA ha hd.1 hd.2 hweight hr
  have hv : g p.point+(h p.point-g p.point) = h p.point := by module
  rw [hv] at hh
  simpa only [step, energy, finish, dissipation, noiseIncrement, p, prepare,
    coupling, sub_eq_add_neg, neg_mul, add_assoc] using hh

omit [CompleteSpace E] in
lemma run_valid {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (n : ℕ) :
    0 ≤ (run L0 L1 v h s n).A ∧ 0 < (run L0 L1 v h s n).guess := by
  induction n with
  | zero => exact ⟨hA, hG⟩
  | succ n ih =>
    have hs := step_weights hL0 hL1 (v n) (h n) (run L0 L1 v h s n) ih.2
    exact ⟨ih.1.trans hs.1.le, hs.2.2⟩

lemma run_energy {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (hdiff : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0+L1*‖g x‖)
    (v h : ℕ → E → E) (u : E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) (n : ℕ) :
    energy f u (run L0 L1 v h s n)+
      (∑ i ∈ Finset.range n, dissipation L0 L1 (v i) (run L0 L1 v h s i)) ≤
      energy f u s+(∑ i ∈ Finset.range n, noiseIncrement L0 L1 g (v i) (h i) u (run L0 L1 v h s i)) := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    have hv := run_valid hL0 hL1 v h s hA hG n
    have hs := step_energy hL0 hL1 hc hg hdiff hH (v n) (h n) u (run L0 L1 v h s n) hv.1 hv.2
    change energy f u (run L0 L1 v h s (n+1))+
      dissipation L0 L1 (v n) (run L0 L1 v h s n) ≤
      energy f u (run L0 L1 v h s n)+noiseIncrement L0 L1 g (v n) (h n) u (run L0 L1 v h s n) at hs
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

omit [CompleteSpace E] in
lemma run_weight_mono {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : ℕ → E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    Monotone (fun n => (run L0 L1 v h s n).A) := by
  apply monotone_nat_of_le_succ
  intro n
  have hv := run_valid hL0 hL1 v h s hA hG n
  exact (step_weights hL0 hL1 (v n) (h n) (run L0 L1 v h s n) hv.2).1.le

omit [CompleteSpace E] in
lemma dissipation_nonneg {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v : E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    0 ≤ dissipation L0 L1 v s := by
  have hM := prepare_curvature_pos hL0 hL1 s (v (coupling s))
  have ha := GeneralizedAccelerated.tentativeWeight_pos s hG
  dsimp only [dissipation]
  positivity

omit [CompleteSpace E] in
lemma step_nominal_recurrence {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (v h : E → E) (s : Iterate E) (hA : 0 ≤ s.A) (hG : 0 < s.guess) :
    tentativeWeight (step L0 L1 v h s) ≤ 5/16*tentativeWeight s+
      20*((step L0 L1 v h s).A-s.A) := by
  let p := prepare L0 L1 s (v (coupling s))
  have hM := prepare_curvature_pos hL0 hL1 s (v (coupling s))
  have ha := GeneralizedAccelerated.tentativeWeight_pos s hG
  have he := GeneralizedAccelerated.tentativeWeight_equation s hA hG
  have hs := step_weights hL0 hL1 v h s hG
  have he' := GeneralizedAccelerated.tentativeWeight_equation (step L0 L1 v h s)
    (hA.trans hs.1.le) hs.2.2
  by_cases hd : p.curvature ≤ s.guess
  · have hcurv : p.curvature = s.guess := le_antisymm hd (le_max_left _ _)
    have heA : (step L0 L1 v h s).A = s.A+tentativeWeight s := by
      change s.A+(s.guess/p.curvature)*tentativeWeight s = _
      rw [hcurv, div_self hG.ne', one_mul]
    have heG : (step L0 L1 v h s).guess = s.guess/16 := by
      change (if p.curvature ≤ s.guess then s.guess/16 else 16*s.guess) = _
      rw [ite_eq_left hd]
    rw [heA, heG] at he'
    have hw := weight_after_down hG hA ha he he'
    rw [heA]
    linarith
  · have heG : (step L0 L1 v h s).guess = 16*s.guess := by
      change (if p.curvature ≤ s.guess then s.guess/16 else 16*s.guess) = _
      rw [ite_eq_right hd]
    rw [heG] at he'
    have hw := weight_after_up hG hA ha he
      (show (step L0 L1 v h s).A-s.A ≤ tentativeWeight s by linarith [hs.2.1])
      (show (16*s.guess)*tentativeWeight (step L0 L1 v h s)^2 =
        s.A+((step L0 L1 v h s).A-s.A)+tentativeWeight (step L0 L1 v h s) by linarith [he'])
    linarith [hs.1]

end OracleTemplate.StochasticGeneralized
