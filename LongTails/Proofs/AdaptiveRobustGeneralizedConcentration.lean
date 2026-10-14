import LongTails.Proofs.AdaptiveRobustGeneralizedProcess

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.AdaptiveRobustGeneralized

open StochasticGeneralized
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

open GeneralizedAccelerated (Iterate Pending tentativeWeight coupling)
open StochasticGeneralized (proofActive proofWeight prepare firstHalf secondHalf)

lemma batchNoise_exp_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f Set.univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (s : Iterate p.E) (hs : proofActive p f u s) :
    let m := estimatorCost p (tentativeWeight s)
    Integrable (fun w : (Fin m → p.Ω) × (Fin m → p.Ω) =>
      Real.exp ((confidence p/p.R^2)*batchNoise p f u oracle s w.1 w.2))
      ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) ∧
    (∫ w : (Fin m → p.Ω) × (Fin m → p.Ω),
      Real.exp ((confidence p/p.R^2)*batchNoise p f u oracle s w.1 w.2)
      ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))) ≤
      Real.exp ((confidence p*p.ε/(1048576*p.R^2))*tentativeWeight s) := by
  rcases hp with ⟨hL0, hL1, hR, hΔ, hσ, hε, hδ, hδ1⟩
  let a := tentativeWeight s
  let m := estimatorCost p a
  let B := radius p a
  let v := p.σ^2/(correctionSize p a : ℝ)
  have ha : 0 < a := GeneralizedAccelerated.tentativeWeight_pos s hs.2.1
  have hB : 0 < B := radius_pos p hR hδ hδ1 ha
  have hℓ : 1 ≤ confidence p := (StochasticGeneralized.confidence_log_gt_one hδ hδ1).le
  have ht : 0 ≤ confidence p/p.R^2 := by positivity
  let r : (Fin m → p.Ω) → Pending p.E := fun ξ =>
    prepare p.L0 p.L1 s (guardedReply p f a oracle (coupling s) ξ)
  let X : (Fin m → p.Ω) → p.E := fun ξ =>
    guardedReply p f a oracle (coupling s) ξ-gradient f (coupling s)
  let Y : (Fin m → p.Ω) × (Fin m → p.Ω) → p.E := fun w =>
    guardedReply p f a oracle (r w.1).point w.2-gradient f (r w.1).point
  let b : (Fin m → p.Ω) → ℝ := fun ξ => s.guess/(r ξ).curvature*a
  have hbatch := measurable_guardedReply p hgrad hg.measurable m
  have hr : Measurable r := by dsimp [r]; fun_prop
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hb : Measurable b := by dsimp [b]; fun_prop
  have hba (ξ : Fin m → p.Ω) : 0 ≤ b ξ ∧ b ξ ≤ a := by
    have hd := StochasticGeneralized.prepare_damping hL0 hL1 s
      (guardedReply p f a oracle (coupling s) ξ) hs.2.1
    exact ⟨mul_nonneg hd.1.le ha.le, mul_le_of_le_one_left ha.le hd.2⟩
  have hcontrol (x : p.E) := guardedReply_moments p μ hg a hB x
  have hbound (x : p.E) (ξ : Fin m → p.Ω) :=
    guardedReply_bound p f a oracle x ξ hB.le
  have hnorm : ‖s.z-u‖ ≤ 3*p.R := by
    have h := StochasticGeneralized.active_distance_bound p hmin s hs
    nlinarith [norm_nonneg (s.z-u)]
  have hsmall := energy_tuning_small hR ha hℓ hnorm
  have h := RobustGradient.two_stage_energy_mgf ha.le (by positivity : 0 ≤ 3*B/2) ht
    hX hY hb hba (hcontrol (coupling s)).1 (hcontrol (coupling s)).2.1
    (hbound (coupling s)) (hcontrol (coupling s)).2.2.1
    (fun ξ => (hcontrol (r ξ).point).1) (fun ξ => (hcontrol (r ξ).point).2.1)
    (fun ξ => hbound (r ξ).point) (fun ξ => (hcontrol (r ξ).point).2.2.2)
    (fun ξ => (hcontrol (r ξ).point).2.2.1) (s.z-u) hsmall
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hscale := correction_variance p hε ha (lt_of_lt_of_le zero_lt_one hℓ)
  have hexp := energy_tuning_exponent hR hε ha hℓ (norm_nonneg (s.z-u)) hnorm hv hscale
  have he (w : (Fin m → p.Ω) × (Fin m → p.Ω)) :
      (-b w.1*⟪s.z-u, Y w⟫+8*a^2*‖X w.1‖^2+6*a^2*‖Y w‖^2) =
      batchNoise p f u oracle s w.1 w.2 := by
    simp only [b, r, a, X, Y, batchNoise, real_inner_comm, norm_sub_rev]
  simp_rw [he] at h
  refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
  exact hexp.trans_eq (by ring)

lemma proofIncrement_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f Set.univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (s : Iterate p.E) :
    Integrable (fun ξ => Real.exp (proofIncrement p f u oracle (proofCost p f u s) s ξ))
      (Measure.pi fun _ : Fin (proofCost p f u s) => μ) ∧
      (∫ ξ, Real.exp (proofIncrement p f u oracle (proofCost p f u s) s ξ)
        ∂Measure.pi (fun _ : Fin (proofCost p f u s) => μ)) ≤ 1 := by
  classical
  by_cases hs : proofActive p f u s
  · let n := proofCost p f u s
    let m := n/2
    let t := confidence p/p.R^2
    let C := (confidence p*p.ε/(1048576*p.R^2))*tentativeWeight s
    have hmEq : m = estimatorCost p (tentativeWeight s) := by
      dsimp [m, n, proofCost]
      rw [ite_eq_left hs]
      omega
    have hbase := batchNoise_exp_control p hp hgrad u hmin hg s hs
    have h : Integrable (fun w : (Fin m → p.Ω) × (Fin m → p.Ω) =>
        Real.exp (t*batchNoise p f u oracle s w.1 w.2))
        ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) ∧
        (∫ w : (Fin m → p.Ω) × (Fin m → p.Ω), Real.exp (t*batchNoise p f u oracle s w.1 w.2)
          ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))) ≤ Real.exp C := by
      rw [hmEq]
      exact hbase
    let F : (Fin m → p.Ω) × (Fin m → p.Ω) → ℝ :=
      fun w => Real.exp (t*batchNoise p f u oracle s w.1 w.2-C)
    have heF : F = fun w => Real.exp (-C)*Real.exp (t*batchNoise p f u oracle s w.1 w.2) := by
      ext w
      dsimp [F]
      rw [← Real.exp_add]
      congr 1
      ring
    have hiF : Integrable F ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) := by
      rw [heF]
      exact h.1.const_mul _
    have hbF : (∫ w, F w ∂((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))) ≤ 1 := by
      rw [heF, integral_const_mul]
      have hh := mul_le_mul_of_nonneg_left h.2 (Real.exp_nonneg (-C))
      simpa only [C, t, ← Real.exp_add, neg_add_cancel, Real.exp_zero] using hh
    have hsplit := StochasticGeneralized.halves_preserving p μ n
    have hl : HasLaw (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ))
        ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
        (Measure.pi fun _ : Fin n => μ) := ⟨hsplit.measurable.aemeasurable, hsplit.map_eq⟩
    have he : (fun ξ : Fin n → p.Ω => Real.exp (proofIncrement p f u oracle n s ξ)) =
        F ∘ (fun ξ : Fin n → p.Ω => (firstHalf ξ, secondHalf ξ)) := by
      ext ξ
      simp only [proofIncrement, proofNoise, proofWeight, ite_eq_left hs]
      rfl
    change Integrable (fun ξ : Fin n → p.Ω => Real.exp (proofIncrement p f u oracle n s ξ)) _ ∧ _
    rw [he]
    refine ⟨hl.integrable_comp hiF, ?_⟩
    rw [hl.integral_comp hiF.aestronglyMeasurable]
    exact hbF
  · simp only [proofIncrement, proofNoise, proofWeight, ite_eq_right hs, mul_zero, sub_zero, Real.exp_zero]
    exact ⟨integrable_const 1, by simp⟩

lemma proof_accumulated_control (p : Params) (hp : spec.valid p)
    {f : p.E → ℝ} (hf : Measurable f) (hgrad : Measurable (gradient f))
    (u : p.E) (hmin : IsMinOn f Set.univ u) {μ : Measure p.Ω} [IsProbabilityMeasure μ]
    {oracle : p.E → p.Ω → p.E} (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (k : ℕ) (s : Iterate p.E) :
    Integrable (fun ξ => Real.exp (accumulated (proofCost p f u) (proofNext p f u oracle)
      (proofIncrement p f u oracle) k s ξ)) (Measure.infinitePi fun _ : ℕ => μ) ∧
      (∫ ξ, Real.exp (accumulated (proofCost p f u) (proofNext p f u oracle)
        (proofIncrement p f u oracle) k s ξ) ∂Measure.infinitePi (fun _ : ℕ => μ)) ≤ 1 := by
  exact accumulated_exp_control μ (measurable_proofCost p hf u)
    (measurable_proofNext p hf hgrad u hg.measurable) (measurable_proofIncrement p hf hgrad u hg.measurable)
    (fun s => (proofIncrement_control p hp hgrad u hmin hg s).1)
    (fun s => (proofIncrement_control p hp hgrad u hmin hg s).2) k s


end OracleTemplate.AdaptiveRobustGeneralized
