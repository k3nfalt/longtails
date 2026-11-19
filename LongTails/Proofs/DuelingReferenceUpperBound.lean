import LongTails.Proofs.DuelingReferenceConvergence
import LongTails.Proofs.DuelingReferenceTuning

open MeasureTheory OracleTemplate
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceDrift
open LongTails.Proofs.DuelingReferenceField
open LongTails.Proofs.DuelingReferencePotential
open LongTails.Proofs.DuelingReferenceConvergence
open LongTails.Proofs.HeavyTailedProductProcess

namespace LongTails.Proofs.DuelingReferenceUpperBound

lemma run_accuracy {Ω : Type} [MeasurableSpace Ω] {p : Params}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (hp : spec.valid p)
    {f : Point p.d → ℝ} {ρ : ℝ → ℝ} (hf : Objective p f) (hr : Transfer p ρ)
    {g : (Ball p.d × Ball p.d) → Ω → Bool} (hg : Measurable (Function.uncurry g))
    (hmean : ∀ x, (∫ z, score (g x z) ∂ν) = ρ (f x.1.val - f x.2.val))
    (u : Ball p.d) (hu : IsMinOn f (Ball p.d) u.val) (K : ℕ)
    (hn : 8*((p.d:ℝ)/radius p)^2 ≤ K*slope p^2*p.μ*p.ε) :
    let Q := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Draw p.d)).prod ν
    let run := trajectory (step (p := p) g) K ((0,retract 0,retract 0) : State p.d)
    Integrable (fun ξ => f (run ξ).2.2.val - f u.val) Q ∧
    (∫ ξ, f (run ξ).2.2.val - f u.val ∂Q) ≤ p.ε := by
  intro Q run
  let s₀ : State p.d := (0,retract 0,retract 0)
  let μ := p.μ
  let m := slope p
  let V := ((p.d:ℝ)/radius p)^2
  let t := (K:ℝ)
  have hμ : 0 < μ := hp.1
  have hm : 0 < m := (tuning hp).1
  have hε := hp.2.2.2.2.2.2
  have hd : 0 < (p.d:ℝ) := by exact_mod_cast NeZero.pos p.d
  have hh := (tuning hp).2.1
  have hv : 0 < V := sq_pos_of_pos (div_pos hd hh)
  change 8*V ≤ t*m^2*μ*p.ε at hn
  have ht : 0 < t := by
    by_contra! ht
    have h0 : t = 0 := le_antisymm ht (Nat.cast_nonneg _)
    rw [h0] at hn
    linarith
  have hmstep := step_measurable hg
  have hmeas : Measurable run := (trajectory_measurable hmstep K).of_uncurry_left
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun z => (hf.differentiable z).continuousAt
  let gap := fun ξ => f (run ξ).2.2.val - f u.val
  have hgap : Measurable gap := (hfc.measurable.comp
    (measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp hmeas)))).sub_const _
  have hi : Integrable gap Q := Integrable.of_bound hgap.aestronglyMeasurable (2*p.G)
    (Filter.Eventually.of_forall fun ξ => by
      have h := hf.lipschitz _ (run ξ).2.2.property u u.property
      have hd' : ‖(run ξ).2.2.val-u.val‖ ≤ 2 := (norm_sub_le _ _).trans
        (by linarith [norm_ball (run ξ).2.2.property,norm_ball u.property])
      exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hd' hp.2.2.1.le]))
  refine ⟨hi,?_⟩
  obtain ⟨hme,B,hB⟩ := storage_bounds hf u
  have he := DuelingReferenceProcess.integral_trajectory_le ((drawLaw p : Measure (Draw p.d)).prod ν)
    (step (p := p) g) hmstep Prod.fst (fun _ _ => rfl) _ hme B hB
    (conditional_descent ν hp hf hr hg hmean u hu) K s₀
  have htime (n : ℕ) (ξ : ℕ → Draw p.d × Ω) : (trajectory (step g) n s₀ ξ).1 = n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [trajectory_succ_last]; exact congrArg Nat.succ ih
  have ht' (ξ) : (run ξ).1 = K := htime K ξ
  have hei : Integrable (fun ξ => energy (p := p) f u (run ξ)) Q :=
    Integrable.of_bound (hme.comp hmeas).aestronglyMeasurable (B K)
      (Filter.Eventually.of_forall fun ξ => by simpa only [ht', Real.norm_eq_abs] using hB (run ξ))
  have hpt (ξ) : t*(t+1)/2*(gap ξ-p.ε/4)-2*t*V/(m^2*μ) ≤ energy (p := p) f u (run ξ) := by
    unfold energy storage
    rw [ht']
    change _ ≤ t*(t+1)/2*(gap ξ-p.ε/4) + μ/8*t*(t+1)*_ - 2*t*V/(m^2*μ)
    nlinarith [mul_nonneg (by positivity : 0 ≤ μ/8*t*(t+1)) (sq_nonneg ‖(run ξ).2.1.val-u.val‖)]
  have hgi := integral_mono (((hi.sub (integrable_const _)).const_mul (t*(t+1)/2)).sub
    (integrable_const (2*t*V/(m^2*μ)))) hei hpt
  have he₀ : energy (p := p) f u s₀ = 0 := by simp [energy,storage,s₀]
  change (∫ ξ, energy (p := p) f u (run ξ) ∂Q) ≤ energy (p := p) f u s₀ at he
  rw [he₀] at he
  have h := hgi.trans he
  change (∫ ξ, t*(t+1)/2*(gap ξ-p.ε/4)-2*t*V/(m^2*μ) ∂Q) ≤ 0 at h
  have hgi' : Integrable (fun ξ => gap ξ-p.ε/4) Q := hi.sub (integrable_const _)
  rw [integral_sub (hgi'.const_mul (t*(t+1)/2)) (integrable_const (2*t*V/(m^2*μ))),
    integral_const_mul, integral_sub hi (integrable_const (p.ε/4))] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  change (∫ ξ, gap ξ ∂Q) ≤ p.ε
  by_contra! hbad
  have hpos := mul_lt_mul_of_pos_left hbad (show 0 < t*(t+1)/2 by positivity)
  have hnoise : 2*t*V/(m^2*μ) ≤ t*t*p.ε/4 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_left hn ht.le]
  nlinarith [mul_pos ht hε]

lemma successful {p : Params} (hp : spec.valid p) (K : ℕ)
    (hn : 8*((p.d:ℝ)/radius p)^2 ≤ K*slope p^2*p.μ*p.ε)
    (f : Point p.d → ℝ) (O : Oracle (Ball p.d × Ball p.d) Bool)
    (hO : spec.admissible p f O) :
    spec.successful p f (fun s => output p O K s.1 s.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _),inferInstance⟩ := by
  obtain ⟨hf,ρ,hr,Ω,mΩ,ν,P,g,hIID,hg,hmean,rfl⟩ := hO
  let : MeasurableSpace Ω := mΩ
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf.differentiable x).continuousAt
  obtain ⟨u,hu,hmin⟩ := (isCompact_closedBall (0 : Point p.d) 1).exists_isMinOn
    ⟨0, by simp⟩ hfc.continuousOn
  let U : Ball p.d := ⟨u,hu⟩
  have heq : (P : Measure _) = Measure.infinitePi (fun _ : ℕ => (ν : Measure Ω)) := by
    simpa only [show (fun (ξ : ℕ → Ω) k => ξ k) = id by rfl,Measure.map_id] using hIID.stream_law.map_eq
  let O : Oracle (Ball p.d × Ball p.d) Bool :=
    {Seed := fun _ => Ω, law := P, answer := fun _ q z => g q.2 z}
  let Q := Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Draw p.d)).prod (ν : Measure Ω)
  let run := trajectory (step (p := p) g) K ((0,retract 0,retract 0) : State p.d)
  let zip := fun s : (algorithm p).Seed × (ℕ → Ω) => fun k => (s.1.2 k,s.2 k)
  have hz : MeasurePreserving zip (((algorithm p).law : Measure _).prod (P : Measure _)) Q := by
    rw [heq]
    exact measurePreserving_snd.comp (HeavyTailedTapeExecution.initial_zip_streams_preserving
      (Measure.dirac ()) (drawLaw p : Measure (Draw p.d)) (ν : Measure Ω))
  have hex (s : (algorithm p).Seed × (ℕ → Ω)) : output p O K s.1 s.2 = (run (zip s)).2.2 :=
    HeavyTailedTapeExecution.execute_fresh_tape _ _ _ _ _ _ _ _ _ _ _
  have hmr : Measurable run := (trajectory_measurable (step_measurable hg) K).of_uncurry_left
  have hme : Measurable (fun s : (algorithm p).Seed × (ℕ → Ω) => output p O K s.1 s.2) := by
    simp_rw [hex]
    exact measurable_snd.comp (measurable_snd.comp (hmr.comp hz.measurable))
  obtain ⟨hi,ha⟩ := run_accuracy ν hp hf hr hg hmean U hmin K hn
  refine ⟨hme,U,hmin,?_,?_⟩
  · change Integrable (fun s : (algorithm p).Seed × (ℕ → Ω) => f (output p O K s.1 s.2).val - f U.val) _
    simp_rw [hex]
    exact hz.integrable_comp_of_integrable hi
  · change (∫ s : (algorithm p).Seed × (ℕ → Ω), f (output p O K s.1 s.2).val - f U.val ∂_) ≤ p.ε
    simp_rw [hex]
    have hm : Measurable (fun ξ => f (run ξ).2.2.val-f U.val) :=
      (hfc.measurable.comp (measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp hmr)))).sub_const _
    have he := integral_map (μ := ((algorithm p).law : Measure _).prod (P : Measure _)) hz.measurable.aemeasurable hm.aestronglyMeasurable
    rw [hz.map_eq] at he
    exact he.ge.trans ha

end LongTails.Proofs.DuelingReferenceUpperBound
