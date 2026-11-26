import LongTails.Proofs.ChiSquareBoundedCentreDroSurvivors
import LongTails.Proofs.ChiSquareBoundedCentreDroComparator
import LongTails.Proofs.ChiSquareBoundedCentreDroBudget
import LongTails.Proofs.ChiSquareBoundedCentreDroInitial

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro
open ChiSquareDro (Adm objective_le radius)
noncomputable section

variable {q : Params} {I : Instance q} {proj : q.E → q.E}

def slot (q : Params) (i : ℕ) := if i < bracketCount q then i else 0

def field (I : Instance q) (proj : q.E → q.E) (ξ : ℕ → q.Ξ) (i : ℕ) :=
  let j := slot q i
  candidate I proj (leftEndpoint q j) (fun t => ξ (j*trainingCount q+t))

def selected (I : Instance q) (proj : q.E → q.E) (ξ : ℕ → q.Ξ) :=
  champion I proj 0 (rounds q) (field I proj ξ) (fun t => ξ (bracketCount q*trainingCount q+t))

lemma field_meas (h : Adm q I proj) : Measurable (field I proj) :=
  Measurable.of_eval fun i => (candidate_meas h (leftEndpoint q (slot q i))).comp (shift_law I.law.toMeasure _).measurable

lemma selected_meas (h : Adm q I proj) : Measurable (selected I proj) :=
  (champion_meas h 0 _).comp ((field_meas h).prodMk (shift_law I.law.toMeasure _).measurable)

lemma slot_lt (i : ℕ) : slot q i < bracketCount q := by
  unfold slot; split
  · assumption
  · unfold bracketCount; omega

lemma field_past (ξ ζ : ℕ → q.Ξ) (H : ∀ i < bracketCount q*trainingCount q, ξ i = ζ i) :
    field I proj ξ = field I proj ζ := by
  funext i
  apply candidate_past
  intro t ht
  apply H
  have hu := Nat.mul_le_mul_right (trainingCount q) (slot_lt (q := q) i)
  rw [Nat.succ_mul] at hu
  omega

lemma d_lower (hq : spec.valid q) (i : ℕ) : q.ε/(8*q.ρ) ≤ leftEndpoint q i := by
  obtain ⟨hρ,_,_,_,hε⟩ := hq
  unfold leftEndpoint
  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))

lemma field_valid (h : Adm q I proj) (hq : spec.valid q) (ξ : ℕ → q.Ξ) (i : ℕ) :
    ValidCandidate I (2*leftEndpoint q (bracketCount q)) (field I proj ξ i) := by
  have hε := hq.2.2.2.2
  have hρ := hq.1
  have hlow := lt_of_lt_of_le (by positivity : 0 < q.ε/(8*q.ρ)) (d_lower hq (slot q i))
  have H := candidate_props h hq hlow (fun t => ξ (slot q i*trainingCount q+t))
  have huv : leftEndpoint q (slot q i) ≤ leftEndpoint q (bracketCount q) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (slot_lt i).le) (by positivity)
  exact ⟨H.1,⟨le_trans (by linarith) H.2.1,H.2.2⟩⟩

lemma selected_valid (h : Adm q I proj) (hq : spec.valid q) (ξ : ℕ → q.Ξ) :
    ValidCandidate I (2*leftEndpoint q (bracketCount q)) (selected I proj ξ) :=
  champion_property _ _ _ (fun j _ => field_valid h hq ξ j) _

lemma execute_selected (P : ProbabilityMeasure (ℕ → q.Ξ)) (ξ : ℕ → q.Ξ) {K : ℕ}
    (hbranch : ¬ min q.B (q.G*q.R) ≤ q.ε) (hK : usedCalls q ≤ K) :
    execute (sampleOracle I proj P) (algorithm q) (fun _ => K) () ξ = (selected I proj ξ).1 := by
  refine (execution_eq q I proj P ξ hK).trans ?_
  change interpret (response I proj ξ) (plan q) 0 = _
  unfold plan
  have hj (j : ℕ) : Depth (trainingCount q) (trainBracket q j) := depth_training q _ _ _ _
  rw [ite_eq_right hbranch, interpret_bind _ (depth_collect q (trainBracket q) hj _),interpret_tournament]
  simp only [Nat.zero_add]
  unfold selected
  apply congrArg Prod.fst
  congr 1
  funext i
  rw [interpret_collect _ (trainBracket q) hj]
  change interpret (fun t x => replyAt I proj x (ξ t)) (trainBracket q _) _ = _
  rw [interpret_training]
  unfold field slot
  split <;> simp_all

set_option maxHeartbeats 800000 in
lemma selected_gap (h : Adm q I proj) (hq : spec.valid q) {xs : q.E} (hxs : xs ∈ I.domain)
    (hm : IsMinOn (objective I) I.domain xs) (hR : ‖q.x0-xs‖ ≤ q.R) (hbranch : ¬ min q.B (q.G*q.R) ≤ q.ε) :
    let P := streamLaw I.law.toMeasure
    let gap := fun ξ => objective I (selected I proj ξ).1-objective I xs
    Integrable gap P ∧ (∫ ξ, gap ξ ∂P) ≤ q.ε := by
  intro P gap
  obtain ⟨hρ,hG,hB,hR0,hε⟩ := hq
  have hv : spec.valid q := ⟨hρ,hG,hB,hR0,hε⟩
  obtain ⟨a,ha,l,hl,hcomp⟩ := low_bias_comparator I hρ hB hε ((lt_of_not_ge hbranch).trans_le (min_le_left _ _))
    (ChiSquareDro.measurable_section h.loss_meas xs) (fun ω => h.bounds ω xs hxs)
  obtain ⟨j,hj,hbr,hdB⟩ := bracket_cover hρ hε hl
  let b := 2*leftEndpoint q (bracketCount q)
  have hb : 0 ≤ b := by dsimp [b,leftEndpoint]; positivity
  have hC w (hw : ValidCandidate I b w) := score_bounds h hρ hB hw.1 hb hw.2
  let X := field I proj
  let n := bracketCount q * trainingCount q
  let F := fun ys (ξ : ℕ → q.Ξ) => trueScore I (champion I proj 0 (rounds q) ys ξ)
  have hF : Measurable (Function.uncurry F) := (score_meas h).comp (champion_meas h _ _)
  have hbd (ξ ζ : ℕ → q.Ξ) : ‖F (X ξ) ζ‖ ≤ q.B+radius q*(q.B+b) :=
    (hC _ (champion_property (I := I) (proj := proj) (W := ValidCandidate I b) 0 (rounds q) (X ξ) (fun i _ => field_valid h hv ξ i) ζ)).2
  have he := fresh_block I.law.toMeasure n X (field_meas h) field_past F hF hbd
  have hslots : j < 2^rounds q := hj.trans_le (Nat.le_pow_clog (by norm_num) _)
  have hbound ξ := champion_expected h hv hb 0 (rounds q) (X ξ) (fun i _ => field_valid h hv ξ i) j hslots
  have hsi : Integrable (fun ξ => trueScore I (X ξ j)) P := Integrable.of_bound
    ((score_meas h).comp ((measurable_pi_apply j).comp (field_meas h))).aestronglyMeasurable _
    (ae_of_all _ fun ξ => (hC _ (field_valid h hv ξ j)).2)
  have hfi : Integrable (fun ξ => ∫ ζ, F (X ξ) ζ ∂P) P := Integrable.of_bound
    (((hF.stronglyMeasurable.integral_prod_right' (ν := P)).measurable.comp (field_meas h)).aestronglyMeasurable)
    (q.B+radius q*(q.B+b)) (ae_of_all _ fun ξ => (norm_integral_le_of_norm_le_const (ae_of_all _ (hbd ξ))).trans_eq (by simp))
  have H := integral_mono hfi (hsi.add (integrable_const (12*allowance q 0))) hbound
  change (∫ ξ, (∫ ζ, F (X ξ) ζ ∂P) ∂P) ≤ ∫ ξ, trueScore I (X ξ j)+12*allowance q 0 ∂P at H
  rw [ChiSquareDro.integral_add_const' P hsi,← he] at H
  have hfield : (∫ ξ, trueScore I (X ξ j) ∂P) =
      ∫ ξ, trueScore I (candidate I proj (leftEndpoint q j) ξ) ∂P := by
    have hslt : slot q j = j := by unfold slot; rw [ite_eq_left hj]
    simp only [X,field,hslt]
    exact transport_integral (g := fun ξ => trueScore I (candidate I proj (leftEndpoint q j) ξ)) (shift_law I.law.toMeasure (j*trainingCount q))
      ((score_meas h).comp (candidate_meas h (leftEndpoint q j)))
  rw [hfield] at H
  have hgood := candidate_expected h hv hxs hm hR ha hbr (d_lower hv j) hdB hcomp
  let out := fun ξ => (selected I proj ξ).1
  have hmO := ChiSquareDro.measurable_objective_comp h hρ hG (selected_meas h).fst
    (fun ξ => (selected_valid h hv ξ).1)
  have hobj ξ := selected_valid h hv ξ
  have hbO ξ := ChiSquareDro.objective_le_bound I hρ.le (ChiSquareDro.measurable_section h.loss_meas (out ξ))
    (fun ω => (h.bounds ω _ (hobj ξ).1).1) (fun ω => (h.bounds ω _ (hobj ξ).1).2)
  have h0O ξ := ChiSquareDro.objective_nonneg I hρ.le (ChiSquareDro.measurable_section h.loss_meas (out ξ))
    (fun ω => (h.bounds ω _ (hobj ξ).1).1) (fun ω => (h.bounds ω _ (hobj ξ).1).2)
  have hOi : Integrable (fun ξ => objective I (out ξ)) P := Integrable.of_bound hmO.aestronglyMeasurable _
    (ae_of_all _ fun ξ => by rw [Real.norm_eq_abs,abs_of_nonneg (h0O ξ)]; exact hbO ξ)
  have hs : Integrable (fun ξ => trueScore I (selected I proj ξ)) P := Integrable.of_bound
    ((score_meas h).comp (selected_meas h)).aestronglyMeasurable _
    (ae_of_all _ fun ξ => (hC _ (hobj ξ)).2)
  have hmono := integral_mono hOi hs (fun ξ => (hC _ (hobj ξ)).1)
  refine ⟨hOi.sub (integrable_const _), ?_⟩
  change (∫ ξ, objective I (out ξ)-objective I xs ∂P) ≤ _
  rw [integral_sub hOi (integrable_const _),integral_const,probReal_univ,one_smul]
  change (∫ ξ, trueScore I (selected I proj ξ) ∂P) ≤ _ at H
  simp only [allowance,pow_zero,mul_one] at H
  linarith

lemma positive_success (q : Params) (hq : spec.valid q) (I : Instance q)
    (O : Oracle q.E (q.E × ℝ × q.E)) (ha : spec.admissible q I O)
    (hbranch : ¬ min q.B (q.G*q.R) ≤ q.ε) {K : ℕ} (hK : usedCalls q ≤ K) :
    spec.successful q I (fun w : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => K) w.1 w.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨proj,P,hiid,rfl,hconv,_,hx0,hpm,hpmem,hpvi,hlm,hsm,hsub,hbd,hsg,xs,hxs,hmin,hR⟩ := ha
  have h : Adm q I proj := ⟨hconv,hx0,hpm,hpmem,hpvi,hlm,hsm,hsub,hbd,hsg⟩
  have he : (fun w : (algorithm q).Seed × ((k : ℕ) → (sampleOracle I proj P).Seed k) =>
      execute (sampleOracle I proj P) (algorithm q) (fun _ => K) w.1 w.2) =
      fun w => (selected I proj w.2).1 := by funext w; exact execute_selected P w.2 hbranch hK
  have hPlaw : P.toMeasure = streamLaw I.law.toMeasure := by
    have HH := hiid.stream_law.map_eq
    change P.toMeasure.map id = _ at HH
    simpa only [Measure.map_id] using HH
  obtain ⟨hi,hE⟩ := selected_gap h hq hxs hmin hR hbranch
  rw [← hPlaw] at hi hE
  obtain ⟨hi',hE'⟩ := ChiSquareDro.integral_snd_eq ((algorithm q).law : Measure (algorithm q).Seed) P.toMeasure hi
  change Measurable _ ∧ _ ∧ _
  rw [he]
  exact ⟨(selected_meas h).fst.comp measurable_snd,fun w => (selected_valid h hq w.2).1,
    xs,hxs,hmin,hi',hE'.le.trans hE⟩

end
end OracleTemplate.ChiSquareBoundedCentreDro
