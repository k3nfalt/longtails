import LongTails.Proofs.ChiSquareBoundedCentreDroTraining
import LongTails.Proofs.ChiSquareConvergence

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro ChiSquareDro
noncomputable section

variable {q : Params} {I : Instance q} {proj : q.E → q.E}

def totals (I : Instance q) (proj : q.E → q.E) (d : ℝ) (ξ : ℕ → q.Ξ) (t : ℕ) : Candidate q.E :=
  let z := trajectory q I proj d ξ
  (∑ i ∈ Finset.range t, proj (z i).1, ∑ i ∈ Finset.range t, ((z i).2.1 - (z i).2.2))

def candidate (I : Instance q) (proj : q.E → q.E) (d : ℝ) (ξ : ℕ → q.Ξ) : Candidate q.E :=
  let T := trainingCount q
  let w := totals I proj d ξ T
  ((T:ℝ)⁻¹ • w.1, (T:ℝ)⁻¹ * w.2)

lemma interpret_training (j k : ℕ) (ξ : ℕ → q.Ξ) :
    interpret (fun t x => replyAt I proj x (ξ t)) (trainBracket q j) k =
      candidate I proj (leftEndpoint q j) (fun i => ξ (k+i)) := by
  let d := leftEndpoint q j
  let ζ := fun i => ξ (k+i)
  let z := trajectory q I proj d ζ
  let total := totals I proj d ζ
  have H (n t : ℕ) (ht : t+n = trainingCount q) :
      interpret (fun t x => replyAt I proj x (ξ t)) (training q d n (z t) (total t)) (k+t) =
        candidate I proj d ζ := by
    induction n generalizing t with
    | zero => simp only [Nat.add_zero] at ht; subst t; simp [training,interpret,candidate,total,div_eq_inv_mul]
    | succ n ih =>
      simp only [training,interpret]
      convert ih (t+1) (by omega) using 1; simp only [total,totals,z,trajectory,ζ,Finset.sum_range_succ,Nat.add_assoc,replyAt]
  simpa [total,totals,z,trajectory,trainBracket,d,ζ] using H (trainingCount q) 0 (by omega)

lemma candidate_meas (h : Adm q I proj) (d : ℝ) : Measurable (candidate I proj d) := by
  unfold candidate totals
  exact ((Finset.measurable_sum (Finset.range (trainingCount q)) fun t _ => h.proj_meas.comp (trajectory_meas h d t).fst).const_smul (trainingCount q : ℝ)⁻¹).prodMk
    ((measurable_const (a := (trainingCount q:ℝ)⁻¹)).mul (Finset.measurable_sum (Finset.range (trainingCount q)) fun t _ =>
      (trajectory_meas h d t).snd.fst.sub (trajectory_meas h d t).snd.snd))

lemma training_pos (hq : spec.valid q) : 0 < trainingCount q := by
  obtain ⟨hρ,_,hB,_,hε⟩ := hq
  unfold trainingCount; apply Nat.ceil_pos.mpr; positivity

lemma candidate_props (h : Adm q I proj) (hq : spec.valid q) {d : ℝ} (hd : 0 < d) (ξ : ℕ → q.Ξ) :
    (candidate I proj d ξ).1 ∈ I.domain ∧ (candidate I proj d ξ).2 ∈ Icc (-(2*d)) q.B := by
  have hT : (0:ℝ) < trainingCount q := by exact_mod_cast training_pos hq
  let z := trajectory q I proj d ξ
  constructor
  · have H := h.convex.sum_mem (t := Finset.range (trainingCount q)) (w := fun _ => (trainingCount q:ℝ)⁻¹)
      (z := fun t => proj (z t).1) (fun _ _ => by positivity)
      (by simp [Finset.card_range]; field_simp) (fun _ _ => h.proj_mem _)
    simpa [candidate,totals,Finset.smul_sum,z] using H
  · apply avg_mem_Icc (training_pos hq) (fun t => (z t).2.1-(z t).2.2)
    intro t
    obtain ⟨ha,hl⟩ := trajectory_mem (I := I) (proj := proj) hq.2.2.1.le hd.le ξ t
    constructor <;> linarith [ha.1,ha.2,hl.1,hl.2]

lemma score_bounds (h : Adm q I proj) (hρ : 0 < q.ρ) (hB : 0 < q.B) {w : Candidate q.E}
    (hx : w.1 ∈ I.domain) {b : ℝ} (hb : 0 ≤ b) (he : w.2 ∈ Icc (-b) q.B) :
    objective I w.1 ≤ trueScore I w ∧ |trueScore I w| ≤ q.B+radius q*(q.B+b) := by
  have hweak := objective_le I hρ.le (measurable_section h.loss_meas w.1)
    (fun ω => (h.bounds ω _ hx).1) (fun ω => (h.bounds ω _ hx).2) w.2
  refine ⟨hweak, ?_⟩
  have h0 := objective_nonneg I hρ.le (measurable_section h.loss_meas w.1)
    (fun ω => (h.bounds ω _ hx).1) (fun ω => (h.bounds ω _ hx).2)
  unfold trueScore
  rw [abs_of_nonneg (h0.trans hweak)]
  have hs : ChiSquareDro.sq I.law (I.loss w.1) w.2 ≤ (q.B+b)^2 := by
    unfold ChiSquareDro.sq
    have hh (ω) : tail (I.loss w.1) w.2 ω ≤ q.B+b := by
      unfold tail; apply max_le <;> linarith [(h.bounds ω _ hx).2,he.1]
    simpa using integral_mono_of_nonneg (μ := I.law.toMeasure) (ae_of_all _ fun ω => sq_nonneg (tail (I.loss w.1) w.2 ω))
      (integrable_const ((q.B+b)^2)) (ae_of_all _ fun ω => pow_le_pow_left₀ (tail_nonneg _ _ _) (hh ω) 2)
  have hn := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_sq (by linarith)] at hn
  exact add_le_add he.2 (mul_le_mul_of_nonneg_left hn (radius_pos hρ).le)

lemma score_meas (h : Adm q I proj) : Measurable (trueScore I) :=
  measurable_snd.add (measurable_const.mul (measurable_nrm_joint h))

lemma candidate_jensen (h : Adm q I proj) (hq : spec.valid q) {d : ℝ} (hd : 0 < d) (ξ : ℕ → q.Ξ) :
    let z := trajectory q I proj d ξ
    trueScore I (candidate I proj d ξ) ≤ (trainingCount q : ℝ)⁻¹ *
      ∑ t ∈ Finset.range (trainingCount q), Q I.law q.ρ (I.loss (proj (z t).1)) (z t).2.1 (z t).2.2 := by
  intro z
  let T := trainingCount q
  let c := radius q
  have hc := radius_pos hq.1
  have hT := training_pos hq
  let k : Cfg := { cfg q 0 with slo := c*d, shi := c*(2*d) }
  have hk : Hyp k I.domain proj I.loss I.sub q.B q.G :=
    { hyp_cfg h hq.1 hq.2.1 hq.2.2.1 hq.2.2.2.2 0 with
      slo_pos := mul_pos hc hd, s_le := mul_le_mul_of_nonneg_left (by linarith) hc.le }
  let es := fun t => (z t).2.1-(z t).2.2
  let ls := fun t => c*(z t).2.2
  let w := candidate I proj d ξ
  let sb := (T:ℝ)⁻¹ * ∑ t ∈ Finset.range T, ls t
  have hs t : ls t ∈ Icc k.slo k.shi := by
    have hl := (trajectory_mem (I := I) (proj := proj) hq.2.2.1.le hd.le ξ t).2
    exact ⟨mul_le_mul_of_nonneg_left hl.1 hc.le, mul_le_mul_of_nonneg_left hl.2 hc.le⟩
  have hsb : 0 < sb := hk.slo_pos.trans_le (avg_mem_Icc hT ls hs).1
  have hw := (candidate_props h hq hd ξ).1
  have hbase := PhiX_ge I.law hk h.loss_meas hw hsb (L := trueScore I w) (η := w.2) le_rfl
  let f := fun t => phiAt k I.loss (proj (z t).1) (es t) (ls t)
  have he t ω : f t ω = majorant q.ρ (I.loss (proj (z t).1) ω) (z t).2.1 (z t).2.2 := by
    have hl : 0 < (z t).2.2 := hd.trans_le (trajectory_mem (I := I) (proj := proj) hq.2.2.1.le hd.le ξ t).2.1
    change es t + c*max (_-es t) 0 ^ 2 / (2*ls t) + c*ls t/2 = _
    unfold es ls majorant
    rw [← radius_sq hq.1]
    change _ = _ + c^2*(z t).2.2/2
    have hc' : 0 < c := hc
    field_simp
  have hi t : Integrable (f t) I.law.toMeasure := by
    simp_rw [show f t = _ from funext (he t)]
    exact majorant_integrable _ (measurable_section h.loss_meas _) (fun ω => (h.bounds ω _ (h.proj_mem _)).2) _ _ _
  have hxint : Integrable (phiAt k I.loss w.1 w.2 sb) I.law.toMeasure := by
    unfold phiAt phi
    exact ((integrable_const _).add (((integrable_tail_sq _ (measurable_section h.loss_meas _)
      (fun ω => (h.bounds ω _ hw).2) w.2).const_mul _).div_const _)).add (integrable_const _)
  have hj ω : phiAt k I.loss w.1 w.2 sb ω ≤ (T:ℝ)⁻¹ * ∑ t ∈ Finset.range T, f t ω :=
    phi_average_le hk hT (fun t => proj (z t).1) es ls (fun _ => h.proj_mem _) hs h.convex ω
  have HH := integral_mono hxint ((integrable_finsetSum _ fun t _ => hi t).const_mul _) hj
  rw [integral_const_mul, integral_finsetSum _ fun t _ => hi t] at HH
  refine hbase.trans (HH.trans_eq ?_)
  simp only [Q,he,T]

lemma candidate_past {d : ℝ} {ξ ζ : ℕ → q.Ξ}
    (H : ∀ i < trainingCount q, ξ i = ζ i) : candidate I proj d ξ = candidate I proj d ζ := by
  have hz t (ht : t ∈ Finset.range (trainingCount q)) : trajectory q I proj d ξ t = trajectory q I proj d ζ t :=
    trajectory_past t (fun i hi => H i (hi.trans (Finset.mem_range.mp ht)))
  unfold candidate totals
  dsimp only
  congr 2 <;> apply Finset.sum_congr rfl <;> intro t ht <;> rw [hz t ht]

lemma candidate_expected (h : Adm q I proj) (hq : spec.valid q) {xs : q.E} (hxs : xs ∈ I.domain)
    (hmin : IsMinOn (objective I) I.domain xs) (hR : ‖q.x0-xs‖ ≤ q.R)
    {a l d : ℝ} (ha : a ∈ Icc 0 q.B) (hl : l ∈ Icc d (2*d))
    (hd : q.ε/(8*q.ρ) ≤ d) (hdB : q.ρ*d ≤ q.B)
    (hc : Q I.law q.ρ (I.loss xs) a l ≤ objective I xs + q.ε/8) :
    (∫ ξ, trueScore I (candidate I proj d ξ) ∂Measure.infinitePi (fun _ : ℕ => I.law.toMeasure)) ≤
      objective I xs + q.ε/2 := by
  let T := trainingCount q
  let P := Measure.infinitePi (fun _ : ℕ => I.law.toMeasure)
  have hρ := hq.1
  have hε := hq.2.2.2.2
  have hB := hq.2.2.1
  have hd' := lt_of_lt_of_le (by positivity : 0 < q.ε/(8*q.ρ)) hd
  have hT : (0:ℝ) < T := by exact_mod_cast training_pos hq
  let obj := fun t (ξ : ℕ → q.Ξ) =>
    let z := trajectory q I proj d ξ t
    Q I.law q.ρ (I.loss (proj z.1)) z.2.1 z.2.2
  have hnz (u : ℝ × ℝ × ℝ) (hu : u ∈ bracketBox q.B d) : u.2.2 ≠ 0 := (hd'.trans_le hu.2.2.1).ne'
  have hI t : Integrable (obj t) P :=
    (field_expectation h hd' hB.le (f := fun u => majorant q.ρ u.1 u.2.1 u.2.2)
      (by unfold majorant; fun_prop)
      (by unfold majorant; fun_prop (disch := intro u hu; first | exact mul_ne_zero two_ne_zero (hnz u hu) | norm_num)) t).2.1
  have hsI : Integrable (fun ξ => trueScore I (candidate I proj d ξ)) P :=
    Integrable.of_bound ((score_meas h).comp (candidate_meas h d)).aestronglyMeasurable _
      (ae_of_all _ fun ξ => (score_bounds h hρ hB (candidate_props h hq hd' ξ).1
        (show 0 ≤ 2*d by positivity) (candidate_props h hq hd' ξ).2).2)
  have H := integral_mono hsI ((integrable_finsetSum (Finset.range T) fun t _ => hI t).const_mul (T:ℝ)⁻¹)
    (candidate_jensen h hq hd')
  rw [integral_const_mul, integral_finsetSum _ fun t _ => hI t] at H
  rw [le_inv_mul_iff₀ hT] at H
  have HH := training_regret h hq hxs hmin ha hl hd hc T
  change 11/8*(∑ t ∈ Finset.range T, ((∫ ξ, obj t ξ ∂P)-objective I xs)) ≤ _ at HH
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,nsmul_eq_mul] at HH
  have hinit := initial_energy h hq hR ha hd' hl hdB
  change _ ≤ (T:ℝ)*q.ε/4 at hinit
  change (∫ ξ, trueScore I (candidate I proj d ξ) ∂P) ≤ _
  apply le_of_mul_le_mul_left (a := (T:ℝ)) _ hT
  nlinarith only [H,HH,hinit,mul_pos hT hε]


end
end OracleTemplate.ChiSquareBoundedCentreDro
