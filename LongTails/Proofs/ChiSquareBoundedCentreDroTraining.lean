import LongTails.Proofs.ChiSquareBoundedCentreDroStep
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro ChiSquareDro

noncomputable section
variable {q : Params} {I : Instance q} {proj : q.E → q.E}

def trueScore (I : Instance q) (w : Candidate q.E) :=
  w.2 + radius q * nrm (I.law : Measure q.Ξ) (I.loss w.1) w.2

lemma score_le_Q (h : Adm q I proj) (hρ : 0 < q.ρ) {x : q.E} (hx : x ∈ I.domain) (a : ℝ)
    {l : ℝ} (hl : 0 < l) : trueScore I (x,a-l) ≤ Q I.law q.ρ (I.loss x) a l := by
  rw [Q_eq I.law (measurable_section h.loss_meas x) (fun ω => (h.bounds ω x hx).2)]
  unfold trueScore
  dsimp only
  rw [← nrm_sq, ← radius_sq hρ]
  field_simp [hl]
  nlinarith [sq_nonneg (nrm (I.law : Measure q.Ξ) (I.loss x) (a-l) - radius q*l)]

def sampleField (I : Instance q) (proj : q.E → q.E) (f : ℝ × ℝ × ℝ → ℝ)
    (z : Triple q.E) (ω : q.Ξ) := f (I.loss (proj z.1) ω,z.2)

def bracketBox (B d : ℝ) := Icc 0 B ×ˢ (Icc 0 B ×ˢ Icc d (2*d))

lemma field_expectation (h : Adm q I proj) {d : ℝ} (hd : 0 < d) (hB : 0 ≤ q.B)
    {f : ℝ × ℝ × ℝ → ℝ} (hm : Measurable f) (hc : ContinuousOn f (bracketBox q.B d)) (t : ℕ) :
    let Z := fun ξ => trajectory q I proj d ξ t
    let F := sampleField I proj f
    let p := I.law.toMeasure
    let P := Measure.infinitePi fun _ : ℕ => p
    Integrable (fun ξ => F (Z ξ) (ξ t)) P ∧ Integrable (fun ξ => ∫ ω, F (Z ξ) ω ∂p) P ∧
    (∫ ξ, F (Z ξ) (ξ t) ∂P) = ∫ ξ, (∫ ω, F (Z ξ) ω ∂p) ∂P := by
  intro Z F p P
  have hz := trajectory_meas h d t
  have hFm : Measurable (Function.uncurry F) := hm.comp
    ((h.loss_meas.comp ((h.proj_meas.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd)).prodMk
    (measurable_snd.comp measurable_fst))
  have hk : IsCompact (bracketBox q.B d) := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuousOn hc
  have hbound (ξ ω) : ‖F (Z ξ) ω‖ ≤ C :=
    hC _ ⟨h.bounds ω _ (h.proj_mem _), trajectory_mem hB hd.le ξ t⟩
  have hI := Integrable.of_bound (μ := P) (hFm.comp (hz.prodMk (measurable_pi_apply t))).aestronglyMeasurable C
    (ae_of_all _ fun ξ => hbound ξ (ξ t))
  refine ⟨hI, ?_, TwoSidedPL.integral_prefix_dep p t Z hz (fun _ _ => trajectory_past t) F hFm hI⟩
  have hm' := (hFm.stronglyMeasurable.integral_prod_right' (ν := p)).measurable
  refine Integrable.of_bound (hm'.comp hz).aestronglyMeasurable C (ae_of_all _ fun ξ => ?_)
  exact norm_integral_le_of_norm_le_const (ae_of_all _ fun ω => hbound ξ ω) |>.trans_eq (by simp)

set_option maxHeartbeats 1600000 in
lemma training_regret (h : Adm q I proj) (hq : spec.valid q) {xs : q.E} (hxs : xs ∈ I.domain)
    (hmin : IsMinOn (objective I) I.domain xs) {a l d : ℝ} (ha : a ∈ Icc 0 q.B) (hl : l ∈ Icc d (2*d))
    (hd : q.ε/(8*q.ρ) ≤ d) (hcomp : Q I.law q.ρ (I.loss xs) a l ≤ objective I xs + q.ε/8)
    (n : ℕ) :
    let p := I.law.toMeasure
    let P := Measure.infinitePi fun _ : ℕ => p
    let obj := fun (t : ℕ) (ξ : ℕ → q.Ξ) =>
      let z := trajectory q I proj d ξ t
      Q p q.ρ (I.loss (proj z.1)) z.2.1 z.2.2
    (11/8:ℝ) * (∑ t ∈ Finset.range n, ((∫ ξ, obj t ξ ∂P) - objective I xs)) ≤
      energy q proj d xs a l (q.x0,0,d) + n*(2*(q.ε/8)+6*q.ε/64) := by
  intro p P obj
  obtain ⟨hρ,hG,hB,hR,hε⟩ := hq
  have hv : spec.valid q := ⟨hρ,hG,hB,hR,hε⟩
  have hd' := lt_of_lt_of_le (by positivity : 0 < q.ε/(8*q.ρ)) hd
  let Z := fun t ξ => trajectory q I proj d ξ t
  let H := fun u : ℝ × ℝ × ℝ => majorant q.ρ u.1 u.2.1 u.2.2
  let N := fun u : ℝ × ℝ × ℝ => noise q d (weight u.1 u.2.1 u.2.2)
  let ref := fun ω => majorant q.ρ (I.loss xs ω) a l
  have hmH : Measurable H := by dsimp [H,majorant]; fun_prop
  have hmN : Measurable N := by dsimp [N,noise,weight]; fun_prop
  have hnz (u : ℝ × ℝ × ℝ) (hu : u ∈ bracketBox q.B d) : u.2.2 ≠ 0 := (hd'.trans_le hu.2.2.1).ne'
  have hcH : ContinuousOn H (bracketBox q.B d) := by
    dsimp [H,majorant]; fun_prop (disch := intro u hu; first | exact mul_ne_zero two_ne_zero (hnz u hu) | norm_num)
  have hcN : ContinuousOn N (bracketBox q.B d) := by
    dsimp [N,noise,weight]; fun_prop (disch := exact hnz)
  let Ht := fun t ξ => sampleField I proj H (Z t ξ) (ξ t)
  let Nt := fun t ξ => sampleField I proj N (Z t ξ) (ξ t)
  let Ni := fun t ξ => ∫ ω, sampleField I proj N (Z t ξ) ω ∂p
  have HA := fun t => field_expectation h hd' hB.le hmH hcH t
  have NA := fun t => field_expectation h hd' hB.le hmN hcN t
  have hP (t : ℕ) : MeasurePreserving (fun ξ : ℕ → q.Ξ => ξ t) P p :=
    measurePreserving_eval_infinitePi _ t
  have hri : Integrable ref p := majorant_integrable p (measurable_section h.loss_meas xs)
    (fun ω => (h.bounds ω xs hxs).2) _ _ _
  have hrt t := (hP t).integrable_comp hri.aestronglyMeasurable |>.mpr hri
  let R := fun t ξ => 2*(Ht t ξ-ref (ξ t))-Nt t ξ
  have hRi t : Integrable (R t) P := ((((HA t).1).sub (hrt t)).const_mul 2).sub (NA t).1
  have hmean t : (11/8)*((∫ ξ, obj t ξ ∂P) - objective I xs) - (2*(q.ε/8)+6*q.ε/64) ≤
      ∫ ξ, R t ξ ∂P := by
    have hpt ξ : Ni t ξ ≤ 6*q.ε/64+(5/8)*(obj t ξ-objective I xs) := by
      let z := Z t ξ
      have hx := h.proj_mem z.1
      have ⟨he,hs⟩ := trajectory_mem (I := I) (proj := proj) hB.le hd'.le ξ t
      have hle : objective I xs ≤ objective I (proj z.1) := isMinOn_iff.mp hmin _ hx
      have hweak := objective_le I hρ.le (measurable_section h.loss_meas (proj z.1))
        (fun ω => (h.bounds ω _ hx).1) (fun ω => (h.bounds ω _ hx).2) (z.2.1-z.2.2)
      have hscore := score_le_Q h hρ hx z.2.1 (l := z.2.2) (hd'.trans_le hs.1)
      have hgap : objective I xs ≤ Q p q.ρ (I.loss (proj z.1)) z.2.1 z.2.2 :=
        hle.trans (hweak.trans hscore)
      exact expected_noise q hv I (x := proj z.1) (a := z.2.1) (d := d) (l := z.2.2) (L := objective I xs)
        (measurable_section h.loss_meas (proj z.1)) (fun ω => h.bounds ω _ hx) he hd hs.1 hle hgap
    have hi : Integrable (obj t) P := (HA t).2.1
    have hni : Integrable (Ni t) P := (NA t).2.1
    have hi' := (hi.sub (integrable_const (objective I xs))).const_mul (5/8:ℝ)
    have hbound := integral_mono hni ((integrable_const (6*q.ε/64)).add hi') hpt
    change (∫ ξ, Ni t ξ ∂P) ≤ ∫ ξ, 6*q.ε/64 + (5/8)*(obj t ξ-objective I xs) ∂P at hbound
    rw [integral_add (f := fun _ => 6*q.ε/64) (g := fun ξ => (5/8)*(obj t ξ-objective I xs)) (integrable_const _) hi',
      integral_const_mul, integral_sub hi (integrable_const _)] at hbound
    simp only [integral_const, probReal_univ, one_smul] at hbound
    change _ ≤ ∫ ξ, 2*(Ht t ξ-ref (ξ t))-Nt t ξ ∂P
    rw [integral_sub (f := fun ξ => 2*(Ht t ξ-ref (ξ t))) (g := Nt t)
      ((((HA t).1).sub (hrt t)).const_mul _) (NA t).1, integral_const_mul,
      integral_sub (f := Ht t) (g := fun ξ => ref (ξ t)) (HA t).1 (hrt t)]
    have hr : (∫ ξ, ref (ξ t) ∂P) = Q p q.ρ (I.loss xs) a l := by
      have HH := integral_map (hP t).measurable.aemeasurable ((hP t).map_eq.symm ▸ hri.aestronglyMeasurable)
      rw [(hP t).map_eq] at HH
      exact HH.symm
    have hH : (∫ ξ, Ht t ξ ∂P) = ∫ ξ, obj t ξ ∂P := (HA t).2.2
    have hN : (∫ ξ, Nt t ξ ∂P) = ∫ ξ, Ni t ξ ∂P := (NA t).2.2
    rw [hr,hH,hN]
    linarith
  have hpath (ξ) : ∀ k, energy q proj d xs a l (Z k ξ) + ∑ t ∈ Finset.range k, R t ξ ≤
      energy q proj d xs a l (q.x0,0,d) := by
    intro k
    induction k with
    | zero => simp [Z,trajectory]
    | succ k ih =>
      have hstep := step_energy h hv hd' hxs ha hl (trajectory_mem (I := I) (proj := proj) hB.le hd'.le ξ k) (ξ k)
      change energy q proj d xs a l (Z (k+1) ξ) ≤ energy q proj d xs a l (Z k ξ) -
        2*(Ht k ξ-ref (ξ k))+Nt k ξ at hstep
      rw [Finset.sum_range_succ]; dsimp only [R]; linarith
  have ht ξ : (∑ t ∈ Finset.range n, R t ξ) ≤ energy q proj d xs a l (q.x0,0,d) := by
    have he : 0 ≤ energy q proj d xs a l (Z n ξ) := by unfold energy pointStep centreStep scaleStep; positivity
    linarith [hpath ξ n]
  have hsum := integral_mono (integrable_finsetSum _ (fun t _ => hRi t)) (integrable_const _) ht
  rw [integral_finsetSum _ (fun t _ => hRi t), integral_const, probReal_univ, one_smul] at hsum
  have HH := (Finset.sum_le_sum (s := Finset.range n) fun t _ => hmean t).trans hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at HH
  linarith

end
end OracleTemplate.ChiSquareBoundedCentreDro
