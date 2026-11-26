import LongTails.Proofs.ChiSquareBoundedCentreDroTournament
import LongTails.Proofs.ChiSquareBoundedCentreDroTraining
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Set
namespace OracleTemplate.ChiSquareBoundedCentreDro
open LongTails.Setups.ChiSquareConstrainedDro ChiSquareDro
open StochasticGeneralized (splitStream splitStream_preserving prefix_preserving)

noncomputable section

abbrev streamLaw {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) :=
  Measure.infinitePi fun _ : ℕ => p

lemma transport_integral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} {f : α → β} (hp : MeasurePreserving f μ ν) {g : β → ℝ} (hg : Measurable g) :
    (∫ x, g (f x) ∂μ) = ∫ y, g y ∂ν := by
  have H := integral_map hp.measurable.aemeasurable (hg.aestronglyMeasurable (μ := μ.map f))
  rw [hp.map_eq] at H
  exact H.symm

lemma shift_law {Ω : Type*} [MeasurableSpace Ω] (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun t => ξ (n+t)) (streamLaw p) (streamLaw p) :=
  measurePreserving_snd.comp (splitStream_preserving p n)

lemma fresh_block {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] (p : Measure Ω)
    [IsProbabilityMeasure p] (n : ℕ) (X : (ℕ → Ω) → Y) (hm : Measurable X)
    (hpast : ∀ ξ ζ, (∀ i < n, ξ i = ζ i) → X ξ = X ζ)
    (f : Y → (ℕ → Ω) → ℝ) (hf : Measurable (Function.uncurry f))
    {C : ℝ} (hC : ∀ ξ ζ, ‖f (X ξ) ζ‖ ≤ C) :
    (∫ ξ, f (X ξ) (fun t => ξ (n+t)) ∂streamLaw p) =
      ∫ ξ, (∫ ζ, f (X ξ) ζ ∂streamLaw p) ∂streamLaw p := by
  obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure p
  let A := X ∘ TwoSidedPL.extendPrefix ω n
  have hA := hm.comp (TwoSidedPL.measurable_extendPrefix ω n)
  let F := fun z : (Fin n → Ω) × (ℕ → Ω) => f (A z.1) z.2
  have hF : Measurable F := hf.comp ((hA.comp measurable_fst).prodMk measurable_snd)
  have hi : Integrable F ((Measure.pi fun _ : Fin n => p).prod (streamLaw p)) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun z => hC _ _)
  have he := TwoSidedPL.factor_prefix ω n X hpast
  simp_rw [he]
  change (∫ ξ, F (splitStream n ξ) ∂streamLaw p) =
    ∫ ξ, (∫ ζ, F (fun i : Fin n => ξ i, ζ) ∂streamLaw p) ∂streamLaw p
  rw [(splitStream_preserving p n).integral_comp' F, integral_prod _ hi]
  exact (transport_integral (prefix_preserving p n)
    ((hF.stronglyMeasurable.integral_prod_right' (ν := streamLaw p)).measurable)).symm

def allowance (q : Params) (r : ℕ) : ℝ := q.ε/32 * (5/6:ℝ)^r

variable {q : Params} {I : Instance q} {proj : q.E → q.E}

lemma batch_accuracy (hq : spec.valid q) (r : ℕ) :
    radius q ^ 2 * q.B^2 ≤ (batchSize q r : ℝ)*(allowance q r)^2 := by
  obtain ⟨hρ,_,hB,_,hε⟩ := hq
  have H := Nat.le_ceil (1024*(1+2*q.ρ)*q.B^2*(3/2:ℝ)^r/q.ε^2)
  change _ ≤ (batchSize q r:ℝ) at H
  rw [div_le_iff₀ (by positivity)] at H
  have hp : 1 ≤ ((3/2:ℝ)*(5/6)^2)^r := one_le_pow₀ (by norm_num)
  rw [mul_pow,← pow_mul, Nat.mul_comm 2 r, pow_mul] at hp
  have hm := mul_le_mul_of_nonneg_right H (sq_nonneg ((5/6:ℝ)^r))
  have hhp := mul_le_mul_of_nonneg_left hp (show 0 ≤ (1+2*q.ρ)*q.B^2 by positivity)
  rw [radius_sq hρ]; unfold allowance
  linarith only [hm,hhp]

lemma estimate_error (h : Adm q I proj) (hq : spec.valid q) {w : Candidate q.E} (hx : w.1 ∈ I.domain)
    (r k : ℕ) :
    let p := I.law.toMeasure
    let err := fun ξ : ℕ → q.Ξ => |estimate I proj w (batchSize q r) (fun i => ξ (k+i))-trueScore I w|
    Integrable err (streamLaw p) ∧ (∫ ξ, err ξ ∂streamLaw p) ≤ allowance q r := by
  intro p err
  let m := batchSize q r
  let δ := allowance q r
  obtain ⟨hρ,hG,hB,hR,hε⟩ := hq
  have hm : 0 < m := by dsimp [m,batchSize]; apply Nat.ceil_pos.mpr; positivity
  have hδ : 0 < δ := by dsimp [δ,allowance]; positivity
  let X := tail (I.loss w.1) w.2
  let a := max (-w.2) 0
  let b := max (q.B-w.2) 0
  have hX := measurable_tail (measurable_section h.loss_meas w.1) w.2
  have hXab (ω) : X ω ∈ Icc a b :=
    ⟨max_le_max (by linarith [(h.bounds ω _ hx).1]) le_rfl,tail_le _ _ (fun ω => (h.bounds ω _ hx).2) ω⟩
  have hw : b-a ≤ q.B := by
    dsimp [b,a]; rcases le_total w.2 0 with he | he
    · rw [max_eq_left (by linarith : 0 ≤ -w.2),max_eq_left (by linarith : 0 ≤ q.B-w.2)]; linarith
    · rw [max_eq_right (by linarith : -w.2 ≤ 0),sub_zero]; apply max_le <;> linarith
  have hab : 0 ≤ b-a := by obtain ⟨ω⟩ := nonempty_of_isProbabilityMeasure p; linarith [(hXab ω).1,(hXab ω).2]
  let D := fun ξ : Fin m → q.Ξ => Real.sqrt ((m:ℝ)⁻¹*∑ i, X (ξ i)^2) - nrm p (I.loss w.1) w.2
  let ν := Measure.pi fun _ : Fin m => p
  have hM : Measurable D := (((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (hX.comp (measurable_pi_apply i)).pow_const 2)).sqrt).sub_const _)
  have h2 : (∫ ξ, D ξ ^ 2 ∂ν) ≤ (b-a)^2/m := rms_width p hX (le_max_right _ _) hXab hm
  have hi2 : Integrable (fun ξ => D ξ^2) ν := by
    have H := (sqrt_mean_dev p hX (fun ω => (le_max_right _ _).trans (hXab ω).1) (fun ω => (hXab ω).2) hm).1
    simpa only [D,div_eq_inv_mul,nrm,ChiSquareDro.sq,X] using H
  let c := radius q
  let F := fun ξ => |c*D ξ|
  have hFm : Measurable F := continuous_abs.measurable.comp ((measurable_const (a := c)).mul hM)
  have hi : Integrable F ν := by
    have H : MemLp D 2 ν := (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).mpr hi2
    exact ((H.integrable (by norm_num)).const_mul c).abs
  have hpt ξ : F ξ ≤ c^2/(2*δ)*D ξ^2+δ/2 := by
    have H := abs_le_amgm (x := c*D ξ) hδ
    convert H using 1; ring
  have HE := integral_mono hi (((hi2.const_mul _).add (integrable_const _))) hpt
  change (∫ ξ, F ξ ∂ν) ≤ ∫ ξ, c^2/(2*δ)*D ξ^2+δ/2 ∂ν at HE
  rw [integral_add_const' ν (hi2.const_mul _) _,integral_const_mul] at HE
  have hparam := batch_accuracy (q := q) ⟨hρ,hG,hB,hR,hε⟩ r
  change c^2*q.B^2 ≤ (m:ℝ)*δ^2 at hparam
  have hbnd : c^2/(2*δ)*((b-a)^2/m) ≤ δ/2 := by
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    field_simp [hδ,hm']
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hab hw 2) (sq_nonneg c)]
  have hF : (∫ ξ, F ξ ∂ν) ≤ δ := by
    linarith [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ c^2/(2*δ))]
  let block := fun ξ : ℕ → q.Ξ => fun i : Fin m => ξ (k+i)
  have hblock : MeasurePreserving block (streamLaw p) ν := (prefix_preserving p m).comp (shift_law p k)
  have herr : err = fun ξ => F (block ξ) := by
    funext ξ; dsimp [err,F,block,D,estimate,trueScore,c,m]
    rw [proj_fix h.proj_vi hx,div_eq_inv_mul]; congr 1; ring
  rw [herr]
  exact ⟨(hblock.integrable_comp hi.aestronglyMeasurable).mpr hi,(transport_integral hblock hFm).le.trans hF⟩

end
end OracleTemplate.ChiSquareBoundedCentreDro
