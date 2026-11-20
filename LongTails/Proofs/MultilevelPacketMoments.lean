import LongTails.Proofs.MultilevelTrajectory
import LongTails.Proofs.MultilevelDraws
import LongTails.Proofs.TerminalClippingEnergy

namespace LongTails.Proofs.MultilevelPacketMoments

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedMeanSquaredSmooth
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultilevelWorkerSchedule
open LongTails.Algorithms.MultilevelTransport (Bits)
open LongTails.Algorithms.MultilevelPipeline
open LongTails.Algorithms.DistributedQuantization (message receive)
open MultilevelTrajectory MultilevelTimetable MultilevelWorkerSchedule

structure Data (p : Params) (f : Point p → ℝ) (g : Fin p.n → Point p → p.Ω → Point p)
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (a : ℝ) : Prop where
  smooth : 0 < p.L
  accuracy : 0 < p.ε
  grad : ∀ x, HasGradientAt f (gradient f x) x
  low : ∀ x, a ≤ f x
  gap : f p.x0 - a ≤ p.Δ
  oracle : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) f (g i) p.σ
  difference : ∀ i x y, Integrable (fun z => ‖g i x z - g i y z‖^2) (μ i : Measure _) ∧
    (∫ z, ‖g i x z - g i y z‖^2 ∂(μ i : Measure _)) ≤ p.L^2 * ‖x-y‖^2

variable {p : Params} {f : Point p → ℝ} {g : Fin p.n → Point p → p.Ω → Point p}
    {μ : Fin p.n → ProbabilityMeasure p.Ω} {a : ℝ}

lemma Data.lip (H : Data p f g μ a) (x y : Point p) :
    ‖gradient f x-gradient f y‖ ≤ p.L*‖x-y‖ :=
  objective_smooth p (μ 0) f (g 0) H.smooth (H.oracle 0) (H.difference 0) x y

def source : Job → ℕ
  | none => 0
  | some (j,s) => s * 2^j

def parent : Job → ℕ
  | none => 0
  | some (j,s) => parentAtRelease (2^j) s

noncomputable def snapshot (p : Params) : Job → Bool
  | none => true
  | some (j,_) => decide (j = height p)

noncomputable def target (p : Params) (bits : ℕ → Bits) (job : Job) (G : Point p → Point p) : Point p :=
  let x := gridPoint p bits (source job)
  let y := gridPoint p bits (parent job)
  if snapshot p job then G x else G x - G y

noncomputable def units (p : Params) : Job → ℕ
  | none => fullBatch p
  | some (j,_) => if j = height p then fullBatch p else 16 * 4^j

noncomputable def clippedGrid (p : Params) (v : Point p) : Point p :=
  receive p.d (width p) (valueSpacing p) (message p.d (width p) (valueSpacing p)
    (OracleTemplate.clip (radiusUnits p * precision p) v))

lemma decoded_pair (p : Params) (bits : ℕ → Bits) (job : Job) :
    decode p (queryBits p bits job) = (gridPoint p bits (source job), gridPoint p bits (parent job)) := by
  have he (x y : Point p) :
      List.take (p.d*width p) (message p.d (width p) (pointSpacing p) x ++ message p.d (width p) (pointSpacing p) y) =
        message p.d (width p) (pointSpacing p) x := by
    rw [← DistributedQuantization.message_length p.d (width p) (pointSpacing p) x]
    simp
  have hd (x y : Point p) :
      List.drop (p.d*width p) (message p.d (width p) (pointSpacing p) x ++ message p.d (width p) (pointSpacing p) y) =
        message p.d (width p) (pointSpacing p) y := by
    rw [← DistributedQuantization.message_length p.d (width p) (pointSpacing p) x]
    simp
  cases job with
  | none => simp [decode,queryBits,source,parent,gridPoint,he,hd]
  | some v => rcases v with ⟨j,s⟩; simp [decode,queryBits,source,parent,gridPoint,he,hd]

lemma flag (p : Params) (bits : ℕ → Bits) (job : Job) :
    (queryBits p bits job).head? = some (snapshot p job) := by
  cases job with
  | none => rfl
  | some v => cases v; rfl

lemma target_indices {job : Job} (h : job ∈ cells p) :
    parent job ≤ source job ∧ source job ≤ wanted p := by
  cases job with
  | none => simp [source,parent]
  | some v =>
    rcases v with ⟨j,s⟩
    exact ⟨parent_known _ _ (by positivity), (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans (in_level h).2⟩

lemma cap_units {job : Job} (h : job ∈ cells p) :
    units p job ≤ 16*(fullBatch p + 4^height p + 1) := by
  have hS : fullBatch p ≤ 16*(fullBatch p+4^height p+1) := by
    calc
      _ ≤ fullBatch p+4^height p+1 := (Nat.le_add_right _ _).trans (Nat.le_succ _)
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by decide)
  cases job with
  | none => exact hS
  | some v =>
    rcases v with ⟨j,s⟩
    have hp := Nat.pow_le_pow_right (by decide : 0 < 4) (in_level h).1
    change (if j = height p then _ else _) ≤ _
    split
    · exact hS
    · exact Nat.mul_le_mul_left 16 (hp.trans ((Nat.le_add_left _ _).trans (Nat.le_succ _)))

lemma full_units (p : Params) : 1 ≤ fullBatch p := le_max_left _ _

lemma units_pos (p : Params) (job : Job) : 1 ≤ units p job := by
  cases job with
  | none => exact full_units _
  | some v =>
    rcases v with ⟨j,s⟩
    change 1 ≤ (if j = height p then fullBatch p else 16*4^j)
    split
    · exact full_units _
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)

lemma variance_budget (p : Params) (he : 0 < p.ε) : p.σ^2 ≤ fullBatch p * precision p^2 := by
  have hδ : 0 < precision p := by unfold precision; positivity
  have h : (512*p.σ/p.ε)^2 ≤ (fullBatch p : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  have heq : p.σ^2 / precision p^2 = (512*p.σ/p.ε)^2 := by unfold precision; field_simp
  apply (div_le_iff₀ (sq_pos_of_pos hδ)).mp
  simpa only [heq] using h

lemma Data.target_norm (H : Data p f g μ a) (b : ℕ → Bits) (job : Job) (hjob : job ∈ cells p) :
    ‖target p b job (gradient f)‖ ≤ (4*(wanted p : ℝ)+2)*precision p := by
  have hδ : 0 < precision p := by unfold precision; linarith [H.accuracy]
  have hi := target_indices hjob
  have hx := grid_gradient p H.smooth H.accuracy f H.grad H.lip a H.low H.gap b hi.2
  have hy := grid_gradient p H.smooth H.accuracy f H.grad H.lip a H.low H.gap b (hi.1.trans hi.2)
  unfold target
  split
  · nlinarith [mul_nonneg (Nat.cast_nonneg (wanted p)) hδ.le]
  · exact (norm_sub_le _ _).trans (by linarith)

lemma Data.raw (H : Data p f g μ a) (b : ℕ → Bits) (job : Job) (hj : job ∈ cells p) (i : Fin p.n) :
    let X := fun z => target p b job (fun x => g i x z)
    let u := target p b job (gradient f)
    Measurable X ∧ Integrable X (μ i : Measure _) ∧ (∫ z, X z ∂(μ i : Measure _)) = u ∧
      Integrable (fun z => ‖X z-u‖^2) (μ i : Measure _) ∧
      (∫ z, ‖X z-u‖^2 ∂(μ i : Measure _)) ≤ units p job * precision p^2 := by
  have hm (x : Point p) : Measurable (g i x) := (H.oracle i).measurable.comp (measurable_const.prodMk measurable_id)
  intro X u
  by_cases hs : snapshot p job = true
  · have hu : units p job = fullBatch p := by
      cases job with
      | none => rfl
      | some v => rcases v with ⟨j,s⟩; simp [snapshot] at hs; simp [units,hs]
    simpa only [X,u,target,hs,ite_true,hu] using
      And.intro (hm (gridPoint p b (source job))) ⟨(H.oracle i).integrable _, (H.oracle i).unbiased _,
        (H.oracle i).variance_integrable _, ((H.oracle i).variance _).trans (variance_budget p H.accuracy)⟩
  · cases job with
    | none => simp [snapshot] at hs
    | some v =>
      rcases v with ⟨j,s⟩
      have hne : j ≠ height p := by simpa [snapshot] using hs
      let x := gridPoint p b (s*2^j)
      let y := gridPoint p b (parentAtRelease (2^j) s)
      have hint := ((H.oracle i).integrable x).sub ((H.oracle i).integrable y)
      have hmean : (∫ z, g i x z - g i y z ∂(μ i : Measure _)) = gradient f x - gradient f y := by
        rw [integral_sub ((H.oracle i).integrable x) ((H.oracle i).integrable y), (H.oracle i).unbiased, (H.oracle i).unbiased]
      have hvar := OracleTemplate.TerminalClipping.centered_second_moment
        (X := fun z => g i x z - g i y z) hint (H.difference i x y).1
      rw [hmean] at hvar
      have hi := target_indices hj
      have hdist := grid_displacement p H.smooth H.accuracy b hi.1 hi.2
      have hlag := parent_lag (2^j) s (by positivity)
      have hw : 0 < (2:ℕ)^j := by positivity
      have hh : source (some (j,s)) - parent (some (j,s)) + 2 ≤ 4*2^j := by dsimp [source,parent]; omega
      have hη := (stride_pos p H.smooth H.accuracy).le
      have hxy : ‖x-y‖ ≤ (4*(2:ℝ)^j)*stride p := hdist.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) hη)
      have hxy' := mul_le_mul_of_nonneg_left hxy H.smooth.le
      have hident : p.L * stride p = precision p := by unfold stride; field_simp [H.smooth.ne']
      rw [mul_left_comm, hident] at hxy'
      have hpow := pow_le_pow_left₀ (mul_nonneg H.smooth.le (norm_nonneg _)) hxy' 2
      rw [mul_pow] at hpow
      have hfinal : p.L^2 * ‖x-y‖^2 ≤ (16*(4:ℝ)^j) * precision p^2 := by
        convert hpow using 1
        rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul, Nat.mul_comm 2 j,pow_mul]
        ring
      simp [X,u,target,hs,source,parent,units,hne]
      exact ⟨(hm x).sub (hm y), hint,hmean,hvar.1,hvar.2.trans ((H.difference i x y).2.trans hfinal)⟩

lemma Data.clearance (H : Data p f g μ a) (b : ℕ → Bits) (job : Job) (hc : job ∈ cells p) :
    (units p job : ℝ) * (height p + 1 : ℕ) * precision p ≤
      radiusUnits p * precision p - ‖target p b job (gradient f)‖ := by
  have hδ : 0 ≤ precision p := by unfold precision; linarith [H.accuracy]
  have hu := cap_units hc
  have hb : units p job * (height p+1) + (4*wanted p+2) ≤ radiusUnits p := by
    unfold radiusUnits
    have := Nat.mul_le_mul_right (height p+1) hu
    nlinarith
  have hb' : (units p job : ℝ) * (height p + 1 : ℕ) + (4*(wanted p : ℝ)+2) ≤ radiusUnits p := by
    exact_mod_cast hb
  have h := mul_le_mul_of_nonneg_right hb' hδ
  linarith [H.target_norm b job hc]

lemma Data.digital (H : Data p f g μ a) (b : ℕ → Bits) (job : Job) (hc : job ∈ cells p) (i : Fin p.n) :
    let Y := fun z => clippedGrid p (target p b job (fun x => g i x z))
    let u := target p b job (gradient f)
    let mean := ∫ z, Y z ∂(μ i : Measure _)
    let δ := precision p
    Integrable Y (μ i : Measure _) ∧
      ‖mean-u‖ ≤ 2*δ / (height p+1 : ℕ) ∧
      Integrable (fun z => ‖Y z-mean‖^2) (μ i : Measure _) ∧
        (∫ z, ‖Y z-mean‖^2 ∂(μ i : Measure _)) ≤ 4 * units p job * δ^2 := by
  intro Y u mean δ
  let m : ℝ := (height p+1 : ℕ)
  let U : ℝ := units p job
  let R := radiusUnits p * δ
  let X := fun z => target p b job (fun x => g i x z)
  have hδ : 0 < δ := by dsimp [δ,precision]; linarith [H.accuracy]
  have hm : 1 ≤ m := by dsimp [m]; exact_mod_cast Nat.le_add_left 1 (height p)
  have hm' : 0 < m := by linarith
  have hU : 1 ≤ U := by dsimp [U]; exact_mod_cast units_pos p job
  have hU' : 0 < U := by linarith
  have hgap : U*m*δ ≤ R-‖u‖ := H.clearance b job hc
  have hR : ‖u‖ < R := by linarith [mul_pos (mul_pos hU' hm') hδ]
  obtain ⟨hXm,hXi,hmean,hX2,hXerr⟩ := H.raw b job hc i
  have hQ : Measurable (clippedGrid p) :=
    (DistributedQuantization.measurable_roundTrip _ _ _).comp (OracleTemplate.measurable_clip _)
  obtain ⟨hYi,hY2,hvar,hbias⟩ := DistributedBatchedSgd.quantized_gradient_control
    (μ i : Measure _) R (δ/m) (U*δ^2) u hR (div_nonneg hδ.le hm'.le)
    X hXm hXi hX2 hmean hXerr _ hQ (value_error p H.accuracy)
  have hfrac : U*δ^2 / (R-‖u‖) ≤ δ/m := by
    rw [div_le_div_iff₀ (sub_pos.mpr hR) hm']
    nlinarith [mul_le_mul_of_nonneg_right hgap hδ.le]
  have hh : δ/m ≤ δ := div_le_self hδ.le hm
  have h2 := pow_le_pow_left₀ (div_nonneg hδ.le hm'.le) hh 2
  have hcenter := OracleTemplate.TerminalClipping.centered_second_moment
    (X := fun z => Y z-u) (hYi.sub (integrable_const u)) hY2
  have hv : (∫ z, Y z-u ∂(μ i : Measure _)) = mean-u := by rw [integral_sub hYi (integrable_const _)]; simp [mean,Y,X]
  simp_rw [hv,sub_sub_sub_cancel_right] at hcenter
  refine ⟨hYi, ?_, hcenter.1,hcenter.2.trans (hvar.trans ?_)⟩
  · change ‖mean-u‖ ≤ 2*δ/m
    calc
      _ ≤ _ := hbias
      _ ≤ δ/m + δ/m := add_le_add_left hfrac _
      _ = _ := by ring
  · nlinarith [mul_le_mul_of_nonneg_right hU (sq_nonneg δ)]

end LongTails.Proofs.MultilevelPacketMoments
