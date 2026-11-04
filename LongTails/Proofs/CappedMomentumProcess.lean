import LongTails.Proofs.CappedMomentum
import LongTails.Proofs.TwoSidedPLSampling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

namespace LongTails.Proofs.CappedMomentumProcess

open MeasureTheory
open scoped RealInnerProductSpace

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  {m m₀ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

lemma conditional_square_add (hm : m ≤ m₀) {X Y : Ω → E}
    (hX : StronglyMeasurable[m] X) (hXi : MemLp X 2 P) (hYi : MemLp Y 2 P)
    (hzero : P[Y | m] =ᵐ[P] 0) :
    P[(fun ω => ‖X ω + Y ω‖ ^ 2) | m] =ᵐ[P]
      (fun ω => ‖X ω‖ ^ 2 + P[(fun v => ‖Y v‖ ^ 2) | m] ω) := by
  have hcross := OracleTemplate.TwoSidedPL.integrable_inner_of_memLp hXi hYi
  have hp := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ)
    hX.aestronglyMeasurable hcross (hYi.integrable (by norm_num))
  have hx : StronglyMeasurable[m] (fun ω => ‖X ω‖ ^ 2) := by
    exact (continuous_norm.pow 2).comp_stronglyMeasurable hX
  have heq : (fun ω => ‖X ω + Y ω‖ ^ 2) =
      (fun ω => ‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2) + (fun ω => 2 * ⟪X ω, Y ω⟫) := by
    funext ω
    simp only [Pi.add_apply, norm_add_sq_real]
    ring
  rw [heq]
  have ha := condExp_add (μ := P) (hXi.norm.integrable_sq.add hYi.norm.integrable_sq)
    (hcross.const_mul 2) m
  have hb := condExp_add (μ := P) hXi.norm.integrable_sq hYi.norm.integrable_sq m
  have hc := condExp_smul (μ := P) (2 : ℝ) (fun ω => ⟪X ω, Y ω⟫) m
  filter_upwards [ha, hb, hc, hp, hzero] with ω ha hb hc hp hz
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha hb hc hp hz ⊢
  change P[(fun v => 2 * ⟪X v, Y v⟫) | m] ω =
    2 * P[(fun v => ⟪X v, Y v⟫) | m] ω at hc
  rw [condExp_of_stronglyMeasurable hm hx hXi.norm.integrable_sq] at hb
  change P[(fun v => ⟪X v, Y v⟫) | m] ω = ⟪X ω, P[Y | m] ω⟫ at hp
  rw [hz, inner_zero_right] at hp
  change P[(fun v => ‖X v‖ ^ 2 + ‖Y v‖ ^ 2) +
    (fun v => 2 * ⟪X v, Y v⟫) | m] ω = _ at ha
  rw [ha, hb, hc, hp]
  simp

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma conditional_smul_square (c : ℝ) (Y : Ω → E) :
    P[(fun ω => ‖c • Y ω‖ ^ 2) | m] =ᵐ[P]
      (fun ω => c ^ 2 * P[(fun v => ‖Y v‖ ^ 2) | m] ω) := by
  have heq : (fun ω => ‖c • Y ω‖ ^ 2) = c ^ 2 • (fun ω => ‖Y ω‖ ^ 2) := by
    funext ω
    simp [norm_smul, mul_pow]
  rw [heq]
  exact condExp_smul (μ := P) (c ^ 2) (fun ω => ‖Y ω‖ ^ 2) m

lemma conditional_ema_square (hm : m ≤ m₀) {Z Y : Ω → E} {α σ s : ℝ}
    (hZ : StronglyMeasurable[m] Z) (hZi : MemLp Z 2 P) (hYi : MemLp Y 2 P)
    (hzero : P[Y | m] =ᵐ[P] 0)
    (hvariance : ∀ᵐ ω ∂P, P[(fun v => ‖Y v‖ ^ 2) | m] ω ≤ σ ^ 2)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hscale : α * σ ^ 2 ≤ s ^ 2) :
    ∀ᵐ ω ∂P, P[(fun v => ‖(1 - α) • Z v + α • Y v‖ ^ 2) | m] ω ≤
      (1 - α) * ‖Z ω‖ ^ 2 + α * s ^ 2 := by
  have hyzero : P[(fun ω => α • Y ω) | m] =ᵐ[P] 0 := by
    have hc := condExp_smul (μ := P) α Y m
    filter_upwards [hc, hzero] with ω hc hz
    change P[(fun v => α • Y v) | m] ω = α • P[Y | m] ω at hc
    rw [hc, hz]
    simp
  have hc := conditional_square_add hm (hZ.const_smul (1 - α))
    (hZi.const_smul (1 - α)) (hYi.const_smul α) hyzero
  have hs := conditional_smul_square (P := P) (m := m) α Y
  filter_upwards [hc, hs, hvariance] with ω hc hs hv
  change P[(fun v => ‖(1 - α) • Z v + α • Y v‖ ^ 2) | m] ω =
    ‖(1 - α) • Z ω‖ ^ 2 + P[(fun v => ‖α • Y v‖ ^ 2) | m] ω at hc
  rw [hc, hs]
  have hmul := mul_le_mul_of_nonneg_left hv (sq_nonneg α)
  have hscale' := mul_le_mul_of_nonneg_left hscale hα
  have hcoef : (1 - α) ^ 2 ≤ 1 - α := by nlinarith
  have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖Z ω‖)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith

def ema (α : ℝ) (Y : ℕ → Ω → E) : ℕ → Ω → E
  | 0 => fun _ => 0
  | n + 1 => fun ω => (1 - α) • ema α Y n ω + α • Y n ω

omit [CompleteSpace E] in
lemma ema_memLp (α : ℝ) {Y : ℕ → Ω → E} (hY : ∀ n, MemLp (Y n) 2 P) :
    ∀ n, MemLp (ema α Y n) 2 P := by
  intro n
  induction n with
  | zero => exact memLp_const 0
  | succ n ih => exact (ih.const_smul (1 - α)).add ((hY n).const_smul α)

omit [CompleteSpace E] in
lemma ema_adapted {F : ℕ → MeasurableSpace Ω} (hF : Monotone F)
    (α : ℝ) {Y : ℕ → Ω → E}
    (hY : ∀ n, StronglyMeasurable[F (n + 1)] (Y n)) :
    ∀ n, StronglyMeasurable[F n] (ema α Y n) := by
  intro n
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    exact ((ih.mono (hF (Nat.le_succ n))).const_smul (1 - α)).add
      ((hY n).const_smul α)

lemma ema_capped_tail {F : ℕ → MeasurableSpace Ω} (hF : Monotone F)
    (hFm : ∀ n, F n ≤ m₀) {Y : ℕ → Ω → E} {α σ s G : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 < s) (hG : 0 < G)
    (hscale : α * σ ^ 2 ≤ s ^ 2)
    (hYi : ∀ n, MemLp (Y n) 2 P)
    (hYa : ∀ n, StronglyMeasurable[F (n + 1)] (Y n))
    (hzero : ∀ n, P[Y n | F n] =ᵐ[P] 0)
    (hvariance : ∀ n, ∀ᵐ ω ∂P, P[(fun v => ‖Y n v‖ ^ 2) | F n] ω ≤ σ ^ 2)
    (n : ℕ) (u : ℝ) :
    P.real {ω | 5 * s * n + (4 * G / α) * u ≤
      ∑ i ∈ Finset.range n, min G ‖ema α Y i ω‖} ≤ Real.exp (-u) := by
  have hZi := ema_memLp α hYi
  have hZa := ema_adapted hF α hYa
  apply CappedMomentum.capped_tail hFm hα hs hG (fun i ω => norm_nonneg _)
    (fun i => ((hZa i).mono (hFm i)).norm.measurable)
    (fun i => (hZi i).norm.integrable_sq)
    (fun i j hji => ((hZa j).mono (hF hji)).norm)
    (fun ω => by simp [ema])
  intro i
  exact conditional_ema_square (hFm i) (hZa i) (hZi i) (hYi i)
    (hzero i) (hvariance i) hα.le hα1 hscale

end LongTails.Proofs.CappedMomentumProcess
