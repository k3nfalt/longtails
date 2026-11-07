import LongTails.Algorithms.ChiSquareBracket
import LongTails.Proofs.ChiSquareDuality

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ChiSquareDro

open LongTails.Setups.ChiSquareConstrainedDro

variable {q : Params} (I : Instance q)

lemma integrable_density_mul {w : q.Ξ → ℝ} (hw : IsFeasibleDensity I w) {f : q.Ξ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ ξ, |f ξ| ≤ C) :
    Integrable (fun ξ => w ξ * f ξ) (I.law : Measure q.Ξ) := by
  have hwi : Integrable w (I.law : Measure q.Ξ) := Feasible.integrable _ hw
  refine Integrable.mono' (hwi.mul_const C) (hw.1.mul hf).aestronglyMeasurable
    (ae_of_all _ fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw.2.1 ξ)]
  exact mul_le_mul_of_nonneg_left (hC ξ) (hw.2.1 ξ)

lemma objective_set_bdd (hρ : 0 ≤ q.ρ) {x : q.E} (hl : Measurable (I.loss x))
    (h0 : ∀ ξ, 0 ≤ I.loss x ξ) (hB : ∀ ξ, I.loss x ξ ≤ q.B) :
    BddAbove {v | ∃ w, IsFeasibleDensity I w ∧ v = ∫ ξ, w ξ * I.loss x ξ ∂(I.law : Measure q.Ξ)} := by
  refine ⟨q.B + radius q * nrm (I.law : Measure q.Ξ) (I.loss x) q.B, ?_⟩
  rintro v ⟨w, hw, rfl⟩
  exact weak_duality _ hl h0 hB hw hρ q.B

lemma objective_le (hρ : 0 ≤ q.ρ) {x : q.E} (hl : Measurable (I.loss x))
    (h0 : ∀ ξ, 0 ≤ I.loss x ξ) (hB : ∀ ξ, I.loss x ξ ≤ q.B) (η : ℝ) :
    objective I x ≤ η + radius q * nrm (I.law : Measure q.Ξ) (I.loss x) η := by
  apply csSup_le
  · exact ⟨_, fun _ => 1, one_feasible _ hρ, rfl⟩
  · rintro v ⟨w, hw, rfl⟩
    exact weak_duality _ hl h0 hB hw hρ η

lemma le_objective (hρ : 0 ≤ q.ρ) {x : q.E} (hl : Measurable (I.loss x))
    (h0 : ∀ ξ, 0 ≤ I.loss x ξ) (hB : ∀ ξ, I.loss x ξ ≤ q.B) {w : q.Ξ → ℝ}
    (hw : IsFeasibleDensity I w) :
    (∫ ξ, w ξ * I.loss x ξ ∂(I.law : Measure q.Ξ)) ≤ objective I x :=
  le_csSup (objective_set_bdd I hρ hl h0 hB) ⟨w, hw, rfl⟩

lemma objective_nonneg (hρ : 0 ≤ q.ρ) {x : q.E} (hl : Measurable (I.loss x))
    (h0 : ∀ ξ, 0 ≤ I.loss x ξ) (hB : ∀ ξ, I.loss x ξ ≤ q.B) : 0 ≤ objective I x := by
  refine le_trans ?_ (le_objective I hρ hl h0 hB (one_feasible _ hρ))
  exact integral_nonneg fun ξ => by simpa using h0 ξ

lemma objective_le_bound (hρ : 0 ≤ q.ρ) {x : q.E} (hl : Measurable (I.loss x))
    (h0 : ∀ ξ, 0 ≤ I.loss x ξ) (hB : ∀ ξ, I.loss x ξ ≤ q.B) : objective I x ≤ q.B := by
  have := objective_le I hρ hl h0 hB q.B
  rwa [nrm_top _ hB, mul_zero, add_zero] at this

lemma dual_attained (hρ : 0 < q.ρ) (hBpos : 0 < q.B) {x : q.E} (hl : Measurable (I.loss x))
    (h0 : ∀ ξ, 0 ≤ I.loss x ξ) (hB : ∀ ξ, I.loss x ξ ≤ q.B) :
    ∃ η ∈ Icc (etaLow q) q.B,
      η + radius q * nrm (I.law : Measure q.Ξ) (I.loss x) η ≤ objective I x := by
  obtain ⟨η, hη, hδ⟩ := strong_duality (I.law : Measure q.Ξ) hl h0 hB hBpos hρ
  refine ⟨η, by rwa [etaLow, ← neg_div], ?_⟩
  refine le_of_forall_pos_le_add fun δ hδpos => ?_
  obtain ⟨w, hw, hle⟩ := hδ δ hδpos
  have := le_objective I hρ.le hl h0 hB (w := w) hw
  unfold radius
  linarith

lemma proj_nonexpansive {D : Set q.E} {proj : q.E → q.E} (hin : ∀ y, proj y ∈ D)
    (hvi : ∀ y, ∀ u ∈ D, ⟪y - proj y, u - proj y⟫ ≤ 0) (x y : q.E) :
    ‖proj x - proj y‖ ≤ ‖x - y‖ := by
  have h1 := hvi x (proj y) (hin y)
  have h2 := hvi y (proj x) (hin x)
  have e : ‖proj x - proj y‖ ^ 2 ≤ ⟪x - y, proj x - proj y⟫ := by
    have : ⟪x - proj x, proj y - proj x⟫ + ⟪y - proj y, proj x - proj y⟫ =
        ⟪x - y, proj y - proj x⟫ + ‖proj x - proj y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    have h3 : ⟪x - y, proj y - proj x⟫ = -⟪x - y, proj x - proj y⟫ := by
      rw [← inner_neg_right, neg_sub]
    linarith
  have hcs := real_inner_le_norm (x - y) (proj x - proj y)
  rcases eq_or_lt_of_le (norm_nonneg (proj x - proj y)) with h | h
  · rw [← h]; exact norm_nonneg _
  · nlinarith

lemma loss_lipschitz {D : Set q.E}
    (hsub : ∀ ξ, ∀ x ∈ D, ∀ y ∈ D, I.loss x ξ + ⟪I.sub x ξ, y - x⟫ ≤ I.loss y ξ)
    (hG : ∀ ξ, ∀ x ∈ D, ‖I.sub x ξ‖ ≤ q.G) {x y : q.E} (hx : x ∈ D) (hy : y ∈ D) (ξ : q.Ξ) :
    I.loss x ξ ≤ I.loss y ξ + q.G * ‖x - y‖ := by
  have h := hsub ξ x hx y hy
  have hcs := real_inner_le_norm (I.sub x ξ) (x - y)
  have hn : ⟪I.sub x ξ, y - x⟫ = -⟪I.sub x ξ, x - y⟫ := by rw [← inner_neg_right, neg_sub]
  have := mul_le_mul_of_nonneg_right (hG ξ x hx) (norm_nonneg (x - y))
  linarith

lemma objective_lipschitz (hρ : 0 ≤ q.ρ) {D : Set q.E} (hl : Measurable (Function.uncurry I.loss))
    (hsub : ∀ ξ, ∀ x ∈ D, ∀ y ∈ D, I.loss x ξ + ⟪I.sub x ξ, y - x⟫ ≤ I.loss y ξ)
    (hG : ∀ ξ, ∀ x ∈ D, ‖I.sub x ξ‖ ≤ q.G)
    (hb : ∀ ξ, ∀ x ∈ D, 0 ≤ I.loss x ξ ∧ I.loss x ξ ≤ q.B) {x y : q.E} (hx : x ∈ D)
    (hy : y ∈ D) : objective I x ≤ objective I y + q.G * ‖x - y‖ := by
  have hlx : Measurable (I.loss x) := hl.comp (measurable_const.prodMk measurable_id)
  have hly : Measurable (I.loss y) := hl.comp (measurable_const.prodMk measurable_id)
  apply csSup_le
  · exact ⟨_, fun _ => 1, one_feasible _ hρ, rfl⟩
  · rintro v ⟨w, hw, rfl⟩
    have hix := integrable_density_mul I hw hlx (C := q.B) fun ξ => by
      rw [abs_of_nonneg (hb ξ x hx).1]; exact (hb ξ x hx).2
    have hiy := integrable_density_mul I hw hly (C := q.B) fun ξ => by
      rw [abs_of_nonneg (hb ξ y hy).1]; exact (hb ξ y hy).2
    have hwi : Integrable w (I.law : Measure q.Ξ) := Feasible.integrable _ hw
    have hmono : (∫ ξ, w ξ * I.loss x ξ ∂(I.law : Measure q.Ξ)) ≤
        ∫ ξ, w ξ * I.loss y ξ + q.G * ‖x - y‖ * w ξ ∂(I.law : Measure q.Ξ) := by
      refine integral_mono hix (hiy.add (hwi.const_mul _)) fun ξ => ?_
      have := mul_le_mul_of_nonneg_left (loss_lipschitz I hsub hG hx hy ξ) (hw.2.1 ξ)
      simp only
      linarith
    rw [integral_add hiy (hwi.const_mul _), integral_const_mul, hw.2.2.2.1, mul_one] at hmono
    have := le_objective I hρ hly (fun ξ => (hb ξ y hy).1) (fun ξ => (hb ξ y hy).2) hw
    linarith

end OracleTemplate.ChiSquareDro
