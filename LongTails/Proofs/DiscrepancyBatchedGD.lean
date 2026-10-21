import LongTails.Algorithms.DiscrepancyBatchedGD
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.GdPL

open scoped RealInnerProductSpace
open MeasureTheory
open OracleTemplate.StochasticGradient OracleTemplate.HeavyTailedMarkovGradient

namespace OracleTemplate.RelativeDiscrepancyPL

open LongTails.Setups.RelativeDiscrepancyPL

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma batch_error (g : ℕ → E → E) (v : E) (D : ℝ)
    (h : ∀ start n, ‖∑ i : Fin n, (g (start + i.val) x - v)‖ ≤ D * ‖v‖)
    (start : ℕ) :
    ‖(batchSize D : ℝ)⁻¹ • (∑ i : Fin (batchSize D), g (start + i.val) x) - v‖ ≤ ‖v‖ / 2 := by
  let B := batchSize D
  have hB : (0 : ℝ) < B := by exact_mod_cast batchSize_pos D
  have hb : 2 * D ≤ (B : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈2 * D⌉₊)
  have he : (B : ℝ)⁻¹ • (∑ i : Fin B, g (start + i.val) x) - v =
      (B : ℝ)⁻¹ • (∑ i : Fin B, (g (start + i.val) x - v)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul]
    simp [hB.ne']
  change ‖(B : ℝ)⁻¹ • (∑ i : Fin B, g (start + i.val) x) - v‖ ≤ _
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hB)]
  have hh := mul_le_mul_of_nonneg_left (h start B) (inv_nonneg.mpr hB.le)
  apply hh.trans
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ hB).mpr
  nlinarith [mul_le_mul_of_nonneg_right hb (norm_nonneg v)]

lemma inexact_descent (f : E → ℝ) {L : ℝ} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x v : E) (he : ‖v - gradient f x‖ ≤ ‖gradient f x‖ / 2) :
    f (x - (1 / L) • v) ≤ f x - 3 * ‖gradient f x‖ ^ 2 / (8 * L) := by
  have hd := Gradient.smooth_upper_bound hg hlip x (x - (1 / L) • v)
  rw [show x - (1 / L) • v - x = -(1 / L) • v by module] at hd
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_pos (one_div_pos.mpr hL), mul_pow] at hd
  have hs : ‖v - gradient f x‖ ^ 2 ≤ (‖gradient f x‖ / 2) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) he 2
  rw [norm_sub_sq_real, ← real_inner_comm v (gradient f x)] at hs
  have hid : -(1 / L) * ⟪gradient f x, v⟫ + L / 2 * ((1 / L) ^ 2 * ‖v‖ ^ 2) =
      (‖v‖ ^ 2 - 2 * ⟪gradient f x, v⟫) / (2 * L) := by field_simp; ring
  rw [add_assoc, hid] at hd
  have hquot : (‖v‖ ^ 2 - 2 * ⟪gradient f x, v⟫) / (2 * L) ≤
      -(3 * ‖gradient f x‖ ^ 2 / (8 * L)) := by
    apply (div_le_iff₀ (show 0 < 2 * L by positivity)).mpr
    field_simp
    nlinarith
  linarith

lemma advance_rate (p : Params) (f : p.E → ℝ) (g : ℕ → p.E → p.E)
    (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (herr : ∀ start n x, ‖∑ i : Fin n, (g (start + i.val) x - gradient f x)‖ ≤ p.D * ‖gradient f x‖)
    (xstar : p.E) (hgap : f p.x0 - f xstar ≤ p.Δ)
    (hpl : ∀ x, 2 * p.μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) (K : ℕ) :
    let B := batchSize p.D
    let step := fun k x => x - (1 / p.L) • ((B : ℝ)⁻¹ • ∑ i : Fin B, g (k * B + i.val) x)
    f (advance step K 0 p.x0) - f xstar ≤ (1 - (3 * p.μ / 4) / p.L) ^ K * p.Δ := by
  let B := batchSize p.D
  let step := fun k x => x - (1 / p.L) • ((B : ℝ)⁻¹ • ∑ i : Fin B, g (k * B + i.val) x)
  have hL : 0 < p.L := hμ.trans_le hμL
  have hq : 0 ≤ 1 - (3 * p.μ / 4) / p.L := by
    apply sub_nonneg.mpr
    apply (div_le_one hL).mpr
    linarith
  change f (advance step K 0 p.x0) - f xstar ≤ _
  induction K with
  | zero => simpa [advance] using hgap
  | succ K ih =>
    rw [advance_add, Nat.zero_add]
    change f (step K (advance step K 0 p.x0)) - f xstar ≤ _
    let x := advance step K 0 p.x0
    have hd := inexact_descent f hL hg hlip x
      ((B : ℝ)⁻¹ • ∑ i : Fin B, g (K * B + i.val) x)
      (batch_error g (gradient f x) p.D (fun start n => herr start n x) (K * B))
    have hp := mul_le_mul_of_nonneg_left (hpl x) (show 0 ≤ 3 / (8 * p.L) by positivity)
    have hid : (3 / (8 * p.L)) * (2 * p.μ * (f x - f xstar)) =
        ((3 * p.μ / 4) / p.L) * (f x - f xstar) := by ring
    rw [hid, show (3 / (8 * p.L)) * ‖gradient f x‖ ^ 2 =
      3 * ‖gradient f x‖ ^ 2 / (8 * p.L) by ring] at hp
    have hi := mul_le_mul_of_nonneg_left ih hq
    dsimp only [step] at ⊢
    rw [pow_succ]
    change f (x - (1 / p.L) • ((B : ℝ)⁻¹ • ∑ i : Fin B, g (K * B + i.val) x)) - f xstar ≤ _
    change (1 - (3 * p.μ / 4) / p.L) * (f x - f xstar) ≤ _ at hi
    nlinarith

lemma execute_accuracy (p : Params) (f : p.E → ℝ) (O : Oracle p.E p.E)
    (hp : spec.valid p) (ho : spec.admissible p f O)
    (ξ : (k : ℕ) → O.Seed k) (K : ℕ)
    (hiterations : ⌈(p.L / (3 * p.μ / 4)) * Real.log (1 + p.Δ / p.ε)⌉₊ ≤ K) :
    let B := max 1 ⌈2 * p.D⌉₊
    let output := execute O (batchedGD p.toPublic) (fun _ => (K * B)) () ξ
    ∃ xstar, IsMinOn f Set.univ xstar ∧ f output - f xstar ≤ p.ε := by
  rcases hp with ⟨hμ, hμL, hD, hΔ, hε⟩
  rcases ho with ⟨hg, hlip, ⟨g, hanswer, herr⟩, xstar, hmin, hgap, hpl⟩
  let B := batchSize p.D
  dsimp only
  change ∃ xstar, IsMinOn f Set.univ xstar ∧
    f (execute O (batchedGD p.toPublic) (fun _ => K * batchSize p.D) () ξ) - f xstar ≤ p.ε
  rw [execute_advance_of_answer O (batchedGD p.toPublic) (K * batchSize p.D) () ξ
    (fun k query => g k query.2) (by
      intro history query
      rcases query with ⟨i, x⟩
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact hanswer history x (ξ history.length))]
  unfold batchedGD
  have he := advance_batched (batchSize_pos p.D) (Gradient.gd (p.L, p.x0))
    (fun x _ => x) (fun _ replies => (batchSize p.D : ℝ)⁻¹ • ∑ i, replies i) 0
    (fun x k => g k x) (fun k => k) K 0 p.x0
  simp only [Nat.zero_mul] at he
  erw [he]
  refine ⟨xstar, hmin, ?_⟩
  exact (advance_rate p f g hμ hμL hg hlip herr xstar hgap hpl _).trans
    (PLGradient.geometric_budget p.L (3 * p.μ / 4) p.Δ p.ε (by positivity) (by linarith) hΔ hε K hiterations)

end OracleTemplate.RelativeDiscrepancyPL
