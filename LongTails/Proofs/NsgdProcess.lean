import LongTails.Proofs.SeparationTrajectory
import LongTails.Proofs.GaussianStep
import LongTails.Proofs.GaussianLinear

namespace LongTails.Proofs.NsgdProcess

open MeasureTheory ProbabilityTheory
open LongTails.Proofs.SeparationInstance LongTails.Proofs.SeparationTrajectory
open LongTails.Proofs.GaussianBlocks LongTails.Proofs.GaussianStep LongTails.Proofs.GaussianFacts
open scoped NNReal

variable (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (B : ℕ)

noncomputable def state (ξ : ℕ → ℝ) (t : ℕ) : ℝ × ℝ := nsgdScalar r ℓ c s η φ B ξ t

noncomputable def beta (y : ℝ) : ℝ := Real.sqrt (r - 1 : ℕ) * |c * φ.slope y|

noncomputable def drive (p : ℝ × ℝ) (z : ℝ) : ℝ := ℓ * p.1 + s * z

lemma state_succ (ξ : ℕ → ℝ) (t : ℕ) :
    state r ℓ c s η φ B ξ (t + 1) =
      ((state r ℓ c s η φ B ξ t).1 -
          η * step (beta r c φ (state r ℓ c s η φ B ξ t).2)
            (drive ℓ s (state r ℓ c s η φ B ξ t) (blockMean B t ξ)),
        (state r ℓ c s η φ B ξ t).2 -
          η * (c * φ.slope (state r ℓ c s η φ B ξ t).2 /
            Real.sqrt (drive ℓ s (state r ℓ c s η φ B ξ t) (blockMean B t ξ) ^ 2 +
              beta r c φ (state r ℓ c s η φ B ξ t).2 ^ 2))) := by
  have hb : beta r c φ (nsgdScalar r ℓ c s η φ B ξ t).2 ^ 2 =
      (r - 1 : ℕ) * (c * φ.slope (nsgdScalar r ℓ c s η φ B ξ t).2) ^ 2 := by
    rw [beta, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), sq_abs]
  simp only [state, nsgdScalar, step, drive]
  rw [hb]

lemma state_local (ξ ξ' : ℕ → ℝ) (t : ℕ) (h : ∀ k < B * t, ξ k = ξ' k) :
    state r ℓ c s η φ B ξ t = state r ℓ c s η φ B ξ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have h' : ∀ k < B * t, ξ k = ξ' k := fun k hk =>
        h k (lt_of_lt_of_le hk (Nat.mul_le_mul_left B (Nat.le_succ t)))
      have hm : blockMean B t ξ = blockMean B t ξ' := by
        unfold blockMean
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        apply h
        have := Finset.mem_range.mp hj
        rw [Nat.mul_succ]
        omega
      rw [state_succ, state_succ, ih h', hm]

lemma measurable_state (t : ℕ) : Measurable (fun ξ => state r ℓ c s η φ B ξ t) := by
  have hslope : Measurable φ.slope := φ.continuous_slope.measurable
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      simp only [state, nsgdScalar]
      have hm := measurable_blockMean B t
      change Measurable (fun ξ => ((state r ℓ c s η φ B ξ t).1 - _, (state r ℓ c s η φ B ξ t).2 - _))
      apply Measurable.prodMk
      · exact ih.fst.sub (measurable_const.mul (((measurable_const.mul ih.fst).add
          (measurable_const.mul hm)).div (((measurable_const.mul ih.fst).add
          (measurable_const.mul hm)).pow_const 2 |>.add (measurable_const.mul
          ((measurable_const.mul (hslope.comp ih.snd)).pow_const 2))).sqrt))
      · exact ih.snd.sub (measurable_const.mul ((measurable_const.mul (hslope.comp ih.snd)).div
          (((measurable_const.mul ih.fst).add (measurable_const.mul hm)).pow_const 2 |>.add
          (measurable_const.mul ((measurable_const.mul (hslope.comp ih.snd)).pow_const 2))).sqrt))

noncomputable def ext (n : ℕ) (p : Fin n → ℝ) : ℕ → ℝ :=
  fun k => if h : k < n then p ⟨k, h⟩ else 0

lemma measurable_ext (n : ℕ) : Measurable (ext n) := by
  apply Measurable.of_eval
  intro k
  unfold ext
  by_cases h : k < n
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

lemma ext_agree (n : ℕ) (ξ : ℕ → ℝ) : ∀ k < n, ext n (fun i : Fin n => ξ i) k = ξ k := by
  intro k hk
  simp [ext, hk]

def Local (n : ℕ) (G : (ℕ → ℝ) → ℝ) : Prop := ∀ ξ ξ', (∀ k < n, ξ k = ξ' k) → G ξ = G ξ'

lemma condition {B : ℕ} (hB : 0 < B) (t : ℕ) {G : (ℕ → ℝ) → ℝ} (hloc : Local (B * t) G)
    (hGm : Measurable G) {CG : ℝ} (hGb : ∀ ξ, |G ξ| ≤ CG)
    {Φ : ℝ × ℝ → ℝ → ℝ} (hΦm : Measurable (Function.uncurry Φ)) {CΦ : ℝ}
    (hΦb : ∀ p z, |Φ p z| ≤ CΦ) :
    (∫ ξ, G ξ * Φ (state r ℓ c s η φ B ξ t) (blockMean B t ξ) ∂stdStream) =
      ∫ ξ, G ξ * ∫ z, Φ (state r ℓ c s η φ B ξ t) z ∂gaussianReal 0 (1 / (B : ℝ≥0)) ∂stdStream := by
  set n := B * t
  set ν := gaussianReal 0 (1 / (B : ℝ≥0))
  set π := Measure.pi fun _ : Fin n => gaussianReal 0 1
  have hS := measurable_state r ℓ c s η φ B t
  let Gp := fun p : Fin n → ℝ => G (ext n p)
  let Sp := fun p : Fin n → ℝ => state r ℓ c s η φ B (ext n p) t
  have hGp : Measurable Gp := hGm.comp (measurable_ext n)
  have hSp : Measurable Sp := hS.comp (measurable_ext n)
  have hagreeG (ξ : ℕ → ℝ) : Gp (fun i : Fin n => ξ i) = G ξ := hloc _ _ (ext_agree n ξ)
  have hagreeS (ξ : ℕ → ℝ) : Sp (fun i : Fin n => ξ i) = state r ℓ c s η φ B ξ t :=
    state_local r ℓ c s η φ B _ _ t (ext_agree n ξ)
  let F := fun q : (Fin n → ℝ) × ℝ => Gp q.1 * Φ (Sp q.1) q.2
  have hFm : Measurable F := (hGp.comp measurable_fst).mul
    (hΦm.comp ((hSp.comp measurable_fst).prodMk measurable_snd))
  have hFi : Integrable F (π.prod ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable (CG * CΦ)
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGb (ext n q.1)) (hΦb (Sp q.1) q.2) (abs_nonneg _)
        ((abs_nonneg _).trans (hGb (ext n q.1)))
  let Ψ := fun p : ℝ × ℝ => ∫ z, Φ p z ∂ν
  have hΨm : Measurable Ψ := hΦm.stronglyMeasurable.integral_prod_right'.measurable
  have hΨb (p : ℝ × ℝ) : |Ψ p| ≤ CΦ := by
    have h := norm_integral_le_of_norm_le_const (μ := ν) (C := CΦ)
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hΦb p z)
    simpa [Real.norm_eq_abs, Ψ] using h
  let F' := fun q : (Fin n → ℝ) × ℝ => Gp q.1 * Ψ (Sp q.1)
  have hF'm : Measurable F' := (hGp.comp measurable_fst).mul (hΨm.comp (hSp.comp measurable_fst))
  have hF'i : Integrable F' (π.prod ν) := by
    apply Integrable.of_bound hF'm.aestronglyMeasurable (CG * CΦ)
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hGb (ext n q.1)) (hΨb (Sp q.1)) (abs_nonneg _)
        ((abs_nonneg _).trans (hGb (ext n q.1)))
  have h1 := freeze hB t hFi
  have h2 := freeze hB t hF'i
  have hl : (∫ ξ, G ξ * Φ (state r ℓ c s η φ B ξ t) (blockMean B t ξ) ∂stdStream) =
      ∫ ξ, F ((fun i : Fin n => ξ i), blockMean B t ξ) ∂stdStream := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by simp only [F, hagreeG, hagreeS]
  have hr : (∫ ξ, G ξ * ∫ z, Φ (state r ℓ c s η φ B ξ t) z ∂ν ∂stdStream) =
      ∫ ξ, F' ((fun i : Fin n => ξ i), blockMean B t ξ) ∂stdStream := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by simp only [F', Ψ, hagreeG, hagreeS]
  rw [hl, hr, h1, h2]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp only [F, F', Ψ]
    rw [integral_const_mul, integral_const, probReal_univ, one_smul]

lemma noise_scale {B : ℕ} (hB : 0 < B) {s : ℝ} (hs : 0 < s) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ z, f (s * z) ∂gaussianReal 0 (1 / (B : ℝ≥0))) =
      ∫ y, f y ∂gaussianReal 0 (s ^ 2 / B).toNNReal := by
  have hmap : (gaussianReal 0 (1 / (B : ℝ≥0))).map (fun z => s * z) =
      gaussianReal 0 (s ^ 2 / B).toNNReal := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.coe_toNNReal', div_eq_mul_inv]
      positivity
  rw [← hmap, integral_map (by fun_prop) hf.aestronglyMeasurable]

end LongTails.Proofs.NsgdProcess
