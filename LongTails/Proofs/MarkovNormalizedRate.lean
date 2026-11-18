import LongTails.Setups.MarkovSmoothNonconvex
import LongTails.Proofs.MarkovBatchAlignment
import LongTails.Proofs.MarkovNormalizedDescent
import LongTails.Proofs.MixedNoiseSelectors

namespace LongTails.Proofs.MarkovBatchParameters

open Setups.MarkovSmoothNonconvex

noncomputable def epochs (p : Params) : ℕ := ⌊2048 * p.L * p.Δ / p.ε^2⌋₊
noncomputable def batch (p : Params) : ℕ := ⌊256 * p.σ^2 / p.ε^2⌋₊ + 1
noncomputable def spacing (p : Params) : ℕ := ⌊p.τ * Real.log (32 + 8192 * p.σ^2 / p.ε^2)⌋₊ + 1
noncomputable def stepSize (p : Params) : ℝ := p.ε / (128*p.L)

lemma batch_size (p : Params) (hp : spec.valid p) : 256*p.σ^2 ≤ (batch p : ℝ)*p.ε^2 := by
  apply (div_le_iff₀ (sq_pos_of_pos hp.2.1)).mp
  simpa only [batch, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one _).le

lemma epochs_size (p : Params) (hp : spec.valid p) :
    p.Δ ≤ ((epochs p+1 : ℕ) : ℝ) * stepSize p * (p.ε/16) := by
  have he := Nat.lt_floor_add_one (2048*p.L*p.Δ / p.ε^2)
  have hh := (div_lt_iff₀ (sq_pos_of_pos hp.2.1)).mp he
  change 2048*p.L*p.Δ < ((epochs p : ℝ)+1)*p.ε^2 at hh
  unfold stepSize
  push_cast
  field_simp [hp.1]
  nlinarith

lemma spacing_decay (p : Params) (hp : spec.valid p) :
    Real.exp (-(spacing p : ℝ) / p.τ) ≤ 1/(32*(batch p : ℝ)) := by
  let a := 256*p.σ^2 / p.ε^2
  let z := 32 + 8192*p.σ^2 / p.ε^2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hτ : 0 < p.τ := by linarith [hp.2.2.1]
  have hh : p.τ*Real.log z ≤ (spacing p : ℝ) := by
    simpa only [spacing, Nat.cast_add, Nat.cast_one, z] using (Nat.lt_floor_add_one (p.τ*Real.log z)).le
  have hB : (batch p : ℝ) ≤ a+1 := by
    dsimp only [batch]; push_cast; linarith [Nat.floor_le ha]
  have hb : 0 < (batch p : ℝ) := by exact_mod_cast Nat.succ_pos _
  have hBz : 32*(batch p : ℝ) ≤ z := by
    have he : z = 32*(a+1) := by dsimp [a,z]; ring
    linarith
  calc
    _ ≤ Real.exp (-Real.log z) := by apply Real.exp_le_exp.mpr; apply (div_le_iff₀ hτ).mpr; linarith
    _ = 1/z := by rw [Real.exp_neg, Real.exp_log hz, one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) hBz

lemma spacing_power (p : Params) (hp : spec.valid p) (i : ℕ) (hi : 0 < i) :
    2*Real.exp (-((i*spacing p : ℕ) : ℝ)/p.τ) ≤ (1/2 : ℝ)^i := by
  have hb : (1 : ℝ) ≤ batch p := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hh := (spacing_decay p hp).trans (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
    (by linarith : 4 ≤ 32*(batch p : ℝ)))
  have he : Real.exp (-((i*spacing p : ℕ) : ℝ)/p.τ) = (Real.exp (-(spacing p : ℝ)/p.τ))^i := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    ring
  rw [he]
  have hpow : 2*(1/4 : ℝ)^i ≤ (1/2 : ℝ)^i := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    rw [pow_succ,pow_succ]
    linarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4 : ℝ) ≤ 1/2) k]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hh i) (by norm_num)).trans hpow

end LongTails.Proofs.MarkovBatchParameters

open MeasureTheory ProbabilityTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovNormalizedRate

open Setups.MarkovSmoothNonconvex
open Setups.HeavyTailedMarkovSmoothAndConvex (pathLaw mixingDistance)
open Algorithms.MarkovNormalizedBatch MarkovNormalizedExecution MarkovNormalizedDescent
open MarkovBatchParameters MarkovBatchAlignment
open OracleTemplate.HeavyTailedMarkovGradient OracleTemplate.MixedNoise

noncomputable def algorithm (p : Params) :=
  method (stepSize p) (epochs p) (batch p) (spacing p) (Nat.succ_pos _) (Nat.succ_pos _) p.x0

lemma accuracy (p : Params) (hp : spec.valid p) (f : Space p → ℝ) (O : Oracle (Space p) (Space p))
    (ha : spec.admissible p f O) :
    spec.successful p f (fun z : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm p) (fun _ => (epochs p+1)*(batch p*spacing p)) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  obtain ⟨g,κ,hκ,π,fstar,rfl,hπ,hd,hm,hgrad,hlip,hlow,_,hgap,hg,hI,hunb,h2,hvar⟩ := ha
  let K := epochs p
  let N := K+1
  let B := batch p
  let h := spacing p
  let η := stepSize p
  have hη : 0 < η := div_pos hp.2.1 (mul_pos (by norm_num) hp.1)
  have hηL : p.L*η = p.ε/128 := by dsimp [η,stepSize]; field_simp [hp.1.ne']
  let P : Measure (ℕ → ℝ) := pathLaw κ π
  let X := output g η B h p.x0
  let G := fun j (ξ : ℕ → ℝ) => ‖gradient f (X ξ j)‖
  let A := alignmentValue (gradient f) g η B h p.x0
  have hgm := measurable_gradient_of_lipschitz hp.1.le hlip
  have hdec (i : ℕ) : (∫ z, mixingDistance κ π (i*h) z ∂(π : Measure ℝ)) ≤ (1/2 : ℝ)^i := by
    cases i with
    | zero =>
      simp only [Nat.zero_mul, pow_zero]
      simpa only [integral_const, probReal_univ, one_smul] using
        integral_mono (hd 0) (integrable_const (1 : ℝ)) (mixingDistance_le_one κ π 0)
    | succ k => exact (hm _).trans (spacing_power p hp _ (Nat.succ_pos _))
  have hsmall : (∫ z, mixingDistance κ π h z ∂(π : Measure ℝ)) ≤ 1/(16*(B : ℝ)) := by
    have hs := spacing_decay p hp
    have he : 2*(1/(32*(B : ℝ))) = 1/(16*(B : ℝ)) := by ring
    exact (hm _).trans ((mul_le_mul_of_nonneg_left hs (by norm_num)).trans_eq he)
  have hh (j : ℕ) : 7/8*(∫ ξ, G j ξ ∂P) - p.ε/4 - 16*p.L*η ≤ ∫ ξ, A j ξ ∂P :=
    batch_alignment κ π hπ hg hgm hp.1.le hη.le hp.2.1 hlip hI hunb h2 hvar B h
      (Nat.succ_pos _) (batch_size p hp) hd hdec hsmall p.x0 j
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hh j)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hdes := integrated_descent P hp.1.le hη.le hgrad hlip hgm hlow hg B h p.x0 hgap N
  change η*(∑ j ∈ Finset.range N, ∫ ξ, A j ξ ∂P) ≤ _ at hdes
  have hΔ : p.Δ ≤ (N : ℝ)*η*(p.ε/16) := epochs_size p hp
  have hbound : (∑ j ∈ Finset.range N, ∫ ξ, G j ξ ∂P) ≤ (N : ℝ)*p.ε := by
    have hc := mul_le_mul_of_nonneg_left hsum hη.le
    have hrewrite : p.L/2*η^2 = η*(p.ε/256) := by nlinarith [congrArg (· * η) hηL]
    rw [hrewrite] at hdes
    have hr : 16*p.L*η = p.ε/8 := by linarith
    rw [show 16*p.L*((N : ℝ)*η) = N*(p.ε/8) by linarith [congrArg ((N : ℝ) * ·) hr]] at hc
    apply le_of_mul_le_mul_left (a := η) _ hη
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (mul_nonneg hη.le hp.2.1.le)]
  let U := (PMF.uniformOfFintype (Fin N)).toMeasure
  let Q := U.prod P
  let Y := fun z : Fin N × (ℕ → ℝ) => G z.1.val z.2
  have hX : Measurable (fun z : Fin N × (ℕ → ℝ) => X z.2 z.1.val) := by
    apply measurable_from_prod_countable_right
    intro i
    exact measurable_output hg η B h p.x0 i.val
  have hmY : Measurable Y := (hgm.comp hX).norm
  have hY : Integrable Y Q := by
    refine Integrable.of_bound hmY.aestronglyMeasurable (‖gradient f p.x0‖+N*(p.L*η)) (.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _ : 0 ≤ Y z)]
    exact (norm_bound hp.1.le hη.le _ hlip g B h p.x0 z.1.val z.2).trans
      (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr z.1.isLt.le)
        (mul_nonneg hp.1.le hη.le)) _)
  have hEY : (∫ z, Y z ∂Q) ≤ p.ε := by
    rw [integral_prod _ hY, integral_uniform_finite, Fintype.card_fin,
      Fin.sum_univ_eq_sum_range (fun j => ∫ ξ, G j ξ ∂P)]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.succ_pos K
    rw [← div_eq_inv_mul, div_le_iff₀ hN]
    simpa [mul_comm] using hbound
  let run := fun z : Fin N × (ℕ → ℝ) => execute
      {Seed := fun _ => ℝ, law := pathLaw κ π, answer := fun _ (_, x) y => g x y}
      (algorithm p) (fun _ => (epochs p+1)*(batch p*spacing p)) z.1 z.2
  have hout : run = fun z => X z.2 z.1.val := by
    funext z
    exact execute_method _ _ _ _ _ _ _ _ _ _ _
  change Measurable run ∧ Integrable (fun z => ‖gradient f (run z)‖) Q ∧
    (∫ z, ‖gradient f (run z)‖ ∂Q) ≤ p.ε
  rw [hout]
  exact ⟨hX,hY,hEY⟩

end LongTails.Proofs.MarkovNormalizedRate
