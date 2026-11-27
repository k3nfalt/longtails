import LongTails.TemplateLowerBound
import LongTails.Proofs.SlidingLowerAdmissible
import LongTails.Proofs.SlidingLowerExecution
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingLowerFailure

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingLowerChain SlidingLowerInstance SlidingLowerOracle SlidingLowerGap SlidingLowerHiding
open SlidingLowerSim SlidingLowerExecution SlidingLowerAdmissible SlidingLowerCoins
open SoftRadialProjection QuasarCoinLaw
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerHiding FiniteSumNondualLowerBound
open Classical

variable {T : ℕ}

abbrev Alg (q : Params) := Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
  (EuclideanSpace ℝ (Fin q.d)) 2

noncomputable def excess (C : Corner T) (Q : Scale) (q : Params) (A : Alg q) (b : Fin 2 → ℕ)
    (seed : A.Seed) (π : Fin (2 * T + 1) ↪ Fin q.d) (β : ℕ → Bool) : ℝ :=
  if C.lev (simSeq (toRun A seed) C.rv (partialReply C Q q.x0) π β b (∑ i, b i)).exposure ≤ 2 * T
  then 0 else 1

lemma excess_measurable (C : Corner T) (Q : Scale) (q : Params) (A : Alg q) (b : Fin 2 → ℕ)
    (seed : A.Seed) (π : Fin (2 * T + 1) ↪ Fin q.d) :
    Measurable (excess C Q q A b seed π) :=
  measurable_of_dep (∑ i, b i) _ (fun β β' h => by
    unfold excess
    rw [simSeq_coin_dep (toRun A seed) C.rv (partialReply C Q q.x0) π β β' b _ h])

lemma excess_bounds (C : Corner T) (Q : Scale) (q : Params) (A : Alg q) (b : Fin 2 → ℕ)
    (seed : A.Seed) (π : Fin (2 * T + 1) ↪ Fin q.d) (β : ℕ → Bool) :
    0 ≤ excess C Q q A b seed π β ∧ excess C Q q A b seed π β ≤ 1 := by
  unfold excess; split_ifs <;> norm_num

noncomputable def cmin (q : Params) (Q : Scale) : ℝ :=
  min ((Q.a / Q.s) ^ 2 / (288 * q.ℓ)) (49 * q.ℓ * Q.s ^ 2 / 512)

lemma pointwise (q : Params) (Q : Scale) (hV : Valid q T Q) (hℓ : 0 < q.ℓ) (C : Corner T)
    (A : Alg q) (b : Fin 2 → ℕ) (seed : A.Seed) (β : ℕ → Bool) (π : Fin (2 * T + 1) ↪ Fin q.d) :
    cmin q Q * (1 - (if isBad C Q q.x0 (toRun A seed) β b (∑ i, b i) π then 1 else 0) -
        excess C Q q A b seed π β) ≤
      LongTails.Setups.SlidingStochasticComposite.moreauGap (hardInstance q Q π)
        (execute (hardOracle q Q hV.p_pos.le hV.p_le π) A b seed β) := by
  have hR0 := (radius_facts hV.radius).1
  have hc : 0 ≤ cmin q Q := by unfold cmin; apply le_min <;> positivity
  have h0 := moreauGap_nonneg q Q hV π (execute (hardOracle q Q hV.p_pos.le hV.p_le π) A b seed β)
  by_cases hb : isBad C Q q.x0 (toRun A seed) β b (∑ i, b i) π
  · rw [ite_eq_left hb]
    have := excess_bounds C Q q A b seed π β
    nlinarith
  · rw [ite_eq_right hb]
    by_cases hx : C.lev (simSeq (toRun A seed) C.rv (partialReply C Q q.x0) π β b
        (∑ i, b i)).exposure ≤ 2 * T
    · have he : excess C Q q A b seed π β = 0 := by unfold excess; rw [ite_eq_left hx]
      rw [he]
      have hsmall := output_small C Q hR0 q.x0 (toRun A seed) β b (∑ i, b i) π hb hx
      have hexec := execute_trueSeq (hardOracle q Q hV.p_pos.le hV.p_le π) A b seed β β
        (fun π b q' => trueReply Q q.x0 π b q') π (answer_eq q Q hV π β)
      rw [hexec]
      have hg := gap_lower hV.a_nonneg hV.s_pos hV.radius hV.smooth hℓ π q.x0 _ hsmall
      unfold LongTails.Setups.SlidingStochasticComposite.moreauGap
        LongTails.Setups.SlidingStochasticComposite.objective
      simp only [sub_zero, mul_one]
      exact hg
    · have he : excess C Q q A b seed π β = 1 := by unfold excess; rw [ite_eq_right hx]
      rw [he]
      nlinarith

lemma bad_fraction (q : Params) (Q : Scale) (hR : 0 < Q.R) (C : Corner T) (A : Alg q)
    (b : Fin 2 → ℕ) (seed : A.Seed) (β : ℕ → Bool)
    (hdim : 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (2 * T + 1 : ℕ) * (64 * Q.R ^ 2) + (2 * T + 1 : ℕ)
      ≤ q.d) :
    8 * (∑ w : CoordinateWords q.d (2 * T),
      if isBad C Q q.x0 (toRun A seed) β b (∑ i, b i) (coordinateEmbedding w) then (1 : ℝ) else 0)
      ≤ Fintype.card (CoordinateWords q.d (2 * T)) := by
  set N := ∑ i, b i
  set D : ℝ := 16 * ((N : ℝ) + 1) * (2 * T + 1 : ℕ) * (64 * Q.R ^ 2)
  have hD0 : 0 ≤ D := by positivity
  have h := bad_count C Q hR q.x0 (toRun A seed) β b N D hD0 hdim
  have he : (∑ w : CoordinateWords q.d (2 * T),
      if isBad C Q q.x0 (toRun A seed) β b N (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (2 * T + 1) (Finset.univ : Finset (Fin q.d))).filter
        (fun w => ∃ π : Fin (2 * T + 1) ↪ Fin q.d, List.ofFn π = w ∧
          isBad C Q q.x0 (toRun A seed) β b N π)).card : ℝ) := by
    have hiff (w : CoordinateWords q.d (2 * T)) :
        isBad C Q q.x0 (toRun A seed) β b N (coordinateEmbedding w) ↔
        ∃ π : Fin (2 * T + 1) ↪ Fin q.d, List.ofFn π = w.val ∧
          isBad C Q q.x0 (toRun A seed) β b N π := by
      constructor
      · intro hw
        exact ⟨coordinateEmbedding w, coordinateEmbedding_labels w, hw⟩
      · rintro ⟨π, hπ, hw⟩
        have hp : π = coordinateEmbedding w := by
          apply Function.Embedding.ext
          intro i
          exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) i
        rwa [← hp]
    rw [Finset.sum_congr rfl (fun w _ => if_congr (hiff w) rfl rfl)]
    convert subtype_indicator_sum (distinctWords (2 * T + 1) (Finset.univ : Finset (Fin q.d)))
      (fun w => ∃ π : Fin (2 * T + 1) ↪ Fin q.d, List.ofFn π = w ∧
        isBad C Q q.x0 (toRun A seed) β b N π)
  rw [he]
  have hcard : (Fintype.card (CoordinateWords q.d (2 * T)) : ℝ) =
      (distinctWords (2 * T + 1) (Finset.univ : Finset (Fin q.d))).card := by
    simp [CoordinateWords]
  rw [hcard]
  have hpos : 0 < 2 * ((N : ℝ) + 1) * (2 * T + 1 : ℕ) * (Q.R ^ 2 / (1 / 8) ^ 2) := by positivity
  have hDe : D = 8 * (2 * ((N : ℝ) + 1) * (2 * T + 1 : ℕ) * (Q.R ^ 2 / (1 / 8) ^ 2)) := by
    simp only [D]; ring
  rw [hDe] at h
  have h2 := (mul_le_mul_iff_right₀ hpos).mp (by linarith [h] :
    2 * ((N : ℝ) + 1) * (2 * T + 1 : ℕ) * (Q.R ^ 2 / (1 / 8) ^ 2) *
      (8 * (((distinctWords (2 * T + 1) (Finset.univ : Finset (Fin q.d))).filter
        (fun w => ∃ π : Fin (2 * T + 1) ↪ Fin q.d, List.ofFn π = w ∧
          isBad C Q q.x0 (toRun A seed) β b N π)).card : ℝ)) ≤
      2 * ((N : ℝ) + 1) * (2 * T + 1 : ℕ) * (Q.R ^ 2 / (1 / 8) ^ 2) *
        (distinctWords (2 * T + 1) (Finset.univ : Finset (Fin q.d))).card)
  exact h2

lemma sum_lower (q : Params) (Q : Scale) (hV : Valid q T Q) (hℓ : 0 < q.ℓ) (C : Corner T)
    (A : Alg q) (b : Fin 2 → ℕ) (seed : A.Seed) (β : ℕ → Bool)
    (hdim : 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (2 * T + 1 : ℕ) * (64 * Q.R ^ 2) + (2 * T + 1 : ℕ)
      ≤ q.d) :
    cmin q Q * ((7 / 8) * Fintype.card (CoordinateWords q.d (2 * T)) -
        ∑ w : CoordinateWords q.d (2 * T), excess C Q q A b seed (coordinateEmbedding w) β) ≤
      ∑ w : CoordinateWords q.d (2 * T),
        LongTails.Setups.SlidingStochasticComposite.moreauGap (hardInstance q Q (coordinateEmbedding w))
          (execute (hardOracle q Q hV.p_pos.le hV.p_le (coordinateEmbedding w)) A b seed β) := by
  have hR0 := (radius_facts hV.radius).1
  have hc : 0 ≤ cmin q Q := by unfold cmin; apply le_min <;> positivity
  have hp := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (CoordinateWords q.d (2 * T)))) =>
    pointwise q Q hV hℓ C A b seed β (coordinateEmbedding w))
  have hb := bad_fraction q Q hR0 C A b seed β hdim
  rw [← Finset.mul_sum] at hp
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hp
  refine le_trans ?_ hp
  apply mul_le_mul_of_nonneg_left _ hc
  linarith

lemma exists_failure (q : Params) (Q : Scale) (hV : Valid q T Q) (hℓ : 0 < q.ℓ) (C : Corner T)
    (A : Alg q) (b : Fin 2 → ℕ)
    (hdim : 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (2 * T + 1 : ℕ) * (64 * Q.R ^ 2) + (2 * T + 1 : ℕ)
      ≤ q.d)
    (hX : ∀ seed π, ∫ β, excess C Q q A b seed π β
      ∂(coinPath Q.p hV.p_pos.le hV.p_le : Measure (ℕ → Bool)) ≤ 1 / 4)
    (hacc : q.ε ^ 2 / (8 * q.ℓ) < (5 / 8) * cmin q Q) :
    ∃ π : Fin (2 * T + 1) ↪ Fin q.d,
      ¬ spec.successful q (hardInstance q Q π)
        (fun z : A.Seed × ((k : ℕ) → (hardOracle q Q hV.p_pos.le hV.p_le π).Seed k) =>
          execute (hardOracle q Q hV.p_pos.le hV.p_le π) A b z.1 z.2)
        ⟨(A.law : Measure _).prod
          ((hardOracle q Q hV.p_pos.le hV.p_le π).law : Measure _), inferInstance⟩ := by
  by_contra hfail
  push Not at hfail
  have hR0 := (radius_facts hV.radius).1
  have hc : 0 ≤ cmin q Q := by unfold cmin; apply le_min <;> positivity
  let μ : Measure A.Seed := (A.law : Measure A.Seed)
  let ν : Measure (ℕ → Bool) := (coinPath Q.p hV.p_pos.le hV.p_le : Measure (ℕ → Bool))
  let W := CoordinateWords q.d (2 * T)
  let f : W → A.Seed × (ℕ → Bool) → ℝ := fun w z =>
    LongTails.Setups.SlidingStochasticComposite.moreauGap (hardInstance q Q (coordinateEmbedding w))
      (execute (hardOracle q Q hV.p_pos.le hV.p_le (coordinateEmbedding w)) A b z.1 z.2)
  have hint (w : W) : Integrable (f w) (μ.prod ν) := (hfail (coordinateEmbedding w)).2.1
  have hbound (w : W) : (∫ z, f w z ∂(μ.prod ν)) ≤ q.ε ^ 2 / (8 * q.ℓ) :=
    (hfail (coordinateEmbedding w)).2.2
  let F : A.Seed × (ℕ → Bool) → ℝ := fun z => ∑ w, f w z
  have hF : Integrable F (μ.prod ν) := integrable_finsetSum _ (fun w _ => hint w)
  have hcard : (0 : ℝ) < Fintype.card W := by
    have hkd : 2 * T + 1 ≤ q.d := by
      have : ((2 * T + 1 : ℕ) : ℝ) ≤ q.d := by
        have : (0 : ℝ) ≤ 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (2 * T + 1 : ℕ) * (64 * Q.R ^ 2) := by
          positivity
        linarith
      exact_mod_cast this
    exact_mod_cast coordinateWords_card_pos q.d (2 * T) hkd
  have hinner : ∀ᵐ s ∂μ, (5 / 8) * cmin q Q * Fintype.card W ≤ ∫ β, F (s, β) ∂ν := by
    filter_upwards [hF.prod_right_ae] with s hs
    have hXi (w : W) : Integrable (fun β => excess C Q q A b s (coordinateEmbedding w) β) ν := by
      apply Integrable.of_bound (excess_measurable C Q q A b s _).aestronglyMeasurable 1
      filter_upwards [] with β
      have := excess_bounds C Q q A b s (coordinateEmbedding w) β
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]
      exact this.2
    have hlow : Integrable (fun β => cmin q Q * ((7 / 8) * Fintype.card W -
        ∑ w : W, excess C Q q A b s (coordinateEmbedding w) β)) ν :=
      ((integrable_const _).sub (integrable_finsetSum _ (fun w _ => hXi w))).const_mul _
    have hm := integral_mono hlow hs (fun β => sum_lower q Q hV hℓ C A b s β hdim)
    rw [integral_const_mul, integral_sub (integrable_const _)
      (integrable_finsetSum _ (fun w _ => hXi w)), integral_const,
      integral_finsetSum _ (fun w _ => hXi w)] at hm
    simp only [probReal_univ, one_smul] at hm
    have hs4 : (∑ w : W, ∫ β, excess C Q q A b s (coordinateEmbedding w) β ∂ν) ≤
        (1 / 4) * Fintype.card W := by
      have := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) =>
        hX s (coordinateEmbedding w))
      simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
    have : cmin q Q * ((5 / 8) * Fintype.card W) ≤
        cmin q Q * ((7 / 8) * Fintype.card W -
          ∑ w : W, ∫ β, excess C Q q A b s (coordinateEmbedding w) β ∂ν) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    linarith
  have hprod : (∫ z, F z ∂(μ.prod ν)) = ∫ s, ∫ β, F (s, β) ∂ν ∂μ := integral_prod F hF
  have hge : (5 / 8) * cmin q Q * Fintype.card W ≤ ∫ z, F z ∂(μ.prod ν) := by
    rw [hprod]
    have := integral_mono_ae (integrable_const ((5 / 8) * cmin q Q * Fintype.card W))
      hF.integral_prod_left hinner
    simpa [integral_const, probReal_univ] using this
  have hle : (∫ z, F z ∂(μ.prod ν)) ≤ Fintype.card W * (q.ε ^ 2 / (8 * q.ℓ)) := by
    simp only [F]
    rw [integral_finsetSum _ (fun w _ => hint w)]
    have := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hbound w)
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hstrict : Fintype.card W * (q.ε ^ 2 / (8 * q.ℓ)) <
      Fintype.card W * ((5 / 8) * cmin q Q) := mul_lt_mul_of_pos_left hacc hcard
  linarith

end LongTails.Proofs.SlidingLowerFailure
