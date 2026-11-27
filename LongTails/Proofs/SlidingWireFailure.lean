import LongTails.TemplateLowerBound
import LongTails.Proofs.SlidingWireAdmissible
import LongTails.Proofs.SlidingLowerExecution
import LongTails.Proofs.SlidingLowerAdmissible
import LongTails.Proofs.QuasarCoinLaw
import LongTails.Proofs.FiniteSumNondualLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingWireFailure

open OracleTemplate LongTails.Setups.HighDimensionalSlidingStochasticComposite
open SlidingWireChain SlidingWireSim SlidingWireGap SlidingWireAdmissible SlidingLowerOracle
open SlidingLowerSim SlidingLowerExecution SlidingLowerHiding QuasarCoinLaw SlidingLowerAdmissible
open FiniteSumNondualLowerAveraging FiniteSumNondualLowerHiding FiniteSumNondualLowerBound
open Classical

abbrev Alg (q : Params) := Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
  (EuclideanSpace ℝ (Fin q.d)) 2

noncomputable def cminB (W : WScale) : ℝ :=
  min ((W.a / W.s) ^ 2 / (819200 * W.ℓ)) (49 * W.ℓ * W.s ^ 2 / 128)

lemma pointwiseB (q : Params) (T : ℕ) (W : WScale) (hV : WVal q T W)
    (hW : WValid W (T * (W.r ^ 2 + 2))) (A : Alg q) (b : Fin 2 → ℕ) (hb : b 1 ≤ T * (W.r ^ 2 + 2))
    (seed : A.Seed) (β : ℕ → Bool) (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d) :
    cminB W * (1 - (if isBadB W q.x0 (toRun A seed) β b (∑ i, b i) π then 1 else 0)) ≤
      LongTails.Setups.SlidingStochasticComposite.moreauGap (wireInstance q W π)
        (execute (wireOracle q W π) A b seed β) := by
  have hG := hV.gap
  have hc : 0 ≤ cminB W := by
    unfold cminB; apply le_min
    · have := hG.ℓ_pos; positivity
    · have := hG.ℓ_pos; positivity
  have h0 : 0 ≤ LongTails.Setups.SlidingStochasticComposite.moreauGap (wireInstance q W π)
      (execute (wireOracle q W π) A b seed β) := by
    apply moreauGap_nonneg_of_lower q _ (-(W.a * (4 + 4 * (T : ℝ)))) (by
      rw [← hV.ell]; exact hG.ℓ_pos.le)
    intro y
    change -(W.a * (4 + 4 * (T : ℝ))) ≤ fB q.ℓ y + hB W.a W.s q.ℓ W.r W.δ W.R W.Λ π q.x0 y
    rw [← hV.ell, F_eq]
    have hR0 : 0 < W.R := by linarith [hG.R_one]
    have := wF_lower W.r (δ := W.δ) hR0 hG.Λ_ge π (rescale W.s q.x0 y)
    nlinarith [hG.a_nonneg]
  by_cases hbad : isBadB W q.x0 (toRun A seed) β b (∑ i, b i) π
  · rw [ite_eq_left hbad]; nlinarith
  · rw [ite_eq_right hbad, sub_zero, mul_one]
    have hlev : levB (T * (W.r ^ 2 + 2))
        (simSeq (toRun A seed) rvB (partialB W q.x0) π β b (∑ i, b i)).exposure ≤
          T * (W.r ^ 2 + 2) := by
      have := exposure_leB (toRun A seed) W q.x0 π β b (∑ i, b i)
      unfold levB; omega
    have hsmall := output_smallB W hW q.x0 (toRun A seed) β b (∑ i, b i) π hbad hlev
    have hexec := execute_trueSeq (wireOracle q W π) A b seed β β
      (fun π b q' => trueB W q.x0 π b q') π (answer_eqB q T W hV π β)
    rw [hexec]
    have hg := gap_lowerB W hG π q.x0 _ hsmall
    unfold LongTails.Setups.SlidingStochasticComposite.moreauGap
      LongTails.Setups.SlidingStochasticComposite.objective
    unfold cminB
    rw [hV.ell] at hg ⊢
    exact hg


lemma bad_fractionB (q : Params) (T : ℕ) (W : WScale) (hW : WValid W (T * (W.r ^ 2 + 2)))
    (A : Alg q) (b : Fin 2 → ℕ) (seed : A.Seed) (β : ℕ → Bool)
    (hdim : 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (T * (W.r ^ 2 + 2) + 1 : ℕ) * ((6 * W.R) ^ 2 / W.θ ^ 2) +
      (T * (W.r ^ 2 + 2) + 1 : ℕ) ≤ q.d) :
    8 * (∑ w : CoordinateWords q.d (T * (W.r ^ 2 + 2)),
      if isBadB W q.x0 (toRun A seed) β b (∑ i, b i) (coordinateEmbedding w) then (1 : ℝ) else 0)
      ≤ Fintype.card (CoordinateWords q.d (T * (W.r ^ 2 + 2))) := by
  set K := T * (W.r ^ 2 + 2)
  set N := ∑ i, b i
  set D : ℝ := 16 * ((N : ℝ) + 1) * (K + 1 : ℕ) * ((6 * W.R) ^ 2 / W.θ ^ 2)
  have hθ := hW.θ_pos
  have hD0 : 0 ≤ D := by positivity
  have h := bad_countB W hW q.x0 (toRun A seed) β b N D hD0 hdim
  have he : (∑ w : CoordinateWords q.d K,
      if isBadB W q.x0 (toRun A seed) β b N (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (K + 1) (Finset.univ : Finset (Fin q.d))).filter
        (fun w => ∃ π : Fin (K + 1) ↪ Fin q.d, List.ofFn π = w ∧
          isBadB W q.x0 (toRun A seed) β b N π)).card : ℝ) := by
    have hiff (w : CoordinateWords q.d K) :
        isBadB W q.x0 (toRun A seed) β b N (coordinateEmbedding w) ↔
        ∃ π : Fin (K + 1) ↪ Fin q.d, List.ofFn π = w.val ∧
          isBadB W q.x0 (toRun A seed) β b N π := by
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
    convert subtype_indicator_sum (distinctWords (K + 1) (Finset.univ : Finset (Fin q.d)))
      (fun w => ∃ π : Fin (K + 1) ↪ Fin q.d, List.ofFn π = w ∧
        isBadB W q.x0 (toRun A seed) β b N π)
  rw [he]
  have hcard : (Fintype.card (CoordinateWords q.d K) : ℝ) =
      (distinctWords (K + 1) (Finset.univ : Finset (Fin q.d))).card := by
    simp [CoordinateWords]
  rw [hcard]
  have hpos : 0 < 2 * ((N : ℝ) + 1) * (K + 1 : ℕ) * ((6 * W.R) ^ 2 / W.θ ^ 2) := by
    have := hW.R_pos; positivity
  have hDe : D = 8 * (2 * ((N : ℝ) + 1) * (K + 1 : ℕ) * ((6 * W.R) ^ 2 / W.θ ^ 2)) := by
    simp only [D]; ring
  rw [hDe] at h
  exact (mul_le_mul_iff_right₀ hpos).mp (by linarith [h])

lemma exists_failureB (q : Params) (T : ℕ) (W : WScale) (hV : WVal q T W)
    (hW : WValid W (T * (W.r ^ 2 + 2))) (A : Alg q) (b : Fin 2 → ℕ) (hb : b 1 ≤ T * (W.r ^ 2 + 2))
    (hdim : 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (T * (W.r ^ 2 + 2) + 1 : ℕ) * ((6 * W.R) ^ 2 / W.θ ^ 2) +
      (T * (W.r ^ 2 + 2) + 1 : ℕ) ≤ q.d)
    (hacc : q.ε ^ 2 / (8 * q.ℓ) < (7 / 8) * cminB W) :
    ∃ π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin q.d,
      ¬ spec.successful q (wireInstance q W π)
        (fun z : A.Seed × ((k : ℕ) → (wireOracle q W π).Seed k) =>
          execute (wireOracle q W π) A b z.1 z.2)
        ⟨(A.law : Measure _).prod ((wireOracle q W π).law : Measure _), inferInstance⟩ := by
  by_contra hfail
  push Not at hfail
  have hG := hV.gap
  have hc : 0 ≤ cminB W := by
    unfold cminB; apply le_min
    · have := hG.ℓ_pos; positivity
    · have := hG.ℓ_pos; positivity
  let μ : Measure A.Seed := (A.law : Measure A.Seed)
  let ν : Measure (ℕ → Bool) := (coinPath 1 zero_le_one le_rfl : Measure (ℕ → Bool))
  let Wd := CoordinateWords q.d (T * (W.r ^ 2 + 2))
  let f : Wd → A.Seed × (ℕ → Bool) → ℝ := fun w z =>
    LongTails.Setups.SlidingStochasticComposite.moreauGap (wireInstance q W (coordinateEmbedding w))
      (execute (wireOracle q W (coordinateEmbedding w)) A b z.1 z.2)
  have hint (w : Wd) : Integrable (f w) (μ.prod ν) := (hfail (coordinateEmbedding w)).2.1
  have hbound (w : Wd) : (∫ z, f w z ∂(μ.prod ν)) ≤ q.ε ^ 2 / (8 * q.ℓ) :=
    (hfail (coordinateEmbedding w)).2.2
  let F : A.Seed × (ℕ → Bool) → ℝ := fun z => ∑ w, f w z
  have hF : Integrable F (μ.prod ν) := integrable_finsetSum _ (fun w _ => hint w)
  have hcard : (0 : ℝ) < Fintype.card Wd := by
    have hkd : T * (W.r ^ 2 + 2) + 1 ≤ q.d := by
      have : ((T * (W.r ^ 2 + 2) + 1 : ℕ) : ℝ) ≤ q.d := by
        have : (0 : ℝ) ≤ 16 * (((∑ i, b i : ℕ) : ℝ) + 1) * (T * (W.r ^ 2 + 2) + 1 : ℕ) *
            ((6 * W.R) ^ 2 / W.θ ^ 2) := by have := hW.θ_pos; positivity
        linarith
      exact_mod_cast this
    exact_mod_cast coordinateWords_card_pos q.d (T * (W.r ^ 2 + 2)) hkd
  have hpt : ∀ z : A.Seed × (ℕ → Bool), (7 / 8) * cminB W * Fintype.card Wd ≤ F z := by
    intro z
    have hp := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset Wd)) =>
      pointwiseB q T W hV hW A b hb z.1 z.2 (coordinateEmbedding w))
    have hbf := bad_fractionB q T W hW A b z.1 z.2 hdim
    rw [← Finset.mul_sum] at hp
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hp
    have : cminB W * ((7 / 8) * Fintype.card Wd) ≤ cminB W * ((Fintype.card Wd : ℝ) -
        ∑ w : Wd, (if isBadB W q.x0 (toRun A z.1) z.2 b (∑ i, b i) (coordinateEmbedding w)
          then (1 : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_left (by linarith) hc
    simp only [F, f]
    linarith
  have hge : (7 / 8) * cminB W * Fintype.card Wd ≤ ∫ z, F z ∂(μ.prod ν) := by
    have := integral_mono (integrable_const ((7 / 8) * cminB W * Fintype.card Wd)) hF hpt
    simpa [integral_const, probReal_univ] using this
  have hle : (∫ z, F z ∂(μ.prod ν)) ≤ Fintype.card Wd * (q.ε ^ 2 / (8 * q.ℓ)) := by
    simp only [F]
    rw [integral_finsetSum _ (fun w _ => hint w)]
    have := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset Wd)) => hbound w)
    simpa [Finset.sum_const, Finset.card_univ] using this
  have hstrict : Fintype.card Wd * (q.ε ^ 2 / (8 * q.ℓ)) <
      Fintype.card Wd * ((7 / 8) * cminB W) := mul_lt_mul_of_pos_left hacc hcard
  linarith

end LongTails.Proofs.SlidingWireFailure
