import LongTails.Proofs.AbcHardExecution
import LongTails.Proofs.SmoothConvexFiniteHiding
import LongTails.Proofs.FiniteSumNondualLowerBound

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.AbcHardCounting

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcChainMask
open LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging

variable {d n : ℕ} {St : Type*}

noncomputable def observation (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  if j.val < N then
    toUnit S x0 (query (simState S qf π x0 query update initial qbar ω j.val))
  else toUnit S x0 (output (simState S qf π x0 query update initial qbar ω j.val))

lemma observation_prefix (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1)) (π ρ : Fin (n + 1) ↪ Fin d)
    (h : ∀ k : Fin (n + 1), k.val < level n qbar ω j.val → π k = ρ k) :
    observation S qf x0 query output update initial qbar ω N j π =
      observation S qf x0 query output update initial qbar ω N j ρ := by
  unfold observation
  rw [simState_prefix S qf π ρ x0 query update initial qbar ω j.val h]

def coordinateBad (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits
    (largeSet (2 * radius n) (1 / 4)
      (observation S qf x0 query output update initial qbar ω N j π))
    ((List.ofFn π).drop (level n qbar ω j.val))

lemma good_small (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S qf x0 query output update initial qbar ω N π)
    (j : Fin (N + 1))
    (hj : ‖observation S qf x0 query output update initial qbar ω N j π‖ ≤ 2 * radius n)
    (i : Fin (n + 1)) (hi : level n qbar ω j.val ≤ i.val) :
    |sel π (observation S qf x0 query output update initial qbar ω N j π) i| ≤ 1 / 4 := by
  rw [sel_apply]
  apply not_largeSet_small _ _ _ hj
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ i hi h⟩

lemma bad_sum_bound (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d) :
    D * (∑ w : CoordinateWords d n, if coordinateBad S qf x0 query output update initial qbar ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (n + 1 : ℕ) * ((2 * radius n) ^ 2 / (1 / 4) ^ 2) *
        Fintype.card (CoordinateWords d n) := by
  let bad := fun π : Fin (n + 1) ↪ Fin d =>
    coordinateBad S qf x0 query output update initial qbar ω N π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (2 * radius n) (1 / 4)
          (observation S qf x0 query output update initial qbar ω N j π))
          (w.val.drop (level n qbar ω j.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro k
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) k
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (2 * radius n) (1 / 4)
      (observation S qf x0 query output update initial qbar ω N j π))
      (w.drop (level n qbar ω j.val))
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) (2 * radius n) (1 / 4) D
    (by have := radius_pos n; positivity) (by norm_num) hD hDs
    (fun j : Fin (N + 1) => level n qbar ω j.val) (fun j => level_le n qbar ω j.val)
    (observation S qf x0 query output update initial qbar ω N)
    (observation_prefix S qf x0 query output update initial qbar ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma good_gradient (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S qf x0 query output update initial qbar ω N π)
    (hlev : level n qbar ω N < n + 1)
    (hq : ∀ m, m ≤ level n qbar ω N → qf m ≤ qbar) :
    S.a / S.lam / 20 ≤
      ‖objGrad S π x0 (output (trueState S qf π x0 query update initial ω N))‖ := by
  have hhit : ∀ t < N,
      let x := query (simState S qf π x0 query update initial qbar ω t)
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), level n qbar ω t ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4 := by
    intro t ht x hx i hi
    have h := good_small S qf x0 query output update initial qbar ω N π hgood ⟨t, by omega⟩
    simp only [observation, ht, ↓reduceIte] at h
    exact h hx i hi
  rw [← coupling S qf π x0 query update initial qbar ω N hhit hq]
  have hpos : 0 ≤ S.a / S.lam := by have := S.ha; have := S.hlam; positivity
  rw [objGrad, norm_smul, Real.norm_of_nonneg hpos]
  set w := toUnit S x0 (output (simState S qf π x0 query update initial qbar ω N))
  have hR := radius_pos n
  by_cases hw : 2 * radius n < ‖w‖
  · rw [hardGrad_outside π w hw.le, wallGrad_norm]
    have : 4 ≤ 2 * ‖w‖ / radius n := by rw [le_div_iff₀ hR]; linarith
    nlinarith
  · push Not at hw
    have h := good_small S qf x0 query output update initial qbar ω N π hgood (Fin.last N)
    simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
    have hl := h hw (Fin.last n) (by simp; omega)
    have hg := hardGrad_lower π w (lt_of_le_of_lt hl (by norm_num))
    nlinarith

end LongTails.Proofs.AbcHardCounting
