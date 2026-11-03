import LongTails.Proofs.FiniteSumNondualLowerHiding
import LongTails.Proofs.FiniteSumNondualLowerSimulation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.FiniteSumNondualLowerExposure

open FiniteSumNondualLowerHiding Classical

variable {ι : Type*} [DecidableEq ι] {K : ℕ} {C : ℝ}

omit [DecidableEq ι] in
lemma prefix_agree (π ρ : Fin K ↪ ι) (p : List ι)
    (hπ : p <+: List.ofFn π) (hρ : p <+: List.ofFn ρ)
    (j : Fin K) (hj : j.val < p.length) : π j = ρ j := by
  have he := (hπ.getElem hj).symm.trans (hρ.getElem hj)
  simpa using he

noncomputable def prefixTree (F : (Fin K ↪ ι) → ℕ × Finset ι)
    (hB : ∀ π, ((F π).2.card : ℝ) ≤ C) (hC : 0 ≤ C) : ℕ → List ι → ExposureTree ι C
  | 0, _ => .leaf ∅ (by simpa using hC)
  | fuel + 1, p =>
    if h : ∃ π : Fin K ↪ ι, p <+: List.ofFn π then
      let π := Classical.choose h
      if (F π).1 ≤ p.length then .leaf (F π).2 (hB π)
      else .reveal (fun i => prefixTree F hB hC fuel (p ++ [i]))
    else .leaf ∅ (by simpa using hC)

lemma prefixTree_correct (F : (Fin K ↪ ι) → ℕ × Finset ι)
    (hB : ∀ π, ((F π).2.card : ℝ) ≤ C) (hC : 0 ≤ C)
    (hK : ∀ π, (F π).1 ≤ K)
    (hF : ∀ π ρ, (∀ j : Fin K, j.val < (F π).1 → π j = ρ j) → F π = F ρ)
    (fuel : ℕ) (p w : List ι) (π : Fin K ↪ ι)
    (hp : p ++ w = List.ofFn π) (hw : w.length ≤ fuel) :
    exposedBad (prefixTree F hB hC fuel p) w =
      decide (0 < hits (F π).2 (w.drop ((F π).1 - p.length))) := by
  classical
  induction fuel generalizing p w with
  | zero =>
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    simp [prefixTree, exposedBad, hits]
  | succ fuel ih =>
    have hπ : p <+: List.ofFn π := ⟨w, hp⟩
    have hex : ∃ ρ : Fin K ↪ ι, p <+: List.ofFn ρ := ⟨π, hπ⟩
    let ρ : Fin K ↪ ι := Classical.choose hex
    have hρ : p <+: List.ofFn ρ := Classical.choose_spec hex
    rw [prefixTree, dite_eq_left hex]
    change exposedBad (if (F ρ).1 ≤ p.length then _ else _) w = _
    by_cases hr : (F ρ).1 ≤ p.length
    · have he : F ρ = F π := hF ρ π (fun j hj =>
        prefix_agree ρ π p hρ hπ j (hj.trans_le hr))
      have hrπ : (F π).1 ≤ p.length := by simpa [he] using hr
      rw [ite_eq_left hr]
      change decide (0 < hits (F ρ).2 w) = _
      simp [he, Nat.sub_eq_zero_of_le hrπ]
    · have hrπ : p.length < (F π).1 := by
        by_contra hn
        have hh : (F π).1 ≤ p.length := by omega
        have he : F π = F ρ := hF π ρ (fun j hj =>
          prefix_agree π ρ p hπ hρ j (hj.trans_le hh))
        exact hr (by simpa [← he] using hh)
      rw [ite_eq_right hr]
      cases w with
      | nil =>
        have hl := congrArg List.length hp
        simp only [List.append_nil, List.length_ofFn] at hl
        have := hK π
        omega
      | cons i w =>
        rw [exposedBad]
        have hp' : (p ++ [i]) ++ w = List.ofFn π := by simpa using hp
        have hw' : w.length ≤ fuel := by simp only [List.length_cons] at hw; omega
        rw [ih (p ++ [i]) w hp' hw']
        have he : (F π).1 - p.length = ((F π).1 - (p ++ [i]).length) + 1 := by
          simp only [List.length_append, List.length_singleton]
          omega
        rw [he, List.drop_succ_cons]

def wordEmbedding (w : List ι) (hw : w.length = K) (hn : w.Nodup) : Fin K ↪ ι where
  toFun j := w[j.val]'(by omega)
  inj' := by
    intro i j hij
    apply Fin.ext
    exact hn.eq_of_getElem_eq (by omega) (by omega) hij

omit [DecidableEq ι] in
lemma wordEmbedding_ofFn (w : List ι) (hw : w.length = K) (hn : w.Nodup) :
    List.ofFn (wordEmbedding w hw hn) = w := by
  apply List.ext_getElem
  · simpa using hw.symm
  · intro j hj hwj
    simp only [List.getElem_ofFn]
    rfl

lemma prefixTree_empty_correct (F : (Fin K ↪ ι) → ℕ × Finset ι)
    (hB : ∀ π, ((F π).2.card : ℝ) ≤ C) (hC : 0 ≤ C)
    (hK : ∀ π, (F π).1 ≤ K)
    (hF : ∀ π ρ, (∀ j : Fin K, j.val < (F π).1 → π j = ρ j) → F π = F ρ)
    (π : Fin K ↪ ι) :
    exposedBad (prefixTree F hB hC K []) (List.ofFn π) =
      decide (0 < hits (F π).2 ((List.ofFn π).drop (F π).1)) := by
  simpa using prefixTree_correct F hB hC hK hF K [] (List.ofFn π) π (by simp) (by simp)

lemma prefix_bad_count_bound (F : (Fin K ↪ ι) → ℕ × Finset ι)
    (hB : ∀ π, ((F π).2.card : ℝ) ≤ C) (hC : 0 ≤ C)
    (hK : ∀ π, (F π).1 ≤ K)
    (hF : ∀ π ρ, (∀ j : Fin K, j.val < (F π).1 → π j = ρ j) → F π = F ρ)
    (s : Finset ι) (D : ℝ) (hD : 0 ≤ D) (hDs : D + K ≤ s.card) :
    D * (((distinctWords K s).filter (fun w => ∃ π : Fin K ↪ ι,
      List.ofFn π = w ∧ 0 < hits (F π).2 (w.drop (F π).1))).card : ℝ) ≤
      (K : ℝ) * C * (distinctWords K s).card := by
  classical
  have he : (distinctWords K s).filter (fun w => ∃ π : Fin K ↪ ι,
      List.ofFn π = w ∧ 0 < hits (F π).2 (w.drop (F π).1)) =
      (distinctWords K s).filter (fun w => exposedBad (prefixTree F hB hC K []) w) := by
    apply Finset.filter_congr
    intro w hw
    constructor
    · rintro ⟨π, rfl, hπ⟩
      rw [prefixTree_empty_correct F hB hC hK hF π]
      simpa using hπ
    · intro h
      have hm := (mem_distinctWords K s w).mp hw
      let π := wordEmbedding w hm.1 hm.2.1
      have hπ : List.ofFn π = w := wordEmbedding_ofFn w hm.1 hm.2.1
      refine ⟨π, hπ, ?_⟩
      rw [← hπ, prefixTree_empty_correct F hB hC hK hF π] at h
      simpa [hπ] using h
  rw [he]
  exact tree_bad_count_bound (prefixTree F hB hC K []) hC K s D hD hDs

omit [DecidableEq ι] in
lemma coordinate_mem_drop (π : Fin K ↪ ι) (r : ℕ) (j : Fin K) (hj : r ≤ j.val) :
    π j ∈ (List.ofFn π).drop r := by
  have hi : j.val - r < ((List.ofFn π).drop r).length := by
    simp only [List.length_drop, List.length_ofFn]
    have := j.isLt
    omega
  have hm := List.getElem_mem hi
  convert hm using 1
  simp only [List.getElem_drop, List.getElem_ofFn]
  congr 1
  apply Fin.ext
  change j.val = r + (j.val - r)
  omega

lemma hits_drop_positive (π : Fin K ↪ ι) (r : ℕ) (B : Finset ι)
    (j : Fin K) (hj : r ≤ j.val) (hB : π j ∈ B) :
    0 < hits B ((List.ofFn π).drop r) := by
  apply List.countP_pos_iff.mpr
  exact ⟨π j, coordinate_mem_drop π r j hj, by simpa using hB⟩

open FiniteSumNondualLowerSimulation FiniteSumNondualLowerGeometry

noncomputable def observedPrefix {d k n : ℕ} {S : Type*} (L δ a θ : ℝ)
    (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (observe : S → EuclideanSpace ℝ (Fin d)) (T : ℕ) (π : Fin (k + 1) ↪ Fin d) :
    ℕ × Finset (Fin d) :=
  let state := simulatedState L δ a π owner query update initial T
  (state.2 + 1, Finset.univ.filter (fun i => θ < |observe state.1 i|))

lemma observedPrefix_bound {d k n : ℕ} {S : Type*} (L δ a θ R : ℝ) (hθ : 0 < θ)
    (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (observe : S → EuclideanSpace ℝ (Fin d))
    (hobs : ∀ s, ∑ i, |observe s i| ≤ R) (T : ℕ) (π : Fin (k + 1) ↪ Fin d) :
    ((observedPrefix L δ a θ owner query update initial observe T π).2.card : ℝ) ≤ R / θ := by
  apply (le_div_iff₀ hθ).mpr
  exact large_coordinates _ θ R (hobs _)

lemma observedPrefix_count {d k n : ℕ} {S : Type*} (L δ a θ : ℝ)
    (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (observe : S → EuclideanSpace ℝ (Fin d)) (T : ℕ) (π : Fin (k + 1) ↪ Fin d) :
    (observedPrefix L δ a θ owner query update initial observe T π).1 ≤ k + 1 :=
  Nat.add_le_add_right (simulatedState_revealed_le L δ a π owner query update initial T) 1

lemma observedPrefix_determined {d k n : ℕ} {S : Type*} (L δ a θ : ℝ)
    (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (observe : S → EuclideanSpace ℝ (Fin d)) (T : ℕ) (π ρ : Fin (k + 1) ↪ Fin d)
    (hπ : ∀ j : Fin (k + 1),
      j.val < (observedPrefix L δ a θ owner query update initial observe T π).1 → π j = ρ j) :
    observedPrefix L δ a θ owner query update initial observe T π =
      observedPrefix L δ a θ owner query update initial observe T ρ := by
  have hs := simulatedState_prefix L δ a π ρ owner query update initial T
    (fun j hj => hπ j (Nat.lt_add_one_of_le hj))
  simp only [observedPrefix, hs]

lemma observed_bad_count_bound {d k n : ℕ} {S : Type*} (L δ a θ R D : ℝ)
    (hθ : 0 < θ) (hR : 0 ≤ R) (hD : 0 ≤ D) (hDs : D + (k + 1 : ℕ) ≤ d)
    (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (observe : S → EuclideanSpace ℝ (Fin d))
    (hobs : ∀ s, ∑ i, |observe s i| ≤ R) (T : ℕ) :
    let F := observedPrefix L δ a θ owner query update initial observe T
    D * (((distinctWords (k + 1) (Finset.univ : Finset (Fin d))).filter
      (fun w => ∃ π : Fin (k + 1) ↪ Fin d,
        List.ofFn π = w ∧ 0 < hits (F π).2 (w.drop (F π).1))).card : ℝ) ≤
      (k + 1 : ℕ) * (R / θ) * (distinctWords (k + 1) (Finset.univ : Finset (Fin d))).card := by
  let F := observedPrefix L δ a θ owner query update initial observe T
  have hb : ∀ π, ((F π).2.card : ℝ) ≤ R / θ :=
    observedPrefix_bound L δ a θ R hθ owner query update initial observe hobs T
  have hk : ∀ π, (F π).1 ≤ k + 1 :=
    observedPrefix_count L δ a θ owner query update initial observe T
  have hf : ∀ π ρ, (∀ j : Fin (k + 1), j.val < (F π).1 → π j = ρ j) → F π = F ρ :=
    observedPrefix_determined L δ a θ owner query update initial observe T
  have hd : D + (k + 1 : ℕ) ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) := by
    simpa using hDs
  have bound := prefix_bad_count_bound F hb (div_nonneg hR hθ.le) hk hf Finset.univ D hD hd
  convert bound using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter]
  rfl

lemma observed_not_bad_small {d k n : ℕ} {S : Type*} (L δ a θ : ℝ)
    (owner : Fin (k + 1) → Fin n)
    (query : S → Fin n × EuclideanSpace ℝ (Fin d))
    (update : S → EuclideanSpace ℝ (Fin d) → S) (initial : S)
    (observe : S → EuclideanSpace ℝ (Fin d)) (T : ℕ) (π : Fin (k + 1) ↪ Fin d)
    (hgood : ¬ 0 < hits (observedPrefix L δ a θ owner query update initial observe T π).2
      ((List.ofFn π).drop (observedPrefix L δ a θ owner query update initial observe T π).1))
    (j : Fin (k + 1)) (hj : (simulatedState L δ a π owner query update initial T).2 < j.val) :
    |observe (simulatedState L δ a π owner query update initial T).1 (π j)| ≤ θ := by
  by_contra h
  apply hgood
  apply hits_drop_positive π _ _ j (by exact Nat.succ_le_of_lt hj)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using lt_of_not_ge h⟩

end LongTails.Proofs.FiniteSumNondualLowerExposure
