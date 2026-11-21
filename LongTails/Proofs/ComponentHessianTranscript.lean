import LongTails.Proofs.ComponentHessianFamily
import LongTails.Proofs.FiniteSumNondualLowerPolicy

namespace LongTails.Proofs.ComponentHessianTranscript

open scoped RealInnerProductSpace Topology
open ComponentHessianFamily ComponentHessianChain ComponentHessianLocalization
open RelativeHessianOracle RelativeHessianSimulation

variable {d k n : ℕ}

def indices (k : ℕ) (known : List (Fin n)) (i : Fin n) : Finset (Fin (k + 1)) :=
  Finset.univ.filter (fun j => known[j.val]? = some i)

lemma row_prefix (π ρ : Fin (k + 1) ↪ Fin d) (r : ℕ)
    (hp : ∀ j : Fin (k + 1), j.val < r → π j = ρ j) (j : Fin (k + 1)) (hj : j.val < r) :
    row π j = row ρ j := by
  induction j using Fin.cases with
  | zero => simp [row, axes, hp _ hj]
  | succ j =>
    have h := hp j.castSucc (show j.val < r by simp at hj; omega)
    simp [row, axes, h, hp _ hj]

lemma part_prefix (π ρ : Fin (k + 1) ↪ Fin d) (known : List (Fin n)) (i : Fin n)
    (hp : ∀ j : Fin (k + 1), j.val < known.length → π j = ρ j) :
    part π (indices k known i) n = part ρ (indices k known i) n := by
  funext x
  unfold part masked raw
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  have h : known[j.val]? = some i := (Finset.mem_filter.mp hj).2
  have hlt : j.val < known.length := by
    by_contra! hle
    simp [List.getElem?_eq_none hle] at h
  rw [row_prefix π ρ known.length hp j hlt]

lemma tail_edge_zero (π : Fin (k + 1) ↪ Fin d) (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| < 1 / 40)
    (j : Fin (k + 1)) (hj : r < j.val) : edge (row π j) (offset k j) x = 0 := by
  induction j using Fin.cases with
  | zero => simp at hj
  | succ j =>
    have h₁ := abs_lt.mp (h j.castSucc (by simpa using hj))
    have h₂ := abs_lt.mp (h j.succ (by omega))
    apply ComponentHessianLink.link_flat
    simp only [row, offset, Fin.cases_succ, inner_sub_left, axes_inner, zero_add]
    linarith

lemma transcript_jet (π : Fin (k + 1) ↪ Fin d) (hn : 0 < n) (r : ℕ)
    (s t : Finset (Fin (k + 1))) (hst : s ⊆ t)
    (ht : ∀ j ∈ t, j ∉ s → r < j.val) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ 2 * radius n (k + 1 : ℕ) →
      ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| < 1 / 40) :
    jet (part π s n) x = jet (part π t n) x := by
  by_cases hr : ‖x‖ ≤ 2 * radius n (k + 1 : ℕ)
  · have he (j : Fin (k + 1)) : ∀ᶠ y in nhds x, r ≤ j.val → |y (π j)| < 1 / 40 := by
      by_cases hj : r ≤ j.val
      · have hc : Continuous (fun y : EuclideanSpace ℝ (Fin d) => |y (π j)|) :=
          (PiLp.continuous_apply 2 _ (π j)).abs
        exact (hc.continuousAt.eventually (gt_mem_nhds (hx hr j hj))).mono (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)
    have eq : part π s n =ᶠ[nhds x] part π t n := by
      filter_upwards [Filter.eventually_all.mpr he] with y hy
      have hs := Finset.sum_subset hst (fun j hj hs => tail_edge_zero π r y hy j (ht j hj hs))
      simp only [part, masked, raw, hs]
    obtain ⟨hf, hg, hH, _⟩ := ThirdOrderAffineCalculus.local_jets_eq eq
    simp only [jet, hf, hg, hH]
  · have hB : 0 < radius n (k + 1 : ℕ) := by unfold radius; positivity
    exact (cutoff_jet_outside hB (raw_smooth s _ _) _ x (le_of_not_ge hr)).trans
      (cutoff_jet_outside hB (raw_smooth t _ _) _ x (le_of_not_ge hr)).symm

def nextKnown (known rest : List (Fin n)) (i : Fin n) : List (Fin n) :=
  if rest.head? = some i then known ++ [i] else known

lemma next_prefix (known rest : List (Fin n)) (i : Fin n) :
    nextKnown known rest i <+: known ++ rest := by
  cases rest with
  | nil => simp [nextKnown]
  | cons j w =>
    by_cases he : j = i <;> simp [nextKnown, he, List.prefix_append]

lemma next_missing (known rest : List (Fin n)) (i : Fin n) :
    indices k (nextKnown known rest i) i ⊆ indices k (known ++ rest) i ∧
      ∀ j ∈ indices k (known ++ rest) i, j ∉ indices k (nextKnown known rest i) i →
        known.length < j.val := by
  obtain ⟨extra, he⟩ := next_prefix known rest i
  constructor
  · intro j hj
    have h := (Finset.mem_filter.mp hj).2
    have hlt : j.val < (nextKnown known rest i).length := by
      by_contra! hle
      simp [List.getElem?_eq_none hle] at h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← he, List.getElem?_append_left hlt]; exact h⟩
  · intro j hj hmiss
    have h := (Finset.mem_filter.mp hj).2
    have hm : (nextKnown known rest i)[j.val]? ≠ some i := by simpa [indices] using hmiss
    by_contra! hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [List.getElem?_append_left hlt] at h
      unfold nextKnown at hm
      split at hm
      · exact hm ((List.getElem?_append_left hlt).trans h)
      · exact hm h
    · rw [heq, List.getElem?_append_right (le_refl _)] at h
      simp only [Nat.sub_self, ← List.head?_eq_getElem?] at h
      apply hm
      simp [nextKnown, heq, h]

end LongTails.Proofs.ComponentHessianTranscript
