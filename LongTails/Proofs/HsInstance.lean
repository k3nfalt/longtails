import LongTails.Proofs.HsStability
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace BigOperators
open LongTails.Proofs.HsProfile LongTails.Proofs.HsChain

namespace LongTails.Proofs.HsInstance

variable {d k : ℕ}

noncomputable def ev (i : Fin d) : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1

lemma inner_ev (i : Fin d) (u : EuclideanSpace ℝ (Fin d)) : ⟪ev i, u⟫ = u i := by
  simp [ev, EuclideanSpace.inner_single_left]

lemma norm_ev (i : Fin d) : ‖ev i‖ = 1 := by simp [ev]

lemma sum_sq_le_norm_sq (π : Fin (k + 1) ↪ Fin d) (u : EuclideanSpace ℝ (Fin d)) :
    ∑ j, u (π j) ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  have h : ∑ j, u (π j) ^ 2 = ∑ i ∈ Finset.univ.map π, u i ^ 2 := by
    rw [Finset.sum_map]
  rw [h]
  calc ∑ i ∈ Finset.univ.map π, u i ^ 2 ≤ ∑ i, u i ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => sq_nonneg _)
    _ = ∑ i, ‖u i‖ ^ 2 := by simp [Real.norm_eq_abs, sq_abs]

variable (π : Fin (k + 1) ↪ Fin d)

noncomputable def pv (j : Fin (k + 1)) : EuclideanSpace ℝ (Fin d) :=
  if hj : 0 < j.val then ev (π ⟨j.val - 1, by omega⟩) else 0

noncomputable def nn (j : Fin (k + 1)) : EuclideanSpace ℝ (Fin d) := pv π j - ev (π j)

noncomputable def cc (j : Fin (k + 1)) : ℝ := if j.val = 0 then 1 else 0

noncomputable def nt (t : ℕ) (j : Fin (k + 1)) : EuclideanSpace ℝ (Fin d) :=
  if j.val ≤ t then nn π j else 0

noncomputable def ct (t : ℕ) (j : Fin (k + 1)) : ℝ := if j.val ≤ t then cc j else -1

lemma norm_pv_le (j : Fin (k + 1)) : ‖pv π j‖ ≤ 1 := by
  unfold pv
  split_ifs
  · rw [norm_ev]
  · simp

lemma norm_nn_le (j : Fin (k + 1)) : ‖nn π j‖ ≤ 2 := by
  unfold nn
  calc ‖pv π j - ev (π j)‖ ≤ ‖pv π j‖ + ‖ev (π j)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_pv_le π j) (le_of_eq (norm_ev _))
    _ = 2 := by norm_num

lemma norm_nt_le (t : ℕ) (j : Fin (k + 1)) : ‖nt π t j‖ ≤ 2 := by
  unfold nt
  split_ifs
  · exact norm_nn_le π j
  · simp

lemma inner_pv (j : Fin (k + 1)) (u : EuclideanSpace ℝ (Fin d)) :
    ⟪pv π j, u⟫ = if hj : 0 < j.val then u (π ⟨j.val - 1, by omega⟩) else 0 := by
  unfold pv
  split_ifs
  · exact inner_ev _ _
  · simp

lemma sum_pv_sq (v : EuclideanSpace ℝ (Fin d)) : ∑ j, ⟪pv π j, v⟫ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [Fin.sum_univ_succ]
  have h0 : ⟪pv π 0, v⟫ = 0 := by rw [inner_pv]; simp
  rw [h0]
  have hs : ∀ i : Fin k, ⟪pv π i.succ, v⟫ = v (π i.castSucc) := by
    intro i
    rw [inner_pv, dite_eq_left (by simp)]
    exact congrArg (fun j => v (π j)) (Fin.ext (by simp))
  simp only [hs]
  have h2 := sum_sq_le_norm_sq π v
  rw [Fin.sum_univ_castSucc] at h2
  have := sq_nonneg (v (π (Fin.last k)))
  linarith [sq_nonneg (0 : ℝ)]

lemma sum_nn_sq (v : EuclideanSpace ℝ (Fin d)) : ∑ j, ⟪nn π j, v⟫ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
  have h1 : ∀ j, ⟪nn π j, v⟫ ^ 2 ≤ 2 * ⟪pv π j, v⟫ ^ 2 + 2 * v (π j) ^ 2 := by
    intro j
    rw [nn, inner_sub_left, inner_ev]
    nlinarith [sq_nonneg (⟪pv π j, v⟫ + v (π j))]
  calc ∑ j, ⟪nn π j, v⟫ ^ 2 ≤ ∑ j, (2 * ⟪pv π j, v⟫ ^ 2 + 2 * v (π j) ^ 2) :=
        Finset.sum_le_sum fun j _ => h1 j
    _ = 2 * ∑ j, ⟪pv π j, v⟫ ^ 2 + 2 * ∑ j, v (π j) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * ‖v‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
        gcongr
        · exact sum_pv_sq π v
        · exact sum_sq_le_norm_sq π v
    _ = 4 * ‖v‖ ^ 2 := by ring

lemma lin_full (j : Fin (k + 1)) (u : EuclideanSpace ℝ (Fin d)) :
    lin (nn π) cc j u = ⟪pv π j, u⟫ - u (π j) + cc j := by
  rw [lin, nn, inner_sub_left, inner_ev]

lemma lin_telescope (u : EuclideanSpace ℝ (Fin d)) :
    ∑ j, lin (nn π) cc j u = 1 - u (π (Fin.last k)) := by
  simp only [lin_full]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hc : ∑ j : Fin (k + 1), cc j = 1 := by
    rw [Fin.sum_univ_succ]
    simp [cc]
  have hp : ∑ j : Fin (k + 1), ⟪pv π j, u⟫ = ∑ i : Fin k, u (π i.castSucc) := by
    rw [Fin.sum_univ_succ]
    have h0 : ⟪pv π 0, u⟫ = 0 := by rw [inner_pv]; simp
    rw [h0, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_pv, dite_eq_left (by simp)]
    exact congrArg (fun j => u (π j)) (Fin.ext (by simp))
  have hu : ∑ j : Fin (k + 1), u (π j) = ∑ i : Fin k, u (π i.castSucc) + u (π (Fin.last k)) :=
    Fin.sum_univ_castSucc _
  rw [hc, hp, hu]
  ring

lemma lin_gt (t : ℕ) (j : Fin (k + 1)) (hj : t < j.val) (u : EuclideanSpace ℝ (Fin d)) :
    lin (nn π) cc j u = u (π ⟨j.val - 1, by omega⟩) - u (π j) := by
  rw [lin_full, inner_pv, dite_eq_left (by omega)]
  have : cc j = 0 := by unfold cc; rw [ite_eq_right (by omega)]
  rw [this]; ring

lemma lin_masked_gt (t : ℕ) (j : Fin (k + 1)) (hj : t < j.val) (u : EuclideanSpace ℝ (Fin d)) :
    lin (nt π t) (ct t) j u = -1 := by
  rw [lin, nt, ct, ite_eq_right (by omega), ite_eq_right (by omega)]
  simp

lemma lin_masked_le (t : ℕ) (j : Fin (k + 1)) (hj : j.val ≤ t) (u : EuclideanSpace ℝ (Fin d)) :
    lin (nt π t) (ct t) j u = lin (nn π) cc j u := by
  rw [lin, lin, nt, ct, ite_eq_left hj, ite_eq_left hj]

lemma nt_eq_le (t : ℕ) (j : Fin (k + 1)) (hj : j.val ≤ t) : nt π t j = nn π j := by
  rw [nt, ite_eq_left hj]

lemma nt_eq_gt (t : ℕ) (j : Fin (k + 1)) (hj : t < j.val) : nt π t j = 0 := by
  rw [nt, ite_eq_right (by omega)]

section Truncation

variable (p p2 : ℕ) (a h w2 lam κ C0 : ℝ)

variable {h}

lemma masked_terms (hp : 1 ≤ p) (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℕ) (θ : ℝ)
    (hθ : 2 * θ ≤ a - h) (u : EuclideanSpace ℝ (Fin d))
    (hu : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) (j : Fin (k + 1)) :
    sp0 p a h (lin (nt π t) (ct t) j u) = sp0 p a h (lin (nn π) cc j u) ∧
      sp1 p a h (lin (nt π t) (ct t) j u) = sp1 p a h (lin (nn π) cc j u) ∧
      sp2 p a h (lin (nt π t) (ct t) j u) = sp2 p a h (lin (nn π) cc j u) ∧
      (nt π t j = nn π j ∨ (sp1 p a h (lin (nn π) cc j u) = 0 ∧ sp2 p a h (lin (nn π) cc j u) = 0)) := by
  by_cases hj : j.val ≤ t
  · rw [lin_masked_le π t j hj]
    exact ⟨rfl, rfl, rfl, Or.inl (nt_eq_le π t j hj)⟩
  · push Not at hj
    have hm := lin_masked_gt π t j hj u
    have hf := lin_gt π t j hj u
    have h1 := hu ⟨j.val - 1, by omega⟩ (by simp; omega)
    have h2 := hu j hj.le
    have hle : lin (nn π) cc j u ≤ a - h := by
      rw [hf]
      have := abs_le.mp h1
      have := abs_le.mp h2
      linarith
    have hle' : lin (nt π t) (ct t) j u ≤ a - h := by rw [hm]; linarith
    have hzero : ∀ s, s ≤ a - h → sp0 p a h s = 0 ∧ sp1 p a h s = 0 ∧ sp2 p a h s = 0 := by
      intro s hs
      refine ⟨sp0_of_le p a hp hh hs, sp1_of_le p a hp hh hs, sp2_eq_zero p a hp hh ?_⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
    obtain ⟨a0, a1, a2⟩ := hzero _ hle
    obtain ⟨b0, b1, b2⟩ := hzero _ hle'
    exact ⟨by rw [a0, b0], by rw [a1, b1], by rw [a2, b2], Or.inr ⟨a1, a2⟩⟩

lemma Cv_masked (hp : 1 ≤ p) (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℕ) (θ : ℝ)
    (hθ : 2 * θ ≤ a - h) (u : EuclideanSpace ℝ (Fin d))
    (hu : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) :
    Cv p a h (nt π t) (ct t) u = Cv p a h (nn π) cc u :=
  Finset.sum_congr rfl fun j _ => (masked_terms π p a hp hh hah t θ hθ u hu j).1

lemma Cg_masked (hp : 1 ≤ p) (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℕ) (θ : ℝ)
    (hθ : 2 * θ ≤ a - h) (u : EuclideanSpace ℝ (Fin d))
    (hu : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) :
    Cg p a h (nt π t) (ct t) u = Cg p a h (nn π) cc u := by
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨_, h1, _, h3⟩ := masked_terms π p a hp hh hah t θ hθ u hu j
  rw [h1]
  rcases h3 with h3 | ⟨h3, _⟩
  · rw [h3]
  · rw [h3, zero_smul, zero_smul]

lemma CH_masked (hp : 1 ≤ p) (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℕ) (θ : ℝ)
    (hθ : 2 * θ ≤ a - h) (u : EuclideanSpace ℝ (Fin d))
    (hu : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) :
    CH p a h (nt π t) (ct t) u = CH p a h (nn π) cc u := by
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨_, _, h2, h3⟩ := masked_terms π p a hp hh hah t θ hθ u hu j
  rw [h2]
  rcases h3 with h3 | ⟨_, h3⟩
  · rw [h3]
  · rw [h3, zero_smul, zero_smul]

lemma answers_masked (hp : 1 ≤ p) (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℕ) (θ : ℝ)
    (hθ : 2 * θ ≤ a - h) (u : EuclideanSpace ℝ (Fin d))
    (hu : ∀ j : Fin (k + 1), t ≤ j.val → |u (π j)| ≤ θ) :
    Fv p p2 a h w2 lam κ C0 (nt π t) (ct t) u = Fv p p2 a h w2 lam κ C0 (nn π) cc u ∧
      DFv p p2 a h w2 lam κ C0 (nt π t) (ct t) u = DFv p p2 a h w2 lam κ C0 (nn π) cc u := by
  have hC := Cv_masked π p a hp hh hah t θ hθ u hu
  have hG := Cg_masked π p a hp hh hah t θ hθ u hu
  have hH := CH_masked π p a hp hh hah t θ hθ u hu
  constructor
  · simp only [Fv, zv, dv, hC, hG]
  · simp only [DFv, zv, dv, hC, hG, hH]

lemma Cv_masked_le (hp : 1 ≤ p) (hh : 0 < h) (hah : 0 ≤ a - h) (t : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) :
    Cv p a h (nt π t) (ct t) u ≤ Cv p a h (nn π) cc u := by
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j.val ≤ t
  · rw [lin_masked_le π t j hj]
  · push Not at hj
    rw [lin_masked_gt π t j hj u, sp0_of_le p a hp hh (by linarith)]
    exact sp0_nonneg p a hp hh _

end Truncation

end LongTails.Proofs.HsInstance
