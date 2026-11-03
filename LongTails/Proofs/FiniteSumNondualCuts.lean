import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Convex.Jensen
import LongTails.Algorithms.FiniteSumNondual
import LongTails.Proofs.StochasticEnvelopeGeometry
import LongTails.Proofs.FiniteSumNondualProxGeometry

open Set Classical
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FiniteSumNondualCuts

lemma functional_coordinates {m : ℕ} (f : (Fin m → ℝ) →L[ℝ] ℝ) (x : Fin m → ℝ) :
    f x = ∑ i, f (Pi.single i 1) * x i := by
  have he : x = ∑ i, x i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

lemma orthant_weights {m : ℕ} {S : Set (Fin m → ℝ)} (hne : S.Nonempty)
    (hco : IsCompact S) (hcv : Convex ℝ S) (δ : ℝ)
    (hdisj : Disjoint S {x | ∀ i, δ ≤ x i}) :
    ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧
      ∀ x ∈ S, (∑ i, a i * x i) < δ := by
  let T : Set (Fin m → ℝ) := {x | ∀ i, δ ≤ x i}
  have hTcv : Convex ℝ T := by
    intro x hx y hy a b ha hb hab i
    change δ ≤ a * x i + b * y i
    calc
      δ = a * δ + b * δ := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x i + b * y i := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
        (mul_le_mul_of_nonneg_left (hy i) hb)
  have hTclosed : IsClosed T := by
    have he : T = ⋂ i, {x : Fin m → ℝ | δ ≤ x i} := by ext x; simp [T]
    rw [he]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  obtain ⟨f, l, r, hS, hlr, hT⟩ := geometric_hahn_banach_compact_closed hcv hco hTcv hTclosed hdisj
  let base : Fin m → ℝ := fun _ => δ
  have hb : base ∈ T := fun _ => le_rfl
  have hbase := hT base hb
  let a : Fin m → ℝ := fun i => f (Pi.single i 1)
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    by_contra hn
    have hi : a i < 0 := lt_of_not_ge hn
    let t := (f base - r + 1) / (-a i)
    have ht : 0 < t := div_pos (by linarith) (neg_pos.mpr hi)
    have hm : base + t • Pi.single i 1 ∈ T := by
      intro j
      change δ ≤ δ + t * ((Pi.single i 1 : Fin m → ℝ) j)
      by_cases hj : i = j
      · subst j; simp only [Pi.single_eq_same, mul_one]; linarith
      · simp only [Pi.single_eq_of_ne (Ne.symm hj), mul_zero, add_zero, le_refl]
    have hh := hT _ hm
    rw [map_add, map_smul, smul_eq_mul] at hh
    change r < f base + t * a i at hh
    have he : t * a i = -(f base - r + 1) := by dsimp [t]; field_simp [hi.ne]
    rw [he] at hh
    linarith
  let A := ∑ i, a i
  have hA : 0 < A := by
    have hnon : 0 ≤ A := Finset.sum_nonneg fun i _ => ha i
    by_contra hn
    have hz : A = 0 := le_antisymm (le_of_not_gt hn) hnon
    have hzero : ∀ i, a i = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hz
      exact fun i => hh i (Finset.mem_univ i)
    obtain ⟨x, hx⟩ := hne
    have hh := (hS x hx).trans (hlr.trans hbase)
    rw [functional_coordinates f x, functional_coordinates f base] at hh
    change (∑ i, a i * x i) < ∑ i, a i * base i at hh
    simp only [hzero, zero_mul, Finset.sum_const_zero] at hh
    exact lt_irrefl _ hh
  refine ⟨fun i => a i / A, fun i => div_nonneg (ha i) hA.le, ?_, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hA.ne'
  · intro x hx
    have hh := (hS x hx).trans (hlr.trans hbase)
    have hb' : f base = δ * A := by
      rw [functional_coordinates]
      dsimp only [base, A, a]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hb'] at hh
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    apply (div_lt_iff₀ hA).mpr
    rw [functional_coordinates f x] at hh
    exact hh

open LongTails.Algorithms.FiniteSumNondual
open RecursiveEnvelopeGeometry (Model)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma empty_cuts_weights {m : ℕ} {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) (w g : Fin m → E) (δ : ℝ)
    (hempty : ¬∃ u ∈ C, ∀ i, δ ≤ ⟪g i, w i - u⟫) :
    ∃ a, CutWeights C w g δ a := by
  let Φ : E → (Fin m → ℝ) := fun u i => ⟪g i, w i - u⟫
  have hcont : Continuous Φ := by
    apply continuous_pi
    intro i
    exact continuous_const.inner (continuous_const.sub continuous_id)
  have himage : Convex ℝ (Φ '' C) := by
    intro x hx y hy a b ha hb hab
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    refine ⟨a • u + b • v, hcv hu hv ha hb hab, ?_⟩
    ext i
    simp only [Φ, inner_sub_right, inner_add_right, inner_smul_right, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ => t * ⟪g i, w i⟫) hab]
  have hdisj : Disjoint (Φ '' C) {x | ∀ i, δ ≤ x i} := by
    apply Set.disjoint_left.mpr
    intro x hx horth
    obtain ⟨u, hu, rfl⟩ := hx
    exact hempty ⟨u, hu, horth⟩
  obtain ⟨a, ha, hsum, hbound⟩ := orthant_weights (hne.image Φ) (hco.image hcont) himage δ hdisj
  exact ⟨a, ha, hsum, fun u hu => hbound (Φ u) ⟨u, hu, rfl⟩⟩

lemma weighted_gap {m : ℕ} {L : ℝ} {f : E → ℝ} {G : E → E} (hf : Model L f G)
    (w : Fin m → E) (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : (∑ i, a i) = 1)
    (u : E) :
    f (∑ i, a i • w i) - f u ≤ ∑ i, a i * ⟪G (w i), w i - u⟫ := by
  have hj := (StochasticEnvelopeGeometry.model_convex hf).map_sum_le
    (t := Finset.univ) (w := a) (p := w) (fun i _ => ha i) hsum (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  have hp (i : Fin m) : f (w i) - f u ≤ ⟪G (w i), w i - u⟫ := by
    have hh := hf.lower (w i) u
    rw [← neg_sub (w i) u, inner_neg_right] at hh
    linarith
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => mul_le_mul_of_nonneg_left (hp i) (ha i))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul] at hh
  linarith

lemma cutOutput_spec {m : ℕ} {C : Set E} (hne : C.Nonempty) (hco : IsCompact C)
    (hcv : Convex ℝ C) {L : ℝ} {f : E → ℝ} {G : E → E} (hf : Model L f G)
    (w g : Fin m → E) (hw : ∀ i, w i ∈ C) (hg : ∀ i, g i = G (w i)) (δ : ℝ)
    (hempty : ¬∃ u ∈ C, ∀ i, δ ≤ ⟪g i, w i - u⟫) :
    cutOutput C w g δ ∈ C ∧ ∀ u ∈ C, f (cutOutput C w g δ) - f u < δ := by
  have hex := empty_cuts_weights hne hco hcv w g δ hempty
  have hs := Classical.choose_spec hex
  rw [cutOutput, dite_eq_left hex]
  refine ⟨hcv.sum_mem (fun i _ => hs.1 i) hs.2.1 (fun i _ => hw i), ?_⟩
  intro u hu
  have hh := weighted_gap hf w (Classical.choose hex) hs.1 hs.2.1 u
  have hb := hs.2.2 u hu
  simp only [hg] at hb
  exact hh.trans_lt hb

end LongTails.Proofs.FiniteSumNondualCuts
