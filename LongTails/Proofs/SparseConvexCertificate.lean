import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

namespace LongTails.Proofs.SparseConvexCertificate

open Set Module

variable {E ι : Type*} [Fintype ι]

lemma small_sublevel_obstruction [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (f : ι → E → ℝ) (t : ℝ)
    (hconvex : ∀ i, ConvexOn ℝ Q (f i))
    (hbad : ¬ (⋂ i, {x ∈ Q | f i x ≤ t}).Nonempty) :
    ∃ S : Finset ι, S.Nonempty ∧ S.card ≤ finrank ℝ E + 1 ∧
      ¬ (⋂ i ∈ S, {x ∈ Q | f i x ≤ t}).Nonempty := by
  classical
  have hfinite : ¬ (⋂ i ∈ (Finset.univ : Finset ι), {x ∈ Q | f i x ≤ t}).Nonempty := by
    simpa using hbad
  have hex : ∃ S ⊆ (Finset.univ : Finset ι), S.card ≤ finrank ℝ E + 1 ∧
      ¬ (⋂ i ∈ S, {x ∈ Q | f i x ≤ t}).Nonempty := by
    by_contra! h
    exact hfinite (Convex.helly_theorem' (fun i _ => (hconvex i).convex_le t) h)
  obtain ⟨S, _, hcard, hempty⟩ := hex
  refine ⟨S, ?_, hcard, hempty⟩
  by_contra hn
  have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp [this] at hempty

section UpperImage


def strictUpperImage (Q : Set E) (f : ι → E → ℝ) : Set (ι → ℝ) :=
  {v | ∃ x ∈ Q, ∀ i, f i x < v i}

lemma strictUpperImage_isOpen (Q : Set E) (f : ι → E → ℝ) :
    IsOpen (strictUpperImage Q f) := by
  have heq : strictUpperImage Q f = ⋃ x ∈ Q, ⋂ i, {v : ι → ℝ | f i x < v i} := by
    ext v
    simp [strictUpperImage]
  rw [heq]
  exact isOpen_iUnion (fun x => isOpen_iUnion (fun _ =>
    isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))))

omit [Fintype ι] in
lemma strictUpperImage_convex [AddCommGroup E] [Module ℝ E] (Q : Set E) (f : ι → E → ℝ)
    (hQ : Convex ℝ Q) (hf : ∀ i, ConvexOn ℝ Q (f i)) :
    Convex ℝ (strictUpperImage Q f) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨x, hx, hv⟩ := hv
  obtain ⟨y, hy, hw⟩ := hw
  refine ⟨a • x + b • y, hQ hx hy ha hb hab, ?_⟩
  intro i
  have h := (hf i).2 hx hy ha hb hab
  have h1 := mul_le_mul_of_nonneg_left (le_of_lt (hv i)) ha
  have h2 := mul_le_mul_of_nonneg_left (le_of_lt (hw i)) hb
  change f i (a • x + b • y) < a * v i + b * w i
  change f i (a • x + b • y) ≤ a * f i x + b * f i y at h
  obtain hapos | hzero := lt_or_eq_of_le ha
  · have hstrict := mul_lt_mul_of_pos_left (hv i) hapos
    linarith
  · have hbpos : 0 < b := by linarith
    have hstrict := mul_lt_mul_of_pos_left (hw i) hbpos
    linarith

lemma functional_coordinates [DecidableEq ι] (f : (ι → ℝ) →ₗ[ℝ] ℝ) (v : ι → ℝ) :
    f v = ∑ i, f (Pi.single i 1) * v i := by
  classical
  calc
    f v = f (∑ i, v i • Pi.single i 1) := congrArg f (pi_eq_sum_univ' v)
    _ = ∑ i, f (Pi.single i 1) * v i := by
      simp only [map_sum, map_smul, smul_eq_mul]
      congr 1
      ext i
      ring

omit [Fintype ι] in
lemma separating_coefficients_nonneg [DecidableEq ι]
    (C : Set (ι → ℝ)) (v p : ι → ℝ) (f : (ι → ℝ) →ₗ[ℝ] ℝ)
    (hv : v ∈ C)
    (hup : ∀ w ∈ C, ∀ i (r : ℝ), 0 ≤ r → w + r • Pi.single i 1 ∈ C)
    (hsep : ∀ w ∈ C, f p < f w) :
    ∀ i, 0 ≤ f (Pi.single i 1) := by
  intro i
  by_contra! hneg
  let r := (f v - f p + 1) / (-f (Pi.single i 1))
  have hr : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg (by linarith [hsep v hv]) (neg_nonneg.mpr hneg.le)
  have hid : r * f (Pi.single i 1) = -(f v - f p + 1) := by
    dsimp [r]
    field_simp [ne_of_lt hneg]
  have h := hsep _ (hup v hv i r hr)
  simp only [map_add, map_smul, smul_eq_mul] at h
  rw [hid] at h
  linarith

lemma separating_coefficients_sum_pos [DecidableEq ι]
    (f : (ι → ℝ) →ₗ[ℝ] ℝ) (v p : ι → ℝ)
    (hnonneg : ∀ i, 0 ≤ f (Pi.single i 1)) (hsep : f p < f v) :
    0 < ∑ i, f (Pi.single i 1) := by
  have hs : 0 ≤ ∑ i, f (Pi.single i 1) := Finset.sum_nonneg (fun i _ => hnonneg i)
  by_contra! hn
  have hz : ∑ i, f (Pi.single i 1) = 0 := le_antisymm hn hs
  have hall : ∀ i, f (Pi.single i 1) = 0 := by
    intro i
    have hi := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
    rw [hz] at hi
    exact le_antisymm hi (hnonneg i)
  rw [functional_coordinates f p, functional_coordinates f v] at hsep
  simp [hall] at hsep

lemma weighted_lower_certificate [AddCommGroup E] [Module ℝ E]
    (Q : Set E) (u : ι → E → ℝ) (t : ℝ) (hne : Q.Nonempty)
    (hQ : Convex ℝ Q) (hu : ∀ i, ConvexOn ℝ Q (u i))
    (hbad : (fun _ : ι => t) ∉ strictUpperImage Q u) :
    ∃ q : ι → ℝ, (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧
      ∀ x ∈ Q, t ≤ ∑ i, q i * u i x := by
  classical
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open
    (strictUpperImage_convex Q u hQ hu) (strictUpperImage_isOpen Q u) hbad
  obtain ⟨x0, hx0⟩ := hne
  let v0 : ι → ℝ := fun i => u i x0 + 1
  have hv0 : v0 ∈ strictUpperImage Q u := ⟨x0, hx0, fun i => by dsimp [v0]; linarith⟩
  have hup : ∀ w ∈ strictUpperImage Q u, ∀ i (r : ℝ), 0 ≤ r →
      w + r • Pi.single i 1 ∈ strictUpperImage Q u := by
    intro w hw i r hr
    obtain ⟨x, hx, hw⟩ := hw
    refine ⟨x, hx, fun j => ?_⟩
    change u j x < w j + r * (Pi.single (M := fun _ : ι => ℝ) i 1 j)
    have hj : 0 ≤ (Pi.single (M := fun _ : ι => ℝ) i 1) j := by
      by_cases h : i = j <;> simp [h]
    linarith [mul_nonneg hr hj, hw j]
  let c : ι → ℝ := fun i => f (Pi.single i 1)
  have hc : ∀ i, 0 ≤ c i := separating_coefficients_nonneg
    (strictUpperImage Q u) v0 (fun _ => t) f.toLinearMap hv0 hup hf
  have hC : 0 < ∑ i, c i := separating_coefficients_sum_pos
    f.toLinearMap v0 (fun _ => t) hc (hf v0 hv0)
  let q : ι → ℝ := fun i => c i / ∑ j, c j
  refine ⟨q, fun i => div_nonneg (hc i) hC.le, ?_, ?_⟩
  · dsimp [q]
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hC)
  · intro x hx
    apply le_of_forall_pos_le_add
    intro r hr
    have hv : (fun i => u i x + r) ∈ strictUpperImage Q u :=
      ⟨x, hx, fun i => by linarith⟩
    have h := hf _ hv
    change f.toLinearMap (fun _ : ι => t) < f.toLinearMap (fun i => u i x + r) at h
    rw [functional_coordinates f.toLinearMap (fun _ => t),
      functional_coordinates f.toLinearMap (fun i => u i x + r)] at h
    change (∑ i, c i * t) < ∑ i, c i * (u i x + r) at h
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at h
    have hq : (∑ i, q i * u i x) * (∑ i, c i) = ∑ i, c i * u i x := by
      dsimp [q]
      simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
      exact div_mul_cancel₀ _ (ne_of_gt hC)
    apply (mul_le_mul_iff_left₀ hC).mp
    nlinarith

lemma sparse_weighted_lower_certificate [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (Q : Set E) (u : ι → E → ℝ) (t : ℝ)
    (hne : Q.Nonempty) (hQ : Convex ℝ Q) (hu : ∀ i, ConvexOn ℝ Q (u i))
    (hbad : ¬ (⋂ i, {x ∈ Q | u i x ≤ t}).Nonempty) :
    ∃ (S : Finset ι) (q : ι → ℝ), S.Nonempty ∧ S.card ≤ finrank ℝ E + 1 ∧
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ (∀ i, i ∉ S → q i = 0) ∧
      ∀ x ∈ Q, t ≤ ∑ i, q i * u i x := by
  classical
  obtain ⟨S, hS, hcard, hempty⟩ := small_sublevel_obstruction Q u t hu hbad
  have hsub : (fun _ : S => t) ∉ strictUpperImage Q (fun i : S => u i) := by
    rintro ⟨x, hx, hxi⟩
    apply hempty
    refine ⟨x, ?_⟩
    simp only [mem_iInter]
    intro i hi
    exact ⟨hx, (hxi ⟨i, hi⟩).le⟩
  obtain ⟨w, hw, hsum, hlower⟩ := weighted_lower_certificate Q (fun i : S => u i)
    t hne hQ (fun i => hu i) hsub
  let q : ι → ℝ := fun i => ∑ j : S, if j.val = i then w j else 0
  have hqnonneg : ∀ i, 0 ≤ q i := by
    intro i
    exact Finset.sum_nonneg (fun j _ => by split_ifs; exact hw j; rfl)
  have hqsum : ∑ i, q i = 1 := by
    dsimp [q]
    rw [Finset.sum_comm]
    simpa using hsum
  have hqsupport : ∀ i, i ∉ S → q i = 0 := by
    intro i hi
    apply Finset.sum_eq_zero
    intro j _
    have hj : j.val ≠ i := by intro h; exact hi (h ▸ j.property)
    simp [hj]
  refine ⟨S, q, hS, hcard, hqnonneg, hqsum, hqsupport, ?_⟩
  intro x hx
  have he : ∑ i, q i * u i x = ∑ j : S, w j * u j x := by
    dsimp [q]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp
  rw [he]
  exact hlower x hx

end UpperImage

end LongTails.Proofs.SparseConvexCertificate
