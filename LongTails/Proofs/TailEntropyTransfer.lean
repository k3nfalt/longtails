import LongTails.Proofs.TailEntropyChain
import LongTails.Proofs.GeneralizedSmoothHardTransfer

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Finset
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.TailEntropyTransfer

open TailEntropyCurvature TailEntropyDual TailEntropyConjugate TailEntropyChain CompactConjugate
open GeneralizedSmoothHardDual (radial feasible)

section

variable {m : ℕ} (G : Fin m → ℝ) (j : Fin m) (u : EuclideanSpace ℝ (Fin m))

noncomputable def moved : ℝ := ∑ l, if j < l then u l * (G j / G l) else 0

noncomputable def later : ℝ := ∑ l, if j < l then u l else 0

noncomputable def transfer : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => u i - (if j < i then u i else 0) + (if i = j then moved G j u else 0))

lemma transfer_apply (i : Fin m) :
    transfer G j u i = u i - (if j < i then u i else 0) + (if i = j then moved G j u else 0) := rfl

lemma transfer_sum : ∑ i, transfer G j u i = ∑ i, u i - later j u + moved G j u := by
  simp only [transfer_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, later]

lemma transfer_inner (a : EuclideanSpace ℝ (Fin m)) :
    ⟪a, transfer G j u⟫ = ⟪a, u⟫ - (∑ l, if j < l then a l * u l else 0) + a j * moved G j u := by
  simp only [PiLp.inner_apply, Real.inner_apply, transfer_apply, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro l _
    split_ifs <;> ring
  · simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

variable (hG : ∀ i, 0 < G i) (horder : ∀ l, j < l → G l ≤ G j) (hu : u ∈ feasible G)

include hG horder hu

omit horder in
lemma moved_nonneg : 0 ≤ moved G j u := by
  unfold moved
  apply Finset.sum_nonneg
  intro l _
  split_ifs
  · exact mul_nonneg (hu.1 l) (div_nonneg (hG j).le (hG l).le)
  · exact le_rfl

lemma later_le_moved : later j u ≤ moved G j u := by
  unfold later moved
  apply Finset.sum_le_sum
  intro l _
  split_ifs with hl
  · have h1 : 1 ≤ G j / G l := (one_le_div (hG l)).mpr (horder l hl)
    nlinarith [hu.1 l]
  · exact le_rfl

lemma transfer_feasible : transfer G j u ∈ feasible G := by
  refine ⟨?_, ?_⟩
  · intro i
    rw [transfer_apply]
    have hm := moved_nonneg G j u hG hu
    by_cases hji : j < i
    · have hne : i ≠ j := (ne_of_lt hji).symm
      simp [hji, hne]
    · by_cases hij : i = j
      · subst hij
        simp only [lt_irrefl, ↓reduceIte]
        linarith [hu.1 i]
      · simp [hji, hij, hu.1 i]
  · have hsum : ∑ i, transfer G j u i / G i = ∑ i, u i / G i := by
      have hm : moved G j u / G j = ∑ l, if j < l then u l / G l else 0 := by
        unfold moved
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs
        · field_simp [(hG j).ne', (hG l).ne']
        · simp
      simp only [transfer_apply, add_div, sub_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have h1 : ∑ i, (if i = j then moved G j u else 0) / G i = moved G j u / G j := by
        simp only [ite_div, zero_div, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have h2 : ∑ i, (if j < i then u i else 0) / G i = ∑ l, if j < l then u l / G l else 0 := by
        apply Finset.sum_congr rfl; intro l _; split_ifs <;> simp
      rw [h1, h2, hm]
      ring
    rw [hsum]
    exact hu.2

omit hG horder hu in
lemma ext_transfer_before (k : ℕ) (hk : k < j.val) : ext (transfer G j u) k = ext u k := by
  have hkm : k < m := lt_trans hk j.isLt
  have hlt : (⟨k, hkm⟩ : Fin m) < j := hk
  have hne : (⟨k, hkm⟩ : Fin m) ≠ j := ne_of_lt hlt
  simp only [TailEntropyDual.ext, hkm, ↓reduceDIte, transfer_apply, not_lt.mpr hlt.le, hne, ↓reduceIte]
  ring

omit hG horder hu in
lemma ext_transfer_at : ext (transfer G j u) j.val = ext u j.val + moved G j u := by
  simp only [TailEntropyDual.ext, j.isLt, ↓reduceDIte, Fin.eta, transfer_apply, lt_irrefl, ↓reduceIte]
  ring

omit hG horder hu in
lemma ext_transfer_after (k : ℕ) (hk : j.val < k) (hkm : k < m) : ext (transfer G j u) k = 0 := by
  have hlt : j < (⟨k, hkm⟩ : Fin m) := hk
  have hne : (⟨k, hkm⟩ : Fin m) ≠ j := (ne_of_lt hlt).symm
  simp only [TailEntropyDual.ext, hkm, ↓reduceDIte, transfer_apply, hlt, hne, ↓reduceIte]
  ring

omit hG horder hu in
lemma later_eq_tail : later j u = tail (ext u) m (j.val + 1) := by
  have h := fin_later_sum j (fun _ x => x) u
  simpa [later, tail] using h

lemma transfer_entropy :
    tailEntropy (transfer G j u) - tailEntropy u ≤
      ∑ l, if j < l then ((l.val : ℝ) - j.val) * u l else 0 := by
  have hp : ∀ k < m, 0 ≤ ext u k := fun k _ => ext_nonneg u hu.1 k
  have hc : tail (ext u) m (j.val + 1) ≤ moved G j u := by
    rw [← later_eq_tail j u]; exact later_le_moved G j u hG horder hu
  have h := entropy_move (ext u) (ext (transfer G j u)) m j.val j.isLt hp (moved G j u) hc
    (ext_transfer_before G j u) (ext_transfer_at G j u) (ext_transfer_after G j u)
  have hs := fin_later_sum j (fun k x => ((k : ℝ) - j.val) * x) u
  unfold tailEntropy
  rw [hs]
  exact h

end

lemma bracket_pos (L₁ h P aj al ρ d : ℝ) (hL₁ : 0 < L₁) (hh : 0 < h) (hh1 : h ≤ 1)
    (hd : 1 ≤ d) (hρ : 1 + d * h ≤ ρ)
    (haj : P + 140 / (L₁ * h) - 14 / L₁ ≤ aj) (hal : al ≤ P + 140 / (L₁ * h) + 14 / L₁) :
    0 < aj * ρ - al - (ρ - 1) * P - 28 / L₁ * d := by
  have hρ0 : 0 ≤ ρ := by nlinarith
  have h1 := mul_le_mul_of_nonneg_right haj hρ0
  have hrest : 0 < (P + 140 / (L₁ * h) - 14 / L₁) * ρ - (P + 140 / (L₁ * h) + 14 / L₁) -
      (ρ - 1) * P - 28 / L₁ * d := by
    have he : (P + 140 / (L₁ * h) - 14 / L₁) * ρ - (P + 140 / (L₁ * h) + 14 / L₁) -
        (ρ - 1) * P - 28 / L₁ * d =
        (140 * (ρ - 1) - 14 * h * (ρ + 1) - 28 * d * h) / (L₁ * h) := by
      field_simp
      ring
    rw [he]
    apply div_pos _ (by positivity)
    have hρ1 : d * h ≤ ρ - 1 := by linarith
    have hρ1' : 0 ≤ ρ - 1 := le_trans (by positivity) hρ1
    have h2 : 14 * h * (ρ - 1) ≤ 14 * (ρ - 1) := by
      nlinarith [mul_le_mul_of_nonneg_right hh1 hρ1']
    nlinarith
  linarith

section

variable {m : ℕ} (L₀ L₁ B : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (G : Fin m → ℝ)
  (hG : ∀ i, 0 < G i) (hB : 0 ≤ B) (hGB : ∀ i, G i ≤ B) (j : Fin m)
  (horder : ∀ l, j < l → G l ≤ G j)

include hL₀ hL₁ hG hB hGB horder

lemma optimizer_later_zero (a u : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible G)
    (hopt : IsMaxOn (fun v => ⟪a, v⟫ - dual L₀ L₁ v) (feasible G) u)
    (hbracket : ∀ l, j < l → 0 < a j * (G j / G l) - a l -
      (G j / G l - 1) * (2 * (Real.log (1 + L₁ * B / L₀) / L₁) + 28 / L₁ * Real.log m) -
        28 / L₁ * ((l.val : ℝ) - j.val)) :
    ∀ l, j < l → u l = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, hl₀, hne⟩ := hcon
  have hpos : 0 < u l₀ := lt_of_le_of_ne (hu.1 l₀) (Ne.symm hne)
  set v := transfer G j u with hv
  have hvf := transfer_feasible G j u hG horder hu
  have hle := hopt hvf
  change ⟪a, v⟫ - dual L₀ L₁ v ≤ ⟪a, u⟫ - dual L₀ L₁ u at hle
  set P := 2 * (Real.log (1 + L₁ * B / L₀) / L₁) + 28 / L₁ * Real.log m with hP
  set Φ' := Real.log (1 + L₁ * B / L₀) / L₁ with hΦ'
  set ρ : Fin m → ℝ := fun l => G j / G l with hρ
  have hmoved : moved G j u = ∑ l, if j < l then u l * ρ l else 0 := rfl
  have hZu0 : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => hu.1 i)
  have hZv := transfer_sum G j u
  have hlm := later_le_moved G j u hG horder hu
  have hZvB : ∑ i, v i ≤ B := GeneralizedSmoothHardTransfer.feasible_sum_le G B hG hB hGB v hvf
  have hrad := radial_sub_le L₀ L₁ (∑ i, u i) (∑ i, v i) B hL₀ hL₁ hZu0 (by rw [hZv]; linarith) hZvB
  have hent := transfer_entropy G j u hG horder hu
  have hinner := transfer_inner G j u a
  have hdiff : ∑ i, v i - ∑ i, u i = ∑ l, if j < l then u l * (ρ l - 1) else 0 := by
    rw [hZv, hmoved]
    unfold later
    rw [show (∑ i, u i - ∑ l, (if j < l then u l else 0) + ∑ l, (if j < l then u l * ρ l else 0)) -
        ∑ i, u i = ∑ l, (if j < l then u l * ρ l else 0) - ∑ l, (if j < l then u l else 0) by ring,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _; split_ifs <;> ring
  have hgain : ∑ l, (if j < l then u l * (a j * ρ l - a l - (ρ l - 1) * P -
      28 / L₁ * ((l.val : ℝ) - j.val)) else 0) ≤
      (⟪a, v⟫ - dual L₀ L₁ v) - (⟪a, u⟫ - dual L₀ L₁ u) := by
    have hdual : dual L₀ L₁ v - dual L₀ L₁ u =
        2 * (radial L₀ L₁ (∑ i, v i) - radial L₀ L₁ (∑ i, u i)) +
          28 / L₁ * (tailEntropy v - tailEntropy u) +
            28 / L₁ * Real.log m * (∑ i, v i - ∑ i, u i) := by
      unfold dual; ring
    have hlin : ⟪a, v⟫ - ⟪a, u⟫ = ∑ l, if j < l then u l * (a j * ρ l - a l) else 0 := by
      rw [hinner, hmoved, Finset.mul_sum]
      rw [show ⟪a, u⟫ - (∑ l, if j < l then a l * u l else 0) +
          ∑ l, a j * (if j < l then u l * ρ l else 0) - ⟪a, u⟫ =
          ∑ l, a j * (if j < l then u l * ρ l else 0) - ∑ l, (if j < l then a l * u l else 0) by ring,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro l _; split_ifs <;> ring
    have hcomb : ∑ l, (if j < l then u l * (a j * ρ l - a l - (ρ l - 1) * P -
        28 / L₁ * ((l.val : ℝ) - j.val)) else 0) =
        (∑ l, if j < l then u l * (a j * ρ l - a l) else 0) -
          P * (∑ l, if j < l then u l * (ρ l - 1) else 0) -
          28 / L₁ * (∑ l, if j < l then ((l.val : ℝ) - j.val) * u l else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro l _; split_ifs <;> ring
    have hent' := mul_le_mul_of_nonneg_left hent (show 0 ≤ 28 / L₁ by positivity)
    have hrad' : radial L₀ L₁ (∑ i, v i) - radial L₀ L₁ (∑ i, u i) ≤
        (∑ l, if j < l then u l * (ρ l - 1) else 0) * Φ' := by
      rw [← hdiff]; exact hrad
    have hPe : P * (∑ l, if j < l then u l * (ρ l - 1) else 0) =
        2 * ((∑ l, if j < l then u l * (ρ l - 1) else 0) * Φ') +
          28 / L₁ * Real.log m * (∑ l, if j < l then u l * (ρ l - 1) else 0) := by
      rw [hP, hΦ']; ring
    rw [hcomb]
    have : (⟪a, v⟫ - dual L₀ L₁ v) - (⟪a, u⟫ - dual L₀ L₁ u) =
        (⟪a, v⟫ - ⟪a, u⟫) - (dual L₀ L₁ v - dual L₀ L₁ u) := by ring
    rw [this, hlin, hdual, hdiff]
    nlinarith [hent', hrad', hPe]
  have hterm_nonneg : ∀ l ∈ Finset.univ, 0 ≤ (if j < l then u l * (a j * ρ l - a l - (ρ l - 1) * P -
      28 / L₁ * ((l.val : ℝ) - j.val)) else 0) := by
    intro l _
    split_ifs with hl
    · exact mul_nonneg (hu.1 l) (hbracket l hl).le
    · exact le_rfl
  have hsingle := Finset.single_le_sum hterm_nonneg (Finset.mem_univ l₀)
  simp only [hl₀, ↓reduceIte] at hsingle
  have hpos' := mul_pos hpos (hbracket l₀ hl₀)
  linarith

end

end LongTails.Proofs.TailEntropyTransfer
