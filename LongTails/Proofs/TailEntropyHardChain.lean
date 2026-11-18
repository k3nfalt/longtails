import LongTails.Proofs.TailEntropyTransfer
import LongTails.Proofs.GeneralizedSmoothHardChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.TailEntropyHardChain

open TailEntropyCurvature TailEntropyDual TailEntropyConjugate TailEntropyChain TailEntropyTransfer
open CompactConjugate
open GeneralizedSmoothHardDual (radial feasible feasible_zero feasible_compact feasible_norm_bound)
open GeneralizedSmoothHardChain (vertex vertex_feasible vertex_sum vertex_inner inner_prefix_eq)
open KnownGapChainWeights (weight peak weight_pos peak_pos weight_le_peak weight_lower weight_ratio
  weight_strict_order)

noncomputable def level (m : ℕ) (L₀ L₁ ε h : ℝ) : ℝ :=
  2 * (Real.log (1 + L₁ * peak m L₁ ε h / L₀) / L₁) + 28 / L₁ * Real.log m + 140 / (L₁ * h)

noncomputable def shift (m : ℕ) (L₀ L₁ ε h : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ => level m L₀ L₁ ε h)

noncomputable def margin (L₁ : ℝ) : ℝ := 14 / L₁

noncomputable def objective (m : ℕ) (L₀ L₁ ε h : ℝ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  value (feasible (weight m L₁ ε h)) (dual L₀ L₁) (y + shift m L₀ L₁ ε h)

noncomputable def field (m : ℕ) (L₀ L₁ ε h : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  maximizer (feasible (weight m L₁ ε h)) (dual L₀ L₁) (y + shift m L₀ L₁ ε h)

lemma shift_apply (m : ℕ) (L₀ L₁ ε h : ℝ) (i : Fin m) :
    shift m L₀ L₁ ε h i = level m L₀ L₁ ε h := rfl

lemma tailEntropy_vertex {m : ℕ} (G : Fin m → ℝ) (i : Fin m) : tailEntropy (vertex G i) = 0 := by
  unfold tailEntropy
  apply Finset.sum_eq_zero
  intro k hk
  have hkm : k < m := Finset.mem_range.mp hk
  have hext (l : ℕ) : ext (vertex G i) l = if l = i.val then G i else 0 := by
    by_cases hl : l < m
    · simp only [TailEntropyDual.ext, hl, ↓reduceDIte, vertex, Fin.ext_iff]
    · have hne : l ≠ i.val := by omega
      simp only [TailEntropyDual.ext, hl, ↓reduceDIte, hne, ↓reduceIte]
  by_cases hki : k = i.val
  · have ht : tail (ext (vertex G i)) m k = ext (vertex G i) k := by
      rw [tail_succ _ hkm]
      have hz : tail (ext (vertex G i)) m (k + 1) = 0 := by
        unfold tail
        apply Finset.sum_eq_zero
        intro l hl
        simp only [Finset.mem_Ico] at hl
        simp only [hext l, show l ≠ i.val by omega, ↓reduceIte]
      rw [hz, add_zero]
    rw [ht, entropyTerm_self]
  · simp only [hext k, hki, ↓reduceIte, entropyTerm_zero]

section

variable {m : ℕ} (L₀ L₁ ε h : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)

include hL₀ hL₁ hε hh

lemma field_tail_zero (hh1 : h ≤ 1) (j : Fin m) (y : EuclideanSpace ℝ (Fin m)) (hyj : -(margin L₁) ≤ y j)
    (hyl : ∀ l, j < l → y l ≤ margin L₁) :
    ∀ l, j < l → field m L₀ L₁ ε h y l = 0 := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hne : (feasible (weight m L₁ ε h)).Nonempty := ⟨0, feasible_zero _⟩
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK hne hH (y + shift m L₀ L₁ ε h)
  apply optimizer_later_zero L₀ L₁ (peak m L₁ ε h) hL₀ hL₁ (weight m L₁ ε h) hG hB hGB j
    (fun l hl => (weight_strict_order L₁ ε h hL₁ hε hh j l hl).le) _ _ hu.1 hu.2
  intro l hl
  have hjl : (j.val : ℝ) + 1 ≤ l.val := by exact_mod_cast hl
  have hratio : weight m L₁ ε h j / weight m L₁ ε h l = Real.exp (((l.val : ℝ) - j.val) * h) := by
    rw [weight_ratio L₁ ε h j l]
    field_simp [(hG l).ne']
  rw [hratio]
  apply bracket_pos L₁ h _ _ _ _ ((l.val : ℝ) - j.val) hL₁ hh hh1 (by linarith)
  · have he := Real.add_one_le_exp (((l.val : ℝ) - j.val) * h)
    linarith
  · change 2 * (Real.log (1 + L₁ * peak m L₁ ε h / L₀) / L₁) + 28 / L₁ * Real.log m +
      140 / (L₁ * h) - 14 / L₁ ≤ y j + level m L₀ L₁ ε h
    unfold level margin at *
    linarith
  · change y l + level m L₀ L₁ ε h ≤ 2 * (Real.log (1 + L₁ * peak m L₁ ε h / L₀) / L₁) +
      28 / L₁ * Real.log m + 140 / (L₁ * h) + 14 / L₁
    have := hyl l hl
    unfold level margin at *
    linarith

lemma objective_vertex_bound (i : Fin m) (y : EuclideanSpace ℝ (Fin m)) :
    weight m L₁ ε h i * (y i + 140 / (L₁ * h)) ≤ objective m L₀ L₁ ε h y := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hne : (feasible (weight m L₁ ε h)).Nonempty := ⟨0, feasible_zero _⟩
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK hne hH (y + shift m L₀ L₁ ε h)
  have hv := hu.2 (vertex_feasible (weight m L₁ ε h) hG i)
  change ⟪y + shift m L₀ L₁ ε h, vertex (weight m L₁ ε h) i⟫ -
      dual L₀ L₁ (vertex (weight m L₁ ε h) i) ≤ objective m L₀ L₁ ε h y at hv
  rw [vertex_inner] at hv
  have hrad := radial_le L₀ L₁ (weight m L₁ ε h i) (peak m L₁ ε h) hL₀ hL₁ (hG i).le (hGB i)
  have hdual : dual L₀ L₁ (vertex (weight m L₁ ε h) i) =
      2 * radial L₀ L₁ (weight m L₁ ε h i) + 28 / L₁ * Real.log m * weight m L₁ ε h i := by
    unfold dual
    rw [vertex_sum, tailEntropy_vertex]
    ring
  rw [hdual] at hv
  have hshift : (y + shift m L₀ L₁ ε h) i = y i + level m L₀ L₁ ε h := rfl
  rw [hshift] at hv
  unfold level at hv
  nlinarith [hG i]

lemma objective_gap (hh1 : h ≤ 1) (i : Fin m) (y : EuclideanSpace ℝ (Fin m)) (hy : -(margin L₁) ≤ y i) :
    252 * ε ≤ objective m L₀ L₁ ε h y := by
  have hb := objective_vertex_bound L₀ L₁ ε h hL₀ hL₁ hε hh i y
  have hw := weight_lower (m := m) L₁ ε h hL₁ hε hh.le i
  have h140 : 140 / L₁ ≤ 140 / (L₁ * h) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have hmar : margin L₁ = 14 / L₁ := rfl
  have hlow : 126 / L₁ ≤ y i + 140 / (L₁ * h) := by
    have : 126 / L₁ = 140 / L₁ - 14 / L₁ := by ring
    linarith
  have hp : 0 ≤ 126 / L₁ := by positivity
  have hm2 := mul_le_mul hw hlow hp (weight_pos m L₁ ε h hL₁ hε i).le
  have he : 2 * ε * L₁ * (126 / L₁) = 252 * ε := by field_simp; ring
  linarith

lemma objective_hasGradientAt (y : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (objective m L₀ L₁ ε h) (field m L₀ L₁ ε h y) y := by
  have hh' := conjugate_hasGradientAt L₀ L₁ hL₀ hL₁ (weight m L₁ ε h) (peak m L₁ ε h)
    (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le) (y + shift m L₀ L₁ ε h)
  rw [hasGradientAt_iff_hasFDerivAt]
  have ht := hh'.hasFDerivAt.comp y ((hasFDerivAt_id y).add_const (shift m L₀ L₁ ε h))
  convert ht using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_id, field]

lemma field_pair (x y : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε h x - field m L₀ L₁ ε h y‖ ≤
      (L₀ + L₁ * max ‖field m L₀ L₁ ε h x‖ ‖field m L₀ L₁ ε h y‖) * ‖x - y‖ := by
  have hh' := conjugate_field_pair L₀ L₁ hL₀ hL₁ (weight m L₁ ε h) (peak m L₁ ε h)
    (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le)
    (x + shift m L₀ L₁ ε h) (y + shift m L₀ L₁ ε h)
  simpa only [field, add_sub_add_right_eq_sub] using hh'

lemma field_norm_bound (y : EuclideanSpace ℝ (Fin m)) :
    ‖field m L₀ L₁ ε h y‖ ≤ peak m L₁ ε h := by
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  exact feasible_norm_bound _ _ hG hB hGB _
    (maximizer_spec hK ⟨0, feasible_zero _⟩ hH _).1

lemma objective_nonnegative (y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m L₀ L₁ ε h y :=
  conjugate_nonnegative L₀ L₁ hL₀ hL₁ (weight m L₁ ε h) (peak m L₁ ε h)
    (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le) _

lemma objective_zero (y : EuclideanSpace ℝ (Fin m))
    (hy : ∀ i, y i + level m L₀ L₁ ε h ≤ 0) :
    objective m L₀ L₁ ε h y = 0 :=
  conjugate_zero_of_nonpositive L₀ L₁ hL₀ hL₁ (weight m L₁ ε h) (peak m L₁ ε h)
    (weight_pos m L₁ ε h hL₁ hε) (peak_pos m L₁ ε h hL₁ hε).le
    (weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le) _ hy

lemma field_prefix_eq (hh1 : h ≤ 1) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(margin L₁) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ margin L₁)
    (hyt : ∀ i, j < i → y i ≤ margin L₁) :
    field m L₀ L₁ ε h x = field m L₀ L₁ ε h y := by
  let σ := shift m L₀ L₁ ε h
  let u := field m L₀ L₁ ε h x
  let v := field m L₀ L₁ ε h y
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (x + σ)
  have hv := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  have hu0 := field_tail_zero L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j x hxj hxt
  have hyj : -(margin L₁) ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hv0 := field_tail_zero L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j y hyj hyt
  have hab (i : Fin m) (hi : i ≤ j) : (x + σ) i = (y + σ) i := by
    change x i + σ i = y i + σ i
    rw [hxy i hi]
  have heu := inner_prefix_eq j (x + σ) (y + σ) u hab hu0
  have hev := inner_prefix_eq j (x + σ) (y + σ) v hab hv0
  have hg := dual_optimizer_growth L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
    (x + σ) u v hu.1 hv.1 hu.2
  have hvu : ⟪y + σ, u⟫ - dual L₀ L₁ u ≤ ⟪y + σ, v⟫ - dual L₀ L₁ v := hv.2 hu.1
  rw [heu, hev] at hg
  have hn : ‖u - v‖ ^ 2 / (2 * (L₀ + L₁ * max ‖u‖ ‖v‖)) ≤ 0 := by linarith
  have hp : 0 < 2 * (L₀ + L₁ * max ‖u‖ ‖v‖) := by positivity
  have hs := (div_le_iff₀ hp).mp hn
  have he : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma objective_remainder (x y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m L₀ L₁ ε h y - objective m L₀ L₁ ε h x - ⟪field m L₀ L₁ ε h x, y - x⟫ ∧
    objective m L₀ L₁ ε h y - objective m L₀ L₁ ε h x - ⟪field m L₀ L₁ ε h x, y - x⟫ ≤
      (L₀ + L₁ * peak m L₁ ε h) * ‖y - x‖ ^ 2 := by
  let σ := shift m L₀ L₁ ε h
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hu := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (x + σ)
  have hv := maximizer_spec hK ⟨0, feasible_zero _⟩ hH (y + σ)
  have hd : ‖field m L₀ L₁ ε h y - field m L₀ L₁ ε h x‖ ≤
      (L₀ + L₁ * peak m L₁ ε h) * ‖(y + σ) - (x + σ)‖ := by
    rw [add_sub_add_right_eq_sub]
    apply (field_pair L₀ L₁ ε h hL₀ hL₁ hε hh y x).trans
    gcongr
    exact max_le (field_norm_bound L₀ L₁ ε h hL₀ hL₁ hε hh y)
      (field_norm_bound L₀ L₁ ε h hL₀ hL₁ hε hh x)
  have hh' := value_remainder_bound (dual L₀ L₁) (x + σ) (y + σ)
    (field m L₀ L₁ ε h x) (field m L₀ L₁ ε h y) (L₀ + L₁ * peak m L₁ ε h)
    (hu.2 hv.1) (hv.2 hu.1) hd
  simpa only [add_sub_add_right_eq_sub, objective, value, field, σ] using hh'

lemma objective_convex : ConvexOn ℝ univ (objective m L₀ L₁ ε h) := by
  let σ := shift m L₀ L₁ ε h
  have hG := weight_pos m L₁ ε h hL₁ hε
  have hB := (peak_pos m L₁ ε h hL₁ hε).le
  have hGB := weight_le_peak (m := m) L₁ ε h hL₁ hε hh.le
  have hK := feasible_compact (weight m L₁ ε h) (peak m L₁ ε h) hG hB hGB
  have hH := dual_continuousOn_feasible L₀ L₁ hL₀ hL₁ (weight m L₁ ε h)
  have hc := value_convex hK ⟨0, feasible_zero _⟩ hH
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh' := hc.2 (mem_univ (x + σ)) (mem_univ (y + σ)) ha hb hab
  have he : a • (x + σ) + b • (y + σ) = (a • x + b • y) + σ := by
    calc
      _ = (a • x + b • y) + (a + b) • σ := by simp only [smul_add, add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  rw [he] at hh'
  exact hh'

lemma field_lipschitz :
    LipschitzWith ⟨L₀ + L₁ * peak m L₁ ε h,
      by have hp := peak_pos m L₁ ε h hL₁ hε; positivity⟩ (field m L₀ L₁ ε h) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖field m L₀ L₁ ε h x - field m L₀ L₁ ε h y‖ ≤ (L₀ + L₁ * peak m L₁ ε h) * ‖x - y‖
  apply (field_pair L₀ L₁ ε h hL₀ hL₁ hε hh x y).trans
  gcongr
  exact max_le (field_norm_bound L₀ L₁ ε h hL₀ hL₁ hε hh x)
    (field_norm_bound L₀ L₁ ε h hL₀ hL₁ hε hh y)

lemma objective_prefix_eq (hh1 : h ≤ 1) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(margin L₁) ≤ x j)
    (hxt : ∀ i, j < i → x i ≤ margin L₁)
    (hyt : ∀ i, j < i → y i ≤ margin L₁) :
    objective m L₀ L₁ ε h x = objective m L₀ L₁ ε h y := by
  let σ := shift m L₀ L₁ ε h
  have hg := field_prefix_eq L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j x y hxy hxj hxt hyt
  have hyj : -(margin L₁) ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hz := field_tail_zero L₀ L₁ ε h hL₀ hL₁ hε hh hh1 j y hyj hyt
  have he := inner_prefix_eq j (x + σ) (y + σ) (field m L₀ L₁ ε h y)
    (fun i hi => by change x i + σ i = y i + σ i; rw [hxy i hi]) hz
  change ⟪x + σ, field m L₀ L₁ ε h x⟫ - dual L₀ L₁ (field m L₀ L₁ ε h x) =
    ⟪y + σ, field m L₀ L₁ ε h y⟫ - dual L₀ L₁ (field m L₀ L₁ ε h y)
  rw [hg, he]

end

end LongTails.Proofs.TailEntropyHardChain
