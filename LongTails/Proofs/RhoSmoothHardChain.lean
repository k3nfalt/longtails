import LongTails.Proofs.RhoSmoothHardDual
import LongTails.Proofs.TailEntropyTransfer
import LongTails.Proofs.GeneralizedSmoothHardChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped BigOperators Topology RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothHardChain

open RhoSmoothLocal RhoSmoothHardDual CompactConjugate TailEntropyTransfer
open GeneralizedSmoothHardDual (feasible feasible_zero feasible_compact feasible_norm_bound)
open GeneralizedSmoothHardChain (vertex vertex_feasible vertex_inner inner_prefix_eq)

noncomputable def weight (m : ℕ) (g : ℝ) (i : Fin m) : ℝ := g * 2 ^ (m - 1 - i.val)

noncomputable def peak (m : ℕ) (g : ℝ) : ℝ := g * 2 ^ (m - 1)

noncomputable def shift (m : ℕ) (σ : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ => σ)

noncomputable def objective (m : ℕ) (A G ρ g σ : ℝ) (y : EuclideanSpace ℝ (Fin m)) : ℝ :=
  value (feasible (weight m g)) (dual A G ρ) (y + shift m σ)

noncomputable def field (m : ℕ) (A G ρ g σ : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  maximizer (feasible (weight m g)) (dual A G ρ) (y + shift m σ)

lemma shift_apply (m : ℕ) (σ : ℝ) (i : Fin m) : shift m σ i = σ := rfl

section

variable {m : ℕ} {g : ℝ} (hg : 0 < g)
include hg

lemma weight_pos (i : Fin m) : 0 < weight m g i := by
  unfold weight
  positivity

lemma peak_pos : 0 < peak m g := by
  unfold peak
  positivity

lemma weight_le_peak (i : Fin m) : weight m g i ≤ peak m g := by
  unfold weight peak
  apply mul_le_mul_of_nonneg_left _ hg.le
  exact pow_le_pow_right₀ (by norm_num) (by omega)

lemma weight_ge (i : Fin m) : g ≤ weight m g i := by
  unfold weight
  have : (1 : ℝ) ≤ 2 ^ (m - 1 - i.val) := one_le_pow₀ (by norm_num)
  nlinarith

lemma weight_double {j l : Fin m} (hjl : j < l) : 2 * weight m g l ≤ weight m g j := by
  unfold weight
  have hl := l.isLt
  have hj : j.val < l.val := hjl
  have hexp : m - 1 - l.val + 1 ≤ m - 1 - j.val := by omega
  have hp : (2 : ℝ) ^ (m - 1 - l.val + 1) ≤ 2 ^ (m - 1 - j.val) :=
    pow_le_pow_right₀ (by norm_num) hexp
  rw [pow_succ] at hp
  nlinarith

lemma weight_order {j l : Fin m} (hjl : j < l) : weight m g l ≤ weight m g j := by
  have h := weight_double hg hjl
  have := weight_pos hg (m := m) l
  linarith

end

section

variable {m : ℕ} (A G ρ L₀ L₁ g σ : ℝ) (hA : 0 < A) (hG : 0 < G) (hρ : 1 < ρ) (hρ2 : ρ ≤ 2)
  (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hAG : A * (ρ - 1) = 2 * G / L₀) (hGL : G ^ ρ * L₁ = L₀)
  (hg : 0 < g)

include hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg

omit hA hG hρ hρ2 hL₀ hL₁ hAG hGL in
lemma compact_feasible : IsCompact (feasible (weight m g)) :=
  feasible_compact _ (peak m g) (weight_pos hg) (peak_pos hg).le (weight_le_peak hg)

omit hA hρ hρ2 hL₀ hL₁ hAG hGL in
lemma maximizer_props (a : EuclideanSpace ℝ (Fin m)) :
    maximizer (feasible (weight m g)) (dual A G ρ) a ∈ feasible (weight m g) ∧
      IsMaxOn (fun v => ⟪a, v⟫ - dual A G ρ v) (feasible (weight m g))
        (maximizer (feasible (weight m g)) (dual A G ρ) a) :=
  maximizer_spec (compact_feasible g hg) ⟨0, feasible_zero _⟩
    (dual_continuous A G ρ hG).continuousOn a

omit hA hρ hρ2 hL₀ hL₁ hAG hGL in
lemma field_norm_bound (y : EuclideanSpace ℝ (Fin m)) : ‖field m A G ρ g σ y‖ ≤ peak m g :=
  feasible_norm_bound _ _ (weight_pos hg) (peak_pos hg).le (weight_le_peak hg) _
    (maximizer_props A G ρ g hG hg _).1

lemma field_pair (x y : EuclideanSpace ℝ (Fin m)) :
    ‖field m A G ρ g σ x - field m A G ρ g σ y‖ ≤
      curv L₀ L₁ ρ (max ‖field m A G ρ g σ x‖ ‖field m A G ρ g σ y‖) * ‖x - y‖ := by
  set u := field m A G ρ g σ x
  set v := field m A G ρ g σ y
  have hu := maximizer_props A G ρ g hG hg (x + shift m σ)
  have hv := maximizer_props A G ρ g hG hg (y + shift m σ)
  have h1 := dual_growth A G ρ L₀ L₁ hA hG hρ hρ2 hL₀ hL₁ hAG hGL (weight m g) (weight_pos hg)
    (x + shift m σ) u v hu.1 hv.1 hu.2
  have h2 := dual_growth A G ρ L₀ L₁ hA hG hρ hρ2 hL₀ hL₁ hAG hGL (weight m g) (weight_pos hg)
    (y + shift m σ) v u hv.1 hu.1 hv.2
  rw [norm_sub_rev v u, max_comm] at h2
  have hM : 0 < curv L₀ L₁ ρ (max ‖u‖ ‖v‖) :=
    curv_pos hL₀ hL₁.le ((norm_nonneg u).trans (le_max_left _ _))
  have hd := maximizer_distance_bound (dual A G ρ) (x + shift m σ) (y + shift m σ) u v _ hM h1 h2
  rwa [add_sub_add_right_eq_sub] at hd

lemma field_lipschitz :
    LipschitzWith ⟨curv L₀ L₁ ρ (peak m g),
      (curv_pos hL₀ hL₁.le (peak_pos hg).le).le⟩ (field m A G ρ g σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change ‖field m A G ρ g σ x - field m A G ρ g σ y‖ ≤ curv L₀ L₁ ρ (peak m g) * ‖x - y‖
  apply (field_pair A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg x y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact curv_mono hL₁.le (by linarith) (le_max_of_le_left (norm_nonneg _))
    (max_le (field_norm_bound A G ρ g σ hG hg x) (field_norm_bound A G ρ g σ hG hg y))

lemma objective_remainder (x y : EuclideanSpace ℝ (Fin m)) :
    0 ≤ objective m A G ρ g σ y - objective m A G ρ g σ x - ⟪field m A G ρ g σ x, y - x⟫ ∧
    objective m A G ρ g σ y - objective m A G ρ g σ x - ⟪field m A G ρ g σ x, y - x⟫ ≤
      curv L₀ L₁ ρ (peak m g) * ‖y - x‖ ^ 2 := by
  have hu := maximizer_props A G ρ g hG hg (x + shift m σ)
  have hv := maximizer_props A G ρ g hG hg (y + shift m σ)
  have hd : ‖field m A G ρ g σ y - field m A G ρ g σ x‖ ≤
      curv L₀ L₁ ρ (peak m g) * ‖(y + shift m σ) - (x + shift m σ)‖ := by
    rw [add_sub_add_right_eq_sub]
    exact (field_lipschitz A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg).dist_le_mul y x
  have hh := value_remainder_bound (dual A G ρ) (x + shift m σ) (y + shift m σ)
    (field m A G ρ g σ x) (field m A G ρ g σ y) (curv L₀ L₁ ρ (peak m g))
    (hu.2 hv.1) (hv.2 hu.1) hd
  simpa only [add_sub_add_right_eq_sub, objective, value, field] using hh

lemma objective_hasGradientAt (y : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (objective m A G ρ g σ) (field m A G ρ g σ y) y :=
  hasGradientAt_of_quadratic_remainder _ _ _ _
    (objective_remainder A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg y)

omit hA hρ hρ2 hL₀ hL₁ hAG hGL in
lemma objective_convex : ConvexOn ℝ univ (objective m A G ρ g σ) := by
  have hc := value_convex (compact_feasible g hg) ⟨0, feasible_zero _⟩
    (dual_continuous (m := m) A G ρ hG).continuousOn
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := hc.2 (mem_univ (x + shift m σ)) (mem_univ (y + shift m σ)) ha hb hab
  have he : a • (x + shift m σ) + b • (y + shift m σ) = (a • x + b • y) + shift m σ := by
    calc
      _ = (a • x + b • y) + (a + b) • shift m σ := by simp only [smul_add, add_smul]; abel
      _ = _ := by rw [hab, one_smul]
  rw [he] at hh
  exact hh

omit hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg in
lemma dual_zero : dual (m := m) A G ρ 0 = 0 := by
  simp [dual, penalty_zero]

omit hρ2 hL₀ hL₁ hAG hGL hg in
lemma dual_nonneg (z : EuclideanSpace ℝ (Fin m)) (hz : ∀ i, 0 ≤ z i) : 0 ≤ dual A G ρ z :=
  Finset.sum_nonneg (fun i _ => penalty_nonneg A G ρ hA hG hρ (hz i))

omit hA hρ hρ2 hL₀ hL₁ hAG hGL in
lemma objective_nonnegative (y : EuclideanSpace ℝ (Fin m)) : 0 ≤ objective m A G ρ g σ y := by
  have h := (maximizer_props A G ρ g hG hg (y + shift m σ)).2 (feasible_zero (weight m g))
  change ⟪y + shift m σ, 0⟫ - dual A G ρ 0 ≤ objective m A G ρ g σ y at h
  rw [inner_zero_right, dual_zero A G ρ] at h
  linarith

omit hρ2 hL₀ hL₁ hAG hGL in
lemma objective_zero (y : EuclideanSpace ℝ (Fin m)) (hy : ∀ i, y i + σ ≤ 0) :
    objective m A G ρ g σ y = 0 := by
  apply le_antisymm _ (objective_nonnegative A G ρ g σ hG hg y)
  have hu := maximizer_props A G ρ g hG hg (y + shift m σ)
  set u := maximizer (feasible (weight m g)) (dual A G ρ) (y + shift m σ)
  change ⟪y + shift m σ, u⟫ - dual A G ρ u ≤ 0
  have hi : ⟪y + shift m σ, u⟫ ≤ 0 := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_nonpos
    intro i _
    have h1 := hu.1.1 i
    have h2 : (y + shift m σ) i = y i + σ := rfl
    rw [h2]
    nlinarith [hy i]
  have := dual_nonneg A G ρ hA hG hρ u hu.1.1
  linarith

omit hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg in
lemma dual_vertex (i : Fin m) :
    dual A G ρ (vertex (weight m g) i) = penalty A G ρ (weight m g i) := by
  unfold dual
  have he (k : Fin m) : penalty A G ρ (vertex (weight m g) i k) =
      if k = i then penalty A G ρ (weight m g i) else 0 := by
    change penalty A G ρ (if k = i then weight m g i else 0) = _
    split_ifs
    · rfl
    · exact penalty_zero A G ρ
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

omit hρ hρ2 hL₀ hL₁ hAG hGL in
lemma objective_vertex_bound (i : Fin m) (y : EuclideanSpace ℝ (Fin m)) :
    weight m g i * (y i + σ - A) ≤ objective m A G ρ g σ y := by
  have hv := (maximizer_props A G ρ g hG hg (y + shift m σ)).2
    (vertex_feasible (weight m g) (weight_pos hg) i)
  change ⟪y + shift m σ, vertex (weight m g) i⟫ - dual A G ρ (vertex (weight m g) i) ≤
    objective m A G ρ g σ y at hv
  rw [vertex_inner, dual_vertex A G ρ g] at hv
  have hp := penalty_le A G ρ hA hG (weight_pos hg i).le
  have hs : (y + shift m σ) i = y i + σ := rfl
  rw [hs] at hv
  nlinarith

omit hρ hρ2 hL₀ hL₁ hAG hGL in
lemma objective_gap (θ : ℝ) (hσ : θ + A ≤ σ) (i : Fin m) (y : EuclideanSpace ℝ (Fin m))
    (hy : -θ ≤ y i) : g * (σ - θ - A) ≤ objective m A G ρ g σ y := by
  have hb := objective_vertex_bound A G ρ g σ hA hG hg i y
  have hw := weight_ge hg i
  have h1 : 0 ≤ σ - θ - A := by linarith
  have h2 : σ - θ - A ≤ y i + σ - A := by linarith
  have := mul_le_mul hw h2 h1 (weight_pos hg i).le
  linarith

omit hρ2 hL₀ hL₁ hAG hGL in
lemma dual_transfer_le (j : Fin m) (u : EuclideanSpace ℝ (Fin m)) (hu : u ∈ feasible (weight m g)) :
    dual A G ρ (transfer (weight m g) j u) - dual A G ρ u ≤ A * moved (weight m g) j u := by
  unfold dual
  rw [← Finset.sum_sub_distrib]
  have hm := moved_nonneg (weight m g) j u (weight_pos hg) hu
  have hterm (i : Fin m) : penalty A G ρ (transfer (weight m g) j u i) - penalty A G ρ (u i) ≤
      if i = j then A * moved (weight m g) j u else 0 := by
    rw [transfer_apply]
    by_cases hij : i = j
    · subst hij
      simp only [lt_irrefl, ↓reduceIte, sub_zero]
      have := penalty_sub_le A G ρ hA hG (show u i ≤ u i + moved (weight m g) i u by linarith)
      simpa using this
    · simp only [hij, ↓reduceIte, add_zero]
      by_cases hji : j < i
      · simp only [hji, ↓reduceIte, sub_self, penalty_zero]
        have := penalty_nonneg A G ρ hA hG hρ (hu.1 i)
        linarith
      · simp [hji]
  calc
    _ ≤ ∑ i, (if i = j then A * moved (weight m g) j u else 0) :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = _ := by simp

omit hρ2 hL₀ hL₁ hAG hGL in
lemma field_tail_zero (θ : ℝ) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ) (j : Fin m)
    (y : EuclideanSpace ℝ (Fin m)) (hyj : -θ ≤ y j) (hyl : ∀ l, j < l → y l ≤ θ) :
    ∀ l, j < l → field m A G ρ g σ y l = 0 := by
  have hp := maximizer_props A G ρ g hG hg (y + shift m σ)
  set u := field m A G ρ g σ y
  set a := y + shift m σ
  have hu : u ∈ feasible (weight m g) := hp.1
  by_contra hcon
  push Not at hcon
  obtain ⟨l₀, hl₀, hne⟩ := hcon
  have hpos : 0 < u l₀ := lt_of_le_of_ne (hu.1 l₀) (Ne.symm hne)
  set v := transfer (weight m g) j u
  have hvf := transfer_feasible (weight m g) j u (weight_pos hg)
    (fun l hl => weight_order hg hl) hu
  have hle := hp.2 hvf
  change ⟪a, v⟫ - dual A G ρ v ≤ ⟪a, u⟫ - dual A G ρ u at hle
  have hdual := dual_transfer_le A G ρ g hA hG hρ hg j u hu
  have hinner := transfer_inner (weight m g) j u a
  have haj : a j = y j + σ := rfl
  have hal (l : Fin m) : a l = y l + σ := rfl
  have hgain : ∑ l, (if j < l then u l * ((a j - A) * (weight m g j / weight m g l) - a l) else 0) ≤
      (⟪a, v⟫ - dual A G ρ v) - (⟪a, u⟫ - dual A G ρ u) := by
    have hlin : ⟪a, v⟫ - ⟪a, u⟫ = a j * moved (weight m g) j u -
        ∑ l, (if j < l then a l * u l else 0) := by
      rw [hinner]; ring
    have hcomb : ∑ l, (if j < l then u l * ((a j - A) * (weight m g j / weight m g l) - a l)
        else 0) = (a j - A) * moved (weight m g) j u - ∑ l, (if j < l then a l * u l else 0) := by
      unfold moved
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l _
      split_ifs <;> ring
    rw [hcomb]
    linarith
  have hterm : ∀ l ∈ Finset.univ, 0 ≤ (if j < l then
      u l * ((a j - A) * (weight m g j / weight m g l) - a l) else 0) := by
    intro l _
    split_ifs with hl
    · apply mul_nonneg (hu.1 l)
      have hr : 2 ≤ weight m g j / weight m g l := by
        rw [le_div_iff₀ (weight_pos hg l)]
        exact weight_double hg hl
      have h1 : 0 ≤ a j - A := by rw [haj]; linarith
      have h2 := mul_le_mul_of_nonneg_left hr h1
      have h3 := hyl l hl
      rw [hal l]
      linarith
    · exact le_rfl
  have hsingle := Finset.single_le_sum hterm (Finset.mem_univ l₀)
  simp only [hl₀, ↓reduceIte] at hsingle
  have hstrict : 0 < (a j - A) * (weight m g j / weight m g l₀) - a l₀ := by
    have hr : 2 ≤ weight m g j / weight m g l₀ := by
      rw [le_div_iff₀ (weight_pos hg l₀)]
      exact weight_double hg hl₀
    have h1 : 0 ≤ a j - A := by rw [haj]; linarith
    have h2 := mul_le_mul_of_nonneg_left hr h1
    have h3 := hyl l₀ hl₀
    rw [hal l₀]
    linarith
  have hpos' := mul_pos hpos hstrict
  linarith

lemma field_prefix_eq (θ : ℝ) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -θ ≤ x j) (hxt : ∀ i, j < i → x i ≤ θ) (hyt : ∀ i, j < i → y i ≤ θ) :
    field m A G ρ g σ x = field m A G ρ g σ y := by
  set u := field m A G ρ g σ x
  set v := field m A G ρ g σ y
  have hu := maximizer_props A G ρ g hG hg (x + shift m σ)
  have hv := maximizer_props A G ρ g hG hg (y + shift m σ)
  have hu0 := field_tail_zero A G ρ g σ hA hG hρ hg θ hθ hσ j x hxj hxt
  have hyj : -θ ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hv0 := field_tail_zero A G ρ g σ hA hG hρ hg θ hθ hσ j y hyj hyt
  have hab (i : Fin m) (hi : i ≤ j) : (x + shift m σ) i = (y + shift m σ) i := by
    change x i + σ = y i + σ
    rw [hxy i hi]
  have heu := inner_prefix_eq j (x + shift m σ) (y + shift m σ) u hab hu0
  have hev := inner_prefix_eq j (x + shift m σ) (y + shift m σ) v hab hv0
  have hgr := dual_growth A G ρ L₀ L₁ hA hG hρ hρ2 hL₀ hL₁ hAG hGL (weight m g) (weight_pos hg)
    (x + shift m σ) u v hu.1 hv.1 hu.2
  have hvu : ⟪y + shift m σ, u⟫ - dual A G ρ u ≤ ⟪y + shift m σ, v⟫ - dual A G ρ v := hv.2 hu.1
  rw [heu, hev] at hgr
  have hM : 0 < 2 * curv L₀ L₁ ρ (max ‖u‖ ‖v‖) :=
    mul_pos (by norm_num) (curv_pos hL₀ hL₁.le ((norm_nonneg u).trans (le_max_left _ _)))
  have hn : ‖u - v‖ ^ 2 / (2 * curv L₀ L₁ ρ (max ‖u‖ ‖v‖)) ≤ 0 := by linarith
  have hs := (div_le_iff₀ hM).mp hn
  have he : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

lemma objective_prefix_eq (θ : ℝ) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -θ ≤ x j) (hxt : ∀ i, j < i → x i ≤ θ) (hyt : ∀ i, j < i → y i ≤ θ) :
    objective m A G ρ g σ x = objective m A G ρ g σ y := by
  have hgf := field_prefix_eq A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg θ hθ hσ j x y
    hxy hxj hxt hyt
  have hyj : -θ ≤ y j := by rw [← hxy j le_rfl]; exact hxj
  have hz := field_tail_zero A G ρ g σ hA hG hρ hg θ hθ hσ j y hyj hyt
  have he := inner_prefix_eq j (x + shift m σ) (y + shift m σ) (field m A G ρ g σ y)
    (fun i hi => by change x i + σ = y i + σ; rw [hxy i hi]) hz
  change ⟪x + shift m σ, field m A G ρ g σ x⟫ - dual A G ρ (field m A G ρ g σ x) =
    ⟪y + shift m σ, field m A G ρ g σ y⟫ - dual A G ρ (field m A G ρ g σ y)
  rw [hgf, he]

end

end LongTails.Proofs.RhoSmoothHardChain
