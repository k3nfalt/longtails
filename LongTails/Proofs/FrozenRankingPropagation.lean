import LongTails.Proofs.SpatialRankingMargins

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FrozenRankingPropagation

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features shift margin)
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
open LongTails.Proofs.LogisticPathLocality
open LongTails.Proofs.SpatialRankingExecution
open LongTails.Proofs.SpatialRankingGradients
open LongTails.Proofs.SpatialRankingMargins

noncomputable def filterMap {d : ℕ} (c : ℝ × ℝ) : Features d →ₗ[ℝ] Features d where
  toFun x := c.1 • x + c.2 • shift x
  map_add' x y := by rw [shift_add, smul_add, smul_add]; abel
  map_smul' k x := by rw [shift_smul, smul_add]; dsimp; module

lemma filtered_gram {p : Params} {D : Items p} (hD : Geometry p D)
    (c : ℝ × ℝ) (g h : Bool) {i j : ℕ} (hi : i ≤ p.n) (hj : j ≤ p.n) :
    ⟪filterMap c (vertex p D g i), filterMap c (vertex p D h j)⟫ =
    if g=h then (if i=j then c.1^2+c.2^2 else 0) +
      c.1*c.2*(lagEntry p.n g i j + lagEntry p.n g j i) else 0 := by
  change ⟪c.1 • vertex p D g i + c.2 • shift (vertex p D g i),
    c.1 • vertex p D h j + c.2 • shift (vertex p D h j)⟫ = _
  have hs := (real_inner_comm (vertex p D h j) (shift (vertex p D g i))).trans
    (vertex_lag hD h g hj hi)
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_shift_shift, vertex_inner hD _ _ hi hj, vertex_lag hD _ _ hi hj,
    hs]
  by_cases hg : g=h
  · subst h
    by_cases hij : i=j <;> simp [hij] <;> ring
  · simp [hg, Ne.symm hg]

lemma force_projection {p : Params} {D : Items p} (hD : Geometry p D)
    (c : ℝ × ℝ) (θ : Point p) (g h : Bool) {i : ℕ} (hl : 0 < i) (hr : i < p.n) :
    let q := mass p D θ g
    ⟪filterMap c (force p D θ g), filterMap c (vertex p D h i)⟫ =
      if g=h then (q 0 + q (p.n-1))*c.1*c.2*traceValue p.n g i +
        (q i - q (i-1))*(c.1^2+c.2^2+2*c.1*c.2*(population g).itemLag)
      else 0 := by
  let q := mass p D θ g
  let U (j : ℕ) := filterMap c (vertex p D g j)
  let y := filterMap c (vertex p D h i)
  have hmap : filterMap c (force p D θ g) = edgeForce p.n U q := by
    unfold force edgeForce
    simp [U, q, map_sum, map_smul, map_sub]
  rw [hmap]
  have gram (j : ℕ) (hj : j ≤ p.n) := filtered_gram hD c g h hj hr.le
  let k := if g=h then c.1^2+c.2^2+2*c.1*c.2*(population g).itemLag else 0
  let τ := if g=h then c.1*c.2*traceValue p.n g i else 0
  have he : p.n-1+1=p.n := by omega
  have e := weighted_interior (n := p.n-1) (j := i-1) (by omega) U y q k τ
  rw [he, show i-1+1=i by omega] at e
  have hl' : ⟪U 0,y⟫ = τ := by
    rw [show ⟪U 0,y⟫ = _ from gram 0 (by omega)]
    by_cases H : g=h <;> simp (disch := omega) [H, lagEntry, τ, hl, hl.ne, hl.ne', hr,
      show 0 ≠ p.n by omega]
  have hr' : ⟪U p.n,y⟫ = -τ := by
    rw [show ⟪U p.n,y⟫ = _ from gram p.n le_rfl]
    by_cases H : g=h <;> simp (disch := omega) [H, lagEntry, τ, hl, hl.ne', hr, hr.ne,
      hr.ne', show p.n ≠ 0 by omega]
  have hd (j : ℕ) (hj : j < p.n-1) : ⟪U (j+1),y⟫ = if j=i-1 then k else 0 := by
    rw [show ⟪U (j+1),y⟫ = _ from gram (j+1) (by omega)]
    by_cases hg : g=h <;> by_cases hij : j=i-1
    all_goals simp (disch := omega) only [k, lagEntry, ite_eq_left, ite_eq_right, ite_true,
      ite_false, hg, hij]
    all_goals simp <;> ring
  rw [e hl' hr' hd]
  by_cases H : g=h <;> simp [k, τ, H, q]
  ring

noncomputable def frozenBatch (p : Params) (D : Items p) (θ : Point p) (h : ℝ) : Point p :=
  (θ.1, θ.2 + h • filterMap θ.1 (force p D θ false + force p D θ true))

def Interior (p : Params) (D : Items p) (c : ℝ × ℝ) (t : ℕ) (θ : Point p) : Prop :=
  θ.1=c ∧ ∀ g, ∃ l : ℝ, 0 ≤ l ∧ ∀ i, t < i → i+t < p.n →
    score p D g i θ = c.1*c.2*l*traceValue p.n g i

lemma initial_interior (p : Params) (D : Items p) (c : ℝ × ℝ) :
    Interior p D c 0 (c,0) := by
  refine ⟨rfl, fun g => ⟨0, le_rfl, ?_⟩⟩
  intro i hl hr
  simp [score, margin]

lemma mass_nonneg (p : Params) (D : Items p) (θ : Point p) (g : Bool) (i : ℕ) :
    0 ≤ mass p D θ g i := by
  unfold mass
  apply mul_nonneg (Real.sigmoid_nonneg _)
  cases g <;> norm_num [population, first, second]

lemma interior_step {p : Params} {D : Items p} (hD : Geometry p D) (c : ℝ × ℝ)
    (t : ℕ) (θ : Point p) (h : ℝ) (hh : 0 ≤ h) (H : Interior p D c t θ) :
    Interior p D c (t+1) (frozenBatch p D θ h) := by
  refine ⟨H.1, ?_⟩
  intro g
  obtain ⟨l,hl,hi⟩ := H.2 g
  let q := mass p D θ g
  refine ⟨l+h*(q 0 + q (p.n-1)), add_nonneg hl (mul_nonneg hh (add_nonneg
    (mass_nonneg _ _ _ _ _) (mass_nonneg _ _ _ _ _))), ?_⟩
  intro i hL hR
  have hqi : q i = q (i-1) := by
    have e : i-1+1=i := by omega
    have hs₁ := trace_step p.n (i-1) g (by omega)
    rw [e] at hs₁
    have hs₂ := trace_step p.n i g (by omega)
    unfold q mass
    rw [margin_eq D g (by omega : i < p.n), margin_eq D g (by omega : i-1 < p.n), e,
      hi i (by omega) (by omega), hi (i+1) (by omega) (by omega), hi (i-1) (by omega) (by omega)]
    congr 3
    rw [hs₂, hs₁]
    ring
  have hz : score p D g i (frozenBatch p D θ h) = score p D g i θ +
      h*(⟪filterMap c (force p D θ false),filterMap c (vertex p D g i)⟫ +
         ⟪filterMap c (force p D θ true),filterMap c (vertex p D g i)⟫) := by
    simp only [frozenBatch, score, margin, H.1, map_add, inner_add_right, real_inner_smul_right]
    have E (x : Features p.d) : ⟪x,filterMap c (vertex p D g i)⟫ =
        c.1*⟪vertex p D g i,x⟫ + c.2*⟪shift (vertex p D g i),x⟫ := by
      rw [real_inner_comm]
      change ⟪c.1 • vertex p D g i + c.2 • shift (vertex p D g i), x⟫ = _
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [E, E]
    ring
  rw [hz, force_projection hD _ _ _ _ (by omega) (by omega),
    force_projection hD _ _ _ _ (by omega) (by omega), hi i (by omega) (by omega)]
  change mass p D θ g i = mass p D θ g (i-1) at hqi
  cases g <;> simp [q, hqi] <;> ring

lemma fails_inside {p : Params} {D : Items p} (c : ℝ × ℝ) (t : ℕ) (θ : Point p)
    (H : Interior p D c t θ) (ht : 2*t+2 < p.n) : ¬Separates p D θ := by
  intro hs
  have he (g : Bool) : 0 < -(population g).scale*(c.1*c.2)*(population g).slope *
      (u p.n)*(v p.n)*(Classical.choose (H.2 g)) := by
    obtain ⟨hl, hh⟩ := Classical.choose_spec (H.2 g)
    have h := hs g (t+1) (by omega)
    rw [margin_eq D g (by omega), hh _ (by omega) (by omega), hh _ (by omega) (by omega),
      trace_step _ (t+1) _ (by omega)] at h
    linarith only [h]
  have hp (g : Bool) : 0 ≤ Classical.choose (H.2 g) := (Classical.choose_spec (H.2 g)).1
  have hu : 0 ≤ u p.n := by unfold u; positivity
  have hv : 0 ≤ v p.n := by unfold v; positivity
  by_cases hc : 0 ≤ c.1*c.2
  · have H := he true
    norm_num [population, second] at H
    nlinarith only [H, mul_nonneg (mul_nonneg (mul_nonneg hc hu) hv) (hp true)]
  · have H := he false
    norm_num [population, first] at H
    nlinarith only [H, mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) hu) hv) (hp false)]

end LongTails.Proofs.FrozenRankingPropagation
