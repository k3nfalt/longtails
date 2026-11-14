import LongTails.Proofs.CoupledMinimaxInner
import LongTails.Proofs.CoupledMinimaxValue

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledMinimaxOuter

open OracleTemplate
open LongTails.Setups.CoupledStronglyConcaveMinimax
open LongTails.Algorithms.CoupledMinimax
open LongTails.Proofs.CoupledMinimaxGeometry
open LongTails.Proofs.CoupledMinimaxTuning
open LongTails.Proofs.CoupledMinimaxInner
open LongTails.Proofs.CoupledMinimaxValue

lemma valueSmoothness_pos {p : Params} (hv : Valid p) : 0 < valueSmoothness p := by
  unfold valueSmoothness
  have hL := smoothness_pos hv
  have hμ := hv.μ_pos
  positivity

lemma projected_descent {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    (g : MinSpace p) {e : ℝ}
    (herr : ‖minGradient p (exactReply p I (query p q (optimizer I q))) q.snd - g‖ ≤ e) :
    let q' := SaddlePoint.project (minDomain p) (q - (1 / (2 * valueSmoothness p)) • g)
    value I q' ≤ value I q - valueSmoothness p * ‖q' - q‖ ^ 2 +
      e ^ 2 / (2 * valueSmoothness p) := by
  let L := valueSmoothness p
  let q' := SaddlePoint.project (minDomain p) (q - (1 / (2 * L)) • g)
  have hL : 0 < L := valueSmoothness_pos hv
  have hs := projectMin_spec hv (q - (1 / (2 * L)) • g)
  have hp := hs.2 q hq
  have hproj : ⟪g, q' - q⟫ ≤ -(2 * L) * ‖q' - q‖ ^ 2 := by
    have he : q - (1 / (2 * L)) • g - q' = -(q' - q) - (1 / (2 * L)) • g := by module
    have he' : q - q' = -(q' - q) := by abel
    change ⟪q - (1 / (2 * L)) • g - q', q - q'⟫ ≤ 0 at hp
    rw [he, he', inner_sub_left, inner_neg_left, inner_neg_right,
      real_inner_smul_left, inner_neg_right, real_inner_self_eq_norm_sq] at hp
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * L)
    have hc : (2 * L) * (1 / (2 * L)) = 1 := by field_simp
    have hci := congrArg (fun r : ℝ => r * ⟪g, q' - q⟫) hc
    nlinarith
  exact CoupledMinimaxDescent.outer_descent hL herr (value_upper hv H hq hs.1) hproj

lemma cleanup_outer_error {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p)
    {y : YSpace p} (hy : y ∈ p.Y)
    (herr : ‖y - optimizer I q‖ ≤ tolerance p / (12 * smoothness p)) :
    let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
    ‖minGradient p (exactReply p I (query p q (optimizer I q))) q.snd -
      minGradient p (exactReply p I (query p q b)) q.snd‖ ≤ tolerance p / 6 := by
  let b := SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y)
  obtain ⟨hu, hm⟩ := optimizer_spec hv H hq
  have hb := (projectY_spec hv (y - (1 / smoothness p) • innerGradient I q y)).1
  have hd := (cleanup_distance hv H hq hu hy hm).trans herr
  have hg := min_gradient_inner_lipschitz hv H hq hu hb
  rw [norm_sub_rev (optimizer I q) b] at hg
  have hL := smoothness_pos hv
  have ht := tolerance_pos hv
  have hh := hg.trans (mul_le_mul_of_nonneg_left hd hL.le)
  have he : smoothness p * (tolerance p / (12 * smoothness p)) = tolerance p / 12 := by
    field_simp
  rw [he] at hh
  exact hh.trans (by linarith)

lemma step_descent {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) {q : MinSpace p} (hq : q ∈ minDomain p) :
    let r := QueryPlan.eval (exactReply p I) (step p q)
    value I r.1 ≤ value I q - valueSmoothness p * r.2.displacement ^ 2 +
      tolerance p ^ 2 / (72 * valueSmoothness p) := by
  let y := QueryPlan.eval (exactReply p I)
    (Algorithms.CoupledMinimaxInner.restart (query p q)
      (fun r => -(lagrangianGradient p r q.snd).snd) (SaddlePoint.project p.Y)
      (smoothness p) (innerIterations p) (innerRestarts p) p.y0)
  obtain ⟨hu, hm⟩ := optimizer_spec hv H hq
  have hy := mapped_accuracy hv H hq hu hm
  let b := SaddlePoint.project p.Y (y + (1 / smoothness p) •
    (lagrangianGradient p (exactReply p I (query p q y)) q.snd).snd)
  have he : b = SaddlePoint.project p.Y (y - (1 / smoothness p) • innerGradient I q y) := by
    simp only [b, innerGradient, lagrangianGradient, exactReply]
    rw [smul_neg, sub_neg_eq_add]
  have herr : ‖minGradient p (exactReply p I (query p q (optimizer I q))) q.snd -
      minGradient p (exactReply p I (query p q b)) q.snd‖ ≤ tolerance p / 6 := by
    rw [he]
    exact cleanup_outer_error hv H hq hy.1 hy.2
  have hd := projected_descent hv H hq
    (minGradient p (exactReply p I (query p q b)) q.snd) herr
  have hc : (tolerance p / 6) ^ 2 / (2 * valueSmoothness p) =
      tolerance p ^ 2 / (72 * valueSmoothness p) := by ring
  dsimp only at hd
  rw [hc] at hd
  unfold step stepCalls
  rw [QueryPlan.eval_bind]
  simp only [QueryPlan.eval]
  exact hd

lemma outer_energy {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) (N : ℕ) {q : MinSpace p} (hq : q ∈ minDomain p) :
    ∃ z ∈ minDomain p,
      valueSmoothness p * ((QueryPlan.eval (exactReply p I) (outer p N q)).map
        (fun c => c.displacement ^ 2)).sum ≤ value I q - value I z +
          N * (tolerance p ^ 2 / (72 * valueSmoothness p)) := by
  induction N generalizing q with
  | zero => exact ⟨q, hq, by simp [outer, QueryPlan.eval]⟩
  | succ N ih =>
      obtain ⟨z, hz, hh⟩ := ih (step_min_mem (I := I) hv q)
      refine ⟨z, hz, ?_⟩
      have hd := step_descent hv H hq
      simp only [outer, QueryPlan.eval_bind, QueryPlan.eval_map, List.map_cons,
        List.sum_cons, Nat.cast_add, Nat.cast_one]
      dsimp only at hd
      nlinarith

lemma outer_length {p : Params} (I : Instance p) (N : ℕ) (q : MinSpace p) :
    (QueryPlan.eval (exactReply p I) (outer p N q)).length = N := by
  induction N generalizing q with
  | zero => rfl
  | succ N ih =>
      simp only [outer, QueryPlan.eval_bind, QueryPlan.eval_map, List.length_cons, ih]

lemma outer_displacement_nonneg {p : Params} (I : Instance p) (N : ℕ)
    (q : MinSpace p) :
    ∀ c ∈ QueryPlan.eval (exactReply p I) (outer p N q), 0 ≤ c.displacement := by
  induction N generalizing q with
  | zero => simp [outer, QueryPlan.eval]
  | succ N ih =>
      simp only [outer, QueryPlan.eval_bind, QueryPlan.eval_map, List.mem_cons]
      intro c hc
      rcases hc with rfl | hc
      · unfold step stepCalls
        rw [QueryPlan.eval_bind]
        simp only [QueryPlan.eval]
        exact norm_nonneg _
      · exact ih _ c hc

lemma fold_selection {p : Params} (cs : List (Candidate p)) (a : Candidate p) :
    let c := cs.foldl (fun a b => if b.displacement ≤ a.displacement then b else a) a
    (c = a ∨ c ∈ cs) ∧ c.displacement ≤ a.displacement ∧
      ∀ b ∈ cs, c.displacement ≤ b.displacement := by
  induction cs generalizing a with
  | nil => simp
  | cons b cs ih =>
      simp only [List.foldl_cons]
      split_ifs with h
      · obtain ⟨hm, ha, hb⟩ := ih b
        refine ⟨?_, ha.trans h, ?_⟩
        · right
          rcases hm with hm | hm
          · exact List.mem_cons.mpr (Or.inl hm)
          · exact List.mem_cons.mpr (Or.inr hm)
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact ha
          · exact hb d hd
      · obtain ⟨hm, ha, hb⟩ := ih a
        refine ⟨?_, ha, ?_⟩
        · rcases hm with hm | hm
          · exact Or.inl hm
          · exact Or.inr (List.mem_cons.mpr (Or.inr hm))
        · intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact ha.trans (le_of_not_ge h)
          · exact hb d hd

lemma selection_spec {p : Params} {cs : List (Candidate p)} (hne : cs ≠ []) :
    ∃ c ∈ cs, select p cs = c.point ∧
      ∀ b ∈ cs, c.displacement ≤ b.displacement := by
  cases cs with
  | nil => exact False.elim (hne rfl)
  | cons a cs =>
      obtain ⟨hm, ha, hb⟩ := fold_selection cs a
      refine ⟨_, List.mem_cons.mpr hm, rfl, ?_⟩
      intro b hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ha
      · exact hb b hmem

lemma list_square_lower {p : Params} (cs : List (Candidate p)) {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ c ∈ cs, a ≤ c.displacement) :
    (cs.length : ℝ) * a ^ 2 ≤ (cs.map (fun c => c.displacement ^ 2)).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      have hc := h c (List.mem_cons_self)
      have hh := ih (fun b hb => h b (List.mem_cons_of_mem c hb))
      simp only [List.length_cons, List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
      nlinarith

lemma energy_displacement {L t N D S d : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hN : 0 < N) (hd : 0 ≤ d) (htune : D ≤ N * t ^ 2 / (72 * L))
    (henergy : L * S ≤ D + N * t ^ 2 / (72 * L))
    (hmin : N * d ^ 2 ≤ S) : d ≤ t / (6 * L) := by
  have he : L * S ≤ N * t ^ 2 / (36 * L) := by
    calc
      L * S ≤ N * t ^ 2 / (72 * L) + N * t ^ 2 / (72 * L) :=
        henergy.trans (add_le_add htune le_rfl)
      _ = N * t ^ 2 / (36 * L) := by ring
  have he' := (le_div_iff₀ (by positivity : 0 < 36 * L)).mp he
  have hm := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ 36 * L ^ 2)
  have hs : (6 * L * d) ^ 2 ≤ t ^ 2 := by
    have hh : N * (6 * L * d) ^ 2 ≤ N * t ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left hh hN
  have hb := (sq_le_sq₀ (by positivity : 0 ≤ 6 * L * d) ht).mp hs
  apply (le_div_iff₀ (by positivity : 0 < 6 * L)).mpr
  nlinarith

lemma outer_tuning {p : Params} (hv : Valid p) :
    gapBound p ≤ (outerIterations p : ℝ) * tolerance p ^ 2 / (72 * valueSmoothness p) := by
  have ht := tolerance_pos hv
  have hL := valueSmoothness_pos hv
  have hn := Nat.le_ceil (72 * valueSmoothness p * gapBound p / tolerance p ^ 2)
  have hn' : 72 * valueSmoothness p * gapBound p / tolerance p ^ 2 ≤
      (outerIterations p : ℝ) := by
    unfold outerIterations
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hh := (div_le_iff₀ (sq_pos_of_pos ht)).mp hn'
  apply (le_div_iff₀ (by positivity : 0 < 72 * valueSmoothness p)).mpr
  nlinarith

lemma selected_displacement {p : Params} {I : Instance p} (hv : Valid p)
    (H : Assumptions p I) :
    let cs := QueryPlan.eval (exactReply p I) (outer p (outerIterations p) (start p))
    ∃ c ∈ cs, select p cs = c.point ∧
      c.displacement ≤ tolerance p / (6 * valueSmoothness p) := by
  let cs := QueryPlan.eval (exactReply p I) (outer p (outerIterations p) (start p))
  have hn : 0 < outerIterations p := by unfold outerIterations; omega
  have hlen : cs.length = outerIterations p := outer_length I _ _
  have hne : cs ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    omega
  obtain ⟨c, hc, hout, hmin⟩ := selection_spec hne
  refine ⟨c, hc, hout, ?_⟩
  have hd := outer_displacement_nonneg I (outerIterations p) (start p) c hc
  have hsum := list_square_lower cs hd hmin
  rw [hlen] at hsum
  obtain ⟨z, hz, he⟩ := outer_energy hv H (outerIterations p) (start_mem hv)
  have hg := initial_gap hv H hz
  have henergy : valueSmoothness p * (cs.map (fun c => c.displacement ^ 2)).sum ≤
      gapBound p + (outerIterations p : ℝ) * tolerance p ^ 2 / (72 * valueSmoothness p) := by
    dsimp [cs]
    simpa only [mul_div_assoc] using he.trans (add_le_add hg le_rfl)
  exact energy_displacement (valueSmoothness_pos hv) (tolerance_pos hv).le
    (by exact_mod_cast hn) hd (outer_tuning hv) henergy hsum

end LongTails.Proofs.CoupledMinimaxOuter
