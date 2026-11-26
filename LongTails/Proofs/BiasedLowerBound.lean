import LongTails.Proofs.BiasedLowerAdmissible

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.BiasedLowerBound

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.AbcChain LongTails.Proofs.AbcHardFunction LongTails.Proofs.AbcHardGeometry
open LongTails.Proofs.AbcHardOracle LongTails.Proofs.AbcHardSimulation
open LongTails.Proofs.AbcHardExecution LongTails.Proofs.AbcHardCounting
open LongTails.Proofs.AbcLowerMeasure LongTails.Proofs.AbcLowerParameters
open LongTails.Proofs.AbcLowerAssembly LongTails.Proofs.AbcLowerBound
open LongTails.Proofs.FiniteSumNondualLowerAveraging LongTails.Proofs.FiniteSumNondualLowerBound
open LongTails.Proofs.BiasedDecoy LongTails.Proofs.BiasedLowerInstance
open LongTails.Proofs.BiasedLowerOracle LongTails.Proofs.BiasedLowerAdmissible
open LongTails.Setups.HighDimensionalBiasedNoiseNonconvex

section Good

variable {d n : ℕ} {St : Type*}

lemma good_query_gradient (S : Scale) (qf : ℕ → ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St) (qbar : ℝ)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S qf x0 query output update initial qbar ω N π)
    (hlev : level n qbar ω N < n + 1)
    (hq : ∀ m, m ≤ level n qbar ω N → qf m ≤ qbar) (t : ℕ) (ht : t < N) :
    S.a / S.lam / 20 ≤
      ‖objGrad S π x0 (query (trueState S qf π x0 query update initial ω t))‖ := by
  have hhit : ∀ t' < t,
      let x := query (simState S qf π x0 query update initial qbar ω t')
      ‖toUnit S x0 x‖ ≤ 2 * radius n →
        ∀ i : Fin (n + 1), level n qbar ω t' ≤ i.val → |sel π (toUnit S x0 x) i| ≤ 1 / 4 := by
    intro t' ht' x hx i hi
    have h := good_small S qf x0 query output update initial qbar ω N π hgood ⟨t', by omega⟩
    simp only [observation, show t' < N by omega, ↓reduceIte] at h
    exact h hx i hi
  have hmono := level_mono n qbar ω ht.le
  have hq' : ∀ m, m ≤ level n qbar ω t → qf m ≤ qbar := fun m hm => hq m (hm.trans hmono)
  rw [← coupling S qf π x0 query update initial qbar ω t hhit hq']
  have hpos : 0 ≤ S.a / S.lam := by have := S.ha; have := S.hlam; positivity
  rw [objGrad, norm_smul, Real.norm_of_nonneg hpos]
  set w := toUnit S x0 (query (simState S qf π x0 query update initial qbar ω t))
  have hR := radius_pos n
  by_cases hw : 2 * radius n < ‖w‖
  · rw [hardGrad_outside π w hw.le, wallGrad_norm]
    have : 4 ≤ 2 * ‖w‖ / radius n := by rw [le_div_iff₀ hR]; linarith
    nlinarith
  · push Not at hw
    have h := good_small S qf x0 query output update initial qbar ω N π hgood ⟨t, by omega⟩
    simp only [observation, ht, ↓reduceIte] at h
    have hl := h hw (Fin.last n) (by simp; omega)
    have hg := hardGrad_lower π w (lt_of_le_of_lt hl (by norm_num))
    nlinarith

end Good

section Execution

variable (q : Params) (S : Scale) (π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d) (sg : ℝ)

noncomputable def compState {St : Type*} (query : St → Space (q.d + 1))
    (update : St → Space (q.d + 1) → St) (initial : St) (ω : ℕ → ℝ) : ℕ → St
  | 0 => initial
  | t + 1 =>
    let s := compState query update initial ω t
    update s (replyB q S π sg (query s) (ω t))

lemma compState_iterate {St : Type*} (query : St → Space (q.d + 1))
    (update : St → Space (q.d + 1) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (replyB q S π sg (query sc.1) (ω sc.2)), sc.2 + 1))^[N]
      (initial, 0)) = (compState q S π sg query update initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_comp (A : Algorithm (Space (q.d + 1)) (Space (q.d + 1)) (Space (q.d + 1)))
    (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (oracleB q S π sg) A (fun _ => N) seed ω =
      A.output (compState q S π sg (fun s => (A.query s).2) A.update (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (oracleB q S π sg) A N seed ω
    (fun t query => replyB q S π sg query.2 (ω t)) (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (compState_iterate q S π sg
    (fun s => (A.query s).2) A.update (A.initial seed) ω N)

lemma comp_eq_true {St : Type*} (hv : spec.valid q) (query : St → Space (q.d + 1))
    (update : St → Space (q.d + 1) → St) (initial : St) (ω : ℕ → ℝ) (N : ℕ)
    (hbig : ∀ t < N, theta q ≤ ‖objGrad S π (drop q.x0) (drop (query
      (trueState S (qfB q) π (drop q.x0) (fun s => drop (query s)) (fun s r => update s (pad r))
        initial ω t)))‖) :
    compState q S π sg query update initial ω N =
      trueState S (qfB q) π (drop q.x0) (fun s => drop (query s)) (fun s r => update s (pad r))
        initial ω N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have he := ih (fun t ht => hbig t (by omega))
    simp only [compState, trueState]
    rw [he]
    have hh : Hides q S π sg (query (trueState S (qfB q) π (drop q.x0) (fun s => drop (query s))
        (fun s r => update s (pad r)) initial ω N)) := by
      unfold Hides
      have h1 := abs_dpr_le (wid_pos q hv) (zc q sg (query (trueState S (qfB q) π (drop q.x0)
        (fun s => drop (query s)) (fun s r => update s (pad r)) initial ω N)))
      have hθ := theta_pos q hv
      have h2 := hbig N (by omega)
      nlinarith
    simp only [replyB, hh, ↓reduceIte]

end Execution

section Assembly

variable (q : Params) (hv : spec.valid q)
include hv

lemma theta_eq_ratio : theta q = (scaleB q hv).a / (scaleB q hv).lam / 20 := by
  have h := amplitude_ratio (abcParams q) (abc_valid q hv).1 (abc_valid q hv).2.2.2.2.1
  have : (scaleB q hv).a / (scaleB q hv).lam = 60 * epsA q := h
  rw [this]; unfold theta; ring

lemma budget_le (N : ℕ)
    (hN : N ≤ ⌊q.L * q.Δ * (1 + q.M + q.σ ^ 2 / ((1 - q.m) * q.ε ^ 2)) /
      (2 ^ 60 * ((1 - q.m) * q.ε ^ 2))⌋₊) :
    N ≤ lowerBudget (abcParams q) := by
  refine hN.trans (Nat.floor_le_floor ?_)
  obtain ⟨hL, hm0, hm1, hM, hσ, hζ, hε, hfloor, hreg, hdim⟩ := hv
  have hv' : spec.valid q := ⟨hL, hm0, hm1, hM, hσ, hζ, hε, hfloor, hreg, hdim⟩
  have hea := epsA_pos q hv'
  have hle := epsA_sq_le q hv'
  have h1m := one_sub_m_pos q hv'
  have hΔ : 0 ≤ q.Δ := by
    by_contra hneg
    push Not at hneg
    nlinarith [sq_nonneg q.ε, mul_neg_of_pos_of_neg hL hneg]
  set r := (1 - q.m) * q.ε ^ 2 with hr
  have hrpos : 0 < r := by positivity
  simp only [abcParams]
  have he2 : 0 < epsA q ^ 2 := by positivity
  have hs : q.σ ^ 2 / r ≤ 25 / 9 * (q.σ ^ 2 / epsA q ^ 2) := by
    have h1 : q.σ ^ 2 / r ≤ q.σ ^ 2 / (9 / 25 * epsA q ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    have h2 : q.σ ^ 2 / (9 / 25 * epsA q ^ 2) = 25 / 9 * (q.σ ^ 2 / epsA q ^ 2) := by ring
    linarith
  have hz0 : (0 : ℝ) * (q.Δ / 2) / epsA q ^ 2 = 0 := by rw [zero_mul, zero_div]
  have hX : 1 + q.M + q.σ ^ 2 / r ≤ 25 / 9 * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 +
      q.σ ^ 2 / epsA q ^ 2) := by
    rw [hz0, add_zero]
    linarith
  have hLΔ : 0 ≤ q.L * q.Δ := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hY : 0 ≤ 1 + q.M + q.σ ^ 2 / r := by positivity
  have h1 : q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) * (2 ^ 53 * epsA q ^ 2) ≤
      q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) * (2 ^ 53 * (25 / 9 * r)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg hLΔ hY)
  have h2 : q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) * (2 ^ 53 * (25 / 9 * r)) ≤
      q.L / 2 * (q.Δ / 2) * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2) *
        (2 ^ 60 * r) := by
    have h3 := mul_le_mul_of_nonneg_left hX (mul_nonneg hLΔ hrpos.le)
    have hY' : 0 ≤ 1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2 := by
      rw [hz0, add_zero]; positivity
    have hT : 0 ≤ q.L * q.Δ * r * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2) :=
      mul_nonneg (mul_nonneg hLΔ hrpos.le) hY'
    have e1 : q.L / 2 * (q.Δ / 2) * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2) *
        (2 ^ 60 * r) = 2 ^ 58 * (q.L * q.Δ * r *
          (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2)) := by ring
    have e2 : q.L * q.Δ * (1 + q.M + q.σ ^ 2 / r) * (2 ^ 53 * (25 / 9 * r)) =
        2 ^ 53 * (25 / 9) * (q.L * q.Δ * r * (1 + q.M + q.σ ^ 2 / r)) := by ring
    have e3 : q.L * q.Δ * r * (25 / 9 * (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 +
        q.σ ^ 2 / epsA q ^ 2)) = 25 / 9 * (q.L * q.Δ * r *
          (1 + q.M + 0 * (q.Δ / 2) / epsA q ^ 2 + q.σ ^ 2 / epsA q ^ 2)) := by ring
    rw [e1, e2]
    rw [e3] at h3
    linarith
  linarith

lemma exists_failure_biased
    (A : Algorithm (Space (q.d + 1)) (Space (q.d + 1)) (Space (q.d + 1))) (N : ℕ)
    (hN : N ≤ lowerBudget (abcParams q)) :
    ∃ π : Fin (chainDim (abcParams q) + 1) ↪ Fin q.d, ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
      ¬ spec.successful q (objB q (scaleB q hv) π sg)
        (fun w : A.Seed × ((k : ℕ) → (oracleB q (scaleB q hv) π sg).Seed k) =>
          execute (oracleB q (scaleB q hv) π sg) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((oracleB q (scaleB q hv) π sg).law : Measure _),
          inferInstance⟩ := by
  set qa := abcParams q
  have hva := abc_valid q hv
  have hn1 := chainDim_succ qa hva
  set S := scaleB q hv
  set n := chainDim qa
  set qf := revealProb qa n
  set qbar := revealBar qa
  set Mh := n / 2
  let query : A.State → Space (q.d + 1) := fun s => (A.query s).2
  let query' : A.State → Space q.d := fun s => drop (query s)
  let update' : A.State → Space q.d → A.State := fun s r => A.update s (pad r)
  let output' : A.State → Space q.d := fun s => drop (A.output s)
  let W := CoordinateWords qa.d n
  let sgn : Bool → ℝ := fun b => if b then 1 else -1
  have hsgn : ∀ b, sgn b = 1 ∨ sgn b = -1 := by intro b; cases b <;> simp [sgn]
  have hθ : theta q = S.a / S.lam / 20 := theta_eq_ratio q hv
  have hε := hv.2.2.2.2.2.2.1
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let xhat : W → Bool → A.Seed × (ℕ → ℝ) → Space (q.d + 1) := fun w b z =>
    A.output (compState q S (coordinateEmbedding w) (sgn b) query A.update (A.initial z.1) z.2 N)
  let loss : W → Bool → A.Seed × (ℕ → ℝ) → ℝ := fun w b z =>
    ‖gradB q S (coordinateEmbedding w) (sgn b) (xhat w b z)‖
  have hloss (w : W) (b : Bool) : (fun z : A.Seed × (ℕ → ℝ) =>
      ‖gradient (objB q S (coordinateEmbedding w) (sgn b))
        (execute (oracleB q S (coordinateEmbedding w) (sgn b)) A (fun _ => N) z.1 z.2)‖) =
      loss w b := by
    funext z
    rw [objB_gradient q hv S _ _, execute_comp]
  have hi (w : W) (b : Bool) : Integrable (loss w b) P := by
    have h := (hcon (coordinateEmbedding w) (sgn b) (hsgn b)).2.1
    rw [← hloss w b]
    exact h
  have hle (w : W) (b : Bool) : ∫ z, loss w b z ∂P ≤ q.ε := by
    have h := (hcon (coordinateEmbedding w) (sgn b) (hsgn b)).2.2
    rw [← hloss w b]
    exact h
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount qbar z.2 N ≤ Mh} 1 z
  set K := max (6 * epsA q) (99 / 100 * amp q) with hK
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      K * (7 / 8) * Fintype.card W * good z ≤ ∑ w, (loss w true z + loss w false z) := by
    by_cases hz : coinCount qbar z.2 N ≤ Mh
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : level n qbar z.2 N < n + 1 := by
        have := min_le_right (n + 1) (coinCount qbar z.2 N)
        unfold level
        omega
      have hq : ∀ m, m ≤ level n qbar z.2 N → qf m ≤ qbar := by
        intro m hm
        have hm' : m ≤ (chainLength qa - 1) / 2 := by
          have := min_le_right (n + 1) (coinCount qbar z.2 N)
          have h2 : m ≤ Mh := by unfold level at hm; omega
          simpa [Mh, n, chainDim] using h2
        exact revealProb_le_bar qa hva.2.2.2.2.1 n m (half_le_level qa hva m hm')
      have hbad := bad_fraction qa hva N hN S query' output' update' (A.initial z.1) z.2
      have hgood (w : W) : ¬ coordinateBad S qf qa.x0 query' output' update' (A.initial z.1)
          qbar z.2 N (coordinateEmbedding w) → K ≤ loss w true z + loss w false z := by
        intro hw
        set π := coordinateEmbedding w
        have hbig : ∀ t < N, theta q ≤ ‖objGrad S π (drop q.x0) (drop (query
            (trueState S (qfB q) π (drop q.x0) (fun s => drop (query s))
              (fun s r => A.update s (pad r)) (A.initial z.1) z.2 t)))‖ := by
          intro t ht
          rw [hθ]
          exact good_query_gradient S qf qa.x0 query' output' update' (A.initial z.1) qbar
            z.2 N π hw hlev hq t ht
        obtain ⟨xh, hxh⟩ : ∃ xh, xh = A.output (trueState S (qfB q) π (drop q.x0)
            (fun s => drop (query s)) (fun s r => A.update s (pad r)) (A.initial z.1) z.2 N) :=
          ⟨_, rfl⟩
        have hxeq : ∀ b, xhat w b z = xh := by
          intro b
          rw [hxh]
          exact congrArg A.output (comp_eq_true q S π (sgn b) hv query A.update (A.initial z.1)
            z.2 N hbig)
        have hout : S.a / S.lam / 20 ≤ ‖objGrad S π (drop q.x0) (drop xh)‖ := by
          rw [hxh]
          exact good_gradient S qf qa.x0 query' output' update' (A.initial z.1) qbar z.2 N π
            hw hlev hq
        rw [← hθ] at hout
        have hlt : ∀ b, loss w b z = ‖gradB q S π (sgn b) xh‖ := by
          intro b
          show ‖gradB q S π (sgn b) (xhat w b z)‖ = _
          rw [hxeq b]
        rw [hlt true, hlt false]
        have hA1 : ‖objGrad S π (drop q.x0) (drop xh)‖ ≤ ‖gradB q S π (sgn true) xh‖ :=
          objGrad_le_gradB q S π (sgn true) xh
        have hA2 : ‖objGrad S π (drop q.x0) (drop xh)‖ ≤ ‖gradB q S π (sgn false) xh‖ :=
          objGrad_le_gradB q S π (sgn false) xh
        have hB1 := decoyGrad_abs_le q hv S π (sgn true) (hsgn true) xh
        have hB2 := decoyGrad_abs_le q hv S π (sgn false) (hsgn false) xh
        have hsum := sign_sum_ge (wid_pos q hv) ⟪eLast (d := q.d), xh - q.x0⟫
        have hz1 : zc q (sgn true) xh = ⟪eLast (d := q.d), xh - q.x0⟫ - 100 * wid q := by
          simp [zc, sgn]
        have hz2 : zc q (sgn false) xh = -⟪eLast (d := q.d), xh - q.x0⟫ - 100 * wid q := by
          simp [zc, sgn]
        rw [hz1] at hB1
        rw [hz2] at hB2
        have ha := amp_nonneg q hv
        have hθ3 : theta q = 3 * epsA q := rfl
        rcases le_total (6 * epsA q) (99 / 100 * amp q) with hc | hc
        · rw [hK, max_eq_right hc]
          nlinarith [mul_le_mul_of_nonneg_left hsum ha]
        · rw [hK, max_eq_left hc]
          linarith
      have hterm (w : W) : K * (1 - if coordinateBad S qf qa.x0 query' output' update'
          (A.initial z.1) qbar z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
          loss w true z + loss w false z := by
        by_cases hw : coordinateBad S qf qa.x0 query' output' update' (A.initial z.1) qbar
            z.2 N (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]
          exact add_nonneg (norm_nonneg _) (norm_nonneg _)
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]; exact hgood w hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hKp : 0 ≤ K := le_max_of_le_left (by have := epsA_pos q hv; positivity)
      nlinarith [mul_le_mul_of_nonneg_left hbad hKp]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount qbar ω N ≤ Mh} := by
    have h := (coinCount_measurable qbar N) (measurableSet_Iic (a := ((Mh : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount qbar z.2 N ≤ Mh} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount qbar ω N ≤ Mh} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount qbar z.2 N ≤ Mh} =
        Prod.snd ⁻¹' {ω | coinCount qbar ω N ≤ Mh} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac : 7 / 8 ≤ stream.real {ω | coinCount qbar ω N ≤ Mh} :=
    good_count_fraction qa hva N hN
  have hint_good : Integrable (fun z => K * (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, (loss w true z + loss w false z)) P :=
    integrable_finsetSum Finset.univ (fun w _ => (hi w true).add (hi w false))
  have hmono := integral_mono hint_good hint_sum hpt
  have hsumint : ∫ z, ∑ w, (loss w true z + loss w false z) ∂P =
      ∑ w, ∫ z, (loss w true z + loss w false z) ∂P :=
    integral_finsetSum Finset.univ (fun w _ => (hi w true).add (hi w false))
  rw [integral_const_mul, hgood_int, hsumint] at hmono
  have hsum : (∑ w : W, ∫ z, (loss w true z + loss w false z) ∂P) ≤ Fintype.card W * (2 * q.ε) := by
    calc _ ≤ ∑ _w : W, 2 * q.ε := Finset.sum_le_sum (fun w _ => by
          rw [integral_add (hi w true) (hi w false)]
          linarith [hle w true, hle w false])
      _ = _ := by simp
  have hd : n + 1 ≤ qa.d := by
    have h := dimension_room qa hva N hN
    have hT : ((n + 1 : ℕ) : ℝ) ≤ qa.d := by
      rw [hn1]
      nlinarith [pow_nonneg (Nat.cast_nonneg (chainLength qa) : (0 : ℝ) ≤ chainLength qa) 3,
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos qa.d n hd
  have hconst := failure_constant q hv
  have hKp : 0 ≤ K := le_max_of_le_left (by have := epsA_pos q hv; positivity)
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ K * (7 / 8) * Fintype.card W)
  have hm2 := mul_lt_mul_of_pos_right hconst hc
  linarith

end Assembly

end LongTails.Proofs.BiasedLowerBound
