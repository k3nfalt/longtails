import LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex
import LongTails.Proofs.StochasticEllSmoothMask
import LongTails.Proofs.EllSmoothLowerBound
import LongTails.Proofs.AbcLowerMeasure
import LongTails.Proofs.AbcHardContinuity
import LongTails.TemplateLowerBound

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StochasticEllSmoothLower

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open Classical
open LongTails.Proofs.EllSmoothProfiles LongTails.Proofs.EllSmoothChain
open LongTails.Proofs.EllSmoothHard LongTails.Proofs.EllSmoothHardBounds
open LongTails.Proofs.EllSmoothSimulation LongTails.Proofs.StochasticEllSmoothMask
open LongTails.Proofs.AbcHardFunction (sel sel_apply)
open LongTails.Proofs.AbcHardOracle (Scale toUnit stage small_of_stage coin unif coin_measurable)
open LongTails.Proofs.AbcHardExecution (coinCount level level_le)
open LongTails.Proofs.AbcLowerMeasure (stream stream_iid coinCount_tail coinCount_measurable)
open LongTails.Proofs.SmoothConvexFiniteHiding LongTails.Proofs.FiniteSumNondualLowerHiding
open LongTails.Proofs.FiniteSumNondualLowerExposure LongTails.Proofs.FiniteSumNondualLowerAveraging
open LongTails.Proofs.FiniteSumNondualLowerBound

section Continuity

variable (S : Shape) {d n : ℕ}

lemma trunc_cont (m : ℕ) : Continuous (trunc (n := n) m) := by
  have h : Continuous (fun u : Chain n => (fun i : Fin (n + 1) => if i.val < m then u i else 0)) := by
    apply continuous_pi
    intro i
    split_ifs
    · exact PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i
    · exact continuous_const
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp h

lemma field_cont : Continuous (field S (n := n)) :=
  continuous_iff_continuousAt.mpr fun u =>
    (LongTails.Proofs.EllSmoothChainHessian.field_differentiableAt S u).continuousAt

lemma chain_cont : Continuous (chain S (n := n)) :=
  continuous_iff_continuousAt.mpr fun u =>
    (chain_hasGradientAt S u).differentiableAt.continuousAt

lemma visibleField_cont (r : ℕ) : Continuous (visibleField S (n := n) r) := by
  have h : Continuous (fun u : Chain n =>
      (fun k : Fin (n + 1) => if k.val < r then field S (trunc r u) k else 0)) := by
    apply continuous_pi
    intro k
    split_ifs
    · exact (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) k).comp
        ((field_cont S).comp (trunc_cont r))
    · exact continuous_const
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp h

lemma cut_cont : Continuous (cut S n) :=
  continuous_iff_continuousAt.mpr fun s => (cut_hasDerivAt S n s).continuousAt

lemma dcut_cont : Continuous (dcut S n) :=
  continuous_iff_continuousAt.mpr fun s => (dcut_hasDerivAt S n s).continuousAt

lemma dwall_cont : Continuous (dwall S n) :=
  continuous_iff_continuousAt.mpr fun s => (dwall_hasDerivAt S n s).continuousAt

lemma pgrad_cont (π : Fin (n + 1) ↪ Fin d) (r : ℕ) : Continuous (pgrad S π r) := by
  have hn : Continuous (fun w : Space d => ‖w‖ ^ 2) := by fun_prop
  have hsel : Continuous (fun w : Space d => sel π w) := (sel π).continuous
  have h1 : Continuous (fun w : Space d => cut S n (‖w‖ ^ 2)) := (cut_cont S (n := n)).comp hn
  have h2 : Continuous (fun w : Space d => (sel π).adjoint (visibleField S r (sel π w))) :=
    (sel π).adjoint.continuous.comp ((visibleField_cont S (n := n) r).comp hsel)
  have h3 : Continuous (fun w : Space d => 2 * dcut S n (‖w‖ ^ 2) * chain S (trunc r (sel π w)) +
      2 * dwall S n (‖w‖ ^ 2)) :=
    ((continuous_const.mul ((dcut_cont S (n := n)).comp hn)).mul ((chain_cont S (n := n)).comp
      ((trunc_cont (n := n) r).comp hsel))).add (continuous_const.mul ((dwall_cont S (n := n)).comp hn))
  have he : pgrad S π r = fun w => cut S n (‖w‖ ^ 2) • (sel π).adjoint (visibleField S r (sel π w)) +
      (2 * dcut S n (‖w‖ ^ 2) * chain S (trunc r (sel π w)) + 2 * dwall S n (‖w‖ ^ 2)) • w := by
    funext w; rfl
  rw [he]
  exact (h1.smul h2).add (h3.smul continuous_id)

lemma knownPart_cont (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 : Space d) :
    Continuous (knownPart S Sc π m x0) := by
  unfold knownPart
  exact ((pgrad_cont S π m).comp
    (LongTails.Proofs.AbcHardContinuity.toUnit_continuous Sc x0)).const_smul (Sc.a / Sc.lam)

lemma objGrad_cont (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Continuous (objGrad S Sc π x0) :=
  continuous_iff_continuousAt.mpr fun x => (objGrad_hasFDerivAt S Sc π x0 x).continuousAt

lemma reply_measurable (Sc : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Measurable (Function.uncurry (reply S Sc q π x0)) := by
  let G : (Space d × ℝ) × ℕ → Space d := fun z =>
    knownPart S Sc π z.2 x0 z.1.1 +
      coin q z.1.2 • (objGrad S Sc π x0 z.1.1 - knownPart S Sc π z.2 x0 z.1.1)
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro m
    have hk : Measurable (fun z : Space d × ℝ => knownPart S Sc π m x0 z.1) :=
      (knownPart_cont S Sc π m x0).measurable.comp measurable_fst
    have ho : Measurable (fun z : Space d × ℝ => objGrad S Sc π x0 z.1) :=
      (objGrad_cont S Sc π x0).measurable.comp measurable_fst
    have hc : Measurable (fun z : Space d × ℝ => coin q z.2) :=
      (coin_measurable q).comp measurable_snd
    exact hk.add (hc.smul (ho.sub hk))
  have he : Function.uncurry (reply S Sc q π x0) =
      G ∘ (fun z : Space d × ℝ => (z, stage (sel π (toUnit Sc x0 z.1)))) := by
    funext z
    rfl
  rw [he]
  exact hG.comp (measurable_id.prodMk
    ((LongTails.Proofs.AbcHardContinuity.stage_measurable Sc π x0).comp measurable_fst))

end Continuity

section Counting

variable (S : Shape) {d n : ℕ} {St : Type*}

noncomputable def observation (Sc : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  if j.val < N then toUnit Sc x0 (query (simState S Sc q π x0 query update initial ω j.val))
  else toUnit Sc x0 (output (simState S Sc q π x0 query update initial ω j.val))

lemma observation_prefix (Sc : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (j : Fin (N + 1)) (π ρ : Fin (n + 1) ↪ Fin d)
    (h : ∀ k : Fin (n + 1), k.val < level n q ω j.val → π k = ρ k) :
    observation S Sc q x0 query output update initial ω N j π =
      observation S Sc q x0 query output update initial ω N j ρ := by
  unfold observation
  rw [simState_prefix S Sc q π ρ x0 query update initial ω j.val h]

def coordinateBad (Sc : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d) : Prop :=
  ∃ j : Fin (N + 1), 0 < hits
    (largeSet (4 * rad S n) (1 / 4) (observation S Sc q x0 query output update initial ω N j π))
    ((List.ofFn π).drop (level n q ω j.val))

lemma good_small (Sc : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S Sc q x0 query output update initial ω N π)
    (j : Fin (N + 1))
    (hj : ‖observation S Sc q x0 query output update initial ω N j π‖ ≤ 4 * rad S n)
    (i : Fin (n + 1)) (hi : level n q ω j.val ≤ i.val) :
    |sel π (observation S Sc q x0 query output update initial ω N j π) i| ≤ 1 / 4 := by
  rw [sel_apply]
  apply not_largeSet_small _ _ _ hj
  intro h
  exact hgood ⟨j, hits_drop_positive π _ _ i hi h⟩

lemma bad_sum_bound (Sc : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hDs : D + (n + 1 : ℕ) ≤ d) :
    D * (∑ w : CoordinateWords d n, if coordinateBad S Sc q x0 query output update initial ω N
      (coordinateEmbedding w) then (1 : ℝ) else 0) ≤
      (N + 1 : ℕ) * (n + 1 : ℕ) * ((4 * rad S n) ^ 2 / (1 / 4) ^ 2) *
        Fintype.card (CoordinateWords d n) := by
  let bad := fun π : Fin (n + 1) ↪ Fin d =>
    coordinateBad S Sc q x0 query output update initial ω N π
  have he (w : CoordinateWords d n) : bad (coordinateEmbedding w) ↔
      ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d, List.ofFn π = w.val ∧
        0 < hits (largeSet (4 * rad S n) (1 / 4)
          (observation S Sc q x0 query output update initial ω N j π))
          (w.val.drop (level n q ω j.val)) := by
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, coordinateEmbedding w, coordinateEmbedding_labels w,
        by simpa only [coordinateEmbedding_labels] using hj⟩
    · rintro ⟨j, π, hπ, hj⟩
      have hp : π = coordinateEmbedding w := by
        apply Function.Embedding.ext
        intro k
        exact congrFun (List.ofFn_injective (hπ.trans (coordinateEmbedding_labels w).symm)) k
      exact ⟨j, by simpa only [hp, ← coordinateEmbedding_labels w] using hj⟩
  let P := fun w : List (Fin d) => ∃ j : Fin (N + 1), ∃ π : Fin (n + 1) ↪ Fin d,
    List.ofFn π = w ∧ 0 < hits (largeSet (4 * rad S n) (1 / 4)
      (observation S Sc q x0 query output update initial ω N j π))
      (w.drop (level n q ω j.val))
  have hs : (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) =
      (((distinctWords (n + 1) (Finset.univ : Finset (Fin d))).filter P).card : ℝ) := by
    simp_rw [he]
    exact subtype_indicator_sum _ P
  change D * (∑ w : CoordinateWords d n, if bad (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ _
  rw [hs]
  have h := bounded_prefix_bad_count (d := d) (K := n + 1) (4 * rad S n) (1 / 4) D
    (by have := rad_pos S n; positivity) (by norm_num) hD hDs
    (fun j : Fin (N + 1) => level n q ω j.val) (fun j => level_le n q ω j.val)
    (observation S Sc q x0 query output update initial ω N)
    (observation_prefix S Sc q x0 query output update initial ω N)
  simp only [Fintype.card_fin, CoordinateWords, Fintype.card_coe] at h ⊢
  convert h using 1
  apply congrArg (fun s : Finset (List (Fin d)) => D * (s.card : ℝ))
  ext w
  simp only [Finset.mem_filter, P]

lemma good_gradient (Sc : Scale) (q : ℝ) (x0 : Space d)
    (query output : St → Space d) (update : St → Space d → St) (initial : St)
    (ω : ℕ → ℝ) (N : ℕ) (π : Fin (n + 1) ↪ Fin d)
    (hgood : ¬ coordinateBad S Sc q x0 query output update initial ω N π)
    (hlev : level n q ω N < n + 1) :
    Sc.a / Sc.lam / 2 ≤
      ‖objGrad S Sc π x0 (output (trueState S Sc q π x0 query update initial ω N))‖ := by
  have hhit : ∀ t < N,
      let x := query (simState S Sc q π x0 query update initial ω t)
      ‖toUnit Sc x0 x‖ ≤ 4 * rad S n →
        ∀ i : Fin (n + 1), level n q ω t ≤ i.val → |sel π (toUnit Sc x0 x) i| ≤ 1 / 4 := by
    intro t ht x hx i hi
    have h := good_small S Sc q x0 query output update initial ω N π hgood ⟨t, by omega⟩
    simp only [observation, ht, ↓reduceIte] at h
    exact h hx i hi
  rw [← coupling S Sc q π x0 query update initial ω N hhit]
  have hpos : 0 < Sc.a / Sc.lam := div_pos Sc.ha Sc.hlam
  rw [objGrad, norm_smul, Real.norm_of_nonneg hpos.le]
  set w := toUnit Sc x0 (output (simState S Sc q π x0 query update initial ω N))
  have hr := rad_pos S n
  have hg : 1 / 2 ≤ ‖hgrad S π w‖ := by
    rcases le_total (4 * rad S n ^ 2) (‖w‖ ^ 2) with hw | hw
    · have := hgrad_far S π w hw
      linarith
    · have hw4 : ‖w‖ ≤ 4 * rad S n := by
        have := norm_le_of_sq_le (w := w) (B := 2 * rad S n) (by positivity) (by nlinarith)
        linarith
      have h := good_small S Sc q x0 query output update initial ω N π hgood (Fin.last N)
      simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at h
      have ht := h hw4 (Fin.last n) (by simp; omega)
      exact hgrad_near_unfinished S π w hw ⟨Fin.last n, lt_of_le_of_lt ht (by norm_num)⟩
  nlinarith [mul_le_mul_of_nonneg_left hg hpos.le]

end Counting

section Assembly

open LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex

abbrev HD := LongTails.Setups.HighDimensionalStochasticEllSmoothNonconvex.spec

variable (q : Params)

noncomputable def horizonY : ℝ := (2 - q.ρ) * (q.Δ * q.ℓ q.ε / q.ε ^ 2)

noncomputable def noiseFactor : ℝ := max 1 ((q.σ / (2 ^ 13 * q.ε)) ^ (q.p / (q.p - 1)))

noncomputable def coinProb : ℝ := 1 / noiseFactor q

noncomputable def chainLen : ℕ := ⌊horizonY q / 2 ^ 27⌋₊

noncomputable def lowerBudget : ℕ :=
  ⌊(2 - q.ρ) * (q.Δ * q.ℓ q.ε / q.ε ^ 2) * max 1 ((q.σ / (2 ^ 13 * q.ε)) ^ (q.p / (q.p - 1))) /
    2 ^ 32⌋₊

def base : LongTails.Setups.EllSmoothNonconvex.Params := ⟨q.d, q.ℓ, q.ρ, q.Δ, q.ε, q.x0⟩

lemma noiseFactor_ge : 1 ≤ noiseFactor q := le_max_left _ _

lemma coinProb_pos : 0 < coinProb q := by
  unfold coinProb; have := noiseFactor_ge q; positivity

lemma coinProb_le : coinProb q ≤ 1 := by
  unfold coinProb; rw [div_le_one (by linarith [noiseFactor_ge q])]; exact noiseFactor_ge q

lemma horizonY_ge (hv : HD.valid q) : 2 ^ 28 ≤ horizonY q := by
  have hε := hv.1.2.2.2.2.2.2.2
  have h := hv.2.2.1
  unfold horizonY
  rw [show (2 - q.ρ) * (q.Δ * q.ℓ q.ε / q.ε ^ 2) = (2 - q.ρ) * q.Δ * q.ℓ q.ε / q.ε ^ 2 by ring,
    le_div_iff₀ (by positivity)]
  exact h

lemma chainLen_bounds (hv : HD.valid q) :
    horizonY q / 2 ^ 27 < (chainLen q : ℝ) + 1 ∧ (chainLen q : ℝ) ≤ horizonY q / 2 ^ 27 := by
  have hY := horizonY_ge q hv
  exact ⟨Nat.lt_floor_add_one _, Nat.floor_le (by positivity)⟩

lemma dim_bound (hv : HD.valid q) :
    2 ^ 56 * (horizonY q * noiseFactor q / 2 ^ 27 + 1) ^ 6 * (q.ℓ q.ε / q.ℓ 0) ^ 4 ≤ q.d :=
  hv.2.2.2

lemma base_valid (hv : HD.valid q) :
    LongTails.Setups.HighDimensionalEllSmoothNonconvex.spec.valid (base q) := by
  have hρ0 : 0 ≤ q.ρ := hv.1.1
  have hρ2 : q.ρ < 2 := hv.1.2.1
  have hreg : LongTails.Setups.EllSmoothNonconvex.Regular q.ℓ q.ρ := hv.1.2.2.1
  have hΔ : 0 ≤ q.Δ := hv.1.2.2.2.2.2.2.1
  have hε : 0 < q.ε := hv.1.2.2.2.2.2.2.2
  have hℓ0 : 0 < q.ℓ 0 := hv.2.1
  have hT : 2 ^ 28 * q.ε ^ 2 ≤ (2 - q.ρ) * q.Δ * q.ℓ q.ε := hv.2.2.1
  have hY := horizonY_ge q hv
  have hε2 : 0 ≤ q.ε ^ 2 := sq_nonneg _
  refine ⟨⟨hρ0, hρ2.le, hreg, hΔ, hε⟩, hρ2, hℓ0, by simp only [base]; linarith, ?_⟩
  simp only [base]
  have hfl : (⌊(2 - q.ρ) * q.Δ * q.ℓ q.ε / (2 ^ 27 * q.ε ^ 2)⌋₊ : ℝ) ≤
      horizonY q * noiseFactor q / 2 ^ 27 := by
    have hl := hreg.2.2 q.ε hε
    have h2ρ : 0 ≤ 2 - q.ρ := by linarith
    have h1 : (⌊(2 - q.ρ) * q.Δ * q.ℓ q.ε / (2 ^ 27 * q.ε ^ 2)⌋₊ : ℝ) ≤
        (2 - q.ρ) * q.Δ * q.ℓ q.ε / (2 ^ 27 * q.ε ^ 2) := Nat.floor_le (by positivity)
    have h2 : (2 - q.ρ) * q.Δ * q.ℓ q.ε / (2 ^ 27 * q.ε ^ 2) = horizonY q / 2 ^ 27 := by
      unfold horizonY
      field_simp
    have h3 : horizonY q / 2 ^ 27 ≤ horizonY q * noiseFactor q / 2 ^ 27 := by
      have := noiseFactor_ge q
      apply div_le_div_of_nonneg_right _ (by norm_num)
      nlinarith
    linarith
  have h0 : (0 : ℝ) ≤ (⌊(2 - q.ρ) * q.Δ * q.ℓ q.ε / (2 ^ 27 * q.ε ^ 2)⌋₊ : ℝ) := Nat.cast_nonneg _
  have hpow := pow_le_pow_left₀ (by linarith) (by linarith : (⌊(2 - q.ρ) * q.Δ * q.ℓ q.ε /
    (2 ^ 27 * q.ε ^ 2)⌋₊ : ℝ) + 1 ≤ horizonY q * noiseFactor q / 2 ^ 27 + 1) 6
  have hq : (0 : ℝ) ≤ (q.ℓ q.ε / q.ℓ 0) ^ 4 := by positivity
  have := dim_bound q hv
  nlinarith [mul_le_mul_of_nonneg_right hpow hq]

noncomputable def shapeOf (hv : HD.valid q) : Shape :=
  LongTails.Proofs.EllSmoothLowerBound.shape (base q) (base_valid q hv)

noncomputable def scaleOf (hv : HD.valid q) : Scale :=
  LongTails.Proofs.EllSmoothLowerBound.scale (base q) (base_valid q hv)

lemma scaleOf_ratio (hv : HD.valid q) : (scaleOf q hv).a / (scaleOf q hv).lam = 8 * q.ε :=
  LongTails.Proofs.EllSmoothLowerBound.scale_ratio (base q) (base_valid q hv)

noncomputable def hardOracle (hv : HD.valid q) (π : Fin (chainLen q + 1) ↪ Fin q.d) :
    Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d)) where
  Seed := fun _ => ℝ
  law := ⟨stream, inferInstance⟩
  answer := fun _ (_, x) ω => reply (shapeOf q hv) (scaleOf q hv) (coinProb q) π q.x0 x ω

lemma chain_gap (hv : HD.valid q) :
    ((chainLen q : ℝ) + 1) * (2 ^ 26 * q.ε ^ 2) ≤ (2 - q.ρ) * q.Δ * q.ℓ q.ε := by
  have hε : 0 < q.ε := hv.1.2.2.2.2.2.2.2
  obtain ⟨_, h2⟩ := chainLen_bounds q hv
  have hY := horizonY_ge q hv
  have hn1 : (chainLen q : ℝ) + 1 ≤ 2 * (horizonY q / 2 ^ 27) := by
    have : (1 : ℝ) ≤ horizonY q / 2 ^ 27 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have he : horizonY q * q.ε ^ 2 = (2 - q.ρ) * q.Δ * q.ℓ q.ε := by
    unfold horizonY; field_simp
  have : ((chainLen q : ℝ) + 1) * (2 ^ 26 * q.ε ^ 2) ≤ 2 * (horizonY q / 2 ^ 27) *
      (2 ^ 26 * q.ε ^ 2) := mul_le_mul_of_nonneg_right hn1 (by positivity)
  nlinarith

lemma moment_bound (hv : HD.valid q) {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 4096 * q.ε) :
    s ^ q.p * (coinProb q * (1 / coinProb q - 1) ^ q.p + (1 - coinProb q)) ≤ q.σ ^ q.p := by
  have hp1 : 1 < q.p := hv.1.2.2.2.1
  have hσ : 0 ≤ q.σ := hv.1.2.2.2.2.2.1
  have hε : 0 < q.ε := hv.1.2.2.2.2.2.2.2
  have hq0 := coinProb_pos q
  have hq1 := coinProb_le q
  rcases (noiseFactor_ge q).eq_or_lt with h1 | h1
  · have hc : coinProb q = 1 := by unfold coinProb; rw [← h1]; norm_num
    rw [hc]
    simp only [div_one, sub_self, Real.zero_rpow (by linarith : q.p ≠ 0), mul_zero, add_zero]
    positivity
  · have hX1 : 1 < (q.σ / (2 ^ 13 * q.ε)) ^ (q.p / (q.p - 1)) := by
      unfold noiseFactor at h1
      rcases lt_max_iff.mp h1 with h | h
      · exact absurd h (lt_irrefl 1)
      · exact h
    have hM : noiseFactor q = (q.σ / (2 ^ 13 * q.ε)) ^ (q.p / (q.p - 1)) := by
      unfold noiseFactor; exact max_eq_right hX1.le
    have hσ0 : 0 < q.σ := by
      by_contra hc
      have : q.σ = 0 := le_antisymm (not_lt.mp hc) hσ
      rw [this, zero_div, Real.zero_rpow (by
        have : 0 < q.p / (q.p - 1) := div_pos (by linarith) (by linarith)
        linarith)] at hX1
      linarith
    have hmom := coin_moment_le (p := q.p) hp1.le hq0 hq1
    have hX0 : 0 < q.σ / (2 ^ 13 * q.ε) := by positivity
    have hp1' : q.p - 1 ≠ 0 := by linarith
    have hpow : coinProb q ^ (1 - q.p) = (q.σ / (2 ^ 13 * q.ε)) ^ q.p := by
      unfold coinProb
      rw [hM, one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
        ← Real.rpow_mul hX0.le]
      congr 1
      field_simp
      ring
    have h2 : s ^ q.p ≤ (4096 * q.ε) ^ q.p := Real.rpow_le_rpow hs0 hs (by linarith)
    have h3 : (4096 * q.ε) ^ q.p * (q.σ / (2 ^ 13 * q.ε)) ^ q.p = (q.σ / 2) ^ q.p := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    have h4 : (q.σ / 2) ^ q.p = q.σ ^ q.p / 2 ^ q.p := Real.div_rpow hσ (by norm_num) _
    have h5 : (2 : ℝ) ≤ 2 ^ q.p := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1.le
      rwa [Real.rpow_one] at this
    have hσp : 0 ≤ q.σ ^ q.p := by positivity
    have hV0 : 0 ≤ coinProb q * (1 / coinProb q - 1) ^ q.p + (1 - coinProb q) := by
      have : 0 ≤ 1 / coinProb q - 1 := by
        rw [sub_nonneg, le_div_iff₀ hq0]; linarith
      have : 0 ≤ (1 / coinProb q - 1) ^ q.p := by positivity
      nlinarith
    calc s ^ q.p * (coinProb q * (1 / coinProb q - 1) ^ q.p + (1 - coinProb q))
        ≤ (4096 * q.ε) ^ q.p * (2 * coinProb q ^ (1 - q.p)) := by
          apply mul_le_mul h2 hmom hV0 (by positivity)
      _ = 2 * ((4096 * q.ε) ^ q.p * (q.σ / (2 ^ 13 * q.ε)) ^ q.p) := by rw [hpow]; ring
      _ = 2 * (q.σ ^ q.p / 2 ^ q.p) := by rw [h3, h4]
      _ ≤ q.σ ^ q.p := by
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith

lemma hard_admissible (hv : HD.valid q) (π : Fin (chainLen q + 1) ↪ Fin q.d) :
    HD.admissible q (objective (shapeOf q hv) (scaleOf q hv) π q.x0) (hardOracle q hv π) := by
  set S := shapeOf q hv
  set Sc := scaleOf q hv
  have hb := base_valid q hv
  have hexact := LongTails.Proofs.EllSmoothLowerBound.instance_admissible (base q) hb (chainLen q)
    (chain_gap q hv) π
  obtain ⟨hgrad, hdiff, hH, hΔ, -⟩ := hexact
  have hgr : ∀ x, gradient (objective S Sc π q.x0) x = objGrad S Sc π q.x0 x :=
    objective_gradient S Sc π q.x0
  have hratio := scaleOf_ratio q hv
  have hsec (x : Space q.d) : ‖objGrad S Sc π q.x0 x -
      knownPart S Sc π (stage (sel π (toUnit Sc q.x0 x))) q.x0 x‖ ≤ 4096 * q.ε := by
    have := secret_norm S Sc π q.x0 x
    rw [hratio] at this
    linarith
  have hdiffpt (x : Space q.d) (ω : ℝ) :
      ‖reply S Sc (coinProb q) π q.x0 x ω - gradient (objective S Sc π q.x0) x‖ ^ q.p =
        |coin (coinProb q) ω - 1| ^ q.p * ‖objGrad S Sc π q.x0 x -
          knownPart S Sc π (stage (sel π (toUnit Sc q.x0 x))) q.x0 x‖ ^ q.p := by
    rw [hgr]
    have : reply S Sc (coinProb q) π q.x0 x ω - objGrad S Sc π q.x0 x =
        (coin (coinProb q) ω - 1) • (objGrad S Sc π q.x0 x -
          knownPart S Sc π (stage (sel π (toUnit Sc q.x0 x))) q.x0 x) := by
      simp only [reply, sub_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  have hcm := coin_moment (p := q.p) (coinProb_pos q) (coinProb_le q)
  refine ⟨fun x ω => reply S Sc (coinProb q) π q.x0 x ω,
    ⟨unif, inferInstanceAs (IsProbabilityMeasure unif)⟩,
    ⟨stream, inferInstanceAs (IsProbabilityMeasure stream)⟩, stream_iid, rfl, hgrad, hdiff, hH,
    hΔ, reply_measurable S Sc _ π q.x0, fun x => reply_integrable S Sc _ π q.x0 x, ?_, ?_, ?_⟩
  · intro x
    exact (reply_integral S Sc (coinProb_pos q) (coinProb_le q) π q.x0 x).trans (hgr x).symm
  · intro x
    have he : (fun ω => ‖reply S Sc (coinProb q) π q.x0 x ω -
        gradient (objective S Sc π q.x0) x‖ ^ q.p) = fun ω =>
        |coin (coinProb q) ω - 1| ^ q.p * ‖objGrad S Sc π q.x0 x -
          knownPart S Sc π (stage (sel π (toUnit Sc q.x0 x))) q.x0 x‖ ^ q.p := by
      funext ω; exact hdiffpt x ω
    change Integrable (fun ω => ‖reply S Sc (coinProb q) π q.x0 x ω -
        gradient (objective S Sc π q.x0) x‖ ^ q.p) unif
    rw [he]
    exact hcm.1.mul_const _
  · intro x
    change (∫ ω, ‖reply S Sc (coinProb q) π q.x0 x ω -
        gradient (objective S Sc π q.x0) x‖ ^ q.p ∂unif) ≤ q.σ ^ q.p
    simp_rw [hdiffpt x]
    rw [integral_mul_const, hcm.2, mul_comm]
    exact moment_bound q hv (norm_nonneg _) (hsec x)

lemma trueState_iterate {d n : ℕ} (S : Shape) (Sc : Scale) (qc : ℝ) (π : Fin (n + 1) ↪ Fin d)
    (x0 : Space d) {St : Type*} (query : St → Space d) (update : St → Space d → St)
    (initial : St) (ω : ℕ → ℝ) (N : ℕ) :
    ((fun sc : St × ℕ => (update sc.1 (reply S Sc qc π x0 (query sc.1) (ω sc.2)), sc.2 + 1))^[N]
      (initial, 0)) = (trueState S Sc qc π x0 query update initial ω N, N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

lemma execute_hard (hv : HD.valid q) (π : Fin (chainLen q + 1) ↪ Fin q.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (seed : A.Seed) (ω : ℕ → ℝ) :
    execute (hardOracle q hv π) A (fun _ => N) seed ω =
      A.output (trueState (shapeOf q hv) (scaleOf q hv) (coinProb q) π q.x0
        (fun s => (A.query s).2) A.update (A.initial seed) ω N) := by
  rw [execute_indexed_of_answer (hardOracle q hv π) A N seed ω
    (fun t query => reply (shapeOf q hv) (scaleOf q hv) (coinProb q) π q.x0 query.2 (ω t))
    (fun _ query => by cases query; rfl)]
  exact congrArg (fun st => A.output st.1) (trueState_iterate (shapeOf q hv) (scaleOf q hv)
    (coinProb q) π q.x0 (fun s => (A.query s).2) A.update (A.initial seed) ω N)

lemma lowerBudget_le (hv : HD.valid q) :
    (lowerBudget q : ℝ) ≤ horizonY q * noiseFactor q / 2 ^ 32 := by
  have hY := horizonY_ge q hv
  have hM := noiseFactor_ge q
  have h0 : 0 ≤ horizonY q * noiseFactor q / 2 ^ 32 :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by norm_num)
  exact Nat.floor_le h0

lemma budget_le (hv : HD.valid q) (N : ℕ) (hN : N ≤ lowerBudget q) :
    (N : ℝ) * coinProb q ≤ horizonY q / 2 ^ 32 := by
  have hY := horizonY_ge q hv
  have hM := noiseFactor_ge q
  have h1 : (N : ℝ) ≤ horizonY q * noiseFactor q / 2 ^ 32 := by
    have h2 : (N : ℝ) ≤ (lowerBudget q : ℝ) := by exact_mod_cast hN
    exact h2.trans (lowerBudget_le q hv)
  have hq : noiseFactor q * coinProb q = 1 := by
    unfold coinProb; field_simp
  calc (N : ℝ) * coinProb q ≤ horizonY q * noiseFactor q / 2 ^ 32 * coinProb q :=
        mul_le_mul_of_nonneg_right h1 (coinProb_pos q).le
    _ = horizonY q / 2 ^ 32 * (noiseFactor q * coinProb q) := by ring
    _ = horizonY q / 2 ^ 32 := by rw [hq, mul_one]

lemma good_count_fraction (hv : HD.valid q) (N : ℕ) (hN : N ≤ lowerBudget q) :
    15 / 16 ≤ stream.real {ω | coinCount (coinProb q) ω N ≤ chainLen q / 2} := by
  have ht := coinCount_tail (coinProb q) (coinProb_pos q).le (coinProb_le q) N (chainLen q / 2)
  have hb := budget_le q hv N hN
  have hY := horizonY_ge q hv
  obtain ⟨hn1, _⟩ := chainLen_bounds q hv
  have hdiv : ((chainLen q : ℝ) + 1) / 2 ≤ ((chainLen q / 2 : ℕ) : ℝ) + 1 := by
    have : chainLen q ≤ 2 * (chainLen q / 2) + 1 := by omega
    have h' : (chainLen q : ℝ) ≤ 2 * ((chainLen q / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have hratio : (N : ℝ) * coinProb q / (((chainLen q / 2 : ℕ) : ℝ) + 1) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : horizonY q / 2 ^ 28 ≤ ((chainLen q / 2 : ℕ) : ℝ) + 1 := by
      have : horizonY q / 2 ^ 28 = (horizonY q / 2 ^ 27) / 2 := by ring
      rw [this]; linarith
    have h2 : horizonY q / 2 ^ 32 = 1 / 16 * (horizonY q / 2 ^ 28) := by ring
    nlinarith
  have hc : {ω : ℕ → ℝ | coinCount (coinProb q) ω N ≤ chainLen q / 2} =
      {ω | chainLen q / 2 + 1 ≤ coinCount (coinProb q) ω N}ᶜ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]; omega
  have hmeas : MeasurableSet {ω : ℕ → ℝ | chainLen q / 2 + 1 ≤ coinCount (coinProb q) ω N} := by
    have h := (coinCount_measurable (coinProb q) N)
      (measurableSet_Ici : MeasurableSet (Set.Ici (((chainLen q / 2 + 1 : ℕ) : ℝ))))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
    constructor <;> intro h <;> exact_mod_cast h
  rw [hc, measureReal_compl hmeas, probReal_univ]
  have : stream.real {ω | chainLen q / 2 + 1 ≤ coinCount (coinProb q) ω N} ≤ 1 / 16 := by
    refine ht.trans ?_
    exact hratio
  linarith

lemma bad_fraction (hv : HD.valid q) (N : ℕ) (hN : N ≤ lowerBudget q)
    {St : Type*} (query output : St → Space q.d) (update : St → Space q.d → St)
    (initial : St) (ω : ℕ → ℝ) :
    8 * (∑ w : CoordinateWords q.d (chainLen q), if coordinateBad (shapeOf q hv) (scaleOf q hv)
      (coinProb q) q.x0 query output update initial ω N (coordinateEmbedding w) then (1 : ℝ)
      else 0) ≤ Fintype.card (CoordinateWords q.d (chainLen q)) := by
  set S := shapeOf q hv
  set n := chainLen q
  have hmu : S.mu = q.ℓ 0 / q.ℓ q.ε := rfl
  have hmu0 := S.hmu
  have hmu1 := S.hmu'
  have hY := horizonY_ge q hv
  have hM := noiseFactor_ge q
  obtain ⟨_, hnY⟩ := chainLen_bounds q hv
  have hn : (n : ℝ) + 1 ≤ horizonY q * noiseFactor q / 2 ^ 27 + 1 := by
    have : horizonY q / 2 ^ 27 ≤ horizonY q * noiseFactor q / 2 ^ 27 :=
      div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
    linarith
  have hNY : (N : ℝ) + 1 ≤ horizonY q * noiseFactor q / 2 ^ 27 + 1 := by
    have h2 : (N : ℝ) ≤ (lowerBudget q : ℝ) := by exact_mod_cast hN
    have h3 : (lowerBudget q : ℝ) ≤ horizonY q * noiseFactor q / 2 ^ 32 := lowerBudget_le q hv
    have h4 : horizonY q * noiseFactor q / 2 ^ 32 ≤ horizonY q * noiseFactor q / 2 ^ 27 :=
      div_le_div_of_nonneg_left (by nlinarith) (by norm_num) (by norm_num)
    linarith
  set Z := horizonY q * noiseFactor q / 2 ^ 27 + 1 with hZ
  have hZ1 : 1 ≤ Z := by
    rw [hZ]; have : 0 ≤ horizonY q * noiseFactor q / 2 ^ 27 := by positivity
    linarith
  have hinv : 1 / S.mu ^ 4 = (q.ℓ q.ε / q.ℓ 0) ^ 4 := by
    rw [hmu, div_pow, div_pow, one_div_div]
  have hdim := dim_bound q hv
  rw [← hZ] at hdim
  let D : ℝ := q.d - (n + 1 : ℕ)
  have hR : (4 * rad S n) ^ 2 / (1 / 4) ^ 2 = 2 ^ 52 * ((n : ℝ) + 1) ^ 4 / S.mu ^ 4 := by
    unfold rad; field_simp; ring
  have hcount : ((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * ((4 * rad S n) ^ 2 / (1 / 4) ^ 2) ≤
      2 ^ 52 * Z ^ 6 * (1 / S.mu ^ 4) := by
    rw [hR]
    push_cast
    have h0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hp4 := pow_le_pow_left₀ h0 hn 4
    have hmu4 : 0 < S.mu ^ 4 := pow_pos hmu0 4
    have e : 2 ^ 52 * ((n : ℝ) + 1) ^ 4 / S.mu ^ 4 = 2 ^ 52 * ((n : ℝ) + 1) ^ 4 * (1 / S.mu ^ 4) := by
      ring
    rw [e]
    have hi : 0 ≤ 1 / S.mu ^ 4 := by positivity
    have hZ6 : Z * Z * (2 ^ 52 * Z ^ 4) = 2 ^ 52 * Z ^ 6 := by ring
    have h1 : ((N : ℝ) + 1) * ((n : ℝ) + 1) * (2 ^ 52 * ((n : ℝ) + 1) ^ 4) ≤
        Z * Z * (2 ^ 52 * Z ^ 4) := by
      apply mul_le_mul (mul_le_mul hNY hn h0 (by linarith)) (by gcongr) (by positivity)
        (by positivity)
    rw [hZ6] at h1
    calc ((N : ℝ) + 1) * ((n : ℝ) + 1) * (2 ^ 52 * ((n : ℝ) + 1) ^ 4 * (1 / S.mu ^ 4))
        = ((N : ℝ) + 1) * ((n : ℝ) + 1) * (2 ^ 52 * ((n : ℝ) + 1) ^ 4) * (1 / S.mu ^ 4) := by ring
      _ ≤ 2 ^ 52 * Z ^ 6 * (1 / S.mu ^ 4) := mul_le_mul_of_nonneg_right h1 hi
  have hroom : 8 * (2 ^ 52 * Z ^ 6 * (1 / S.mu ^ 4)) ≤ D := by
    dsimp only [D]
    rw [hinv]
    rw [hinv] at hcount
    have hq4 : (1 : ℝ) ≤ (q.ℓ q.ε / q.ℓ 0) ^ 4 := by
      apply one_le_pow₀
      rw [le_div_iff₀ hv.2.1, one_mul]
      exact hv.1.2.2.1.1 0 q.ε le_rfl hv.1.2.2.2.2.2.2.2.le
    have hZ6 : Z ≤ Z ^ 6 := by
      calc Z = Z ^ 1 := (pow_one _).symm
        _ ≤ Z ^ 6 := pow_le_pow_right₀ hZ1 (by norm_num)
    have hn' : ((n + 1 : ℕ) : ℝ) ≤ Z := by push_cast; exact hn
    nlinarith [mul_le_mul_of_nonneg_left hq4 (by positivity : (0 : ℝ) ≤ Z ^ 6)]
  have hD : 0 ≤ D := le_trans (by positivity) hroom
  have hDs : D + (n + 1 : ℕ) ≤ q.d := by dsimp only [D]; linarith
  have hb := bad_sum_bound S (scaleOf q hv) (coinProb q) q.x0 query output update initial ω N D hD
    hDs
  have hcard : (0 : ℝ) ≤ Fintype.card (CoordinateWords q.d n) := Nat.cast_nonneg _
  have hsum : 0 ≤ ∑ w : CoordinateWords q.d n, if coordinateBad S (scaleOf q hv) (coinProb q) q.x0
      query output update initial ω N (coordinateEmbedding w) then (1 : ℝ) else 0 :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  by_contra hcon
  push Not at hcon
  have hX : 0 < ((N + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * ((4 * rad S n) ^ 2 / (1 / 4) ^ 2) := by
    have := rad_pos S n; positivity
  have h1 := mul_le_mul_of_nonneg_right (hcount.trans (by linarith : 2 ^ 52 * Z ^ 6 *
    (1 / S.mu ^ 4) ≤ 8 * (2 ^ 52 * Z ^ 6 * (1 / S.mu ^ 4)))) hsum
  have h2 := mul_lt_mul_of_pos_left hcon hX
  have h3 := mul_le_mul_of_nonneg_right hroom hsum
  nlinarith

lemma exists_failure (hv : HD.valid q)
    (A : Algorithm (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))
      (EuclideanSpace ℝ (Fin q.d))) (N : ℕ) (hN : N ≤ lowerBudget q) :
    ∃ π : Fin (chainLen q + 1) ↪ Fin q.d,
      ¬ HD.successful q (objective (shapeOf q hv) (scaleOf q hv) π q.x0)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle q hv π).Seed k) =>
          execute (hardOracle q hv π) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((hardOracle q hv π).law : Measure _), inferInstance⟩ := by
  have hε : 0 < q.ε := hv.1.2.2.2.2.2.2.2
  set S := shapeOf q hv
  set Sc := scaleOf q hv
  set n := chainLen q
  set qc := coinProb q
  set Mh := n / 2
  let query : A.State → Space q.d := fun s => (A.query s).2
  let W := CoordinateWords q.d n
  have hratio : Sc.a / Sc.lam = 8 * q.ε := scaleOf_ratio q hv
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : W → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    ‖objGrad S Sc (coordinateEmbedding w) q.x0 (A.output (trueState S Sc qc (coordinateEmbedding w)
      q.x0 query A.update (A.initial z.1) z.2 N))‖
  have hloss (w : W) : (fun z : A.Seed × (ℕ → ℝ) => ‖gradient (objective S Sc (coordinateEmbedding w)
      q.x0) (execute (hardOracle q hv (coordinateEmbedding w)) A (fun _ => N) z.1 z.2)‖) =
        loss w := by
    funext z
    rw [objective_gradient, execute_hard]
  have hi (w : W) : Integrable (loss w) P := by
    have h := (hcon (coordinateEmbedding w)).2.1
    rw [← hloss w]
    exact h
  have hle (w : W) : ∫ z, loss w z ∂P ≤ q.ε := by
    have h := (hcon (coordinateEmbedding w)).2.2
    rw [← hloss w]
    exact h
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N ≤ Mh} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      4 * q.ε * (7 / 8) * Fintype.card W * good z ≤ ∑ w, loss w z := by
    by_cases hz : coinCount qc z.2 N ≤ Mh
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hlev : level n qc z.2 N < n + 1 := by
        have := min_le_right (n + 1) (coinCount qc z.2 N)
        unfold level
        omega
      have hbad := bad_fraction q hv N hN query A.output A.update (A.initial z.1) z.2
      have hgood (w : W) : ¬ coordinateBad S Sc qc q.x0 query A.output A.update (A.initial z.1)
          z.2 N (coordinateEmbedding w) → 4 * q.ε ≤ loss w z := by
        intro hw
        have h := good_gradient S Sc qc q.x0 query A.output A.update (A.initial z.1) z.2 N
          (coordinateEmbedding w) hw hlev
        rw [hratio] at h
        dsimp only [loss]
        linarith
      have hterm (w : W) : 4 * q.ε * (1 - if coordinateBad S Sc qc q.x0 query A.output A.update
          (A.initial z.1) z.2 N (coordinateEmbedding w) then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad S Sc qc q.x0 query A.output A.update (A.initial z.1) z.2 N
            (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]; exact norm_nonneg _
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]; exact hgood w hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset W)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hεp : 0 ≤ 4 * q.ε := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbad hεp]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => norm_nonneg _)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount qc ω N ≤ Mh} := by
    have h := (coinCount_measurable qc N) (measurableSet_Iic (a := ((Mh : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N ≤ Mh} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount qc ω N ≤ Mh} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      dsimp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount qc z.2 N ≤ Mh} =
        Prod.snd ⁻¹' {ω | coinCount qc ω N ≤ Mh} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac := good_count_fraction q hv N hN
  have hint_good : Integrable (fun z => 4 * q.ε * (7 / 8) * Fintype.card W * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int, integral_finsetSum Finset.univ (fun w _ => hi w)] at hmono
  have hsum : (∑ w : W, ∫ z, loss w z ∂P) ≤ Fintype.card W * q.ε := by
    calc _ ≤ ∑ _w : W, q.ε := Finset.sum_le_sum (fun w _ => hle w)
      _ = _ := by simp
  have hd : n + 1 ≤ q.d := by
    have hb := base_valid q hv
    have := LongTails.Proofs.EllSmoothLowerBound.ell_pos (base q) hb
    have hY := horizonY_ge q hv
    obtain ⟨_, hnY⟩ := chainLen_bounds q hv
    have hdim := dim_bound q hv
    have hM := noiseFactor_ge q
    have hq4 : (1 : ℝ) ≤ (q.ℓ q.ε / q.ℓ 0) ^ 4 := by
      apply one_le_pow₀
      rw [le_div_iff₀ hv.2.1, one_mul]
      exact hv.1.2.2.1.1 0 q.ε le_rfl hε.le
    set Z := horizonY q * noiseFactor q / 2 ^ 27 + 1 with hZdef
    have hZ : (n : ℝ) + 1 ≤ Z := by
      have : horizonY q / 2 ^ 27 ≤ horizonY q * noiseFactor q / 2 ^ 27 :=
        div_le_div_of_nonneg_right (by nlinarith) (by norm_num)
      rw [hZdef]; linarith
    have hZ1 : (1 : ℝ) ≤ Z := by
      rw [hZdef]; have : 0 ≤ horizonY q * noiseFactor q / 2 ^ 27 := by positivity
      linarith
    have hZ6 : Z ≤ Z ^ 6 := by
      calc Z = Z ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hZ1 (by norm_num)
    have hT : ((n + 1 : ℕ) : ℝ) ≤ q.d := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hq4 (by positivity : (0 : ℝ) ≤ Z ^ 6)]
    exact_mod_cast hT
  have hc : (0 : ℝ) < Fintype.card W := by exact_mod_cast coordinateWords_card_pos q.d n hd
  have hm1 := mul_le_mul_of_nonneg_left hfrac
    (by positivity : (0 : ℝ) ≤ 4 * q.ε * (7 / 8) * Fintype.card W)
  nlinarith

end Assembly

end LongTails.Proofs.StochasticEllSmoothLower
