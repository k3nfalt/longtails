import LongTails.Proofs.NcConcaveAssembly

open MeasureTheory OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.NcConcaveLower

open Classical
open LongTails.Proofs.NcConcavePartTwo LongTails.Proofs.NcConcaveBlock
open LongTails.Proofs.NcConcaveChainGrad LongTails.Proofs.NcConcaveLocality
open LongTails.Proofs.NcConcavePartThree LongTails.Proofs.NcConcaveEmbed
open LongTails.Proofs.NcConcaveStage LongTails.Proofs.NcConcaveOracle
open LongTails.Proofs.NcConcaveExecution LongTails.Proofs.NcConcaveCounting
open LongTails.Proofs.NcConcaveFailure LongTails.Proofs.NcConcaveParams
open LongTails.Proofs.NcConcaveAssembly
open LongTails.Proofs.AbcHardOracle (coin unif coin_integrable coin_integral coin_sq_integral setOf_le_measurable coin_measurable)
open LongTails.Proofs.AbcHardExecution (coinCount)
open LongTails.Proofs.AbcLowerMeasure (stream stream_iid coinCount_tail coinCount_measurable)
open LongTails.Proofs.SmoothConvexFiniteHiding (largeSet not_largeSet_small bounded_prefix_bad_count)
open LongTails.Proofs.FiniteSumNondualLowerHiding (hits distinctWords)
open LongTails.Proofs.FiniteSumNondualLowerAveraging (CoordinateWords coordinateEmbedding coordinateEmbedding_labels subtype_indicator_sum)
open LongTails.Proofs.FiniteSumNondualLowerBound (coordinateWords_card_pos)
open LongTails.Setups.StochasticNonconvexConcaveMinimax

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace

section valid

variable {q : Params} (hv : spec.valid q)
include hv

theorem good_word_loss (A : Algorithm (spec.Query q) (spec.Reply q) (spec.Output q)) (N : ℕ)
    (seed : A.Seed) (ω : ℕ → ℝ) (hcoin : coinCount (pOf q) ω N < nOf q * (mOf q + 1))
    (π : Fin (K (nOf q) (mOf q)) ↪ Fin q.d)
    (hgood : ¬ coordinateBad (θOf q) (alpha (mOf q)) (pOf q) (sOf q) (ℓOf q)
      (fun st => (A.query st).2.1) A.output A.update (A.initial seed) ω N (Real.sqrt (Bsq q))
      (θOf q / 2) π) :
    cδ / 6 * ℓOf q * sOf q ≤ stationarity (hardF q ⟨π⟩)
      (A.output (trueState (fun z ξ => hardG q ⟨π⟩ z.1 z.2 ξ) (fun st => (A.query st).2.1) A.update
        (A.initial seed) ω N)) := by
  set W : Word q.d (nOf q) (mOf q) := ⟨π⟩
  set θ := θOf q
  set τ := alpha (mOf q)
  set p := pOf q
  set s := sOf q
  set ℓ := ℓOf q
  set qry : A.State → Prim q.d × Dual q.d := fun st => (A.query st).2.1
  have hs := s_pos hv
  have hθ := θ_pos hv
  have hθ1 := θ_le_one hv
  have hτ := alpha_pos (mOf q)
  have hB0 : 0 ≤ Bsq q := by unfold Bsq; have := radiusU_pos hv; positivity
  have hlev := level_lt_K (n := nOf q) (m := mOf q) p ω N hcoin
  have hhit : ∀ t < N, SmallFrom (θ / 2) (levelSeq (nOf q) (mOf q) p ω t)
      (selC W s (qry (simState θ τ p W s ℓ qry A.update (A.initial seed) ω t)).1
        (qry (simState θ τ p W s ℓ qry A.update (A.initial seed) ω t)).2) := by
    intro t ht
    apply small_of_obs hs W
    intro k hk
    have hobs : observation θ τ p s ℓ qry A.output A.update (A.initial seed) ω N ⟨t, by omega⟩ π =
        obsVec s (qry (simState θ τ p W s ℓ qry A.update (A.initial seed) ω t)) := by
      simp only [observation, ht, ↓reduceIte]; rfl
    have hz := (A.query (simState θ τ p W s ℓ qry A.update (A.initial seed) ω t)).2.2
    have hnorm : ‖observation θ τ p s ℓ qry A.output A.update (A.initial seed) ω N ⟨t, by omega⟩ π‖ ≤
        Real.sqrt (Bsq q) := by
      rw [hobs, Real.le_sqrt (norm_nonneg _) hB0]
      refine (obsVec_norm hs _).trans ?_
      unfold Bsq
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h1 := norm_sq_prim (qry (simState θ τ p W s ℓ qry A.update (A.initial seed) ω t)).1
      have hx0 := hz.1.1
      have hx1 := hz.1.2
      rw [radiusAB_eq] at hx1
      have hy : ‖(qry (simState θ τ p W s ℓ qry A.update (A.initial seed) ω t)).2‖ ≤ q.D / 2 := by
        have := hz.2; simpa [dualSet] using this
      have hy2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      simp only [qry] at *
      nlinarith
    have h := good_small θ τ p s ℓ qry A.output A.update (A.initial seed) ω N (Real.sqrt (Bsq q))
      (θ / 2) π hgood ⟨t, by omega⟩ hnorm k hk
    rw [hobs] at h
    exact h
  have hcoup := coupling hθ hθ1 hτ p W s ℓ qry A.update (A.initial seed) ω N hhit
  have hcoup' : trueState (fun z ξ => hardG q ⟨π⟩ z.1 z.2 ξ) (fun st => (A.query st).2.1) A.update
      (A.initial seed) ω N = simState θ τ p W s ℓ qry A.update (A.initial seed) ω N := hcoup.symm
  rw [hcoup']
  set x := A.output (simState θ τ p W s ℓ qry A.update (A.initial seed) ω N)
  have hx := output_condition hv W x (fun hb => by
    have hobs : observation θ τ p s ℓ qry A.output A.update (A.initial seed) ω N (Fin.last N) π =
        obsVec s (x, (0 : Dual q.d)) := by
      simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte]; rfl
    have hk : levelSeq (nOf q) (mOf q) p ω (Fin.last N).val ≤
        (posU (m := mOf q) (Fin.last (nOf q)) : Fin (K (nOf q) (mOf q))).val := by
      simp only [Fin.val_last, posU, pU]
      unfold K at hlev
      omega
    have h := good_small θ τ p s ℓ qry A.output A.update (A.initial seed) ω N (Real.sqrt (Bsq q))
      (θ / 2) π hgood (Fin.last N) (by rw [hobs]; exact hb) _ hk
    rw [hobs] at h
    have h2 := obs_U hs (x, (0 : Dual q.d)) (π (posU (Fin.last (nOf q))))
    have h3 : |x (0, W.πU (Fin.last (nOf q)))| / s ≤ θ / 2 := h2.trans h
    rwa [div_le_iff₀ hs] at h3)
  exact stationarity_lower q W hs radiusAB_eq (ℓ_pos hv) L_eq hθ hθ1 le_rfl
    (by have := alpha_le_one (mOf q); linarith) (radiusU_pos hv) (hRU hv) (hsmall hv) le_rfl
    (hηL hv) (hD8 hv) (hD hv) x hx

lemma c_big : (64 / 49 : ℝ) * q.ε < cδ / 6 * ℓOf q * sOf q := by
  have hε := hε hv
  have e : cδ / 6 * ℓOf q * sOf q = cδ / 6 * (2 ^ 32 * q.ε / 2401500) := by
    rw [mul_assoc, ℓs_eq hv]
  rw [e]; unfold cδ
  nlinarith

theorem exists_failure (A : Algorithm (spec.Query q) (spec.Reply q) (spec.Output q)) (N : ℕ)
    (hN : (N : ℝ) ≤ B1 q + B2 q) :
    ∃ W : Word q.d (nOf q) (mOf q),
      ¬ spec.successful q (hardF q W)
        (fun w : A.Seed × ((k : ℕ) → (hardOracle q W).Seed k) =>
          execute (hardOracle q W) A (fun _ => N) w.1 w.2)
        ⟨(A.law : Measure _).prod ((hardOracle q W).law : Measure _), inferInstance⟩ := by
  set n := nOf q
  set m := mOf q
  set p := pOf q
  set c := cδ / 6 * ℓOf q * sOf q
  set qry : A.State → Prim q.d × Dual q.d := fun st => (A.query st).2.1
  have hε := hε hv
  have hp0 := p_pos hv
  have hp1 := p_le_one hv
  let Wd := CoordinateWords q.d (n * (m + 4))
  let emb : Wd → Fin (K n m) ↪ Fin q.d := fun w => coordinateEmbedding w
  by_contra hcon
  push Not at hcon
  let P : Measure (A.Seed × (ℕ → ℝ)) := (A.law : Measure A.Seed).prod stream
  let loss : Wd → A.Seed × (ℕ → ℝ) → ℝ := fun w z =>
    stationarity (hardF q ⟨emb w⟩) (A.output (trueState (fun y ξ => hardG q ⟨emb w⟩ y.1 y.2 ξ) qry
      A.update (A.initial z.1) z.2 N))
  have hloss (w : Wd) : (fun z : A.Seed × (ℕ → ℝ) => stationarity (hardF q ⟨emb w⟩)
      (execute (hardOracle q ⟨emb w⟩) A (fun _ => N) z.1 z.2)) = loss w := by
    funext z
    rw [execute_hard]
  have hi (w : Wd) : Integrable (loss w) P := by
    have h := (hcon ⟨emb w⟩).2.1
    rw [← hloss w]; exact h
  have hle (w : Wd) : ∫ z, loss w z ∂P ≤ q.ε := by
    have h := (hcon ⟨emb w⟩).2.2
    rw [← hloss w]; exact h
  have hnm : 1 ≤ n * (m + 1) := by
    have h1 : (1 : ℝ) ≤ n := by
      have := n_ge hv; have := Λ1_ge hv
      have : (1 : ℝ) ≤ Λ1 q / 2 ^ 60 := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    have h1' : 1 ≤ n := by exact_mod_cast h1
    nlinarith
  let good : A.Seed × (ℕ → ℝ) → ℝ := fun z =>
    Set.indicator {z : A.Seed × (ℕ → ℝ) | coinCount p z.2 N < n * (m + 1)} 1 z
  have hpt (z : A.Seed × (ℕ → ℝ)) :
      c * (7 / 8) * Fintype.card Wd * good z ≤ ∑ w, loss w z := by
    by_cases hz : coinCount p z.2 N < n * (m + 1)
    · have hg : good z = 1 := by simp [good, hz]
      rw [hg, mul_one]
      have hK0 : (0 : ℝ) < (K n m : ℕ) := by unfold K; positivity
      have hBpos : 0 < Bsq q := by unfold Bsq; have := s_pos hv; have := radiusU_pos hv; positivity
      have hθpos := θ_pos hv
      set X := ((N + 1 : ℕ) : ℝ) * ((K n m : ℕ) : ℝ) * (Bsq q / (θOf q / 2) ^ 2)
      have hX : 0 < X := by positivity
      have hdim := dim_ok hv N hN
      set Dm : ℝ := q.d - (K n m : ℕ)
      have hDm : 8 * X ≤ Dm := by simp only [Dm, X]; linarith
      have hbad := bad_sum_bound (θOf q) (alpha m) p (sOf q) (ℓOf q) qry A.output A.update
        (A.initial z.1) z.2 N (Real.sqrt (Bsq q)) (θOf q / 2) (Real.sqrt_nonneg _) (by positivity)
        Dm (by linarith) (by simp only [Dm]; linarith)
      rw [Real.sq_sqrt hBpos.le] at hbad
      set Sb := ∑ w : Wd, if coordinateBad (θOf q) (alpha m) p (sOf q) (ℓOf q) qry A.output A.update
        (A.initial z.1) z.2 N (Real.sqrt (Bsq q)) (θOf q / 2) (coordinateEmbedding w) then (1 : ℝ) else 0
      have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
      have hcard : 8 * Sb ≤ Fintype.card Wd := by
        have h1 : 8 * X * Sb ≤ Dm * Sb := mul_le_mul_of_nonneg_right hDm hSb0
        have h2 : Dm * Sb ≤ X * Fintype.card Wd := hbad
        have h3 : X * (8 * Sb) ≤ X * Fintype.card Wd := by nlinarith
        exact le_of_mul_le_mul_left h3 hX
      have hterm (w : Wd) : c * (1 - if coordinateBad (θOf q) (alpha m) p (sOf q) (ℓOf q) qry A.output
          A.update (A.initial z.1) z.2 N (Real.sqrt (Bsq q)) (θOf q / 2) (coordinateEmbedding w)
          then (1 : ℝ) else 0) ≤ loss w z := by
        by_cases hw : coordinateBad (θOf q) (alpha m) p (sOf q) (ℓOf q) qry A.output A.update
            (A.initial z.1) z.2 N (Real.sqrt (Bsq q)) (θOf q / 2) (coordinateEmbedding w)
        · simp only [hw, ↓reduceIte, sub_self, mul_zero]; exact stationarity_nonneg hv _ _
        · simp only [hw, ↓reduceIte, sub_zero, mul_one]
          exact good_word_loss hv A N z.1 z.2 hz (emb w) hw
      have hs := Finset.sum_le_sum (fun w (_ : w ∈ (Finset.univ : Finset Wd)) => hterm w)
      simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one] at hs
      have hc0 : 0 ≤ c := by unfold c cδ; have := ℓ_pos hv; have := s_pos hv; positivity
      nlinarith [mul_le_mul_of_nonneg_left hcard hc0]
    · have hg : good z = 0 := by simp [good, hz]
      rw [hg, mul_zero]
      exact Finset.sum_nonneg (fun w _ => stationarity_nonneg hv _ _)
  have hsetmeas : MeasurableSet {ω : ℕ → ℝ | coinCount p ω N < n * (m + 1)} := by
    have h := (coinCount_measurable p N) (measurableSet_Iio (a := ((n * (m + 1) : ℕ) : ℝ)))
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio]
    constructor <;> intro h <;> exact_mod_cast h
  have hgoodmeas : MeasurableSet {z : A.Seed × (ℕ → ℝ) | coinCount p z.2 N < n * (m + 1)} :=
    measurable_snd hsetmeas
  have hgood_int : ∫ z, good z ∂P = stream.real {ω | coinCount p ω N < n * (m + 1)} := by
    rw [integral_indicator_one hgoodmeas]
    have hm : P.map Prod.snd = stream := by
      simp only [P]; rw [Measure.map_snd_prod]; simp
    have hpre : {z : A.Seed × (ℕ → ℝ) | coinCount p z.2 N < n * (m + 1)} =
        Prod.snd ⁻¹' {ω | coinCount p ω N < n * (m + 1)} := rfl
    rw [hpre, Measure.real, ← Measure.map_apply measurable_snd hsetmeas, hm]
    rfl
  have hfrac : 7 / 8 ≤ stream.real {ω | coinCount p ω N < n * (m + 1)} := by
    have ht := coinCount_tail p hp0.le hp1 N (n * (m + 1) - 1)
    have hb := budget_ok hv N hN
    have he : ((n * (m + 1) - 1 : ℕ) : ℝ) + 1 = (n : ℝ) * ((m : ℝ) + 1) := by
      rw [Nat.cast_sub hnm, Nat.cast_one]; push_cast; ring
    have hc : {ω : ℕ → ℝ | coinCount p ω N < n * (m + 1)} =
        {ω | n * (m + 1) - 1 + 1 ≤ coinCount p ω N}ᶜ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]; omega
    have hmeas : MeasurableSet {ω : ℕ → ℝ | n * (m + 1) - 1 + 1 ≤ coinCount p ω N} := by
      have h := (coinCount_measurable p N)
        (measurableSet_Ici : MeasurableSet (Set.Ici (((n * (m + 1) - 1 + 1 : ℕ) : ℝ))))
      convert h using 1
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici]
      constructor <;> intro h <;> exact_mod_cast h
    rw [hc, measureReal_compl hmeas, probReal_univ]
    have hpos : (0 : ℝ) < (n : ℝ) * ((m : ℝ) + 1) := by
      have : (1 : ℝ) ≤ ((n * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hnm
      push_cast at this; linarith
    have : stream.real {ω | n * (m + 1) - 1 + 1 ≤ coinCount p ω N} ≤ 1 / 8 := by
      refine ht.trans ?_
      rw [he, div_le_iff₀ hpos]
      linarith
    linarith
  have hint_good : Integrable (fun z => c * (7 / 8) * Fintype.card Wd * good z) P :=
    ((integrable_const (1 : ℝ)).indicator hgoodmeas).const_mul _
  have hint_sum : Integrable (fun z => ∑ w, loss w z) P :=
    integrable_finsetSum Finset.univ (fun w _ => hi w)
  have hmono := integral_mono hint_good hint_sum hpt
  rw [integral_const_mul, hgood_int, integral_finsetSum Finset.univ (fun w _ => hi w)] at hmono
  have hsum : (∑ w : Wd, ∫ z, loss w z ∂P) ≤ Fintype.card Wd * q.ε := by
    calc _ ≤ ∑ _w : Wd, q.ε := Finset.sum_le_sum (fun w _ => hle w)
      _ = _ := by simp
  have hd : n * (m + 4) + 1 ≤ q.d := by
    have h := dim_ok hv N hN
    have hK0 : (0 : ℝ) ≤ 8 * ((N + 1 : ℕ) : ℝ) * ((K n m : ℕ) : ℝ) * (Bsq q / (θOf q / 2) ^ 2) := by
      have := θ_pos hv
      have : 0 ≤ Bsq q := by unfold Bsq; have := s_pos hv; have := radiusU_pos hv; positivity
      positivity
    have : ((K n m : ℕ) : ℝ) ≤ q.d := by linarith
    exact_mod_cast this
  have hcW : (0 : ℝ) < Fintype.card Wd := by exact_mod_cast coordinateWords_card_pos q.d _ hd
  have hcb : 64 / 49 * q.ε < c := c_big hv
  have hc0 : 0 ≤ c := by unfold c cδ; have := ℓ_pos hv; have := s_pos hv; positivity
  have hm1 := mul_le_mul_of_nonneg_left hfrac (by positivity : (0 : ℝ) ≤ c * (7 / 8) * Fintype.card Wd)
  linarith [mul_lt_mul_of_pos_left hcb hcW]

end valid

end LongTails.Proofs.NcConcaveLower
