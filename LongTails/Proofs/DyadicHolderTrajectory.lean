import LongTails.Proofs.DyadicHolderProcess
import LongTails.Proofs.NormalizedStormMoments

open MeasureTheory

namespace OracleTemplate.DyadicHolder

open OracleTemplate.NormalizedStorm

section Arith

variable (cfg : DyadicConfig)

lemma DyadicConfig.pow_level_dvd (k : ℕ) : 2 ^ cfg.level k ∣ cfg.pos k :=
  pow_padicValNat_dvd

lemma DyadicConfig.pow_level_le {k : ℕ} (hk : cfg.pos k ≠ 0) : 2 ^ cfg.level k ≤ cfg.pos k :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (cfg.pow_level_dvd k)

lemma DyadicConfig.pos_le (k : ℕ) : cfg.pos k ≤ k := Nat.mod_le _ _

lemma DyadicConfig.pos_lt (k : ℕ) : cfg.pos k < 2 ^ cfg.J := Nat.mod_lt _ (by positivity)

lemma DyadicConfig.pred_lt {k : ℕ} (hk : cfg.pos k ≠ 0) : cfg.pred k < k := by
  have h1 := cfg.pow_level_le hk
  have h2 := cfg.pos_le k
  have h3 : 0 < 2 ^ cfg.level k := by positivity
  show k - 2 ^ cfg.level k < k
  generalize 2 ^ cfg.level k = a at *
  omega

lemma DyadicConfig.sub_pred {k : ℕ} (hk : cfg.pos k ≠ 0) : k - cfg.pred k = 2 ^ cfg.level k := by
  have h1 := cfg.pow_level_le hk
  have h2 := cfg.pos_le k
  show k - (k - 2 ^ cfg.level k) = 2 ^ cfg.level k
  generalize 2 ^ cfg.level k = a at *
  omega

lemma DyadicConfig.level_lt {k : ℕ} (hk : cfg.pos k ≠ 0) : cfg.level k < cfg.J := by
  have h1 := cfg.pow_level_le hk
  have h2 := cfg.pos_lt k
  have : 2 ^ cfg.level k < 2 ^ cfg.J := lt_of_le_of_lt h1 h2
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this

lemma DyadicConfig.pos_pred {k : ℕ} (hk : cfg.pos k ≠ 0) :
    cfg.pos (cfg.pred k) = cfg.pos k - 2 ^ cfg.level k := by
  have h1 := cfg.pow_level_le hk
  unfold DyadicConfig.pred DyadicConfig.pos at *
  have hk' : k = 2 ^ cfg.J * (k / 2 ^ cfg.J) + k % 2 ^ cfg.J := (Nat.div_add_mod k _).symm
  have e : k - 2 ^ cfg.level k =
      (k % 2 ^ cfg.J - 2 ^ cfg.level k) + 2 ^ cfg.J * (k / 2 ^ cfg.J) := by
    generalize 2 ^ cfg.level k = a at *
    generalize 2 ^ cfg.J * (k / 2 ^ cfg.J) = Q at *
    generalize k % 2 ^ cfg.J = r at *
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt k (show 0 < 2 ^ cfg.J by positivity)
  generalize 2 ^ cfg.level k = a at *
  generalize 2 ^ cfg.J = N at *
  omega

lemma DyadicConfig.level_pred_gt {k : ℕ} (hk : cfg.pos k ≠ 0) (hp : cfg.pos (cfg.pred k) ≠ 0) :
    cfg.level k < cfg.level (cfg.pred k) := by
  set t := cfg.pos k
  set j := cfg.level k
  have hdvd : 2 ^ j ∣ t := cfg.pow_level_dvd k
  have hndvd : ¬ 2 ^ (j + 1) ∣ t := by
    have : padicValNat 2 t < j + 1 := Nat.lt_succ_self _
    intro h
    have := (padicValNat_dvd_iff_le (p := 2) hk).mp h
    omega
  obtain ⟨u, hu⟩ := hdvd
  have hu_odd : u % 2 = 1 := by
    by_contra hc
    have he : u % 2 = 0 := by omega
    obtain ⟨w, hw⟩ := Nat.dvd_of_mod_eq_zero he
    apply hndvd
    exact ⟨w, by rw [hu, hw, pow_succ]; ring⟩
  have hpp : cfg.pos (cfg.pred k) = 2 ^ (j + 1) * (u / 2) := by
    rw [cfg.pos_pred hk]
    change t - 2 ^ j = _
    rw [hu]
    have : u = 2 * (u / 2) + 1 := by omega
    conv_lhs => rw [this]
    rw [pow_succ]
    ring_nf
    omega
  have hd : 2 ^ (j + 1) ∣ cfg.pos (cfg.pred k) := ⟨u / 2, hpp⟩
  have := (padicValNat_dvd_iff_le (p := 2) hp).mp hd
  unfold DyadicConfig.level
  omega

end Arith

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Traj

variable (cfg : DyadicConfig) (g : E → Ω → E) (x0 : E) (τ : ℕ) (ξ : ℕ → Ω)

noncomputable def X (k : ℕ) : E := (boundary cfg g x0 τ ξ k).xs k

noncomputable def D (k : ℕ) : E := (boundary cfg g x0 τ ξ (k + 1)).ds k

variable {cfg g x0 τ ξ}

lemma xs_stable : ∀ k j, j ≤ k → (boundary cfg g x0 τ ξ k).xs j = X cfg g x0 τ ξ j
  | 0, j, h => by
      have : j = 0 := by omega
      subst this; rfl
  | k + 1, j, h => by
      by_cases hj : j = k + 1
      · subst hj; rfl
      · have h1 : (boundary cfg g x0 τ ξ (k + 1)).xs j = (boundary cfg g x0 τ ξ k).xs j := by
          simp only [boundary]
          rw [Function.update_of_ne hj]
        rw [h1]
        exact xs_stable k j (by omega)

lemma ds_stable : ∀ k j, j < k → (boundary cfg g x0 τ ξ k).ds j = D cfg g x0 τ ξ j
  | 0, j, h => by omega
  | k + 1, j, h => by
      by_cases hj : j = k
      · subst hj; rfl
      · have h1 : (boundary cfg g x0 τ ξ (k + 1)).ds j = (boundary cfg g x0 τ ξ k).ds j := by
          simp only [boundary]
          rw [Function.update_of_ne hj]
        rw [h1]
        exact ds_stable k j (by omega)

lemma X_zero : X cfg g x0 τ ξ 0 = x0 := rfl

lemma X_succ (k : ℕ) :
    X cfg g x0 τ ξ (k + 1) = stormStep cfg.η (X cfg g x0 τ ξ k) (D cfg g x0 τ ξ k) := by
  simp only [X, D, boundary, Function.update_self]

lemma D_anchor {k : ℕ} (hk : cfg.pos k = 0) :
    D cfg g x0 τ ξ k = (1 / (cfg.bA : ℝ)) •
      ∑ i ∈ Finset.range cfg.bA, g (X cfg g x0 τ ξ k) (ξ (off cfg k + i)) := by
  simp only [D, boundary, Function.update_self, dyadicEstimate, hk, ite_true, accum, contrib,
    boundary_k, DyadicConfig.batch]
  rfl

lemma D_level {k : ℕ} (hk : cfg.pos k ≠ 0) :
    D cfg g x0 τ ξ k = D cfg g x0 τ ξ (cfg.pred k) + (1 / (cfg.b (cfg.level k) : ℝ)) •
      ∑ i ∈ Finset.range (cfg.b (cfg.level k)),
        (g (X cfg g x0 τ ξ k) (ξ (off cfg k + i)) -
          g (X cfg g x0 τ ξ (cfg.pred k)) (ξ (off cfg k + i))) := by
  have hp := cfg.pred_lt hk
  have e1 := ds_stable (cfg := cfg) (g := g) (x0 := x0) (τ := τ) (ξ := ξ) k (cfg.pred k) hp
  have e2 := xs_stable (cfg := cfg) (g := g) (x0 := x0) (τ := τ) (ξ := ξ) k (cfg.pred k) hp.le
  show (boundary cfg g x0 τ ξ (k + 1)).ds k = _
  simp only [boundary, Function.update_self, dyadicEstimate, hk, ite_false, accum, contrib,
    boundary_k, DyadicConfig.batch]
  rw [e1, e2]
  rfl

lemma X_dist (hη : 0 ≤ cfg.η) : ∀ k m, ‖X cfg g x0 τ ξ (k + m) - X cfg g x0 τ ξ k‖ ≤ m * cfg.η
  | k, 0 => by simp
  | k, m + 1 => by
      rw [← Nat.add_assoc, X_succ]
      have h1 := stormStep_dist hη (X cfg g x0 τ ξ (k + m)) (D cfg g x0 τ ξ (k + m))
      have h2 := X_dist hη k m
      calc ‖stormStep cfg.η (X cfg g x0 τ ξ (k + m)) (D cfg g x0 τ ξ (k + m)) - X cfg g x0 τ ξ k‖
          ≤ ‖stormStep cfg.η (X cfg g x0 τ ξ (k + m)) (D cfg g x0 τ ξ (k + m)) -
              X cfg g x0 τ ξ (k + m)‖ + ‖X cfg g x0 τ ξ (k + m) - X cfg g x0 τ ξ k‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ cfg.η + m * cfg.η := add_le_add h1 h2
        _ = ((m + 1 : ℕ) : ℝ) * cfg.η := by push_cast; ring

lemma X_pred_dist (hη : 0 ≤ cfg.η) {k : ℕ} (hk : cfg.pos k ≠ 0) :
    ‖X cfg g x0 τ ξ k - X cfg g x0 τ ξ (cfg.pred k)‖ ≤ 2 ^ cfg.level k * cfg.η := by
  have h := X_dist (cfg := cfg) (g := g) (x0 := x0) (τ := τ) (ξ := ξ) hη (cfg.pred k)
    (2 ^ cfg.level k)
  have e : cfg.pred k + 2 ^ cfg.level k = k := by
    have := cfg.sub_pred hk; have := (cfg.pred_lt hk).le; omega
  rw [e] at h
  simpa using h

end Traj

section Congr

variable {cfg : DyadicConfig} {g : E → Ω → E} {x0 : E} {τ : ℕ}

lemma off_mono {k m : ℕ} (h : k ≤ m) : off cfg k ≤ off cfg m := by
  induction m with
  | zero => have : k = 0 := by omega
            subst this; rfl
  | succ m ih =>
      rcases Nat.lt_or_ge k (m + 1) with hk | hk
      · exact (ih (by omega)).trans (by simp only [off]; omega)
      · have : k = m + 1 := by omega
        subst this; rfl

lemma boundary_congr {ξ ξ' : ℕ → Ω} :
    ∀ k, (∀ i, i < off cfg k → ξ i = ξ' i) → boundary cfg g x0 τ ξ k = boundary cfg g x0 τ ξ' k
  | 0, _ => rfl
  | k + 1, h => by
      have ih := boundary_congr k (fun i hi => h i (lt_of_lt_of_le hi (off_mono (Nat.le_succ k))))
      have ha : accum cfg g (boundary cfg g x0 τ ξ k) ξ (off cfg k) (cfg.batch k) =
          accum cfg g (boundary cfg g x0 τ ξ' k) ξ' (off cfg k) (cfg.batch k) := by
        rw [ih]
        unfold accum
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [h (off cfg k + i) (by simp only [off]; have := Finset.mem_range.mp hi; omega)]
      simp only [boundary]
      rw [ha, ih]

lemma X_congr {ξ ξ' : ℕ → Ω} (k : ℕ) (h : ∀ i, i < off cfg k → ξ i = ξ' i) :
    X cfg g x0 τ ξ k = X cfg g x0 τ ξ' k := by
  unfold X; rw [boundary_congr k h]

lemma D_congr {ξ ξ' : ℕ → Ω} (k : ℕ) (h : ∀ i, i < off cfg (k + 1) → ξ i = ξ' i) :
    D cfg g x0 τ ξ k = D cfg g x0 τ ξ' k := by
  unfold D; rw [boundary_congr (k + 1) h]

end Congr

section Meas

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {cfg : DyadicConfig} {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E) (τ : ℕ)
include hg

lemma measurable_boundary : ∀ k, (∀ j, Measurable fun ξ : ℕ → Ω => (boundary cfg g x0 τ ξ k).xs j) ∧
    (∀ j, Measurable fun ξ : ℕ → Ω => (boundary cfg g x0 τ ξ k).ds j)
  | 0 => ⟨fun _ => measurable_const, fun _ => measurable_const⟩
  | k + 1 => by
      obtain ⟨hx, hd⟩ := measurable_boundary k
      have hgk : ∀ (y : (ℕ → Ω) → E), Measurable y → ∀ c : ℕ,
          Measurable fun ξ : ℕ → Ω => g (y ξ) (ξ c) :=
        fun y hy c => hg.comp (hy.prodMk (measurable_pi_apply c))
      have hacc : Measurable fun ξ : ℕ → Ω =>
          accum cfg g (boundary cfg g x0 τ ξ k) ξ (off cfg k) (cfg.batch k) := by
        unfold accum contrib
        simp only [boundary_k]
        refine Finset.measurable_sum _ fun i _ => ?_
        split_ifs
        · exact hgk _ (hx k) _
        · exact (hgk _ (hx k) _).sub (hgk _ (hx _) _)
      have hest : Measurable fun ξ : ℕ → Ω => dyadicEstimate cfg (boundary cfg g x0 τ ξ k).ds k
          (accum cfg g (boundary cfg g x0 τ ξ k) ξ (off cfg k) (cfg.batch k)) := by
        unfold dyadicEstimate
        split_ifs
        · exact hacc.const_smul _
        · exact (hd _).add (hacc.const_smul _)
      refine ⟨fun j => ?_, fun j => ?_⟩
      · simp only [boundary]
        by_cases hj : j = k + 1
        · subst hj
          simp only [Function.update_self]
          exact (measurable_stormStep cfg.η).comp ((hx k).prodMk hest)
        · simp only [Function.update_of_ne hj]
          exact hx j
      · simp only [boundary]
        by_cases hj : j = k
        · subst hj
          simp only [Function.update_self]
          exact hest
        · simp only [Function.update_of_ne hj]
          exact hd j

lemma measurable_X (k : ℕ) : Measurable fun ξ : ℕ → Ω => X cfg g x0 τ ξ k :=
  (measurable_boundary hg x0 τ k).1 k

lemma measurable_D (k : ℕ) : Measurable fun ξ : ℕ → Ω => D cfg g x0 τ ξ k :=
  (measurable_boundary hg x0 τ (k + 1)).2 k

end Meas

section Exec

lemma boundary_tau_eq {cfg : DyadicConfig} {g : E → Ω → E} {x0 : E} (τ : ℕ) (ξ : ℕ → Ω) :
    ∀ k, boundary cfg g x0 τ ξ k = { boundary cfg g x0 0 ξ k with tau := τ }
  | 0 => rfl
  | k + 1 => by
      rw [boundary, boundary, boundary_tau_eq τ ξ k]
      rfl

lemma execute_dyadicVR [MeasurableSpace Ω] (cfg : DyadicConfig) (hb : ∀ k, 1 ≤ cfg.batch k)
    (g : E → Ω → E) (P : ProbabilityMeasure (ℕ → Ω)) (x0 : E) (B : ℕ)
    (τ : (dyadicVR (E := E) cfg x0).Seed) (ξ : ℕ → Ω) (hB : off cfg (cfg.K + 1) ≤ B) :
    execute (pairOracle g P) (dyadicVR cfg x0) (fun _ => B) τ ξ =
      X cfg g x0 0 ξ (τ : Fin (cfg.K + 1)).val := by
  refine (execute_indexed_of_answer (pairOracle g P) (dyadicVR cfg x0) B τ ξ (fun k q => (g q.2.1 (ξ k), g q.2.2 (ξ k))) (fun _ _ => rfl)).trans ?_
  change Fin (cfg.K + 1) at τ
  have hit : ∀ c, (fun sc : DyadicState E × ℕ =>
      (dyadicUpdate cfg sc.1 ((pairOracle g P).answer [] (0, dyadicQuery cfg sc.1) (ξ sc.2)),
        sc.2 + 1))^[c] ((dyadicVR cfg x0).initial τ, 0) = (callState cfg g x0 τ.val ξ c, c) := by
    intro c
    induction c with
    | zero => rfl
    | succ c ih =>
        rw [Function.iterate_succ_apply', ih]
        rfl
  change (((fun sc : DyadicState E × ℕ =>
      (dyadicUpdate cfg sc.1 ((pairOracle g P).answer [] (0, dyadicQuery cfg sc.1) (ξ sc.2)),
        sc.2 + 1))^[B] ((dyadicVR cfg x0).initial τ, 0)).1).xs
      (((fun sc : DyadicState E × ℕ =>
      (dyadicUpdate cfg sc.1 ((pairOracle g P).answer [] (0, dyadicQuery cfg sc.1) (ξ sc.2)),
        sc.2 + 1))^[B] ((dyadicVR cfg x0).initial τ, 0)).1).tau = _
  rw [hit]
  have hbd := callState_boundary (g := g) hb x0 τ.val ξ (cfg.K + 1) le_rfl
  obtain ⟨m, hm⟩ : ∃ m, B = off cfg (cfg.K + 1) + m := ⟨B - off cfg (cfg.K + 1), by omega⟩
  have hfr := callState_frozen (cfg := cfg) (g := g) x0 τ.val ξ (off cfg (cfg.K + 1))
    (by rw [hbd, boundary_k]) m
  simp only
  rw [hm, hfr, hbd, boundary_tau]
  have hτ : τ.val ≤ cfg.K + 1 := by have := τ.isLt; omega
  rw [xs_stable (cfg.K + 1) τ.val hτ]
  unfold X
  rw [boundary_tau_eq τ.val ξ τ.val]

end Exec

end OracleTemplate.DyadicHolder
