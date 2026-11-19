import LongTails.Proofs.AdditiveCubeAnchoringRate

open MeasureTheory
open LongTails.Setups.AdditiveCubeFixedPoint LongTails.Algorithms.AdditiveCubeAnchoring

namespace LongTails.Proofs.AdditiveCubeAnchoringAccuracy

open AdditiveFixedPointBatch AdditiveCubeAnchoringExecution AdditiveCubeAnchoringRate
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)

variable {p : Params}

lemma block_accuracy (μ : Measure (Point p)) [IsProbabilityMeasure μ] (P : Measure (ℕ → Point p))
    [IsProbabilityMeasure P] (hP : IID (fun k (ξ : ℕ → Point p) => ξ k) μ P)
    (hd : 0 < p.d) (hi : Integrable (fun z => z) μ) (hz : (∫ z, z ∂μ) = 0)
    (hi2 : Integrable (fun z => ‖z‖^2) μ) (hσ : ∫ z, ‖z‖^2 ∂μ ≤ p.σ^2)
    {τ : ℝ} (ht : 0 < τ) {n : ℕ} (hn : 0 < n)
    (hb : 8*Real.log (2*p.d)*p.σ^2 ≤ n*τ^2) (off : ℕ) :
    Integrable (fun ξ => ‖blockSum ξ off n‖ / n) P ∧
    (∫ ξ, ‖blockSum ξ off n‖ / n ∂P) ≤ τ := by
  let _ : NeZero p.d := ⟨hd.ne'⟩
  have h := batch_accuracy μ hi hz hi2 hσ ht hn hb
  have hpres := measurePreserving_snd.comp (hP.prefix_tail_law off)
  refine ⟨hpres.integrable_comp_of_integrable h.1, ?_⟩
  have hm : Measurable (fun ξ : ℕ → Point p => ‖sampleSum n ξ‖ / n) := by unfold sampleSum; fun_prop
  have hi' := integral_map (μ := P) hpres.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hpres.map_eq] at hi'
  exact hi'.symm.le.trans h.2

lemma expected_noise (μ : Measure (Point p)) [IsProbabilityMeasure μ]
    (P : Measure (ℕ → Point p)) [IsProbabilityMeasure P]
    (hP : IID (fun k (ξ : ℕ → Point p) => ξ k) μ P)
    (hd : 0 < p.d) (hi : Integrable (fun z => z) μ) (hz : (∫ z, z ∂μ) = 0)
    (hi2 : Integrable (fun z => ‖z‖^2) μ) (hσ : ∫ z, ‖z‖^2 ∂μ ≤ p.σ^2)
    (m n off : ℕ) (hn : 0 < n) {τ : ℝ} (ht : 0 < τ)
    (hb : 8*Real.log (2*p.d)*p.σ^2 ≤ n*τ^2) :
    Integrable (fun ξ => totalNoise ξ m n off) P ∧
    (∫ ξ, totalNoise ξ m n off ∂P) ≤ 12*τ := by
  induction m generalizing τ n off with
  | zero =>
    have h j := block_accuracy μ P hP hd hi hz hi2 hσ ht hn hb (off+j*n)
    refine ⟨integrable_finsetSum (Finset.range 6) (fun j _ => (h j).1), ?_⟩
    change (∫ ξ, ∑ j ∈ Finset.range 6, ‖blockSum ξ (off+j*n) n‖/n ∂P) ≤ _
    rw [integral_finsetSum _ (fun j _ => (h j).1)]
    have hs := Finset.sum_le_sum (s := Finset.range 6) (fun j _ => (h j).2)
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat] at hs
    linarith
  | succ m ih =>
    let M : ℕ := 8^(m+1)
    have hM : 0 < (M : ℝ) := by dsimp [M]; positivity
    have h j := block_accuracy μ P hP hd hi hz hi2 hσ ht hn hb (off+j*n)
    have hphase : Integrable (fun ξ => noiseSum ξ off n (6*M)) P :=
      integrable_finsetSum _ (fun j _ => (h j).1)
    have hrest := ih (4*n) (off+6*M*n) (by omega) (τ := τ/2) (by positivity)
      (by push_cast; nlinarith only [hb])
    refine ⟨(hphase.const_mul (M : ℝ)⁻¹).add hrest.1, ?_⟩
    change (∫ ξ, (M : ℝ)⁻¹ * noiseSum ξ off n (6*M) + totalNoise ξ m (4*n) (off+6*M*n) ∂P) ≤ _
    rw [integral_add (hphase.const_mul _) hrest.1, integral_const_mul]
    have hs : (∫ ξ, noiseSum ξ off n (6*M) ∂P) ≤ (6*M : ℕ)*τ := by
      unfold noiseSum
      rw [integral_finsetSum _ (fun j _ => (h j).1)]
      simpa using Finset.sum_le_sum (s := Finset.range (6*M)) (fun j _ => (h j).2)
    have hh := add_le_add (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hM.le)) hrest.2
    apply hh.trans
    push_cast
    field_simp
    ring_nf
    exact le_rfl

lemma program_length (m n : ℕ) (hn : 0 < n) : (program m n).length ≤ 12*8^m*n := by
  induction m generalizing n with
  | zero => simp [program, stage_length 1 n (by decide) hn]; omega
  | succ m ih =>
    simp only [program, List.length_append, stage_length (8^(m+1)) n (by positivity) hn]
    have h := ih (4*n) (by omega)
    rw [pow_succ]
    nlinarith

lemma budget_suffices (he : 0 < p.ε) (hr : p.ε < p.R) :
    (program (depth p) (replicas p)).length ≤
      ⌈4096*(p.R/p.ε)*(1+2097152*Real.log (2*p.d)*(p.σ/p.ε)^2)⌉₊ := by
  let T := (p.R : ℝ)/p.ε
  have ht : 1 < T := (one_lt_div he).mpr hr
  have hbase : 1 < ⌈32*T⌉₊ := by
    by_contra! ha
    have := (Nat.le_ceil (32*T)).trans (show (⌈32*T⌉₊ : ℝ) ≤ 1 by exact_mod_cast ha)
    linarith
  have hpow := Nat.pow_pred_clog_lt_self (b := 8) (by decide) hbase
  have hdep : 0 < depth p := by
    have hc := Nat.le_pow_clog (by decide : 1 < 8) ⌈32*T⌉₊
    by_contra! hz
    change Nat.clog 8 _ ≤ 0 at hz
    have : Nat.clog 8 ⌈32*T⌉₊ = 0 := by simpa [depth, T, mul_div_assoc] using hz
    rw [this, pow_zero] at hc
    omega
  have hdp : (8 : ℝ)^depth p ≤ 264*T := by
    have hc : depth p = Nat.clog 8 ⌈32*T⌉₊ := by simp [depth, T, mul_div_assoc]
    rw [← Nat.sub_add_cancel hdep, pow_succ, hc]
    have hlt : (8:ℝ) ^ (Nat.clog 8 ⌈32*T⌉₊ - 1) < (⌈32*T⌉₊ : ℝ) := by exact_mod_cast hpow
    linarith [Nat.ceil_lt_add_one (show 0 ≤ 32*T by positivity)]
  let W := 2097152*Real.log (2*p.d)*(p.σ/p.ε)^2
  have hw : 0 ≤ W := by
    have hlog : 0 ≤ Real.log (2*(p.d:ℝ)) := by
      by_cases hd : p.d = 0
      · simp [hd]
      · have hd' : (1:ℝ) ≤ p.d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
        exact Real.log_nonneg (by linarith)
    dsimp [W]; positivity
  have hn : 0 < replicas p := Nat.le_max_left 1 _
  have hrep : (replicas p : ℝ) ≤ 1+W := by
    change (max 1 ⌈W⌉₊ : ℕ) ≤ (1:ℝ)+W
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith [Nat.ceil_lt_add_one hw])
  apply (program_length _ _ hn).trans
  apply (Nat.cast_le (α := ℝ)).mp
  apply le_trans _ (Nat.le_ceil _)
  push_cast
  have h := mul_le_mul hdp hrep (Nat.cast_nonneg _) (by positivity)
  change _ ≤ 4096*T*(1+W)
  nlinarith [mul_nonneg (le_of_lt (lt_trans zero_lt_one ht)) (show 0 ≤ 1+W by linarith)]

lemma run_measurable {T : Cube p → Cube p} (hT : LipschitzWith 1 T) (cs : List Command) (off : ℕ)
    {s : (ℕ → Point p) → Data p} (hs : Measurable s) : Measurable (fun ξ => run T ξ cs off (s ξ)) := by
  induction cs generalizing off s with
  | nil => exact hs
  | cons c cs ih =>
    apply ih
    have hm : Measurable (mean T) := measurable_subtype_coe.comp (hT.continuous.measurable.comp
      (project_lipschitz p).continuous.measurable)
    have hreply := (hm.comp hs.fst).add (measurable_pi_apply off)
    cases c with
    | none => exact hs.fst.prodMk (hs.snd.fst.prodMk (hs.snd.snd.add hreply))
    | some c =>
      rcases c with ⟨M,n,b⟩
      cases b <;> simp only [applyReply, Bool.false_eq_true, ↓reduceIte] <;> fun_prop

lemma residual_bound {T : Cube p → Cube p} (hT : LipschitzWith 1 T)
    (ξ : ℕ → Point p) (he : 0 < p.ε) :
    let z := project p (run T ξ (program (depth p) (replicas p)) 0 (0,0,0)).1
    dist (T z) z ≤ p.ε/16 + 30*totalNoise ξ (depth p) (replicas p) 0 := by
  let M : ℕ := 8^depth p
  let a := (M : ℝ)⁻¹
  have hM : 0 < (M : ℝ) := by dsimp [M]; positivity
  have ha : 0 < a := inv_pos.mpr hM
  have hr : a*(p.R : ℝ) ≤ p.ε/32 := by
    have hc := (Nat.le_ceil (32*p.R/p.ε)).trans (Nat.cast_le.mpr (Nat.le_pow_clog (by decide : 1<8) _))
    change 32*(p.R:ℝ)/p.ε ≤ M at hc
    have hh := (div_le_iff₀ he).mp hc
    rw [← div_eq_inv_mul, div_le_iff₀ hM]
    linarith
  obtain ⟨u,hu⟩ := SmoothBanachAnchoring.exists_anchored_root (mean T) (mean_ne hT) a ha (0 : Point p)
  have heq : mean T u = (1+a) • u := by simpa using (sub_eq_zero.mp (by simpa using hu : (1+a) • u - mean T u = 0)).symm
  have hnorm : ‖u‖ ≤ p.R := by
    have hh := (T (project p u)).property
    change ‖mean T u‖ ≤ p.R at hh
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)] at hh
    nlinarith [mul_nonneg ha.le (norm_nonneg u)]
  have hres : ‖u-mean T u‖ = a*‖u‖ := by
    rw [heq, show u-(1+a) • u = (-a) • u by module, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ha]
  let y := (run T ξ (program (depth p) (replicas p)) 0 (0,0,0)).1
  have hh := terminal_residual hT ξ (depth p) (replicas p) 0 (Nat.le_max_left 1 _) 0 0 u hu
  change ‖y-mean T y‖ ≤ ‖u-mean T u‖ + a*‖0-u‖ + _ at hh
  simp only [zero_sub, norm_neg, hres] at hh
  have hproj := (project_lipschitz p).dist_le_mul y (mean T y)
  rw [NNReal.coe_one, one_mul, show project p (mean T y) = T (project p y) from project_fix _, dist_comm] at hproj
  apply hproj.trans
  rw [dist_eq_norm]
  linarith [mul_le_mul_of_nonneg_left hnorm ha.le]

lemma execution_accuracy {T : Cube p → Cube p} (hT : LipschitzWith 1 T)
    (μ : ProbabilityMeasure (Point p)) (P : ProbabilityMeasure (ℕ → Point p))
    (hP : IID (fun k (ξ : ℕ → Point p) => ξ k) (μ : Measure (Point p)) (P : Measure _))
    (hd : 0 < p.d) (he : 0 < p.ε) (hi : Integrable (fun z => z) (μ : Measure (Point p)))
    (hz : (∫ z, z ∂(μ : Measure (Point p))) = 0) (hi2 : Integrable (fun z => ‖z‖^2) (μ : Measure (Point p)))
    (hσ : ∫ z, ‖z‖^2 ∂(μ : Measure (Point p)) ≤ p.σ^2) (b : ℕ)
    (hb : (program (depth p) (replicas p)).length ≤ b) :
    let O : OracleTemplate.Oracle (Cube p) (Point p) :=
      { Seed := fun _ => Point p, law := P, answer := fun _ (_,x) z => (T x).val+z }
    spec.successful p T (output p O (fun _ => b)) P := by
  let f := fun ξ : ℕ → Point p => project p (run T ξ (program (depth p) (replicas p)) 0 (0,0,0)).1
  let O : OracleTemplate.Oracle (Cube p) (Point p) :=
    { Seed := fun _ => Point p, law := P, answer := fun _ (_,x) z => (T x).val+z }
  change spec.successful p T (output p O (fun _ => b)) P
  rw [show output p O (fun _ => b) = f from funext (execute_run P T b hb)]
  have hm : Measurable f := (project_lipschitz p).continuous.measurable.comp
    (run_measurable hT _ 0 (s := fun _ => (0,0,0)) measurable_const).fst
  have hresm := (hT.continuous.measurable.comp hm).dist hm
  have hresi : Integrable (fun ξ => dist (T (f ξ)) (f ξ)) (P : Measure _) := by
    apply Integrable.of_bound hresm.aestronglyMeasurable (2*(p.R:ℝ))
    apply ae_of_all
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Subtype.dist_eq, dist_eq_norm]
    exact (norm_sub_le _ _).trans ((add_le_add (T (f ξ)).property (f ξ).property).trans_eq (by ring))
  have hn : 0 < replicas p := Nat.le_max_left 1 _
  have hb' : 8*Real.log (2*p.d)*p.σ^2 ≤ replicas p*(p.ε/512)^2 := by
    have hc := (Nat.le_ceil (2097152*Real.log (2*p.d)*(p.σ/p.ε)^2)).trans
      (Nat.cast_le.mpr (Nat.le_max_right 1 _) : _ ≤ (replicas p : ℝ))
    field_simp at hc
    nlinarith only [hc]
  have hh := expected_noise (μ : Measure (Point p)) (P : Measure _) hP hd hi hz hi2 hσ (depth p)
    (replicas p) 0 hn (τ := p.ε/512) (by positivity) hb'
  refine ⟨hm, hresi, ?_⟩
  have hfin := integral_mono hresi ((integrable_const _).add (hh.1.const_mul 30)) (fun ξ => residual_bound hT ξ he)
  simp only [Pi.add_apply, integral_add (integrable_const _) (hh.1.const_mul 30), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hfin
  linarith [hh.2]

end LongTails.Proofs.AdditiveCubeAnchoringAccuracy
