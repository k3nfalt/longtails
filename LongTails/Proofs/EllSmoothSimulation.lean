import LongTails.Proofs.EllSmoothHardBounds
import LongTails.Proofs.AbcHardOracle
import LongTails.Proofs.Execution

open OracleTemplate
open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.EllSmoothSimulation

open LongTails.Proofs.EllSmoothProfiles
open LongTails.Proofs.AbcChainProfiles (pos rr abs_sub_le_sum pos_nonneg pos_of_nonneg pos_of_nonpos)
open LongTails.Proofs.EllSmoothChain LongTails.Proofs.EllSmoothChainHessian
open LongTails.Proofs.EllSmoothHard LongTails.Proofs.EllSmoothHardBounds
open LongTails.Proofs.AbcHardFunction (sel sel_apply sel_norm sel_opNorm sel_adjoint adjoint_norm
  adjoint_congr)
open LongTails.Proofs.AbcHardOracle (Scale toUnit toUnit_hasFDerivAt)

variable (S : Shape) {d n : ℕ}

noncomputable def pval (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d) : ℝ :=
  cut S n (‖w‖ ^ 2) * chain S (trunc r (sel π w)) + wall S n (‖w‖ ^ 2)

noncomputable def pgrad (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d) : Space d :=
  cut S n (‖w‖ ^ 2) • (sel π).adjoint (visibleField S r (sel π w)) +
    (2 * dcut S n (‖w‖ ^ 2) * chain S (trunc r (sel π w)) + 2 * dwall S n (‖w‖ ^ 2)) • w

lemma pval_prefix (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) : pval S π r w = pval S ρ r w := by
  have hs : ∀ i : Fin (n + 1), i.val < r → sel π w i = sel ρ w i := by
    intro i hi; rw [sel_apply, sel_apply, h i hi]
  unfold pval
  rw [trunc_congr r _ _ hs]

lemma pgrad_prefix (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) : pgrad S π r w = pgrad S ρ r w := by
  have hs : ∀ i : Fin (n + 1), i.val < r → sel π w i = sel ρ w i := by
    intro i hi; rw [sel_apply, sel_apply, h i hi]
  have hv := visibleField_congr S r _ _ hs
  have hsupp : ∀ k : Fin (n + 1), r ≤ k.val → visibleField S r (sel ρ w) k = 0 := by
    intro k hk
    simp only [visibleField]
    rw [ite_eq_right (by omega)]
  unfold pgrad
  rw [trunc_congr r _ _ hs, hv, adjoint_congr π ρ _ r hsupp h]

lemma far_sq {w : Space d} (hw : ¬ ‖w‖ ≤ 4 * rad S n) : 16 * rad S n ^ 2 ≤ ‖w‖ ^ 2 := by
  have hr := rad_pos S n
  push Not at hw
  nlinarith

lemma pval_exact (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (h : ‖w‖ ≤ 4 * rad S n → ∀ i : Fin (n + 1), r ≤ i.val → |sel π w i| ≤ 1 / 4) :
    pval S π (r + 1) w = hval S π w := by
  unfold pval hval
  by_cases hw : ‖w‖ ≤ 4 * rad S n
  · rw [chain_trunc_succ S r _ (h hw)]
  · rw [cut_of_ge S n (far_sq S hw), zero_mul, zero_mul]

lemma pgrad_exact (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (w : Space d)
    (h : ‖w‖ ≤ 4 * rad S n → ∀ i : Fin (n + 1), r ≤ i.val → |sel π w i| ≤ 1 / 4) :
    pgrad S π (r + 1) w = hgrad S π w := by
  unfold pgrad hgrad bco vfield
  by_cases hw : ‖w‖ ≤ 4 * rad S n
  · rw [chain_trunc_succ S r _ (h hw), visibleField_eq S r _ (h hw)]
  · rw [cut_of_ge S n (far_sq S hw), dcut_of_ge S n (far_sq S hw)]
    simp

noncomputable def objective (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) : ℝ :=
  Sc.a * hval S π (toUnit Sc x0 x)

noncomputable def objGrad (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) : Space d :=
  (Sc.a / Sc.lam) • hgrad S π (toUnit Sc x0 x)

lemma objective_hasGradientAt (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    HasGradientAt (objective S Sc π x0) (objGrad S Sc π x0 x) x := by
  have hd := ((hval_hasGradientAt S π (toUnit Sc x0 x)).hasFDerivAt.comp x
    (toUnit_hasFDerivAt Sc x0 x)).const_mul Sc.a
  rw [hasGradientAt_iff_hasFDerivAt]
  refine hd.congr_fderiv ?_
  ext v
  simp only [objGrad, InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
    smul_apply, smul_eq_mul,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.map_smul]
  field_simp

lemma objective_gradient (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    gradient (objective S Sc π x0) x = objGrad S Sc π x0 x :=
  (objective_hasGradientAt S Sc π x0 x).gradient

lemma objGrad_hasFDerivAt (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    HasFDerivAt (objGrad S Sc π x0)
      ((Sc.a / Sc.lam) • ((fderiv ℝ (hgrad S π) (toUnit Sc x0 x)).comp
        ((1 / Sc.lam) • ContinuousLinearMap.id ℝ (Space d)))) x :=
  (((hgrad_differentiable S π (toUnit Sc x0 x)).hasFDerivAt).comp x
    (toUnit_hasFDerivAt Sc x0 x)).const_smul (Sc.a / Sc.lam)

lemma objGrad_fderiv_norm_le (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    ‖fderiv ℝ (objGrad S Sc π x0) x‖ ≤
      Sc.a / Sc.lam ^ 2 * ‖fderiv ℝ (hgrad S π) (toUnit Sc x0 x)‖ := by
  have ha := Sc.ha
  have hl := Sc.hlam
  rw [(objGrad_hasFDerivAt S Sc π x0 x).fderiv]
  have hpos : (0 : ℝ) ≤ Sc.a / Sc.lam ^ 2 * ‖fderiv ℝ (hgrad S π) (toUnit Sc x0 x)‖ := by
    positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hpos
  intro v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Sc.a / Sc.lam)]
  have h1 := ContinuousLinearMap.le_opNorm (fderiv ℝ (hgrad S π) (toUnit Sc x0 x))
    ((1 / Sc.lam) • v)
  rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Sc.lam)] at h1
  calc Sc.a / Sc.lam * ‖fderiv ℝ (hgrad S π) (toUnit Sc x0 x) ((1 / Sc.lam) • v)‖
      ≤ Sc.a / Sc.lam * (‖fderiv ℝ (hgrad S π) (toUnit Sc x0 x)‖ * (1 / Sc.lam * ‖v‖)) := by
        gcongr
    _ = _ := by field_simp

abbrev Method (d : ℕ) := Algorithm (Space d) (ℝ × Space d) (Space d)

noncomputable def partialReply (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d) :
    ℝ × Space d :=
  (Sc.a * pval S π r (toUnit Sc x0 x), (Sc.a / Sc.lam) • pgrad S π r (toUnit Sc x0 x))

lemma partial_prefix (Sc : Scale) (π ρ : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d)
    (h : ∀ i : Fin (n + 1), i.val < r → π i = ρ i) :
    partialReply S Sc π r x0 x = partialReply S Sc ρ r x0 x := by
  simp only [partialReply, pval_prefix S π ρ r _ h, pgrad_prefix S π ρ r _ h]

lemma partial_exact (Sc : Scale) (π : Fin (n + 1) ↪ Fin d) (r : ℕ) (x0 x : Space d)
    (h : ‖toUnit Sc x0 x‖ ≤ 4 * rad S n →
      ∀ i : Fin (n + 1), r ≤ i.val → |sel π (toUnit Sc x0 x) i| ≤ 1 / 4) :
    partialReply S Sc π (r + 1) x0 x = (objective S Sc π x0 x, objGrad S Sc π x0 x) := by
  simp only [partialReply, objective, objGrad, pval_exact S π r _ h, pgrad_exact S π r _ h]

noncomputable def simulated (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (π : Fin (n + 1) ↪ Fin d) : ℕ → A.State
  | 0 => s
  | j + 1 =>
    let st := simulated A s Sc x0 π j
    A.update st (partialReply S Sc π (j + 1) x0 (A.query st).2)

lemma simulated_prefix (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (π ρ : Fin (n + 1) ↪ Fin d) (j : ℕ) (h : ∀ i : Fin (n + 1), i.val < j → π i = ρ i) :
    simulated S A s Sc x0 π j = simulated S A s Sc x0 ρ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [simulated, ih (fun i hi => h i (by omega)), partial_prefix S Sc π ρ _ _ _ h]

noncomputable def observation (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (j : Fin (n + 1)) (π : Fin (n + 1) ↪ Fin d) : Space d :=
  let st := simulated S A s Sc x0 π j.val
  toUnit Sc x0 (if j.val < n then (A.query st).2 else A.output st)

lemma observation_prefix (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (j : Fin (n + 1)) (π ρ : Fin (n + 1) ↪ Fin d)
    (h : ∀ i : Fin (n + 1), i.val < j → π i = ρ i) :
    observation S A s Sc x0 j π = observation S A s Sc x0 j ρ := by
  simp only [observation, simulated_prefix S A s Sc x0 π ρ j.val h]

noncomputable def realStep (A : Method d) (Sc : Scale) (x0 : Space d)
    (π : Fin (n + 1) ↪ Fin d) (st : A.State) : A.State :=
  let x := (A.query st).2
  A.update st (objective S Sc π x0 x, objGrad S Sc π x0 x)

lemma hard_output (A : Method d) (s : A.State) (Sc : Scale) (x0 : Space d)
    (π : Fin (n + 1) ↪ Fin d) (h : ∀ j : Fin (n + 1),
      ‖observation S A s Sc x0 j π‖ ≤ 4 * rad S n →
      ∀ i : Fin (n + 1), j.val ≤ i.val → |sel π (observation S A s Sc x0 j π) i| ≤ 1 / 4) :
    Sc.a / Sc.lam / 2 ≤ ‖objGrad S Sc π x0 (A.output ((realStep S A Sc x0 π)^[n] s))‖ := by
  have eqsim (j : ℕ) (hj : j ≤ n) :
      (realStep S A Sc x0 π)^[j] s = simulated S A s Sc x0 π j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      have hlt : j < n := by omega
      have hh := h ⟨j, by omega⟩
      simp only [observation, hlt, ↓reduceIte] at hh
      rw [Function.iterate_succ_apply', ih (by omega), simulated, partial_exact S _ _ _ _ _ hh]
      rfl
  rw [eqsim n le_rfl]
  let w := toUnit Sc x0 (A.output (simulated S A s Sc x0 π n))
  change Sc.a / Sc.lam / 2 ≤ ‖(Sc.a / Sc.lam) • hgrad S π w‖
  have hpos := div_pos Sc.ha Sc.hlam
  rw [norm_smul, Real.norm_of_nonneg hpos.le]
  have hr := rad_pos S n
  have hg : 1 / 2 ≤ ‖hgrad S π w‖ := by
    rcases le_total (4 * rad S n ^ 2) (‖w‖ ^ 2) with hw | hw
    · have := hgrad_far S π w hw
      linarith
    · have hw4 : ‖w‖ ≤ 4 * rad S n := by
        have := norm_le_of_sq_le (w := w) (B := 2 * rad S n) (by positivity) (by nlinarith)
        linarith
      have hh := h (Fin.last n)
      simp only [observation, Fin.val_last, lt_self_iff_false, ↓reduceIte] at hh
      have ht := hh hw4 (Fin.last n) le_rfl
      exact hgrad_near_unfinished S π w hw ⟨Fin.last n, lt_of_le_of_lt ht (by norm_num)⟩
  nlinarith [mul_le_mul_of_nonneg_left hg hpos.le]

noncomputable def oracle (f : Space d → ℝ) : Oracle (Space d) (ℝ × Space d) where
  answer _ q _ := (f q.2, gradient f q.2)

lemma exact_output (A : Method d) (seed : A.Seed) (x0 : Space d) (Sc : Scale)
    (π : Fin (n + 1) ↪ Fin d) (ξ : (k : ℕ) → (oracle (objective S Sc π x0)).Seed k) :
    execute (oracle (objective S Sc π x0)) A (fun _ => n) seed ξ =
      A.output ((realStep S A Sc x0 π)^[n] (A.initial seed)) := by
  let f := objective S Sc π x0
  let resp := fun (_ : ℕ) (q : Fin 1 × Space d) => ((f q.2, gradient f q.2) : ℝ × Space d)
  let step := fun z : A.State × ℕ => (A.update z.1 (resp z.2 (A.query z.1)), z.2 + 1)
  rw [execute_indexed_of_answer _ A n seed ξ resp (fun _ _ => rfl)]
  change A.output ((step^[n]) (A.initial seed, 0)).1 = _
  have hpost (j : ℕ) :
      (step^[j]) (A.initial seed, 0) = ((realStep S A Sc x0 π)^[j] (A.initial seed), j) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      simp [step, realStep, resp, f, objective_gradient]
  rw [hpost]

end LongTails.Proofs.EllSmoothSimulation
