import LongTails.Proofs.StochasticCompositeGeneralizedConcentration

open MeasureTheory ProbabilityTheory
open OracleTemplate.RobustGradient
open LongTails.Proofs.AdaptiveOracleConcentration
open LongTails.Proofs.StoppedVectorConcentration

namespace LongTails.Proofs.DistributedContaminationConcentration

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

lemma stopped_exp_sum {X : ℕ → Ω → E} (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) P)
    (h2i : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    (hz : ∀ i, ∫ ω, X i ω ∂P = 0) {v : ℕ → ℝ} {B r t : ℝ}
    (hB : 0 ≤ B) (hv0 : ∀ i, 0 ≤ v i) (ht : 0 ≤ t)
    (hb : ∀ i ω, ‖X i ω‖ ≤ B) (hv : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂P) ≤ v i)
    (hs : t * (2 * B * r + B ^ 2) ≤ 1) (n : ℕ)
    (hind : ∀ k < n, IndepFun (fun ω (i : Fin k) => X i ω) (X k) P) :
    let S := fun ω => stoppedSum (fun i => X i ω) r n
    Integrable (fun ω => Real.exp (t * ‖S ω‖ ^ 2)) P ∧
    (∫ ω, Real.exp (t * ‖S ω‖ ^ 2) ∂P) ≤
      Real.exp ((t + 2 * t ^ 2 * (4 * r ^ 2 + B ^ 2)) * ∑ i ∈ Finset.range n, v i) := by
  let Y : (n : ℕ) → (Fin n → E) × E → E := fun _ z => z.2
  let H := historyStoppedSum Y r
  let state (k : ℕ) (ω : Ω) := stoppedSum (fun i => X i ω) r k
  let c := t + 2 * t ^ 2 * (4 * r ^ 2 + B ^ 2)
  have he (k : ℕ) (ω : Ω) : H k (fun j => X j ω) = state k ω := by
    rw [show H = historyStoppedSum Y r from rfl, history_stopped_sum_eq]
  induction n with
  | zero => simp [stoppedSum]
  | succ n ih =>
    specialize ih (fun k hk => hind k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    let history (ω : Ω) (j : Fin n) := X j ω
    have hHist : Measurable history := Measurable.of_eval (fun (i : Fin n) => hm i)
    have hH : Measurable (H n) := history_stopped_sum_measurable (fun _ => measurable_snd) r n
    let F (z : (Fin n → E) × E) := Real.exp (t * ‖stoppedSumStep r (H n z.1) z.2‖ ^ 2)
    let weight (z : Fin n → E) := Real.exp (t * ‖H n z‖ ^ 2)
    have hw : Measurable weight := ((hH.norm.pow_const 2).const_mul t).exp
    have hF : Measurable F := (((measurable_stoppedSumStep r).comp
      ((hH.comp measurable_fst).prodMk measurable_snd)).norm.pow_const 2 |>.const_mul t).exp
    have hwi : Integrable weight (P.map history) := by
      apply (integrable_map_measure hw.aestronglyMeasurable hHist.aemeasurable).mpr
      simpa [Function.comp_def, weight, history, he, state] using ih.1
    have hloc (a : Fin n → E) := stoppedSumStep_exp_control (hm n) (hi n) (h2i n) (hz n)
      hB (hv0 n) ht (H n a) (hb n) (hv n) hs
    have hlocMap (a : Fin n → E) : Measurable (fun x => F (a, x)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have hlocI (a : Fin n → E) : Integrable (fun x => F (a, x)) (P.map (X n)) :=
      (integrable_map_measure (hlocMap a).aestronglyMeasurable (hm n).aemeasurable).mpr (hloc a).1
    have hlocB (a : Fin n → E) : (∫ x, F (a,x) ∂P.map (X n)) ≤ weight a * Real.exp (c * v n) := by
      rw [integral_map (hm n).aemeasurable (hlocMap a).aestronglyMeasurable]
      apply (hloc a).2.trans_eq
      dsimp only [weight]
      rw [← Real.exp_add]
      congr 1
      dsimp [c]
      ring
    have hh := independent_nonnegative_fiber_bound hHist (hm n) (hind n (Nat.lt_succ_self n))
      rfl hF (fun _ => Real.exp_nonneg _) hlocI (hwi.mul_const (Real.exp (c * v n))) hlocB
    have hcomp (ω : Ω) : F (history ω, X n ω) = Real.exp (t * ‖state (n+1) ω‖ ^ 2) := by
      simp only [F, history, he, state, stoppedSum, stoppedSumStep]
    refine ⟨by simpa only [hcomp, state] using hh.1, ?_⟩
    have hew (ω : Ω) : weight (history ω) = Real.exp (t * ‖state n ω‖ ^ 2) := by
      simp only [weight, history, he]
    have hfinal := hh.2
    rw [integral_mul_const, integral_map hHist.aemeasurable hw.aestronglyMeasurable] at hfinal
    simp only [hcomp, hew] at hfinal
    apply hfinal.trans
    apply (mul_le_mul_of_nonneg_right ih.2 (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, Finset.sum_range_succ]
    congr 1
    dsimp [c]
    ring

lemma vector_bernstein {X : ℕ → Ω → E} (hm : ∀ i, Measurable (X i))
    (hi : ∀ i, Integrable (X i) P) (h2i : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    (hz : ∀ i, ∫ ω, X i ω ∂P = 0) {v : ℕ → ℝ} {B r q : ℝ}
    (hB : 0 < B) (hv0 : ∀ i, 0 ≤ v i) (hr : 0 < r) (hq : 1 ≤ q)
    (hb : ∀ i ω, ‖X i ω‖ ≤ B) (hv : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂P) ≤ v i)
    (n : ℕ) (hind : ∀ k < n, IndepFun (fun ω (i : Fin k) => X i ω) (X k) P)
    (hsize : 128 * q * ((∑ i ∈ Finset.range n, v i) + B * r) ≤ r ^ 2) :
    P.real {ω | r < ‖∑ i ∈ Finset.range n, X i ω‖} ≤ Real.exp (-q) := by
  let V := ∑ i ∈ Finset.range n, v i
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _ => hv0 i)
  have hd : 0 < V + B * r := by positivity
  change 128 * q * (V + B * r) ≤ r ^ 2 at hsize
  have hdom := mul_le_mul_of_nonneg_right hq (show 0 ≤ 128 * (V + B * r) by positivity)
  have hBr : B ≤ r := by
    by_contra! hh
    nlinarith [mul_pos hr (sub_pos.mpr hh), mul_pos hB hr]
  have hVr : 4 * V ≤ r ^ 2 := by nlinarith [mul_pos hB hr]
  let t := 1 / (64 * (V + B * r))
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have htune := squared_sum_energy_tuning hB.le hV hr.le hBr hVr hd
  have h := stopped_exp_sum hm hi h2i hz hB.le hv0 ht hb hv htune.1 n hind
  have htail := exponential_tail_of_bound ht h.1 h.2 (r ^ 2)
  have hsub : {ω | r < ‖∑ i ∈ Finset.range n, X i ω‖} ⊆
      {ω | r ^ 2 ≤ ‖stoppedSum (fun i => X i ω) r n‖ ^ 2} := by
    intro ω hω
    by_contra hn
    have hn' : ‖stoppedSum (fun i => X i ω) r n‖ ≤ r := by
      simp only [Set.mem_ofPred_eq, not_le] at hn
      nlinarith [norm_nonneg (stoppedSum (fun i => X i ω) r n)]
    rw [stopped_sum_eq_unstopped hn'] at hn'
    exact (not_le.mpr hω) hn'
  apply (measureReal_mono hsub).trans (htail.trans (Real.exp_le_exp.mpr ?_))
  have hfrac : q ≤ r ^ 2 / (128 * (V + B * r)) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  apply le_trans ?_ (neg_le_neg hfrac)
  convert htune.2 using 1
  dsimp only [t, V]
  ring

private lemma fin_vector_bernstein {N : ℕ} {X : Fin N → Ω → E} (hm : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hi : ∀ i, Integrable (X i) P)
    (h2i : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    (hz : ∀ i, ∫ ω, X i ω ∂P = 0) {v : Fin N → ℝ} {B r q : ℝ}
    (hB : 0 < B) (hv0 : ∀ i, 0 ≤ v i) (hr : 0 < r) (hq : 1 ≤ q)
    (hb : ∀ i ω, ‖X i ω‖ ≤ B) (hv : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂P) ≤ v i)
    (hsize : 128 * q * ((∑ i, v i) + B * r) ≤ r ^ 2) :
    P.real {ω | r < ‖∑ i, X i ω‖} ≤ Real.exp (-q) := by
  classical
  let Y (j : ℕ) : Ω → E := if h : j < N then X ⟨j,h⟩ else 0
  let w (j : ℕ) := if h : j < N then v ⟨j,h⟩ else 0
  have him (k : ℕ) (hk : k < N) : IndepFun (fun ω (i : Fin k) => Y i ω) (Y k) P := by
    let z : Fin N := ⟨k,hk⟩
    have hd : Disjoint (Finset.Iio z) {z} := by simp
    have hh := hind.indepFun_finset _ _ hd hm
    let head (a : (j : ↥(Finset.Iio z)) → E) (i : Fin k) := a ⟨⟨i, i.isLt.trans hk⟩, by
      apply Finset.mem_Iio.mpr; exact i.isLt⟩
    let last (a : (j : ↥({z} : Finset (Fin N))) → E) := a ⟨z, by simp⟩
    have hh' := hh.comp (show Measurable head by dsimp [head]; fun_prop)
      (show Measurable last by exact measurable_pi_apply _)
    convert hh' using 1
    · funext ω i
      simp [Y, i.isLt.trans hk, head]
    · funext ω
      simp [Y, hk, last, z]
  have hw : ∑ i ∈ Finset.range N, w i = ∑ i, v i := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [w]
  have hy (ω) : ∑ i ∈ Finset.range N, Y i ω = ∑ i, X i ω := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [Y]
  have hh := vector_bernstein (X := Y) (v := w)
    (fun i => by dsimp [Y]; split <;> first | exact hm _ | exact measurable_const)
    (fun i => by dsimp [Y]; split <;> simp_all)
    (fun i => by dsimp [Y]; split <;> simp_all)
    (fun i => by dsimp [Y]; split <;> simp_all) hB
    (fun i => by dsimp [w]; split <;> simp_all) hr hq
    (fun i ω => by dsimp [Y]; split <;> simp_all [hB.le])
    (fun i => by by_cases h : i < N <;> simp [Y, w, h, hv]) N him (by rwa [hw])
  simpa only [hy] using hh

lemma finite_vector_bernstein {ι : Type*} [Fintype ι] {X : ι → Ω → E}
    (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X P) (hi : ∀ i, Integrable (X i) P)
    (h2i : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ 2) P)
    (hz : ∀ i, ∫ ω, X i ω ∂P = 0) {v : ι → ℝ} {B r q : ℝ}
    (hB : 0 < B) (hv0 : ∀ i, 0 ≤ v i) (hr : 0 < r) (hq : 1 ≤ q)
    (hb : ∀ i ω, ‖X i ω‖ ≤ B) (hv : ∀ i, (∫ ω, ‖X i ω‖ ^ 2 ∂P) ≤ v i)
    (hsize : 128 * q * ((∑ i, v i) + B * r) ≤ r ^ 2) :
    P.real {ω | r < ‖∑ i, X i ω‖} ≤ Real.exp (-q) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hh := fin_vector_bernstein (X := fun j => X (e j)) (v := fun j => v (e j))
    (fun j => hm _) (hind.precomp e.injective) (fun j => hi _) (fun j => h2i _)
    (fun j => hz _) hB (fun j => hv0 _) hr hq (fun j => hb _) (fun j => hv _)
    (by simpa only [e.sum_comp v] using hsize)
  simpa only [show ∀ ω, ∑ i, X (e i) ω = ∑ i, X i ω from fun ω => e.sum_comp (fun i => X i ω)] using hh

lemma pooled_bernstein {ι : Type*} [Fintype ι] {Y : ι → Ω → E}
    (hm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P) (hi : ∀ i, Integrable (Y i) P)
    (h2i : ∀ i, Integrable (fun ω => ‖Y i ω‖ ^ 2) P)
    {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q)
    (hb : ∀ i ω, ‖Y i ω‖ ≤ 3 * s / (4096 * q))
    (hbias : (∑ i, ‖∫ ω, Y i ω ∂P‖) ≤ s / 4)
    (hvar : (∑ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂P) ≤ 145 * s ^ 2 / (16777216 * q)) :
    P.real {ω | s < ‖∑ i, Y i ω‖} ≤ Real.exp (-q) := by
  let u (i : ι) := ∫ ω, Y i ω ∂P
  let X (i : ι) (ω : Ω) := Y i ω - u i
  let v (i : ι) := ∫ ω, ‖Y i ω‖ ^ 2 ∂P
  have hq0 : 0 < q := by linarith
  have hv (i) := OracleTemplate.TerminalClipping.centered_second_moment (hi i) (h2i i)
  have hum (i) : ‖u i‖ ≤ 3 * s / (4096 * q) := by
    simpa [u] using norm_integral_le_of_norm_le_const (μ := P) (Filter.Eventually.of_forall (hb i))
  have hX (i ω) : ‖X i ω‖ ≤ 3 * s / (2048 * q) := by
    have he := norm_sub_le (Y i ω) (u i)
    change ‖Y i ω - u i‖ ≤ _
    linarith [hb i ω, hum i, show 3*s/(2048*q) = 2*(3*s/(4096*q)) by ring]
  have hsum := finite_vector_bernstein (X := X) (v := v)
    (fun i => (hm i).sub_const _) (hind.comp (fun i y => y - u i) (fun i => measurable_id.sub_const _))
    (fun i => (hi i).sub (integrable_const _)) (fun i => (hv i).1)
    (fun i => by simp [X, u, integral_sub (hi i) (integrable_const _)])
    (show 0 < 3 * s / (2048 * q) by positivity) (fun i => integral_nonneg fun _ => sq_nonneg _)
    (show 0 < 3 * s / 4 by positivity) hq hX (fun i => (hv i).2)
    (by
      have hh := mul_le_mul_of_nonneg_left hvar (show 0 ≤ 128 * q by positivity)
      change 128 * q * ((∑ i, ∫ ω, ‖Y i ω‖ ^ 2 ∂P) + _) ≤ _
      have he : 128 * q * (145 * s ^ 2 / (16777216 * q) +
          3*s/(2048*q) * (3*s/4)) ≤ (3*s/4)^2 := by
        field_simp
        nlinarith [mul_nonneg hq0.le (sq_nonneg s)]
      linarith)
  apply (measureReal_mono ?_).trans hsum
  intro ω hω
  change 3 * s / 4 < ‖∑ i, (Y i ω - u i)‖
  rw [Finset.sum_sub_distrib]
  have hu : ‖∑ i, u i‖ ≤ s / 4 := (norm_sum_le _ _).trans hbias
  have htri := norm_sub_norm_le (∑ i, Y i ω) (∑ i, u i)
  change s < ‖∑ i, Y i ω‖ at hω
  linarith

end LongTails.Proofs.DistributedContaminationConcentration
