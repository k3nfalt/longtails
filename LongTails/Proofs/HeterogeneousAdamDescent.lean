import LongTails.Proofs.HeterogeneousAdamExecution

open scoped RealInnerProductSpace
open MeasureTheory LongTails.Algorithms.HeterogeneousAdam
open LongTails.Proofs.HeterogeneousAdamExecution
open LongTails.Proofs.AdaptiveHistoryAlgebra
open LongTails.Proofs.AdaptiveHistoryTracking LongTails.Proofs.AdaptiveHistoryFinite
namespace LongTails.Proofs.HeterogeneousAdamDescent

lemma head_coordinate_moments {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {b h : ℕ} {G : Ω → Point b h} {q : Point b h} {σ : ℝ}
    (hGm : Measurable G) (hGi : Integrable G p) (hmean : (∫ ω,G ω ∂p)=q)
    (hni : Integrable (fun ω => ∑ i : Fin h,((G ω-q) (.inr i))^2) p)
    (hnB : (∫ ω,∑ i : Fin h,((G ω-q) (.inr i))^2 ∂p) ≤ σ^2) (j : Fin h) :
    MemLp (fun ω => G ω (.inr j)) 2 p ∧
      (∫ ω,G ω (.inr j) ∂p)=q (.inr j) ∧
      (∫ ω,(G ω (.inr j))^2 ∂p) ≤ (q (.inr j))^2+σ^2 := by
  let N := fun ω => (G ω-q) (.inr j)
  let H := fun ω => G ω (.inr j)
  have hm : Measurable N := by dsimp [N]; fun_prop
  have hH : Measurable H := by dsimp [H]; fun_prop
  have hni' : Integrable (fun ω => N ω^2) p := hni.mono' (hm.pow_const 2).aestronglyMeasurable (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun i : Fin h => ((G ω-q) (.inr i))^2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  have hn2 : MemLp N 2 p := (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr hni'
  have hH2 : MemLp H 2 p := by
    convert hn2.add (memLp_const (q (.inr j))) using 1
    funext ω
    simp [N,H]
  have hHi := hH2.integrable (by norm_num)
  have he : (∫ ω,H ω ∂p) = q (.inr j) := by
    have hh := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin b ⊕ Fin h => ℝ) (.inr j)).integral_comp_comm hGi
    simpa only [PiLp.proj_apply,hmean] using hh
  have hnBound : (∫ ω,N ω^2 ∂p) ≤ σ^2 :=
    (integral_mono hni' hni (fun ω => Finset.single_le_sum (f := fun i : Fin h => ((G ω-q) (.inr i))^2) (fun i _ => sq_nonneg _) (Finset.mem_univ j))).trans hnB
  have heq : (∫ ω,H ω^2 ∂p) = (∫ ω,N ω^2 ∂p)+(q (.inr j))^2 := by
    have hf : (fun ω => H ω^2) = fun ω => (N ω^2+2*q (.inr j)*H ω)-(q (.inr j))^2 := by
      funext ω
      dsimp [N,H]
      ring
    have his : Integrable (fun ω => N ω^2+2*q (.inr j)*H ω) p := hni'.add (hHi.const_mul _)
    rw [hf,integral_sub his (integrable_const ((q (.inr j))^2)),
      integral_add hni' (hHi.const_mul (2*q (.inr j))),integral_const_mul,he,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    ring
  exact ⟨hH2,he,by rw [heq]; linarith⟩


lemma sum_head_sq_le_norm_sq {b h : ℕ} (v : Point b h) :
    (∑ j : Fin h,v (.inr j)^2) ≤ ‖v‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma head_gradient_change_sq {b h : ℕ} {grad : Point b h → Point b h}
    {L : ℝ} (hL : 0 ≤ L) (hg : ∀ x y, ‖grad x-grad y‖ ≤ L*‖x-y‖)
    (x y : Point b h) :
    (∑ j : Fin h,(grad x (.inr j)-grad y (.inr j))^2) ≤ L^2*‖x-y‖^2 := by
  have hs := sum_head_sq_le_norm_sq (grad x-grad y)
  simp only [PiLp.sub_apply] at hs
  have hh := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mpr (hg x y)
  rw [mul_pow] at hh
  exact hs.trans hh


lemma head_normalization_error {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {G d : Ω → ℝ} {q r σ : ℝ}
    (hr : 0 < r) (hG : MemLp G 2 p) (hd : Measurable d)
    (hd0 : ∀ ω, 0 ≤ d ω) (hdr : ∀ ω, d ω ≤ 1/r)
    (hG2 : (∫ ω,G ω^2 ∂p) ≤ q^2+σ^2) :
    Integrable (fun ω => q*G ω*d ω) p ∧
      (∫ ω,q*G ω*d ω ∂p) ≤ q^2/(2*r)+(q^2+σ^2)/2*(∫ ω,d ω ∂p) := by
  have hdm : MemLp d 2 p := MemLp.of_bound hd.aestronglyMeasurable (1/r)
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hd0 ω)] using hdr ω)
  have hGa : MemLp (fun ω => |G ω|) 2 p := by simpa only [Real.norm_eq_abs] using hG.norm
  have hi : Integrable (fun ω => q*G ω*d ω) p := by
    convert (hG.integrable_mul hdm).const_mul q using 1
    funext ω
    simp only [Pi.mul_apply]
    ring
  have hia : Integrable (fun ω => |q| * (|G ω| * d ω)) p := (hGa.integrable_mul hdm).const_mul _
  have hc := LongTails.Proofs.AdaptiveHistoryTracking.integral_mul_le_square_moments
    hGa hdm (fun ω => abs_nonneg _) hd0
  simp only [sq_abs] at hc
  have hdi := hdm.integrable (by norm_num)
  have hd2 : (∫ ω,d ω^2 ∂p) ≤ (∫ ω,d ω ∂p)/r := by
    calc
      _ ≤ ∫ ω,d ω/r ∂p := integral_mono hdm.integrable_sq (hdi.div_const r) (fun ω => by
        have hh := mul_le_mul_of_nonneg_left (hdr ω) (hd0 ω)
        simpa only [pow_two,div_eq_mul_inv,one_mul] using hh)
      _ = _ := integral_div r d
  have h0 : 0 ≤ ∫ ω,d ω ∂p := integral_nonneg hd0
  have hG20 : 0 ≤ ∫ ω,G ω^2 ∂p := integral_nonneg (fun _ => sq_nonneg _)
  have hd20 : 0 ≤ ∫ ω,d ω^2 ∂p := integral_nonneg (fun _ => sq_nonneg _)
  have hcs : (∫ ω,q*G ω*d ω ∂p) ≤
      |q| * (Real.sqrt (q^2+σ^2) * Real.sqrt ((∫ ω,d ω ∂p)/r)) := by
    calc
      _ ≤ ∫ ω, |q| * (|G ω| * d ω) ∂p := integral_mono hi hia (fun ω => by
        have hh := mul_le_mul_of_nonneg_right (le_abs_self (q*G ω)) (hd0 ω)
        simpa only [abs_mul,mul_assoc] using hh)
      _ = |q| * (∫ ω,|G ω| *d ω ∂p) := integral_const_mul _ _
      _ ≤ |q| * (Real.sqrt (∫ ω,G ω^2 ∂p)*Real.sqrt (∫ ω,d ω^2 ∂p)) :=
        mul_le_mul_of_nonneg_left hc (abs_nonneg _)
      _ ≤ _ := by gcongr
  have hy : |q| * (Real.sqrt (q^2+σ^2)*Real.sqrt ((∫ ω,d ω ∂p)/r)) ≤
      q^2/(2*r)+(q^2+σ^2)/2*(∫ ω,d ω ∂p) := by
    have he : |q| * (Real.sqrt (q^2+σ^2)*Real.sqrt ((∫ ω,d ω ∂p)/r)) =
        (|q|/Real.sqrt r)*(Real.sqrt (q^2+σ^2)*Real.sqrt (∫ ω,d ω ∂p)) := by
      rw [Real.sqrt_div h0]
      ring
    rw [he]
    have hq : (|q|/Real.sqrt r)^2 = q^2/r := by
      rw [div_pow,sq_abs,Real.sq_sqrt hr.le]
    have hz : (Real.sqrt (q^2+σ^2)*Real.sqrt (∫ ω,d ω ∂p))^2 =
        (q^2+σ^2)*(∫ ω,d ω ∂p) := by
      rw [mul_pow,Real.sq_sqrt (add_nonneg (sq_nonneg q) (sq_nonneg σ)),Real.sq_sqrt h0]
    have hs := sq_nonneg (|q|/Real.sqrt r - Real.sqrt (q^2+σ^2)*Real.sqrt (∫ ω,d ω ∂p))
    have heq : q^2/(2*r) = (q^2/r)/2 := by ring
    rw [heq]
    nlinarith
  exact ⟨hi,hcs.trans hy⟩


lemma head_expected_potential_step {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {G d : Ω → ℝ} {q qprev r σ η D : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hG : MemLp G 2 p) (hd : Measurable d)
    (hd0 : ∀ ω, 0 ≤ d ω) (hdr : ∀ ω, d ω ≤ 1/r)
    (hmean : (∫ ω,G ω ∂p)=q) (hG2 : (∫ ω,G ω^2 ∂p) ≤ q^2+σ^2)
    (hchange : |q-qprev| ≤ D) :
    Integrable (fun ω => -η*q*G ω*(1/r-d ω)) p ∧
      (∫ ω,-η*q*G ω*(1/r-d ω) ∂p) ≤
        -η/4*(q^2/r)+η/2*(qprev^2/r-(∫ ω,q^2*(1/r-d ω) ∂p))+
          3*η/(2*r)*D^2+η*σ^2/2*(∫ ω,d ω ∂p) := by
  have he := head_normalization_error hr hG hd hd0 hdr hG2
  have hGi := hG.integrable (by norm_num)
  have hdm : MemLp d 2 p := MemLp.of_bound hd.aestronglyMeasurable (1/r)
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hd0 ω)] using hdr ω)
  have hdi := hdm.integrable (by norm_num)
  have hbase : Integrable (fun ω => q/r*G ω) p := hGi.const_mul _
  have hu : Integrable (fun ω => -η*q*G ω*(1/r-d ω)) p := by
    convert (hbase.sub he.1).const_mul (-η) using 1
    funext ω
    simp only [Pi.sub_apply]
    ring
  have hI : (∫ ω,-η*q*G ω*(1/r-d ω) ∂p) =
      -η*(q^2/r-(∫ ω,q*G ω*d ω ∂p)) := by
    have hf : (fun ω => -η*q*G ω*(1/r-d ω)) =
        fun ω => -η*(q/r*G ω-q*G ω*d ω) := by funext ω; ring
    rw [hf,integral_const_mul,integral_sub hbase he.1,integral_const_mul,hmean]
    ring
  have hpot : (∫ ω,q^2*(1/r-d ω) ∂p) = q^2/r-q^2*(∫ ω,d ω ∂p) := by
    rw [integral_const_mul,integral_sub (integrable_const _) hdi,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    ring
  have hc := LongTails.Proofs.AdaptiveHistoryAlgebra.head_potential_change hr hη hchange
  refine ⟨hu,?_⟩
  rw [hI,hpot]
  have hh := mul_le_mul_of_nonneg_left he.2 hη
  have hnorm : η/2*((q^2-qprev^2)/r) = η/2*(q^2/r-qprev^2/r) := by ring
  rw [hnorm] at hc
  simp only [div_eq_mul_inv,mul_inv_rev] at hc hh ⊢
  norm_num at hc hh ⊢
  nlinarith


lemma head_adagrad_expected_potential_step {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {G : Ω → ℝ} {q qprev r σ η D : ℝ}
    (hr : 0 < r) (hη : 0 ≤ η) (hGm : Measurable G) (hG : MemLp G 2 p)
    (hmean : (∫ ω,G ω ∂p)=q) (hG2 : (∫ ω,G ω^2 ∂p) ≤ q^2+σ^2)
    (hchange : |q-qprev| ≤ D) :
    Integrable (fun ω => -η*q*G ω/Real.sqrt (r^2+G ω^2)) p ∧
      (∫ ω,-η*q*G ω/Real.sqrt (r^2+G ω^2) ∂p) ≤
        -η/4*(q^2/r)+η/2*(qprev^2/r-(∫ ω,q^2/Real.sqrt (r^2+G ω^2) ∂p))+
          3*η/(2*r)*D^2+η*σ^2/2*(∫ ω,1/r-1/Real.sqrt (r^2+G ω^2) ∂p) := by
  let d := fun ω => 1/r-1/Real.sqrt (r^2+G ω^2)
  have hs (ω) : r ≤ Real.sqrt (r^2+G ω^2) :=
    (Real.le_sqrt hr.le (add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr (by nlinarith [sq_nonneg (G ω)])
  have hd : Measurable d := by dsimp [d]; fun_prop
  have hd0 (ω) : 0 ≤ d ω := by
    dsimp [d]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hr (hs ω))
  have hdr (ω) : d ω ≤ 1/r := by
    dsimp [d]
    have hp : 0 ≤ 1/Real.sqrt (r^2+G ω^2) := by positivity
    linarith
  have hh := head_expected_potential_step hr hη hG hd hd0 hdr hmean hG2 hchange
  simpa only [d,sub_sub_cancel,div_eq_mul_inv,one_mul] using hh


lemma integral_log_le_log_mean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hXi : Integrable X P) (hX1 : ∀ ω, 1 ≤ X ω) :
    Integrable (fun ω => Real.log (X ω)) P ∧
      (∫ ω,Real.log (X ω) ∂P) ≤ Real.log (∫ ω,X ω ∂P) := by
  have hX0 (ω) : 0 < X ω := lt_of_lt_of_le zero_lt_one (hX1 ω)
  have hl0 (ω) : 0 ≤ Real.log (X ω) := Real.log_nonneg (hX1 ω)
  have hlm : Measurable (fun ω => Real.log (X ω)) := by fun_prop
  have hli : Integrable (fun ω => Real.log (X ω)) P := hXi.mono' hlm.aestronglyMeasurable (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hl0 ω)]
    exact (Real.log_le_sub_one_of_pos (hX0 ω)).trans (by linarith))
  have hI : 1 ≤ ∫ ω,X ω ∂P := by
    simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one] using
      integral_mono (integrable_const (1 : ℝ)) hXi hX1
  have hIp : 0 < ∫ ω,X ω ∂P := lt_of_lt_of_le zero_lt_one hI
  have hb (ω) : Real.log (X ω) ≤ Real.log (∫ ω,X ω ∂P)+X ω/(∫ ω,X ω ∂P)-1 := by
    have hh := Real.log_le_sub_one_of_pos (div_pos (hX0 ω) hIp)
    rw [Real.log_div (hX0 ω).ne' hIp.ne'] at hh
    linarith
  refine ⟨hli,?_⟩
  have his : Integrable (fun ω => Real.log (∫ ω,X ω ∂P)+X ω/(∫ ω,X ω ∂P)) P :=
    (integrable_const _).add (hXi.div_const _)
  have hh := integral_mono hli (his.sub (integrable_const 1)) hb
  simp only [Pi.sub_apply] at hh
  rw [integral_sub his (integrable_const 1),
    integral_add (integrable_const (Real.log (∫ ω,X ω ∂P))) (hXi.div_const (∫ ω,X ω ∂P)),integral_div] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul,div_self hIp.ne',add_sub_cancel_right] using hh



lemma prefix_head_coordinate_second_moment {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω] {P : Measure X} {p : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure p] {b h : ℕ}
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {x : X → Point b h} {B σ : ℝ} (hB0 : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle)) (hx : Measurable x)
    (hi : ∀ z, Integrable (oracle z) p) (hmean : ∀ z, (∫ ω,oracle z ω ∂p)=grad z)
    (hni : ∀ z, Integrable (fun ω => ∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2) p)
    (hσ : ∀ z, (∫ ω,∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2 ∂p) ≤ σ^2)
    (j : Fin h) (hB : ∀ a, |grad (x a) (.inr j)| ≤ B) :
    MemLp (fun w : X × Ω => oracle (x w.1) w.2 (.inr j)) 2 (P.prod p) ∧
      (∫ w : X × Ω,(oracle (x w.1) w.2 (.inr j))^2 ∂P.prod p) ≤ B^2+σ^2 := by
  have hm : Measurable (fun w : X × Ω => oracle (x w.1) w.2 (.inr j)) := by
    have hc : Measurable (fun v : Point b h => v (.inr j)) := by fun_prop
    exact hc.comp (ho.comp ((hx.comp measurable_fst).prodMk measurable_snd))
  have hs (a : X) := head_coordinate_moments (ho.comp measurable_prodMk_left)
    (hi (x a)) (hmean (x a)) (hni (x a)) (hσ (x a)) j
  have hb (a) : (grad (x a) (.inr j))^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB0).mpr (hB a)
  have hh := LongTails.Proofs.AdaptiveHistoryTracking.memLp_two_prod_of_uniform_square_moment
    (p := P) (P := p) (κ := Real.sqrt (B^2+σ^2)) hm (fun a => (hs a).1)
    (fun a => by
      rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact (hs a).2.2.trans (add_le_add_left (hb a) _))
  simpa only [Real.sq_sqrt (add_nonneg (sq_nonneg B) (sq_nonneg σ))] using hh

lemma iid_head_reply_second_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {B σ : ℝ} (hB0 : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle))
    (hi : ∀ z, Integrable (oracle z) p) (hmean : ∀ z, (∫ ω,oracle z ω ∂p)=grad z)
    (hni : ∀ z, Integrable (fun ω => ∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2) p)
    (hσ : ∀ z, (∫ ω,∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ) (j : Fin h)
    (hB : ∀ z : ℕ → Ω, |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) (.inr j)| ≤ B) :
    MemLp (fun ω => oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inr j)) 2 P ∧
      (∫ ω,(oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inr j))^2 ∂P) ≤ B^2+σ^2 := by
  let x := fun z : Fin n → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) n
  have hx : Measurable x := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a) n
  have hh := prefix_head_coordinate_second_moment (P := Measure.pi (fun _ : Fin n => p)) hB0
    ho hx hi hmean hni hσ j (fun z => hB (paddedSamples a z))
  let F := fun w : (Fin n → Ω) × Ω => oracle (x w.1) w.2 (.inr j)
  have hp := iid_prefix_sample_law hs n
  have he (ω : Ξ) : F ((fun i : Fin n => ξ i ω),ξ n ω) =
      oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω) (.inr j) := by
    dsimp [F,x]
    rw [← trajectory_prefix_representation cfg x₀ oracle a (fun k => ξ k ω) n]
  have hFm : MemLp F 2 ((Measure.pi fun _ : Fin n => p).prod p) := hh.1
  refine ⟨?_,?_⟩
  · have hc := hFm.comp_measurePreserving hp
    simpa only [Function.comp_def,he] using hc
  · have hm := integral_map hp.measurable.aemeasurable
      (f := fun w => F w^2) (hp.map_eq.symm ▸ hFm.integrable_sq.aestronglyMeasurable)
    simp only [hp.map_eq,he] at hm
    exact hm.symm.le.trans hh.2


lemma run_head_accumulator_sum {b h : ℕ} (cfg : Config) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (g : ℕ → Point b h → Point b h) (n : ℕ) (j : Fin h) :
    (run cfg x₀ seed g n).accumulator (.inr j) = cfg.r₀^2+
      ∑ t ∈ Finset.range n,(g t (trajectory cfg x₀ g t) (.inr j))^2 := by
  induction n with
  | zero => simp [run,initial]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    change (run cfg x₀ seed g n).accumulator (.inr j)+
      (g n (run cfg x₀ seed g n).point (.inr j))^2 = _
    rw [ih,run_point]
    ring

lemma iid_head_accumulator_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {B σ : ℝ} (hB0 : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle))
    (hi : ∀ z, Integrable (oracle z) p) (hmean : ∀ z, (∫ ω,oracle z ω ∂p)=grad z)
    (hni : ∀ z, Integrable (fun ω => ∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2) p)
    (hσ : ∀ z, (∫ ω,∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ) (j : Fin h)
    (hB : ∀ t<n, ∀ z : ℕ → Ω,
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B) :
    Integrable (fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inr j)) P ∧
      (∫ ω,(run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).accumulator (.inr j) ∂P) ≤
        cfg.r₀^2+n*(B^2+σ^2) := by
  let G := fun t ω => oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t) (ξ t ω) (.inr j)
  have hm (t) (ht : t∈Finset.range n) := iid_head_reply_second_moment cfg x₀ a hB0 ho hi hmean hni hσ hs t j
    (hB t (Finset.mem_range.mp ht))
  have hsi : Integrable (fun ω => ∑ t ∈ Finset.range n,(G t ω)^2) P :=
    integrable_finsetSum _ (fun t ht => (hm t ht).1.integrable_sq)
  simp_rw [run_head_accumulator_sum]
  refine ⟨(integrable_const _).add hsi,?_⟩
  rw [integral_add (integrable_const _) hsi,integral_const,
    integral_finsetSum _ (fun t ht => (hm t ht).1.integrable_sq)]
  simp only [probReal_univ,smul_eq_mul,one_mul]
  apply add_le_add_right
  have hh := Finset.sum_le_sum (s := Finset.range n) (fun t ht => (hm t ht).2)
  simpa [mul_add] using hh



lemma expected_head_movement_log {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hr : 0 < cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {ξ : ℕ → Ξ → Ω}
    (ho : Measurable (Function.uncurry oracle)) (hξ : ∀ k,Measurable (ξ k))
    {η V : ℝ} (hη : ∀ n,cfg.headStep n=η) (T : ℕ) (j : Fin h)
    (hvi : Integrable (fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) T).accumulator (.inr j)) P)
    (hV : (∫ ω,(run cfg x₀ seed (fun k x => oracle x (ξ k ω)) T).accumulator (.inr j) ∂P) ≤ V) :
    Integrable (fun ω => ∑ n ∈ Finset.range T,
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (n+1)).point (.inr j)-
        (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).point (.inr j))^2) P ∧
      (∫ ω,∑ n ∈ Finset.range T,
        ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (n+1)).point (.inr j)-
          (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).point (.inr j))^2 ∂P) ≤
        η^2*Real.log (V/cfg.r₀^2) := by
  let v := fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) T).accumulator (.inr j)
  let Z := fun ω => v ω/cfg.r₀^2
  let Y := fun ω => ∑ n ∈ Finset.range T,
    ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (n+1)).point (.inr j)-
      (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) n).point (.inr j))^2
  have hr2 : 0 < cfg.r₀^2 := sq_pos_of_pos hr
  have hv (ω) : cfg.r₀^2 ≤ v ω := run_head_accumulator_lower cfg x₀ seed (fun k x => oracle x (ξ k ω)) T j
  have hc : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
  have hvm : Measurable v := hc.comp (run_core_measurable cfg x₀ seed ho hξ T).2.2
  have hZm : Measurable Z := hvm.div_const _
  have hZi : Integrable Z P := hvi.div_const _
  have hZ1 (ω) : 1 ≤ Z ω := by
    dsimp [Z]
    apply (le_div_iff₀ hr2).mpr
    simpa only [one_mul] using hv ω
  have hlog := integral_log_le_log_mean hZm hZi hZ1
  have hYm : Measurable Y := by
    apply Finset.measurable_sum
    intro n _
    exact ((hc.comp (run_core_measurable cfg x₀ seed ho hξ (n+1)).1).sub
      (hc.comp (run_core_measurable cfg x₀ seed ho hξ n).1)).pow_const 2
  have hY0 (ω) : 0 ≤ Y ω := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbound (ω) : Y ω ≤ η^2*Real.log (Z ω) := by
    have hh := run_head_movement_log cfg hr x₀ seed (fun k x => oracle x (ξ k ω)) hη T j
    have he : Real.log (Z ω) = Real.log (v ω)-Real.log (cfg.r₀^2) :=
      Real.log_div (hr2.trans_le (hv ω)).ne' hr2.ne'
    rw [he]
    exact hh
  have hYi : Integrable Y P := (hlog.1.const_mul (η^2)).mono' hYm.aestronglyMeasurable (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hY0 ω)]
    exact hbound ω)
  have hIZ : (∫ ω,Z ω ∂P) ≤ V/cfg.r₀^2 := by
    rw [show Z = fun ω => v ω/cfg.r₀^2 from rfl,integral_div]
    exact div_le_div_of_nonneg_right hV hr2.le
  have hIZ1 : 1 ≤ ∫ ω,Z ω ∂P := by
    simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one] using
      integral_mono (integrable_const (1 : ℝ)) hZi hZ1
  refine ⟨hYi,?_⟩
  calc
    _ ≤ ∫ ω,η^2*Real.log (Z ω) ∂P := integral_mono hYi (hlog.1.const_mul _) hbound
    _ = η^2*(∫ ω,Real.log (Z ω) ∂P) := integral_const_mul _ _
    _ ≤ η^2*Real.log (∫ ω,Z ω ∂P) := mul_le_mul_of_nonneg_left hlog.2 (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log (lt_of_lt_of_le zero_lt_one hIZ1) hIZ) (sq_nonneg _)



lemma head_accumulator_energy {ι : Type*} [Fintype ι]
    (G q r : ι → ℝ) {R r₀ : ℝ} (hR : 0 ≤ R) (hr₀ : 0 ≤ r₀)
    (hr : ∀ i,0 < r i) (hrR : ∀ i,r i ≤ R)
    (he : R^2=r₀^2+∑ i,(G i)^2) :
    R ≤ 2*r₀+(∑ i,(q i)^2/r i)+2*Real.sqrt (∑ i,(G i-q i)^2) := by
  let x : EuclideanSpace ℝ ι := WithLp.toLp 2 G
  let y : EuclideanSpace ℝ ι := WithLp.toLp 2 q
  have hx : ‖x‖^2=∑ i,(G i)^2 := by
    simp [EuclideanSpace.norm_sq_eq,x,Real.norm_eq_abs]
  have hy : ‖y‖^2=∑ i,(q i)^2 := by
    simp [EuclideanSpace.norm_sq_eq,y,Real.norm_eq_abs]
  have hxy : ‖x-y‖=Real.sqrt (∑ i,(G i-q i)^2) := by
    simp [EuclideanSpace.norm_eq,x,y,Real.norm_eq_abs]
  have hq : (∑ i,(q i)^2) ≤ R*(∑ i,(q i)^2/r i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hh := mul_le_mul_of_nonneg_right (hrR i) (div_nonneg (sq_nonneg (q i)) (hr i).le)
    have hid : r i*((q i)^2/r i)=(q i)^2 := by field_simp [ne_of_gt (hr i)]
    rwa [hid] at hh
  have hA : 0 ≤ ∑ i,(q i)^2/r i := Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hr i).le)
  have hyB : ‖y‖ ≤ Real.sqrt (R*(∑ i,(q i)^2/r i)) := by
    rw [← Real.sqrt_sq (norm_nonneg y)]
    exact Real.sqrt_le_sqrt (hy ▸ hq)
  have hbase : R ≤ r₀+‖x‖ := by
    nlinarith [norm_nonneg x,mul_nonneg hr₀ (norm_nonneg x)]
  apply accumulator_of_energy hR hA
  have ht : ‖x‖ ≤ ‖y‖+‖x-y‖ := by simpa [norm_sub_rev,add_comm] using norm_le_insert y x
  rw [hxy] at ht
  linarith

lemma integral_sqrt_le_sqrt_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {v : Ω → ℝ}
    (hv : Integrable v P) (hv0 : ∀ ω,0 ≤ v ω) :
    Integrable (fun ω => Real.sqrt (v ω)) P ∧
      (∫ ω,Real.sqrt (v ω) ∂P) ≤ Real.sqrt (∫ ω,v ω ∂P) := by
  have hm : AEStronglyMeasurable (fun ω => Real.sqrt (v ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hv.aestronglyMeasurable
  have hsq : (fun ω => (Real.sqrt (v ω))^2)=v := by
    funext ω
    exact Real.sq_sqrt (hv0 ω)
  have h2 : MemLp (fun ω => Real.sqrt (v ω)) 2 P :=
    (memLp_two_iff_integrable_sq hm).mpr (by simpa only [hsq] using hv)
  refine ⟨h2.integrable (by norm_num),?_⟩
  have hc := LongTails.Proofs.AdaptiveHistoryTracking.integral_mul_le_square_moments
    (memLp_const (1 : ℝ)) h2 (fun _ => by norm_num) (fun ω => Real.sqrt_nonneg (v ω))
  simpa only [one_mul,one_pow,integral_const,probReal_univ,smul_eq_mul,
    mul_one,Real.sqrt_one,hsq] using hc

lemma integral_sum_roots {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : ℕ} {v : Fin h → Ω → ℝ} {V : ℝ}
    (hv : ∀ j,Integrable (v j) P) (hv0 : ∀ j ω,0 ≤ v j ω)
    (hV : (∑ j,∫ ω,v j ω ∂P) ≤ V) :
    Integrable (fun ω => ∑ j,Real.sqrt (v j ω)) P ∧
      (∫ ω,∑ j,Real.sqrt (v j ω) ∂P) ≤ Real.sqrt h*Real.sqrt V := by
  have hh := fun j => integral_sqrt_le_sqrt_integral (hv j) (hv0 j)
  refine ⟨integrable_finsetSum _ (fun j _ => (hh j).1),?_⟩
  rw [integral_finsetSum _ (fun j _ => (hh j).1)]
  have hsum := Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
    (f := fun _ : Fin h => (1 : ℝ)) (g := fun j => ∫ ω,v j ω ∂P)
    (fun _ => by norm_num) (fun j => integral_nonneg (hv0 j))
  simp only [Real.sqrt_one,one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hsum
  exact (Finset.sum_le_sum (fun j _ => (hh j).2)).trans
    (hsum.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hV) (Real.sqrt_nonneg _)))

open LongTails.Algorithms.HeterogeneousAdam
open LongTails.Proofs.HeterogeneousAdamExecution

lemma run_head_accumulator_energy {b h : ℕ} (cfg : Config) (hr : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (g : ℕ → Point b h → Point b h) (q : ℕ → ℝ) (T : ℕ) (j : Fin h) :
    Real.sqrt ((run cfg x₀ seed g T).accumulator (.inr j)) ≤ 2*cfg.r₀+
      (∑ t : Fin T,(q t)^2/Real.sqrt ((run cfg x₀ seed g t).accumulator (.inr j)))+
      2*Real.sqrt (∑ t : Fin T,(g t (trajectory cfg x₀ g t) (.inr j)-q t)^2) := by
  let v := fun t => (run cfg x₀ seed g t).accumulator (.inr j)
  have hv (t) : 0 < v t := (sq_pos_of_pos hr).trans_le (run_head_accumulator_lower cfg x₀ seed g t j)
  have hmono : Monotone v := monotone_nat_of_le_succ (fun t => by
    change v t ≤ v t+(g t (run cfg x₀ seed g t).point (.inr j))^2
    exact le_add_of_nonneg_right (sq_nonneg _))
  have he : (Real.sqrt (v T))^2=cfg.r₀^2+
      ∑ t : Fin T,(g t (trajectory cfg x₀ g t) (.inr j))^2 := by
    rw [Real.sq_sqrt (hv T).le]
    rw [show v T = cfg.r₀^2+∑ t ∈ Finset.range T,(g t (trajectory cfg x₀ g t) (.inr j))^2 from run_head_accumulator_sum cfg x₀ seed g T j]
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun t => (g t (trajectory cfg x₀ g t) (.inr j))^2) T).symm
  exact head_accumulator_energy (fun t : Fin T => g t (trajectory cfg x₀ g t) (.inr j))
    (fun t : Fin T => q t) (fun t : Fin T => Real.sqrt (v t))
    (Real.sqrt_nonneg _) hr.le (fun t => Real.sqrt_pos.mpr (hv t))
    (fun t => Real.sqrt_le_sqrt (hmono t.isLt.le)) he



lemma prefix_head_noise_moment {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {b h : ℕ} {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {x : X → Point b h} {σ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hx : Measurable x)
    (hi : ∀ z,Integrable (fun ω => ∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2) p)
    (hσ : ∀ z,(∫ ω,∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2 ∂p) ≤ σ^2) :
    Integrable (fun w : X × Ω => ∑ j : Fin h,((oracle (x w.1) w.2-grad (x w.1)) (.inr j))^2) (P.prod p) ∧
      (∫ w : X × Ω,∑ j : Fin h,((oracle (x w.1) w.2-grad (x w.1)) (.inr j))^2 ∂P.prod p) ≤ σ^2 := by
  let F := fun w : X × Ω => ∑ j : Fin h,((oracle (x w.1) w.2-grad (x w.1)) (.inr j))^2
  have hm : Measurable F := by
    dsimp [F]
    apply Finset.measurable_sum
    intro j _
    have hc : Measurable (fun v : Point b h => v (.inr j)) := by fun_prop
    exact (hc.comp ((ho.comp ((hx.comp measurable_fst).prodMk measurable_snd)).sub
      (hg.comp (hx.comp measurable_fst)))).pow_const 2
  have h0 (w) : 0 ≤ F w := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hh := LongTails.Proofs.AdaptiveHistoryTracking.prefix_absolute_moment (P := P) hm
    (fun a => hi (x a)) (fun a => by simpa only [abs_of_nonneg (h0 _)] using hσ (x a))
  simpa only [abs_of_nonneg (h0 _)] using hh

lemma iid_head_noise_moment {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {σ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ z,Integrable (fun ω => ∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2) p)
    (hσ : ∀ z,(∫ ω,∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (n : ℕ) :
    let x := fun ω => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n
    Integrable (fun ω => ∑ j : Fin h,((oracle (x ω) (ξ n ω)-grad (x ω)) (.inr j))^2) P ∧
      (∫ ω,∑ j : Fin h,((oracle (x ω) (ξ n ω)-grad (x ω)) (.inr j))^2 ∂P) ≤ σ^2 := by
  dsimp only
  let x := fun z : Fin n → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) n
  have hx : Measurable x := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a) n
  have hh := prefix_head_noise_moment (P := Measure.pi (fun _ : Fin n => p)) ho hg hx hi hσ
  let F := fun w : (Fin n → Ω) × Ω => ∑ j : Fin h,((oracle (x w.1) w.2-grad (x w.1)) (.inr j))^2
  have hp := iid_prefix_sample_law hs n
  have he (ω : Ξ) : F ((fun i : Fin n => ξ i ω),ξ n ω) =
      ∑ j : Fin h,((oracle (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n) (ξ n ω)-
        grad (trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) n)) (.inr j))^2 := by
    dsimp [F,x]
    rw [← trajectory_prefix_representation cfg x₀ oracle a (fun k => ξ k ω) n]
  have hFi : Integrable F ((Measure.pi fun _ : Fin n => p).prod p) := hh.1
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,he] using hp.integrable_comp_of_integrable hFi
  · have hm := integral_map hp.measurable.aemeasurable (f := F) (hp.map_eq.symm ▸ hFi.aestronglyMeasurable)
    simp only [hp.map_eq,he] at hm
    exact hm.symm.le.trans hh.2



lemma integral_temporal_noise_roots {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h T : ℕ}
    {N : Fin T → Fin h → Ω → ℝ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hm : ∀ t j,Measurable (N t j))
    (hi : ∀ t,Integrable (fun ω => ∑ j,(N t j ω)^2) P)
    (hσ : ∀ t,(∫ ω,∑ j,(N t j ω)^2 ∂P) ≤ σ^2) :
    Integrable (fun ω => ∑ j : Fin h,Real.sqrt (∑ t : Fin T,(N t j ω)^2)) P ∧
      (∫ ω,∑ j : Fin h,Real.sqrt (∑ t : Fin T,(N t j ω)^2) ∂P) ≤
        Real.sqrt h*σ*Real.sqrt T := by
  have hni (t : Fin T) (j : Fin h) : Integrable (fun ω => (N t j ω)^2) P :=
    (hi t).mono' (hm t j |>.pow_const 2 |>.aestronglyMeasurable) (by
      filter_upwards [] with ω
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact Finset.single_le_sum (fun l _ => sq_nonneg (N t l ω)) (Finset.mem_univ j))
  have hv (j : Fin h) : Integrable (fun ω => ∑ t : Fin T,(N t j ω)^2) P :=
    integrable_finsetSum _ (fun t _ => hni t j)
  have hV : (∑ j : Fin h,∫ ω,∑ t : Fin T,(N t j ω)^2 ∂P) ≤ T*σ^2 := by
    simp_rw [integral_finsetSum _ (fun t _ => hni t _)]
    rw [Finset.sum_comm]
    have he (t : Fin T) : (∑ j : Fin h,∫ ω,(N t j ω)^2 ∂P) =
        ∫ ω,∑ j : Fin h,(N t j ω)^2 ∂P := (integral_finsetSum _ (fun j _ => hni t j)).symm
    simp_rw [he]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun t _ => hσ t)
  have hh := integral_sum_roots hv (fun j ω => Finset.sum_nonneg (fun t _ => sq_nonneg _)) hV
  refine ⟨hh.1,?_⟩
  convert hh.2 using 1
  rw [Real.sqrt_mul (Nat.cast_nonneg T),Real.sqrt_sq hσ0]
  ring



lemma reverse_window_tracking {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω}
    [IsProbabilityMeasure p] {b h m n : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hcfgδ : 0 < cfg.δ)
    (x₀ : Point b h) (a : Ω) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {K : Ω → ℝ}
    {L μ B δ : ℝ} (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-grad x) (.inl j)-(oracle y ω-grad y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hμ : (∫ ω,K ω ∂p) ≤ μ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hδ : 0 < δ) (s : ℕ) (hs : s ≤ m) (j : Fin b)
    (hsym : ∀ x,(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hGB : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) s) (.inl j)| ≤ B)
    (hVi : Integrable (fun pre : Fin m → Ω => Real.sqrt ((999/1000 : ℝ)^(n+1)*
      (run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m).accumulator (.inl j)))
      (Measure.pi (fun _ : Fin m => p))) :
    let P₀ := Measure.pi (fun _ : Fin m => p)
    let Q := P₀.prod (Measure.pi (fun _ : Fin (n+1) => p))
    let x := fun pre : Fin m → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a pre k)) s
    let old := fun pre : Fin m → Ω => run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m
    let Z := fun i : Fin (n+1) => fun w : (Fin m → Ω) × (Fin (n+1) → Ω) =>
      oracle (trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 w.2 k)) (m+i.rev)) (w.2 i) (.inl j)
    let W := fun i : Fin (n+1) => fun w : (Fin m → Ω) × (Fin (n+1) → Ω) => oracle (x w.1) (w.2 i) (.inl j)
    let aa := fun i : Fin (n+1) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
    let bb := fun i : Fin (n+1) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
    let D := fun i : Fin (n+1) => fun w : (Fin m → Ω) × (Fin n → Ω) =>
      ‖trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) (m+i.rev)-
        trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) s‖
    let U := fun w : (Fin m → Ω) × (Fin (n+1) → Ω) => |grad (x w.1) (.inl j)| *
      |((9/10 : ℝ)^(n+1)*(old w.1).momentum (.inl j)+∑ i,aa i*Z i w)/
        (δ+Real.sqrt ((999/1000 : ℝ)^(n+1)*(old w.1).accumulator (.inl j)+∑ i,bb i*(Z i w)^2))-
        (∑ i,aa i*W i w)/(δ+Real.sqrt (∑ i,bb i*(W i w)^2))|
    Integrable U Q ∧ (∫ w,U w ∂Q) ≤
      16*((L+μ)*127*(∑ i,Real.sqrt (bb i)*Real.sqrt (∫ z,D i z^2 ∂P₀.prod (Measure.pi (fun _ : Fin n => p))))+
        B*((n+1)*(1/2 : ℝ)^n))+
      16*(127*(∫ pre,Real.sqrt ((999/1000 : ℝ)^(n+1)*(old pre).accumulator (.inl j)) ∂P₀)+B*(1/2 : ℝ)^(n+1)) := by
  dsimp only
  let x := fun pre : Fin m → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a pre k)) s
  let old := fun pre : Fin m → Ω => run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m
  let G := fun pre => grad (x pre) (.inl j)
  let noise := fun pre ω => (oracle (x pre) ω-grad (x pre)) (.inl j)
  let Z := fun i : Fin (n+1) => fun w : (Fin m → Ω) × (Fin (n+1) → Ω) =>
    oracle (trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 w.2 k)) (m+i.rev)) (w.2 i) (.inl j)
  let D := fun i : Fin (n+1) => fun w : (Fin m → Ω) × (Fin n → Ω) =>
    ‖trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) (m+i.rev)-
      trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) s‖
  have hc : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
  have hx : Measurable x := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a) s
  have hG : Measurable G := hc.comp (hg.comp hx)
  have hold := run_core_measurable cfg x₀ seed ho (paddedSamples_measurable (n := m) a) m
  have hM : Measurable (fun pre => (old pre).momentum (.inl j)) := hc.comp hold.2.1
  have hV : Measurable (fun pre => (old pre).accumulator (.inl j)) := hc.comp hold.2.2
  have hInv (pre : Fin m → Ω) := run_body_moment_bound cfg hα hβ x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m j
  have hn : Measurable (Function.uncurry noise) :=
    (joint_body_noise_measurable ho hg j).comp ((hx.comp measurable_fst).prodMk measurable_snd)
  have hZ (i) : Measurable (Z i) := hc.comp (ho.comp
    ((trajectory_measurable cfg x₀ ho (prefixReverseSamples_measurable a) (m+i.rev)).prodMk
      ((measurable_pi_apply i).comp measurable_snd)))
  have hd (i) : MemLp (D i) 2 ((Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin n => p))) :=
    reverse_complementary_displacement_memLp cfg hα hβ hcfgδ x₀ ho i a (m+i.rev) s _
  have he := reverse_window_reply_difference (p := p) (n := n) cfg x₀ a hgrad hnoise s hs j
  have hw (pre : Fin m → Ω) (ω : Ω) : G pre+noise pre ω=oracle (x pre) ω (.inl j) := by
    dsimp [G,noise]
    ring
  have hh := default_prefix_full_history_tracking hG hM hV (fun pre => (hInv pre).1)
    (fun pre => (hInv pre).2) hVi hn (fun pre => hsym (x pre)) hZ hL hB hδ
    (fun pre => hGB (paddedSamples a pre)) hK hK0 hμ hd (fun _ _ => norm_nonneg _) (by
      simpa only [hw] using he)
  simpa only [hw] using hh


noncomputable def bodyWindowError {Ω : Type*} {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (grad : Point b h → Point b h)
    (δ : ℝ) (s m n : ℕ) (j : Fin b) (z : ℕ → Ω) : ℝ :=
  let g := fun k x => oracle x (z k)
  let x := trajectory cfg x₀ g s
  let v := run cfg x₀ seed g (m+n)
  let W := fun i : Fin n => oracle x (z (m+i.rev)) (.inl j)
  |grad x (.inl j)| * |v.momentum (.inl j)/(δ+Real.sqrt (v.accumulator (.inl j)))-
    (∑ i : Fin n,(1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*W i)/
      (δ+Real.sqrt (∑ i : Fin n,(1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(W i)^2))|

lemma bodyWindowError_reconstruct {Ω : Type*} {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (grad : Point b h → Point b h)
    (δ : ℝ) (s m n : ℕ) (hs : s ≤ m+n) (j : Fin b) (a : Ω) (z : ℕ → Ω) :
    bodyWindowError cfg x₀ seed oracle grad δ s m n j
      (prefixReverseSamples a (fun i : Fin m => z i) (fun i : Fin n => z (m+i.rev))) =
      bodyWindowError cfg x₀ seed oracle grad δ s m n j z := by
  dsimp only [bodyWindowError]
  rw [← trajectory_prefix_reverse_representation cfg x₀ oracle a z m n s hs,
    ← run_prefix_reverse_representation cfg x₀ seed oracle a z m n (m+n) le_rfl]
  have he (i : Fin n) := prefixReverseSamples_reconstruct a z m n (m+i.rev) (by have hi := i.rev.isLt; omega)
  simp only [he]

lemma bodyWindowError_prefix {Ω : Type*} {b h m n : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (grad : Point b h → Point b h)
    (δ : ℝ) (s : ℕ) (hs : s ≤ m) (j : Fin b) (a : Ω)
    (pre : Fin m → Ω) (z : Fin n → Ω) :
    let x := trajectory cfg x₀ (fun k x => oracle x (paddedSamples a pre k)) s
    let old := run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m
    let Z := fun i : Fin n => oracle (trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a pre z k)) (m+i.rev)) (z i) (.inl j)
    let W := fun i : Fin n => oracle x (z i) (.inl j)
    let aa := fun i : Fin n => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)
    let bb := fun i : Fin n => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)
    bodyWindowError cfg x₀ seed oracle grad δ s m n j (prefixReverseSamples a pre z) =
      |grad x (.inl j)| * |((9/10 : ℝ)^n*old.momentum (.inl j)+∑ i,aa i*Z i)/
        (δ+Real.sqrt ((999/1000 : ℝ)^n*old.accumulator (.inl j)+∑ i,bb i*(Z i)^2))-
        (∑ i,aa i*W i)/(δ+Real.sqrt (∑ i,bb i*(W i)^2))| := by
  dsimp only
  have hh := run_reverse_window_history cfg hα hβ x₀ seed oracle a pre z j
  dsimp only at hh
  have he (i : Fin n) : prefixReverseSamples a pre z (m+i.rev)=z i := by
    have hnm : ¬m+(i.rev : ℕ)<m := by omega
    simp only [prefixReverseSamples,dite_eq_right hnm,Nat.add_sub_cancel_left,paddedSamples,
      dite_eq_left i.rev.isLt]
    change z i.rev.rev=z i
    rw [Fin.rev_rev]
  dsimp only [bodyWindowError]
  rw [hh.1,hh.2,trajectory_prefixReverse_before cfg x₀ oracle a pre z s hs]
  simp only [he]

lemma iid_bodyWindowError_integral {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    (oracle : Point b h → Ω → Point b h) (grad : Point b h → Point b h)
    (δ : ℝ) (s m n : ℕ) (hs : s ≤ m+n) (j : Fin b) (a : Ω)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hi : Integrable (fun w : (Fin m → Ω) × (Fin n → Ω) =>
      bodyWindowError cfg x₀ seed oracle grad δ s m n j (prefixReverseSamples a w.1 w.2))
      ((Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin n => p)))) :
    Integrable (fun ω => bodyWindowError cfg x₀ seed oracle grad δ s m n j (fun k => ξ k ω)) P ∧
    (∫ w : (Fin m → Ω) × (Fin n → Ω),
      bodyWindowError cfg x₀ seed oracle grad δ s m n j (prefixReverseSamples a w.1 w.2)
      ∂(Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin n => p))) =
      ∫ ω,bodyWindowError cfg x₀ seed oracle grad δ s m n j (fun k => ξ k ω) ∂P := by
  have hp := iid_prefix_reverse_window_law hsamples m n
  have he (ω) := bodyWindowError_reconstruct cfg x₀ seed oracle grad δ s m n hs j a (fun k => ξ k ω)
  constructor
  · simpa only [Function.comp_def,he] using hp.integrable_comp_of_integrable hi
  · have hm := integral_map hp.measurable.aemeasurable
      (f := fun w : (Fin m → Ω) × (Fin n → Ω) =>
        bodyWindowError cfg x₀ seed oracle grad δ s m n j (prefixReverseSamples a w.1 w.2))
      (hp.map_eq.symm ▸ hi.aestronglyMeasurable)
    simpa only [hp.map_eq,he] using hm

lemma iid_body_window_tracking {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h m n : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hcfgδ : 0 < cfg.δ)
    (x₀ : Point b h) (a : Ω) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {K : Ω → ℝ}
    {L μ B δ : ℝ} (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-grad x) (.inl j)-(oracle y ω-grad y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hμ : (∫ ω,K ω ∂p) ≤ μ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hδ : 0 < δ) (s : ℕ) (hs : s ≤ m) (j : Fin b)
    (hsym : ∀ x,(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hGB : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) s) (.inl j)| ≤ B)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hVi : Integrable (fun ω => Real.sqrt ((999/1000 : ℝ)^(n+1)*
      (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) m).accumulator (.inl j))) P) :
    Integrable (fun ω => bodyWindowError cfg x₀ seed oracle grad δ s m (n+1) j (fun k => ξ k ω)) P ∧
    (∫ ω,bodyWindowError cfg x₀ seed oracle grad δ s m (n+1) j (fun k => ξ k ω) ∂P) ≤
      16*((L+μ)*127*(∑ i : Fin (n+1),Real.sqrt ((1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))*
        Real.sqrt (∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) (m+i.rev)-
          trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) s‖^2 ∂P))+B*((n+1)*(1/2 : ℝ)^n))+
      16*(127*(∫ ω,Real.sqrt ((999/1000 : ℝ)^(n+1)*
        (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) m).accumulator (.inl j)) ∂P)+B*(1/2 : ℝ)^(n+1)) := by
  let P₀ := Measure.pi (fun _ : Fin m => p)
  let Q := P₀.prod (Measure.pi (fun _ : Fin (n+1) => p))
  let U := fun w : (Fin m → Ω) × (Fin (n+1) → Ω) =>
    bodyWindowError cfg x₀ seed oracle grad δ s m (n+1) j (prefixReverseSamples a w.1 w.2)
  let old := fun pre : Fin m → Ω => run cfg x₀ seed (fun k x => oracle x (paddedSamples a pre k)) m
  let D := fun i : Fin (n+1) => fun w : (Fin m → Ω) × (Fin n → Ω) =>
    ‖trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) (m+i.rev)-
      trajectory cfg x₀ (fun k x => oracle x (prefixReverseSamples a w.1 (i.insertNth a w.2) k)) s‖
  let E := 16*((L+μ)*127*(∑ i : Fin (n+1),Real.sqrt ((1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))*
    Real.sqrt (∫ w,D i w^2 ∂P₀.prod (Measure.pi (fun _ : Fin n => p))))+B*((n+1)*(1/2 : ℝ)^n))+
    16*(127*(∫ pre,Real.sqrt ((999/1000 : ℝ)^(n+1)*(old pre).accumulator (.inl j)) ∂P₀)+B*(1/2 : ℝ)^(n+1))
  have hacc := (run_core_measurable cfg x₀ seed ho (paddedSamples_measurable (n := m) a) m).2.2
  have hc : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
  have hm : Measurable (fun pre : Fin m → Ω => Real.sqrt ((999/1000 : ℝ)^(n+1)*(old pre).accumulator (.inl j))) :=
    (measurable_const.mul (hc.comp hacc)).sqrt
  have ht := iid_prefix_run_integral cfg x₀ seed oracle a hsamples m
    (fun st => Real.sqrt ((999/1000 : ℝ)^(n+1)*st.accumulator (.inl j))) hm.aestronglyMeasurable
  have hpvi := ht.1.mpr hVi
  have hh := reverse_window_tracking cfg hα hβ hcfgδ x₀ a seed ho hg hgrad hnoise hK hK0 hμ
    hL hB hδ s hs j hsym hGB hpvi
  have hprod : Integrable U Q ∧ (∫ w,U w ∂Q) ≤ E := by
    dsimp [U,Q,E,D,old,P₀]
    simpa only [bodyWindowError_prefix cfg hα hβ x₀ seed oracle grad δ s hs j a,Fin.val_rev] using hh
  have hpull := iid_bodyWindowError_integral cfg x₀ seed oracle grad δ s m (n+1) (by omega) j a hsamples hprod.1
  refine ⟨hpull.1,?_⟩
  rw [← hpull.2]
  refine hprod.2.trans_eq ?_
  have hD (i : Fin (n+1)) :
      (∫ w,D i w^2 ∂P₀.prod (Measure.pi (fun _ : Fin n => p))) =
        ∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) (m+i.rev)-
          trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) s‖^2 ∂P :=
    iid_reverse_deleted_displacement_moment cfg hα hβ hcfgδ x₀ ho hsamples i a (m+i.rev) s le_rfl (by omega)
  dsimp only [E]
  simp_rw [hD]
  dsimp only [old,P₀]
  rw [ht.2]


lemma iid_prefix_history_coercive {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {m n : ℕ}
    {G S : (Fin m → Ω) → ℝ} {noise : (Fin m → Ω) → Ω → ℝ} {δ B : ℝ}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hδ : 0 < δ) (hB : 0 ≤ B) (hG : Measurable G) (hS : Measurable S)
    (hGB : ∀ x,|G x| ≤ B) (hm : Measurable (Function.uncurry noise))
    (hi : ∀ x,Integrable (noise x) p)
    (hsym : ∀ x,(p.map (noise x)).map (fun z : ℝ => -z)=p.map (noise x))
    (hSbound : ∀ x,(∫ ω,|noise x ω| ∂p) ≤ S x) :
    let pre := fun ω => fun i : Fin m => ξ i ω
    let H := fun ω => G (pre ω)*historyField δ
      (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
      (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))
      (G (pre ω)) (fun i => noise (pre ω) (ξ (m+i.rev) ω))
    let φ := fun ω => (G (pre ω))^2/(90*(δ+66*(|G (pre ω)|+S (pre ω))))
    Integrable H P ∧ Integrable φ P ∧ (∫ ω,φ ω ∂P) ≤ ∫ ω,H ω ∂P := by
  dsimp only
  let H := fun w : (Fin m → Ω) × (Fin (n+2) → Ω) => G w.1*historyField δ
    (fun i : Fin (n+2) => (1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ))
    (fun i : Fin (n+2) => (1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))
    (G w.1) (fun i => noise w.1 (w.2 i))
  let φ := fun x : Fin m → Ω => (G x)^2/(90*(δ+66*(|G x|+S x)))
  have hh := prefix_default_history_coercive (P := Measure.pi (fun _ : Fin m => p))
    (n := n) hδ hB hG hS hGB hm hi hsym hSbound
  have hHi : Integrable H ((Measure.pi (fun _ : Fin m => p)).prod (Measure.pi (fun _ : Fin (n+2) => p))) := hh.1
  have hφi : Integrable φ (Measure.pi (fun _ : Fin m => p)) := hh.2.1
  have hp := iid_prefix_reverse_window_law hsamples m (n+2)
  have hpre := (measurePreserving_fst (μ := Measure.pi (fun _ : Fin m => p))
    (ν := Measure.pi (fun _ : Fin (n+2) => p))).comp hp
  refine ⟨?_,?_,?_⟩
  · simpa only [Function.comp_def,H] using hp.integrable_comp_of_integrable hHi
  · simpa only [Function.comp_def,φ] using hpre.integrable_comp_of_integrable hφi
  · have hHmap := integral_map hp.measurable.aemeasurable (f := H) (hp.map_eq.symm ▸ hHi.aestronglyMeasurable)
    have hφmap := integral_map hpre.measurable.aemeasurable (f := φ) (hpre.map_eq.symm ▸ hφi.aestronglyMeasurable)
    rw [hp.map_eq] at hHmap
    rw [hpre.map_eq] at hφmap
    have he := hφmap.symm.le.trans (hh.2.2.trans_eq hHmap)
    simpa only [Function.comp_def,H,φ] using he

open LongTails.Algorithms.HeterogeneousAdam

lemma iid_frozen_body_coercive {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h m n : ℕ}
    (cfg : Config) (x₀ : Point b h) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {δ B : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ x,Integrable (oracle x) p)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hδ : 0 < δ) (hB : 0 ≤ B) (s : ℕ) (hs : s ≤ m) (j : Fin b)
    (hGB : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) s) (.inl j)| ≤ B)
    (hsym : ∀ x,(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j))) :
    let x := fun ω => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) s
    let W := fun ω (i : Fin (n+2)) => oracle (x ω) (ξ (m+i.rev) ω) (.inl j)
    let H := fun ω => grad (x ω) (.inl j)*
      (∑ i : Fin (n+2),(1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*W ω i)/
        (δ+Real.sqrt (∑ i : Fin (n+2),(1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*(W ω i)^2))
    let φ := fun ω => (grad (x ω) (.inl j))^2/
      (90*(δ+66*(|grad (x ω) (.inl j)|+(∫ u,|(oracle (x ω) u-grad (x ω)) (.inl j)| ∂p))))
    Integrable H P ∧ Integrable φ P ∧ (∫ ω,φ ω ∂P) ≤ ∫ ω,H ω ∂P := by
  dsimp only
  let x := fun pre : Fin m → Ω => trajectory cfg x₀ (fun k x => oracle x (paddedSamples a pre k)) s
  let G := fun pre => grad (x pre) (.inl j)
  let noise := fun pre u => (oracle (x pre) u-grad (x pre)) (.inl j)
  let S := fun pre => ∫ u,|noise pre u| ∂p
  have hc : Measurable (fun v : Point b h => v (.inl j)) := by fun_prop
  have hx : Measurable x := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a) s
  have hG : Measurable G := hc.comp (hg.comp hx)
  have hn : Measurable (Function.uncurry noise) :=
    (joint_body_noise_measurable ho hg j).comp ((hx.comp measurable_fst).prodMk measurable_snd)
  have hna : Measurable (fun w : (Fin m → Ω) × Ω => |noise w.1 w.2|) := by fun_prop
  have hS : Measurable S := hna.stronglyMeasurable.integral_prod_right'.measurable
  have hni (pre : Fin m → Ω) : Integrable (noise pre) p :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin b ⊕ Fin h => ℝ) (.inl j)).integrable_comp
      ((hi (x pre)).sub (integrable_const (grad (x pre))))
  have hh := iid_prefix_history_coercive (n := n) hsamples hδ hB hG hS
    (fun pre => hGB (paddedSamples a pre)) hn hni (fun pre => hsym (x pre)) (fun _ => le_rfl)
  have he (ω : Ξ) : x (fun i : Fin m => ξ i ω)=trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) s := by
    apply trajectory_sample_congr_prefix
    intro k hk
    have hkm : k < m := lt_of_lt_of_le hk hs
    simp only [paddedSamples,dite_eq_left hkm]
  have hw (pre : Fin m → Ω) (u : Ω) : G pre+noise pre u=oracle (x pre) u (.inl j) := by
    dsimp [G,noise]
    ring
  dsimp only at hh
  simp only [historyField,hw] at hh
  simpa only [G,S,noise,he,mul_div_assoc] using hh


lemma frozen_direction_transfer {g g₀ F F₀ C D : ℝ}
    (hF : |F| ≤ C) (hD : |g-g₀| ≤ D) :
    g₀*F₀ ≤ g*F+|g₀| * |F-F₀|+C*D := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hF
  have h1 : g₀*(F₀-F) ≤ |g₀| * |F-F₀| := by
    calc
      _ ≤ |g₀*(F₀-F)| := le_abs_self _
      _ = _ := by rw [abs_mul,abs_sub_comm]
  have h2 : (g₀-g)*F ≤ C*D := by
    calc
      _ ≤ |(g₀-g)*F| := le_abs_self _
      _ = |F| * |g-g₀| := by rw [abs_mul,abs_sub_comm,mul_comm]
      _ ≤ C*D := mul_le_mul hF hD (abs_nonneg _) hC
  nlinarith

lemma bias_weighted_coercivity {A I E q : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hq0 : 3/100 ≤ q) (hq1 : q ≤ 10) (hcoerce : A/90 ≤ I+E) :
    A/3000 ≤ q*I+10*E := by
  have hq : 0 ≤ q := by linarith
  have hm := mul_le_mul_of_nonneg_left hcoerce hq
  have ha := mul_le_mul_of_nonneg_right hq0 hA
  have he := mul_le_mul_of_nonneg_right hq1 hE
  nlinarith

lemma integral_frozen_direction_transfer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G G₀ F F₀ D φ : Ω → ℝ} {L q : ℝ}
    (hI : Integrable (fun ω => G ω*F ω) P)
    (hJ : Integrable (fun ω => G₀ ω*F₀ ω) P)
    (hE : Integrable (fun ω => |G₀ ω| * |F ω-F₀ ω|) P) (hD : Integrable D P)
    (hφ0 : ∀ ω,0 ≤ φ ω) (hD0 : ∀ ω,0 ≤ D ω) (hL : 0 ≤ L)
    (hF : ∀ ω,|F ω| ≤ 8) (hDiff : ∀ ω,|G ω-G₀ ω| ≤ L*D ω)
    (hcoerce : (∫ ω,φ ω ∂P)/90 ≤ ∫ ω,G₀ ω*F₀ ω ∂P)
    (hq0 : 3/100 ≤ q) (hq1 : q ≤ 10) :
    (∫ ω,φ ω ∂P)/3000 ≤ q*(∫ ω,G ω*F ω ∂P)+
      10*(∫ ω,|G₀ ω| * |F ω-F₀ ω| ∂P)+80*L*(∫ ω,D ω ∂P) := by
  have hpoint (ω) : G₀ ω*F₀ ω ≤ G ω*F ω+|G₀ ω| * |F ω-F₀ ω|+(8*L)*D ω := by
    have hh := frozen_direction_transfer (F₀ := F₀ ω) (hF ω) (hDiff ω)
    nlinarith
  have hh := integral_mono hJ ((hI.add hE).add (hD.const_mul (8*L))) hpoint
  have hsplit := integral_add (hI.add hE) (hD.const_mul (8*L))
  have hsplit₂ := integral_add hI hE
  simp only [Pi.add_apply] at hh hsplit hsplit₂
  rw [hsplit,hsplit₂,integral_const_mul] at hh
  have he0 : 0 ≤ (∫ ω,|G₀ ω| * |F ω-F₀ ω| ∂P)+(8*L)*(∫ ω,D ω ∂P) :=
    add_nonneg (integral_nonneg (fun ω => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (mul_nonneg (by positivity) (integral_nonneg hD0))
  have hb := bias_weighted_coercivity (A := ∫ ω,φ ω ∂P) (I := ∫ ω,G ω*F ω ∂P) (integral_nonneg hφ0) he0 hq0 hq1 (by linarith [hcoerce])
  nlinarith


lemma iid_body_descent_step {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h m n : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {L B : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (s : ℕ) (hs : s ≤ m) (j : Fin b)
    (hGs : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) s) (.inl j)| ≤ B)
    (hGt : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) (m+n+1)) (.inl j)| ≤ B)
    (hsym : ∀ x,(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hη : 0 ≤ cfg.bodyStep (m+n+1)) :
    let t := m+n+1
    let η := cfg.bodyStep t
    let δₜ := cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let x := fun k ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) k
    let Ψ := fun ω => (grad (x s ω) (.inl j))^2/
      (90*(δₜ+66*(|grad (x s ω) (.inl j)|+(∫ u,|(oracle (x s ω) u-grad (x s ω)) (.inl j)| ∂p))))
    Integrable (fun ω => grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j))) P ∧
    Integrable Ψ P ∧
    (∫ ω,grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) ∂P) ≤
      -η*(3/100)*(∫ ω,Ψ ω ∂P)+
        10*η*(∫ ω,bodyWindowError cfg x₀ seed oracle grad δₜ s m (n+2) j (fun k => ξ k ω) ∂P)+
        80*η*L*(∫ ω,‖x t ω-x s ω‖ ∂P) := by
  dsimp only
  let t := m+n+1
  let η := cfg.bodyStep t
  let δₜ := cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let q := Real.sqrt (1-(999/1000 : ℝ)^(t+1))/(1-(9/10 : ℝ)^(t+1))
  let x := fun k ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) k
  let G := fun ω => grad (x t ω) (.inl j)
  let G₀ := fun ω => grad (x s ω) (.inl j)
  let F := fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (t+1)).momentum (.inl j)/
    (δₜ+Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (t+1)).accumulator (.inl j)))
  let F₀ := fun ω =>
    (∑ i : Fin (n+2),(1-(9/10 : ℝ))*(9/10 : ℝ)^(i : ℕ)*oracle (x s ω) (ξ (m+i.rev) ω) (.inl j))/
      (δₜ+Real.sqrt (∑ i : Fin (n+2),(1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ)*
        (oracle (x s ω) (ξ (m+i.rev) ω) (.inl j))^2))
  let Ψ := fun ω => (G₀ ω)^2/
    (90*(δₜ+66*(|G₀ ω|+(∫ u,|(oracle (x s ω) u-grad (x s ω)) (.inl j)| ∂p))))
  let D := fun ω => ‖x t ω-x s ω‖
  have hδₜ : 0 < δₜ := (default_effective_stabilizer hδ t).1
  have hq := default_bias_multiplier_bounds t
  have hco := iid_frozen_body_coercive (m := m) (n := n) cfg x₀ a ho hg hi hsamples hδₜ hB s hs j hGs hsym
  have hJ : Integrable (fun ω => G₀ ω*F₀ ω) P := by
    simpa only [mul_div_assoc] using hco.1
  have hΨ : Integrable Ψ P := hco.2.1
  have hIc : Integrable (fun ω => G ω*F ω) P :=
    body_gradient_direction_integrable cfg hα hβ x₀ seed ho hg hsamples.measurable t (t+1) j hδₜ hB hGt
  have hIs : Integrable (fun ω => G₀ ω*F ω) P :=
    body_gradient_direction_integrable cfg hα hβ x₀ seed ho hg hsamples.measurable s (t+1) j hδₜ hB hGs
  have hE : Integrable (fun ω => |G₀ ω| * |F ω-F₀ ω|) P := by
    convert (hIs.sub hJ).abs using 1
    funext ω
    simp only [Pi.sub_apply,← mul_sub,abs_mul]
  have hD : Integrable D P :=
    (trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hsamples.measurable t s P).integrable (by norm_num)
  have hφ0 (ω) : 0 ≤ 90*Ψ ω := by
    have hS : 0 ≤ ∫ u,|(oracle (x s ω) u-grad (x s ω)) (.inl j)| ∂p := integral_nonneg (fun _ => abs_nonneg _)
    dsimp [Ψ]
    positivity
  have hFb (ω) : |F ω| ≤ 8 := run_body_normalized_bound cfg hα hβ x₀ seed
    (fun k x => oracle x (ξ k ω)) (t+1) j hδₜ
  have hDiff (ω) : |G ω-G₀ ω| ≤ L*D ω := by
    have hh := (PiLp.norm_apply_le (grad (x t ω)-grad (x s ω)) (.inl j)).trans (hgrad (x t ω) (x s ω))
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using hh
  have hc : (∫ ω,90*Ψ ω ∂P)/90 ≤ ∫ ω,G₀ ω*F₀ ω ∂P := by
    rw [integral_const_mul]
    have hh : (∫ ω,Ψ ω ∂P) ≤ ∫ ω,G₀ ω*F₀ ω ∂P := by
      simpa only [mul_div_assoc] using hco.2.2
    linarith
  have htransfer := integral_frozen_direction_transfer hIc hJ hE hD hφ0 (fun _ => norm_nonneg _) hL hFb hDiff hc hq.1 hq.2
  rw [integral_const_mul] at htransfer
  have he (ω) : grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) =
      (-η*q)*(G ω*F ω) := by
    have hh := run_body_update_identity cfg hα hβ hδ x₀ seed (fun k x => oracle x (ξ k ω)) t j
    rw [run_point,run_point] at hh
    change G ω*(x (t+1) ω (.inl j)-x t ω (.inl j)) = _
    rw [hh]
    dsimp [η,q,F,δₜ,x]
    ring
  have herror (ω) : |G₀ ω| * |F ω-F₀ ω| =
      bodyWindowError cfg x₀ seed oracle grad δₜ s m (n+2) j (fun k => ξ k ω) := by
    rfl
  refine ⟨?_,hΨ,?_⟩
  · exact (hIc.const_mul (-η*q)).congr (Filter.Eventually.of_forall (fun ω => (he ω).symm))
  · change (∫ ω,grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) ∂P) ≤
      -η*(3/100)*(∫ ω,Ψ ω ∂P)+
        10*η*(∫ ω,bodyWindowError cfg x₀ seed oracle grad δₜ s m (n+2) j (fun k => ξ k ω) ∂P)+
        80*η*L*(∫ ω,D ω ∂P)
    simp_rw [he]
    rw [integral_const_mul]
    simp_rw [herror] at htransfer
    have hh := mul_le_mul_of_nonneg_left htransfer hη
    nlinarith


lemma head_potential_integrability {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {G : X × Ω → ℝ} {q r : X → ℝ} {r₀ B η : ℝ}
    (hG : Measurable G) (hq : Measurable q) (hr : Measurable r)
    (hr₀ : 0 < r₀) (hrB : ∀ a,r₀ ≤ r a) (hB : 0 ≤ B) (hqB : ∀ a,|q a| ≤ B) :
    Integrable (fun w : X × Ω => -η*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2)) (P.prod p) ∧
    Integrable (fun w : X × Ω => (q w.1)^2/Real.sqrt ((r w.1)^2+G w^2)) (P.prod p) ∧
    Integrable (fun w : X × Ω => 1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2)) (P.prod p) ∧
    Integrable (fun a => (q a)^2/r a) P := by
  have hrp (a) : 0 < r a := lt_of_lt_of_le hr₀ (hrB a)
  have hs (w : X × Ω) : r w.1 ≤ Real.sqrt ((r w.1)^2+G w^2) :=
    (Real.le_sqrt (hrp _).le (add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr (by nlinarith [sq_nonneg (G w)])
  have hsp (w : X × Ω) : 0 < Real.sqrt ((r w.1)^2+G w^2) := lt_of_lt_of_le (hrp _) (hs w)
  have hq2 (a) : (q a)^2 ≤ B^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hqB a)
  have hU : Measurable (fun w : X × Ω => -η*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2)) := by fun_prop
  have hV : Measurable (fun w : X × Ω => (q w.1)^2/Real.sqrt ((r w.1)^2+G w^2)) := by fun_prop
  have hE : Measurable (fun w : X × Ω => 1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2)) := by fun_prop
  have hA : Measurable (fun a => (q a)^2/r a) := by fun_prop
  have hUb (w : X × Ω) : ‖-η*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2)‖ ≤ |η| *B := by
    have he : -η*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2) =
      (-η*q w.1)*(G w/Real.sqrt ((r w.1)^2+G w^2)) := by ring
    rw [he,Real.norm_eq_abs,abs_mul,abs_mul,abs_neg]
    calc
      _ ≤ (|η| *B)*1 := mul_le_mul (mul_le_mul_of_nonneg_left (hqB _) (abs_nonneg _))
        (adagrad_direction_bound (sq_nonneg _)) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB)
      _ = _ := mul_one _
  have hVb (w : X × Ω) : ‖(q w.1)^2/Real.sqrt ((r w.1)^2+G w^2)‖ ≤ B^2/r₀ := by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (hsp w).le)]
    exact div_le_div₀ (sq_nonneg _) (hq2 _) hr₀ ((hrB _).trans (hs w))
  have hEb (w : X × Ω) : ‖1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2)‖ ≤ 1/r₀ := by
    have h0 := sub_nonneg.mpr (one_div_le_one_div_of_le (hrp _) (hs w))
    rw [Real.norm_eq_abs,abs_of_nonneg h0]
    have h1 := one_div_le_one_div_of_le hr₀ (hrB w.1)
    have h2 : 0 ≤ 1/Real.sqrt ((r w.1)^2+G w^2) := by positivity
    linarith
  have hAb (a) : ‖(q a)^2/r a‖ ≤ B^2/r₀ := by
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (hrp a).le)]
    exact div_le_div₀ (sq_nonneg _) (hq2 _) hr₀ (hrB a)
  exact ⟨(show MemLp _ 1 _ from MemLp.of_bound hU.aestronglyMeasurable (|η| *B) (Filter.Eventually.of_forall hUb)).integrable (by norm_num),
    (show MemLp _ 1 _ from MemLp.of_bound hV.aestronglyMeasurable (B^2/r₀) (Filter.Eventually.of_forall hVb)).integrable (by norm_num),
    (show MemLp _ 1 _ from MemLp.of_bound hE.aestronglyMeasurable (1/r₀) (Filter.Eventually.of_forall hEb)).integrable (by norm_num),
    (show MemLp _ 1 _ from MemLp.of_bound hA.aestronglyMeasurable (B^2/r₀) (Filter.Eventually.of_forall hAb)).integrable (by norm_num)⟩



lemma prefix_head_potential_step {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {G : X → Ω → ℝ} {q qprev r D : X → ℝ} {σ η : ℝ}
    (hr : ∀ a, 0 < r a) (hη : 0 ≤ η)
    (hGm : ∀ a, Measurable (G a)) (hG : ∀ a, MemLp (G a) 2 p)
    (hmean : ∀ a, (∫ ω,G a ω ∂p)=q a)
    (hG2 : ∀ a, (∫ ω,G a ω^2 ∂p) ≤ (q a)^2+σ^2)
    (hchange : ∀ a, |q a-qprev a| ≤ D a)
    (hU : Integrable (fun w : X × Ω => -η*q w.1*G w.1 w.2/Real.sqrt ((r w.1)^2+G w.1 w.2^2)) (P.prod p))
    (hV : Integrable (fun w : X × Ω => (q w.1)^2/Real.sqrt ((r w.1)^2+G w.1 w.2^2)) (P.prod p))
    (hE : Integrable (fun w : X × Ω => 1/r w.1-1/Real.sqrt ((r w.1)^2+G w.1 w.2^2)) (P.prod p))
    (hA : Integrable (fun a => (q a)^2/r a) P)
    (hB : Integrable (fun a => (qprev a)^2/r a) P)
    (hC : Integrable (fun a => (D a)^2/r a) P) :
    (∫ w : X × Ω,-η*q w.1*G w.1 w.2/Real.sqrt ((r w.1)^2+G w.1 w.2^2) ∂P.prod p) ≤
      -η/4*(∫ a,(q a)^2/r a ∂P)+
      η/2*((∫ a,(qprev a)^2/r a ∂P)-(∫ w : X × Ω,(q w.1)^2/Real.sqrt ((r w.1)^2+G w.1 w.2^2) ∂P.prod p))+
      (3*η/2)*(∫ a,(D a)^2/r a ∂P)+
      η*σ^2/2*(∫ w : X × Ω,1/r w.1-1/Real.sqrt ((r w.1)^2+G w.1 w.2^2) ∂P.prod p) := by
  have hiU := hU.integral_prod_left
  have hiV := hV.integral_prod_left
  have hiE := hE.integral_prod_left
  have hiR := ((hA.const_mul (-η/4)).add ((hB.sub hiV).const_mul (η/2))).add
    ((hC.const_mul (3*η/2)).add (hiE.const_mul (η*σ^2/2)))
  have hb := integral_mono hiU hiR (fun a => by
    have hh := (head_adagrad_expected_potential_step (hr a) hη (hGm a) (hG a)
      (hmean a) (hG2 a) (hchange a)).2
    dsimp only [Pi.add_apply,Pi.sub_apply] at *
    convert hh using 1
    ring)
  rw [integral_prod _ hU]
  calc
    _ ≤ ∫ a, ((-η/4)*((q a)^2/r a)+η/2*((qprev a)^2/r a-
        (∫ ω,(q a)^2/Real.sqrt ((r a)^2+G a ω^2) ∂p)))+
        ((3*η/2)*((D a)^2/r a)+η*σ^2/2*(∫ ω,1/r a-1/Real.sqrt ((r a)^2+G a ω^2) ∂p)) ∂P := hb
    _ = _ := by
      have h1 := integral_add ((hA.const_mul (-η/4)).add ((hB.sub hiV).const_mul (η/2)))
        ((hC.const_mul (3*η/2)).add (hiE.const_mul (η*σ^2/2)))
      have h2 := integral_add (hA.const_mul (-η/4)) ((hB.sub hiV).const_mul (η/2))
      have h3 := integral_add (hC.const_mul (3*η/2)) (hiE.const_mul (η*σ^2/2))
      have h4 := integral_sub hB hiV
      simp only [Pi.add_apply,Pi.sub_apply] at h1 h2 h3 h4
      rw [h1,h2,h3,integral_const_mul,integral_const_mul,integral_const_mul,
        integral_const_mul,h4,← integral_prod _ hV,← integral_prod _ hE]
      ring


lemma bounded_prefix_head_potential_step {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {P : Measure X} {p : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure p]
    {G : X × Ω → ℝ} {q qprev r : X → ℝ} {r₀ B σ η : ℝ}
    (hGm : Measurable G) (hq : Measurable q) (hqp : Measurable qprev) (hrm : Measurable r)
    (hr₀ : 0 < r₀) (hrB : ∀ a,r₀ ≤ r a) (hB : 0 ≤ B)
    (hqB : ∀ a,|q a| ≤ B) (hqpB : ∀ a,|qprev a| ≤ B) (hη : 0 ≤ η)
    (hG : ∀ a, MemLp (fun ω => G (a,ω)) 2 p)
    (hmean : ∀ a, (∫ ω,G (a,ω) ∂p)=q a)
    (hG2 : ∀ a, (∫ ω,G (a,ω)^2 ∂p) ≤ (q a)^2+σ^2) :
    (∫ w : X × Ω,-η*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2) ∂P.prod p) ≤
      -η/4*(∫ a,(q a)^2/r a ∂P)+
      η/2*((∫ a,(qprev a)^2/r a ∂P)-(∫ w : X × Ω,(q w.1)^2/Real.sqrt ((r w.1)^2+G w^2) ∂P.prod p))+
      (3*η/2)*(∫ a,(q a-qprev a)^2/r a ∂P)+
      η*σ^2/2*(∫ w : X × Ω,1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2) ∂P.prod p) := by
  have hi := head_potential_integrability (P := P) (p := p) (η := η) hGm hq hrm hr₀ hrB hB hqB
  have hip := head_potential_integrability (P := P) (p := p) (η := η) hGm hqp hrm hr₀ hrB hB hqpB
  have hdB (a) : |q a-qprev a| ≤ 2*B := by
    exact (abs_sub _ _).trans (by linarith [hqB a,hqpB a])
  have hic := head_potential_integrability (P := P) (p := p) (η := η) hGm (hq.sub hqp) hrm hr₀ hrB
    (mul_nonneg (by norm_num) hB) hdB
  have hc : Integrable (fun a => |q a-qprev a|^2/r a) P := by
    simpa only [sq_abs,Pi.sub_apply] using hic.2.2.2
  have hh := prefix_head_potential_step (G := fun a ω => G (a,ω))
    (D := fun a => |q a-qprev a|) (fun a => lt_of_lt_of_le hr₀ (hrB a)) hη
    (fun a => hGm.comp measurable_prodMk_left) hG hmean hG2 (fun _ => le_rfl)
    hi.1 hi.2.1 hi.2.2.1 hi.2.2.2 hip.2.2.2 hc
  simpa only [sq_abs] using hh

lemma run_prefix_head_potential_step {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {b h : ℕ}
    (cfg : Config) (hr₀ : 0 < cfg.r₀) (x₀ : LongTails.Algorithms.HeterogeneousAdam.Point b h)
    (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : LongTails.Algorithms.HeterogeneousAdam.Point b h → Ω → LongTails.Algorithms.HeterogeneousAdam.Point b h}
    {grad : LongTails.Algorithms.HeterogeneousAdam.Point b h → LongTails.Algorithms.HeterogeneousAdam.Point b h}
    {B σ : ℝ} (hB : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ x,Integrable (oracle x) p) (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=grad x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2 ∂p) ≤ σ^2)
    (n : ℕ) (j : Fin h) (hη : 0 ≤ cfg.headStep n)
    (hqn : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) (.inr j)| ≤ B)
    (hqp : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) (n-1)) (.inr j)| ≤ B) :
    let μ := Measure.pi (fun _ : Fin n => p)
    let u := fun z : Fin n → Ω => run cfg x₀ seed (fun k x => oracle x (paddedSamples a z k)) n
    let q := fun z => grad (u z).point (.inr j)
    let qp := fun z : Fin n → Ω => grad (trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) (n-1)) (.inr j)
    let r := fun z => Real.sqrt ((u z).accumulator (.inr j))
    let G := fun w : (Fin n → Ω) × Ω => oracle (u w.1).point w.2 (.inr j)
    let η := cfg.headStep n
    (∫ w,-η*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2) ∂μ.prod p) ≤
      -η/4*(∫ z,(q z)^2/r z ∂μ)+
      η/2*((∫ z,(qp z)^2/r z ∂μ)-(∫ w,(q w.1)^2/Real.sqrt ((r w.1)^2+G w^2) ∂μ.prod p))+
      (3*η/2)*(∫ z,(q z-qp z)^2/r z ∂μ)+
      η*σ^2/2*(∫ w,1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2) ∂μ.prod p) := by
  dsimp only
  let u := fun z : Fin n → Ω => run cfg x₀ seed (fun k x => oracle x (paddedSamples a z k)) n
  let q := fun z => grad (u z).point (.inr j)
  let qp := fun z : Fin n → Ω => grad (trajectory cfg x₀ (fun k x => oracle x (paddedSamples a z k)) (n-1)) (.inr j)
  let r := fun z => Real.sqrt ((u z).accumulator (.inr j))
  let G := fun w : (Fin n → Ω) × Ω => oracle (u w.1).point w.2 (.inr j)
  have hu := run_core_measurable cfg x₀ seed ho (paddedSamples_measurable a (n := n)) n
  have hj : Measurable (fun v : Point b h => v (.inr j)) := by fun_prop
  have hqm : Measurable q := hj.comp (hg.comp hu.1)
  have hqpm : Measurable qp := by
    have hx := trajectory_measurable cfg x₀ ho (paddedSamples_measurable a (n := n)) (n-1)
    dsimp [qp]; fun_prop
  have hrm : Measurable r := (hj.comp hu.2.2).sqrt
  have hGm : Measurable G := by
    have hh := ho.comp ((hu.1.comp measurable_fst).prodMk measurable_snd)
    exact hj.comp hh
  have hrB (z) : cfg.r₀ ≤ r z := by
    have hv := run_head_accumulator_lower cfg x₀ seed (fun k x => oracle x (paddedSamples a z k)) n j
    exact (Real.le_sqrt hr₀.le ((sq_nonneg cfg.r₀).trans hv)).mpr hv
  have hqB (z) : |q z| ≤ B := by simpa only [q,u,run_point] using hqn (paddedSamples a z)
  have hqpB (z) : |qp z| ≤ B := hqp (paddedSamples a z)
  have hs (z : Fin n → Ω) := head_coordinate_moments (ho.comp measurable_prodMk_left)
    (hi (u z).point) (hmean (u z).point) (hni (u z).point) (hσ (u z).point) j
  exact bounded_prefix_head_potential_step hGm hqm hqpm hrm hr₀ hrB hB hqB hqpB hη
    (fun z => (hs z).1) (fun z => (hs z).2.1) (fun z => (hs z).2.2)

lemma iid_head_descent_step {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hr₀ : 0 < cfg.r₀) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {B σ : ℝ} (hB : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ x,Integrable (oracle x) p) (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=grad x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (n : ℕ) (j : Fin h) (hη : 0 ≤ cfg.headStep n)
    (hqn : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) (.inr j)| ≤ B)
    (hqp : ∀ z : ℕ → Ω,|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) (n-1)) (.inr j)| ≤ B) :
    let v := fun ω k => run cfg x₀ seed (fun t x => oracle x (ξ t ω)) k
    let q := fun ω => grad (v ω n).point (.inr j)
    let qp := fun ω => grad (v ω (n-1)).point (.inr j)
    let r := fun ω k => Real.sqrt ((v ω k).accumulator (.inr j))
    let η := cfg.headStep n
    (∫ ω,q ω*((v ω (n+1)).point (.inr j)-(v ω n).point (.inr j)) ∂P) ≤
      -η/4*(∫ ω,(q ω)^2/r ω n ∂P)+
      η/2*((∫ ω,(qp ω)^2/r ω n ∂P)-(∫ ω,(q ω)^2/r ω (n+1) ∂P))+
      (3*η/2)*(∫ ω,(q ω-qp ω)^2/r ω n ∂P)+
      η*σ^2/2*(∫ ω,1/r ω n-1/r ω (n+1) ∂P) := by
  let μ := Measure.pi (fun _ : Fin n => p)
  let u := fun (z : Fin n → Ω) k => run cfg x₀ seed (fun t x => oracle x (paddedSamples a z t)) k
  let v := fun (ω : Ξ) k => run cfg x₀ seed (fun t x => oracle x (ξ t ω)) k
  let q := fun z => grad (u z n).point (.inr j)
  let qp := fun z => grad (u z (n-1)).point (.inr j)
  let r := fun z => Real.sqrt ((u z n).accumulator (.inr j))
  let G := fun w : (Fin n → Ω) × Ω => oracle (u w.1 n).point w.2 (.inr j)
  have he (ω : Ξ) (k : ℕ) (hk : k ≤ n) : u (fun i : Fin n => ξ i ω) k=v ω k := by
    apply run_congr_prefix
    intro t ht
    simp only [paddedSamples,dite_eq_left (show t<n by omega)]
  have hp := iid_prefix_sample_law hs n
  have hp0 := (measurePreserving_fst (μ := μ) (ν := p)).comp hp
  have hprefix (F : (Fin n → Ω) → ℝ) (hF : Measurable F) :
      (∫ z,F z ∂μ) = ∫ ω,F (fun i : Fin n => ξ i ω) ∂P := by
    have hh := integral_map hp0.measurable.aemeasurable (hp0.map_eq.symm ▸ (show AEStronglyMeasurable F μ from hF.aestronglyMeasurable))
    have hmap : P.map (fun ω => fun i : Fin n => ξ i ω)=μ := hp0.map_eq
    simp only [Function.comp_def] at hh
    simpa only [hmap] using hh
  have hpair (F : (Fin n → Ω) × Ω → ℝ) (hF : Measurable F) :
      (∫ w,F w ∂μ.prod p) = ∫ ω,F ((fun i : Fin n => ξ i ω),ξ n ω) ∂P := by
    have hh := integral_map hp.measurable.aemeasurable (hp.map_eq.symm ▸ (show AEStronglyMeasurable F (μ.prod p) from hF.aestronglyMeasurable))
    simpa only [hp.map_eq] using hh
  have hj : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
  have hu (k) := run_core_measurable cfg x₀ seed ho (paddedSamples_measurable a (n := n)) k
  have hqm : Measurable q := hj.comp (hg.comp (hu n).1)
  have hqpm : Measurable qp := hj.comp (hg.comp (hu (n-1)).1)
  have hrm : Measurable r := (hj.comp (hu n).2.2).sqrt
  have hGm : Measurable G := hj.comp (ho.comp (((hu n).1.comp measurable_fst).prodMk measurable_snd))
  have hroot (ω : Ξ) : Real.sqrt ((r (fun i : Fin n => ξ i ω))^2+G ((fun i : Fin n => ξ i ω),ξ n ω)^2)=
      Real.sqrt ((v ω (n+1)).accumulator (.inr j)) := by
    have hv := (sq_nonneg cfg.r₀).trans (run_head_accumulator_lower cfg x₀ seed (fun t x => oracle x (ξ t ω)) n j)
    dsimp [r,G]
    rw [he ω n le_rfl,Real.sq_sqrt hv]
    rfl
  have hU := hpair (fun w => -cfg.headStep n*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2)) (by fun_prop)
  have hV := hpair (fun w => (q w.1)^2/Real.sqrt ((r w.1)^2+G w^2)) (by fun_prop)
  have hE := hpair (fun w => 1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2)) (by fun_prop)
  have hA := hprefix (fun z => (q z)^2/r z) (by fun_prop)
  have hB' := hprefix (fun z => (qp z)^2/r z) (by fun_prop)
  have hC := hprefix (fun z => (q z-qp z)^2/r z) (by fun_prop)
  have hh := run_prefix_head_potential_step cfg hr₀ x₀ seed a hB ho hg hi hmean hni hσ n j hη hqn hqp
  dsimp only at hh
  simp only [← run_point cfg x₀ seed] at hh
  change (∫ w,-cfg.headStep n*q w.1*G w/Real.sqrt ((r w.1)^2+G w^2) ∂μ.prod p) ≤
    -cfg.headStep n/4*(∫ z,(q z)^2/r z ∂μ)+
    cfg.headStep n/2*((∫ z,(qp z)^2/r z ∂μ)-(∫ w,(q w.1)^2/Real.sqrt ((r w.1)^2+G w^2) ∂μ.prod p))+
    (3*cfg.headStep n/2)*(∫ z,(q z-qp z)^2/r z ∂μ)+
    cfg.headStep n*σ^2/2*(∫ w,1/r w.1-1/Real.sqrt ((r w.1)^2+G w^2) ∂μ.prod p) at hh
  rw [hU,hV,hE,hA,hB',hC] at hh
  simp_rw [hroot] at hh
  simp only [q,qp,r,G,he _ n le_rfl,he _ (n-1) (Nat.sub_le _ _)] at hh
  have hstep (ω : Ξ) : grad (v ω n).point (.inr j)*((v ω (n+1)).point (.inr j)-(v ω n).point (.inr j)) =
      -cfg.headStep n*grad (v ω n).point (.inr j)*oracle (v ω n).point (ξ n ω) (.inr j)/Real.sqrt ((v ω (n+1)).accumulator (.inr j)) := by
    rw [run_head_update_identity]
    change _ = _ / Real.sqrt ((v ω n).accumulator (.inr j)+(oracle (v ω n).point (ξ n ω) (.inr j))^2)
    ring
  dsimp only
  change (∫ ω,grad (v ω n).point (.inr j)*((v ω (n+1)).point (.inr j)-(v ω n).point (.inr j)) ∂P) ≤ _
  simp_rw [hstep]
  exact hh


lemma objective_integrable_of_bounded_displacement {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {b h : ℕ}
    {f : Point b h → ℝ} {g : Point b h → Point b h} {L Δ D : ℝ}
    {x₀ : Point b h} {x : Ω → Point b h}
    (hg : ∀ z,HasGradientAt f (g z) z)
    (hlip : ∀ y z,‖g y-g z‖ ≤ L*‖y-z‖) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hgap : ∀ z,f x₀-f z ≤ Δ) (hx : Measurable x) (hbound : ∀ ω,‖x ω-x₀‖ ≤ D) :
    Integrable (fun ω => f (x ω)) P := by
  have hΔ : 0 ≤ Δ := by simpa using hgap x₀
  have hf : Measurable f := (continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt).measurable
  let B := |f x₀|+Δ+‖g x₀‖*D+L/2*D^2
  have hb (ω) : ‖f (x ω)‖ ≤ B := by
    have hu := OracleTemplate.Gradient.smooth_upper_bound hg hlip x₀ (x ω)
    have hi := (real_inner_le_norm (g x₀) (x ω-x₀)).trans
      (mul_le_mul_of_nonneg_left (hbound ω) (norm_nonneg _))
    have hs : ‖x ω-x₀‖^2 ≤ D^2 := (sq_le_sq₀ (norm_nonneg _) hD).mpr (hbound ω)
    have hLs := mul_le_mul_of_nonneg_left hs (show 0 ≤ L/2 by positivity)
    have hlow := hgap (x ω)
    have hGD := mul_nonneg (norm_nonneg (g x₀)) hD
    have hLD : 0 ≤ L/2*D^2 := by positivity
    rw [Real.norm_eq_abs,abs_le]
    dsimp [B]
    constructor <;> linarith [le_abs_self (f x₀),neg_abs_le (f x₀)]
  exact (show MemLp (fun ω => f (x ω)) 1 P from MemLp.of_bound
    (hf.comp hx).aestronglyMeasurable B (Filter.Eventually.of_forall hb)).integrable (by norm_num)


lemma expected_block_smoothness {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {b h : ℕ}
    {f : Point b h → ℝ} {g : Point b h → Point b h} {L : ℝ}
    {x y : Ω → Point b h}
    (hg : ∀ z,HasGradientAt f (g z) z)
    (hlip : ∀ u v,‖g u-g v‖ ≤ L*‖u-v‖)
    (hfx : Integrable (fun ω => f (x ω)) P) (hfy : Integrable (fun ω => f (y ω)) P)
    (hib : ∀ j : Fin b,Integrable (fun ω => g (x ω) (.inl j)*(y ω-x ω) (.inl j)) P)
    (hih : ∀ j : Fin h,Integrable (fun ω => g (x ω) (.inr j)*(y ω-x ω) (.inr j)) P)
    (hm : Integrable (fun ω => ‖y ω-x ω‖^2) P) :
    (∫ ω,f (y ω)-f (x ω) ∂P) ≤
      (∑ j : Fin b,∫ ω,g (x ω) (.inl j)*(y ω-x ω) (.inl j) ∂P)+
      (∑ j : Fin h,∫ ω,g (x ω) (.inr j)*(y ω-x ω) (.inr j) ∂P)+
      L/2*(∫ ω,‖y ω-x ω‖^2 ∂P) := by
  have hb := integrable_finsetSum Finset.univ (fun j _ => hib j)
  have hh := integrable_finsetSum Finset.univ (fun j _ => hih j)
  have hu := integral_mono (hfy.sub hfx) ((hb.add hh).add (hm.const_mul (L/2))) (fun ω => by
    have hs := OracleTemplate.Gradient.smooth_upper_bound hg hlip (x ω) (y ω)
    simp only [PiLp.inner_apply,Fintype.sum_sum_type,RCLike.inner_apply,conj_trivial] at hs
    simp only [Pi.add_apply,Pi.sub_apply]
    simp_rw [mul_comm] at hs
    linarith)
  have he1 := integral_add (hb.add hh) (hm.const_mul (L/2))
  have he2 := integral_add hb hh
  simp only [Pi.add_apply,Pi.sub_apply] at hu he1 he2
  rw [he1,he2,integral_const_mul,integral_finsetSum _ (fun j _ => hib j),
    integral_finsetSum _ (fun j _ => hih j)] at hu
  exact hu


lemma run_expected_block_smoothness {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {f : Point b h → ℝ}
    {ξ : ℕ → Ξ → Ω} {B L Δ : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (ho : Measurable (Function.uncurry oracle)) (hgm : Measurable grad)
    (hg : ∀ x,HasGradientAt f (grad x) x)
    (hlip : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hξ : ∀ k,Measurable (ξ k)) (n : ℕ)
    (hGB : ∀ (z : ℕ → Ω) (j : Fin b ⊕ Fin h),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) n) j| ≤ B) :
    let x := fun ω k => (run cfg x₀ seed (fun t x => oracle x (ξ t ω)) k).point
    (∫ ω,f (x ω (n+1))-f (x ω n) ∂P) ≤
      (∑ j : Fin b,∫ ω,grad (x ω n) (.inl j)*(x ω (n+1)-x ω n) (.inl j) ∂P)+
      (∑ j : Fin h,∫ ω,grad (x ω n) (.inr j)*(x ω (n+1)-x ω n) (.inr j) ∂P)+
      L/2*(∫ ω,‖x ω (n+1)-x ω n‖^2 ∂P) := by
  let x := fun ω k => (run cfg x₀ seed (fun t x => oracle x (ξ t ω)) k).point
  have hx (k) : Measurable (fun ω => x ω k) := (run_core_measurable cfg x₀ seed ho hξ k).1
  have hfi (k) : Integrable (fun ω => f (x ω k)) P := by
    exact objective_integrable_of_bounded_displacement hg hlip hL
      (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _) hgap (hx k)
      (fun ω => run_displacement_sum cfg hα hβ hδ x₀ seed (fun t x => oracle x (ξ t ω)) k)
  have hci (j) : Integrable (fun ω => grad (x ω n) j*(x ω (n+1)-x ω n) j) P :=
    run_gradient_increment_integrable cfg hα hβ hδ x₀ seed hB ho hgm hξ n j (fun z => hGB z j)
  have hm : Integrable (fun ω => ‖x ω (n+1)-x ω n‖^2) P := by
    have hh := (trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hξ (n+1) n P).integrable_sq
    simpa only [x,run_point] using hh
  exact expected_block_smoothness hg hlip (hfi n) (hfi (n+1))
    (fun j => hci (.inl j)) (fun j => hci (.inr j)) hm


lemma expected_path_windows_energy {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} (x : Ω → ℕ → E) (N k : ℕ)
    (hw : ∀ t,Integrable (fun ω => ‖x ω (t+k)-x ω t‖^2) P)
    (hm : ∀ t,Integrable (fun ω => ‖x ω (t+1)-x ω t‖^2) P) :
    (∑ t ∈ Finset.range N,∫ ω,‖x ω (t+k)-x ω t‖^2 ∂P) ≤
      (k : ℝ)^2*(∑ t ∈ Finset.range (N+k),∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
  have hh := integral_mono (integrable_finsetSum _ (fun t _ => hw t))
    ((integrable_finsetSum _ (fun t _ => hm t)).const_mul ((k : ℝ)^2))
    (fun ω => path_windows_energy (x ω) N k)
  rw [integral_const_mul,integral_finsetSum _ (fun t _ => hw t),
    integral_finsetSum _ (fun t _ => hm t)] at hh
  exact hh

lemma expected_path_windows_root_sum {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} (x : Ω → ℕ → E) (N k : ℕ)
    (hw : ∀ t,Integrable (fun ω => ‖x ω (t+k)-x ω t‖^2) P)
    (hm : ∀ t,Integrable (fun ω => ‖x ω (t+1)-x ω t‖^2) P) :
    (∑ t ∈ Finset.range N,Real.sqrt (∫ ω,‖x ω (t+k)-x ω t‖^2 ∂P)) ≤
      k*Real.sqrt N*Real.sqrt (∑ t ∈ Finset.range (N+k),∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
  have hh := expected_path_windows_energy x N k hw hm
  have hsum := Real.sum_sqrt_mul_sqrt_le (s := Finset.range N)
    (f := fun _ => (1 : ℝ)) (g := fun t => ∫ ω,‖x ω (t+k)-x ω t‖^2 ∂P)
    (fun _ => by norm_num) (fun _ => integral_nonneg fun _ => sq_nonneg _)
  simp only [Real.sqrt_one,one_mul,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hsum
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_mul (sq_nonneg (k : ℝ)),Real.sqrt_sq (Nat.cast_nonneg k)] at hroot
  have hb := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (N : ℝ))
  exact hsum.trans (by nlinarith [hb])


lemma expected_coordinate_movement_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {b h : ℕ}
    (x : Ω → ℕ → Point b h) (T : ℕ) {A H : ℝ} (hA : 0 ≤ A)
    (hx : ∀ t,Measurable (fun ω => x ω t))
    (hm : ∀ t,Integrable (fun ω => ‖x ω (t+1)-x ω t‖^2) P)
    (hb : ∀ ω t (j : Fin b),|(x ω (t+1)-x ω t) (.inl j)| ≤ A)
    (hh : ∀ j : Fin h,(∑ t ∈ Finset.range T,∫ ω,((x ω (t+1)-x ω t) (.inr j))^2 ∂P) ≤ H) :
    (∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) ≤
      b*T*A^2+h*H := by
  have hi (t) (j : Fin b ⊕ Fin h) : Integrable (fun ω => ((x ω (t+1)-x ω t) j)^2) P := by
    have hj : Measurable (fun z : Point b h => z j) := by fun_prop
    apply (hm t).mono' ((hj.comp ((hx (t+1)).sub (hx t))).pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    simp only [Function.comp_def,Pi.sub_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hc := PiLp.norm_apply_le (x ω (t+1)-x ω t) j
    simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc
  have hbody (t) (j : Fin b) : (∫ ω,((x ω (t+1)-x ω t) (.inl j))^2 ∂P) ≤ A^2 := by
    have hh := integral_mono (hi t (.inl j)) (integrable_const (A^2)) (fun ω => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hA).mpr (hb ω t j))
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh
  have he (t) : (∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) =
      (∑ j : Fin b,∫ ω,((x ω (t+1)-x ω t) (.inl j))^2 ∂P)+
      (∑ j : Fin h,∫ ω,((x ω (t+1)-x ω t) (.inr j))^2 ∂P) := by
    simp_rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type]
    rw [integral_add (integrable_finsetSum _ (fun j _ => hi t (.inl j)))
      (integrable_finsetSum _ (fun j _ => hi t (.inr j))),
      integral_finsetSum _ (fun j _ => hi t (.inl j)),
      integral_finsetSum _ (fun j _ => hi t (.inr j))]
  calc
    _ = (∑ j : Fin b,∑ t ∈ Finset.range T,∫ ω,((x ω (t+1)-x ω t) (.inl j))^2 ∂P)+
        (∑ j : Fin h,∑ t ∈ Finset.range T,∫ ω,((x ω (t+1)-x ω t) (.inr j))^2 ∂P) := by
      simp_rw [he]
      rw [Finset.sum_add_distrib]
      congr 1 <;> exact Finset.sum_comm
    _ ≤ (∑ _j : Fin b,∑ _t ∈ Finset.range T,A^2)+(∑ _j : Fin h,H) :=
      add_le_add (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun t _ => hbody t j)
        (Finset.sum_le_sum fun j _ => hh j)
    _ = _ := by simp [mul_assoc]


lemma run_expected_movement_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (hr : 0 < cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {ξ : ℕ → Ξ → Ω}
    (ho : Measurable (Function.uncurry oracle)) (hξ : ∀ k,Measurable (ξ k))
    {ηb ηh V : ℝ} (hηb : ∀ n,cfg.bodyStep n=ηb) (hηh : ∀ n,cfg.headStep n=ηh) (T : ℕ)
    (hvi : ∀ j : Fin h,Integrable (fun ω => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) T).accumulator (.inr j)) P)
    (hV : ∀ j : Fin h,(∫ ω,(run cfg x₀ seed (fun k x => oracle x (ξ k ω)) T).accumulator (.inr j) ∂P) ≤ V) :
    (∑ t ∈ Finset.range T,∫ ω,‖(run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (t+1)).point-
      (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point‖^2 ∂P) ≤
      6400*b*T*ηb^2+h*ηh^2*Real.log (V/cfg.r₀^2) := by
  let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
  have hx (t) : Measurable (fun ω => x ω t) := (run_core_measurable cfg x₀ seed ho hξ t).1
  have hm (t) : Integrable (fun ω => ‖x ω (t+1)-x ω t‖^2) P := by
    simpa only [x,run_point] using
      (trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hξ (t+1) t P).integrable_sq
  have hbody (ω) (t) (j : Fin b) : |(x ω (t+1)-x ω t) (.inl j)| ≤ 80*|ηb| := by
    simpa [x,hηb] using run_body_increment cfg hα hβ hδ x₀ seed (fun k x => oracle x (ξ k ω)) t j
  have hi (t) (j : Fin h) : Integrable (fun ω => ((x ω (t+1)-x ω t) (.inr j))^2) P := by
    have hj : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
    apply (hm t).mono' ((hj.comp ((hx (t+1)).sub (hx t))).pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    simp only [Function.comp_def,Pi.sub_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hc := PiLp.norm_apply_le (x ω (t+1)-x ω t) (.inr j)
    simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc
  have hhead (j : Fin h) : (∑ t ∈ Finset.range T,∫ ω,((x ω (t+1)-x ω t) (.inr j))^2 ∂P) ≤
      ηh^2*Real.log (V/cfg.r₀^2) := by
    have hh := (expected_head_movement_log cfg hr x₀ seed ho hξ hηh T j (hvi j) (hV j)).2
    rw [← integral_finsetSum _ (fun t _ => hi t j)]
    exact hh
  have hh := expected_coordinate_movement_energy x T (show 0 ≤ 80*|ηb| by positivity) hx hm hbody hhead
  convert hh using 1
  simp only [mul_pow,sq_abs]
  ring


lemma integral_linear_root_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {G A : Ω → ℝ} {c N : ℝ}
    (hGm : AEStronglyMeasurable G P) (hG0 : ∀ ω,0 ≤ G ω)
    (hAi : Integrable A P) (hA0 : ∀ ω,0 ≤ A ω) (hN : 0 ≤ N)
    (hb : ∀ ω,G ω ≤ c*A ω+Real.sqrt (N*A ω)) :
    Integrable G P ∧ (∫ ω,G ω ∂P) ≤ c*(∫ ω,A ω ∂P)+Real.sqrt (N*(∫ ω,A ω ∂P)) := by
  have hr := integral_sqrt_le_sqrt_integral (hAi.const_mul N) (fun ω => mul_nonneg hN (hA0 ω))
  have hi := (hAi.const_mul c).add hr.1
  have hGi : Integrable G P := hi.mono' hGm (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hG0 ω)]
    exact hb ω)
  have hh := integral_mono hGi hi hb
  have he := integral_add (hAi.const_mul c) hr.1
  simp only [Pi.add_apply] at hh he
  rw [he,integral_const_mul] at hh
  have hroot := hr.2
  rw [integral_const_mul] at hroot
  exact ⟨hGi,by linarith⟩

lemma integral_square_product_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {G A R : Ω → ℝ}
    (hGm : AEStronglyMeasurable G P) (hG0 : ∀ ω,0 ≤ G ω)
    (hAi : Integrable A P) (hA0 : ∀ ω,0 ≤ A ω)
    (hRi : Integrable R P) (hR0 : ∀ ω,0 ≤ R ω)
    (hb : ∀ ω,(G ω)^2 ≤ A ω*R ω) :
    Integrable G P ∧ (∫ ω,G ω ∂P) ≤ Real.sqrt (∫ ω,A ω ∂P)*Real.sqrt (∫ ω,R ω ∂P) := by
  have hAm : AEStronglyMeasurable (fun ω => Real.sqrt (A ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hAi.aestronglyMeasurable
  have hRm : AEStronglyMeasurable (fun ω => Real.sqrt (R ω)) P :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hRi.aestronglyMeasurable
  have hA2 : MemLp (fun ω => Real.sqrt (A ω)) 2 P :=
    (memLp_two_iff_integrable_sq hAm).mpr (hAi.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hA0 ω)).symm))
  have hR2 : MemLp (fun ω => Real.sqrt (R ω)) 2 P :=
    (memLp_two_iff_integrable_sq hRm).mpr (hRi.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hR0 ω)).symm))
  have hprod := hA2.integrable_mul hR2
  have hp (ω) : G ω ≤ Real.sqrt (A ω)*Real.sqrt (R ω) := by
    rw [← Real.sqrt_mul (hA0 ω)]
    exact (Real.le_sqrt (hG0 ω) (mul_nonneg (hA0 ω) (hR0 ω))).mpr (hb ω)
  have hGi : Integrable G P := hprod.mono' hGm (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hG0 ω)]
    exact hp ω)
  have hc := LongTails.Proofs.AdaptiveHistoryTracking.integral_mul_le_square_moments
    hA2 hR2 (fun ω => Real.sqrt_nonneg (A ω)) (fun ω => Real.sqrt_nonneg (R ω))
  simp_rw [Real.sq_sqrt (hA0 _),Real.sq_sqrt (hR0 _)] at hc
  exact ⟨hGi,(integral_mono hGi hprod hp).trans hc⟩


lemma integral_head_root_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h T : ℕ}
    {R : Fin h → Ω → ℝ} {A N : Fin T → Fin h → Ω → ℝ} {r₀ σ : ℝ}
    (hRm : ∀ j,Measurable (R j)) (hR0 : ∀ j ω,0 ≤ R j ω)
    (hAi : ∀ t j,Integrable (A t j) P)
    (hσ0 : 0 ≤ σ) (hNm : ∀ t j,Measurable (N t j))
    (hNi : ∀ t,Integrable (fun ω => ∑ j,(N t j ω)^2) P)
    (hN : ∀ t,(∫ ω,∑ j,(N t j ω)^2 ∂P) ≤ σ^2)
    (hb : ∀ j ω,R j ω ≤ 2*r₀+(∑ t,A t j ω)+2*Real.sqrt (∑ t,(N t j ω)^2)) :
    Integrable (fun ω => ∑ j,R j ω) P ∧
      (∫ ω,∑ j,R j ω ∂P) ≤ 2*h*r₀+
        (∑ t,∑ j,∫ ω,A t j ω ∂P)+2*Real.sqrt h*σ*Real.sqrt T := by
  have hn := integral_temporal_noise_roots hσ0 hNm hNi hN
  have ha : Integrable (fun ω => ∑ j,∑ t,A t j ω) P :=
    integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun t _ => hAi t j))
  have hu := ((integrable_const (2*(h : ℝ)*r₀)).add ha).add (hn.1.const_mul 2)
  have hbound (ω) : (∑ j,R j ω) ≤ 2*h*r₀+(∑ j,∑ t,A t j ω)+2*(∑ j,Real.sqrt (∑ t,(N t j ω)^2)) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j ω)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,← Finset.mul_sum,mul_left_comm,mul_assoc] using hh
  have hrm : Measurable (fun ω => ∑ j,R j ω) := Finset.measurable_sum _ (fun j _ => hRm j)
  have hri : Integrable (fun ω => ∑ j,R j ω) P := hu.mono' hrm.aestronglyMeasurable (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg fun j _ => hR0 j ω)]
    exact hbound ω)
  have hh := integral_mono hri hu hbound
  have he1 := integral_add ((integrable_const (2*(h : ℝ)*r₀)).add ha) (hn.1.const_mul 2)
  have he2 := integral_add (integrable_const (2*(h : ℝ)*r₀)) ha
  simp only [Pi.add_apply] at hh he1 he2
  rw [he1,he2,integral_const_mul,integral_const] at hh
  simp only [probReal_univ,smul_eq_mul,one_mul] at hh
  have heA : (∫ ω,∑ j,∑ t,A t j ω ∂P) = ∑ t,∑ j,∫ ω,A t j ω ∂P := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun t _ => hAi t j))]
    simp_rw [integral_finsetSum _ (fun t _ => hAi t _)]
    exact Finset.sum_comm
  rw [heA,integral_const_mul] at hh
  exact ⟨hri,by linarith [hn.2]⟩


lemma integrable_sq_div_of_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {q r : Ω → ℝ} {B r₀ : ℝ}
    (hq : Measurable q) (hr : Measurable r) (hB : 0 ≤ B) (hr₀ : 0 < r₀)
    (hqb : ∀ ω,|q ω| ≤ B) (hrb : ∀ ω,r₀ ≤ r ω) :
    Integrable (fun ω => (q ω)^2/r ω) P := by
  have hm : Measurable (fun ω => (q ω)^2/r ω) := (hq.pow_const 2).div hr
  apply (show MemLp (fun ω => (q ω)^2/r ω) 1 P from MemLp.of_bound hm.aestronglyMeasurable
    (B^2/r₀) ?_).integrable (by norm_num)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (hr₀.le.trans (hrb ω)))]
  have hq2 : (q ω)^2 ≤ B^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hqb ω)
  exact div_le_div₀ (sq_nonneg _) hq2 hr₀ (hrb ω)

lemma iid_head_terminal_root_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hr₀ : 0 < cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {B σ : ℝ}
    (hB : 0 ≤ B) (hσ0 : 0 ≤ σ)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ z,Integrable (fun ω => ∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2) p)
    (hσ : ∀ z,(∫ ω,∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (T : ℕ)
    (hGB : ∀ (z : ℕ → Ω) (t : Fin T) (j : Fin h),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B) :
    let x := fun ω t => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t
    let r := fun ω t j => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
    Integrable (fun ω => ∑ j : Fin h,r ω T j) P ∧
      (∫ ω,∑ j : Fin h,r ω T j ∂P) ≤ 2*h*cfg.r₀+
        (∑ t : Fin T,∑ j : Fin h,∫ ω,(grad (x ω t) (.inr j))^2/r ω t j ∂P)+
        2*Real.sqrt h*σ*Real.sqrt T := by
  let x := fun ω t => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t
  let r := fun ω t j => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
  let A := fun (t : Fin T) (j : Fin h) ω => (grad (x ω t) (.inr j))^2/r ω t j
  let N := fun (t : Fin T) (j : Fin h) ω => (oracle (x ω t) (ξ t ω)-grad (x ω t)) (.inr j)
  have hx (t) : Measurable (fun ω => x ω t) := trajectory_measurable cfg x₀ ho hs.measurable t
  have hj (j : Fin h) : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
  have hrm (t) (j : Fin h) : Measurable (fun ω => r ω t j) :=
    ((hj j).comp (run_core_measurable cfg x₀ seed ho hs.measurable t).2.2).sqrt
  have hrb (ω) (t) (j : Fin h) : cfg.r₀ ≤ r ω t j := by
    have hv := run_head_accumulator_lower cfg x₀ seed (fun k x => oracle x (ξ k ω)) t j
    exact (Real.le_sqrt hr₀.le ((sq_nonneg cfg.r₀).trans hv)).mpr hv
  have hAi (t : Fin T) (j : Fin h) : Integrable (A t j) P :=
    integrable_sq_div_of_lower_bound ((hj j).comp (hg.comp (hx t))) (hrm t j) hB hr₀
      (fun ω => hGB (fun k => ξ k ω) t j) (fun ω => hrb ω t j)
  have hNm (t : Fin T) (j : Fin h) : Measurable (N t j) :=
    (hj j).comp ((ho.comp ((hx t).prodMk (hs.measurable t))).sub (hg.comp (hx t)))
  have hn (t : Fin T) := iid_head_noise_moment cfg x₀ a ho hg hi hσ hs t
  have hb (j : Fin h) (ω : Ξ) : r ω T j ≤ 2*cfg.r₀+(∑ t : Fin T,A t j ω)+
      2*Real.sqrt (∑ t : Fin T,(N t j ω)^2) := by
    simpa [r,A,N,x] using run_head_accumulator_energy cfg hr₀ x₀ seed
      (fun k x => oracle x (ξ k ω)) (fun t => grad (x ω t) (.inr j)) T j
  exact integral_head_root_energy (fun j => hrm T j) (fun j ω => Real.sqrt_nonneg _)
    hAi hσ0 hNm (fun t => (hn t).1) (fun t => (hn t).2) hb


lemma integral_head_time_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {T h : ℕ} {q r : Fin T → Fin h → Ω → ℝ} {R : Fin h → Ω → ℝ}
    (hqm : ∀ t j,Measurable (q t j)) (hr : ∀ t j ω,0 < r t j ω)
    (hR : ∀ t j ω,r t j ω ≤ R j ω) (hR0 : ∀ j ω,0 ≤ R j ω)
    (hAi : Integrable (fun ω => ∑ t,∑ j,(q t j ω)^2/r t j ω) P)
    (hRi : Integrable (fun ω => ∑ j,R j ω) P) :
    Integrable (fun ω => ∑ t,∑ j,|q t j ω|) P ∧
      (∫ ω,∑ t,∑ j,|q t j ω| ∂P) ≤ Real.sqrt T*
        Real.sqrt (∫ ω,∑ t,∑ j,(q t j ω)^2/r t j ω ∂P)*Real.sqrt (∫ ω,∑ j,R j ω ∂P) := by
  have hGm : Measurable (fun ω => ∑ t,∑ j,|q t j ω|) :=
    Finset.measurable_sum _ (fun t _ => Finset.measurable_sum _ (fun j _ => by simpa only [Real.norm_eq_abs] using (hqm t j).norm))
  have hG0 (ω) : 0 ≤ ∑ t,∑ j,|q t j ω| :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hA0 (ω) : 0 ≤ ∑ t,∑ j,(q t j ω)^2/r t j ω :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hr t j ω).le
  have hh := integral_square_product_bound hGm.aestronglyMeasurable hG0 hAi hA0
    (hRi.const_mul (T : ℝ)) (fun ω => mul_nonneg (Nat.cast_nonneg T) (Finset.sum_nonneg fun j _ => hR0 j ω))
    (fun ω => head_time_energy_bound (fun t j => q t j ω) (fun t j => r t j ω) (fun j => R j ω)
      (fun t j => hr t j ω) (fun t j => hR t j ω))
  refine ⟨hh.1,?_⟩
  have hb := hh.2
  rw [integral_const_mul,Real.sqrt_mul (Nat.cast_nonneg T)] at hb
  convert hb using 1
  ring


lemma integral_body_abs_sum_energy {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {q S d : ι → Ω → ℝ} {δ σ : ℝ}
    (hqm : ∀ i,Measurable (q i)) (hδ : 0 ≤ δ) (hσ : 0 ≤ σ)
    (hd : ∀ i ω,0 < d i ω) (hdδ : ∀ i ω,d i ω ≤ δ)
    (hS : ∀ i ω,0 ≤ S i ω) (hSum : ∀ ω,(∑ i,S i ω) ≤ σ)
    (hAi : Integrable (fun ω => ∑ i,(q i ω)^2/(d i ω+66*(|q i ω|+S i ω))) P) :
    Integrable (fun ω => ∑ i,|q i ω|) P ∧
      (∫ ω,∑ i,|q i ω| ∂P) ≤
        66*(∫ ω,∑ i,(q i ω)^2/(d i ω+66*(|q i ω|+S i ω)) ∂P)+
        Real.sqrt ((Fintype.card ι*δ+66*σ)*(∫ ω,∑ i,(q i ω)^2/(d i ω+66*(|q i ω|+S i ω)) ∂P)) := by
  have hm : Measurable (fun ω => ∑ i,|q i ω|) :=
    Finset.measurable_sum _ (fun i _ => by simpa only [Real.norm_eq_abs] using (hqm i).norm)
  have hA0 (ω) : 0 ≤ ∑ i,(q i ω)^2/(d i ω+66*(|q i ω|+S i ω)) :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _)
      (add_nonneg (hd i ω).le (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (hS i ω))))
  exact integral_linear_root_bound hm.aestronglyMeasurable
    (fun ω => Finset.sum_nonneg fun i _ => abs_nonneg _) hAi hA0 (by positivity)
    (fun ω => body_abs_sum_energy (fun i => q i ω) (fun i => S i ω) (fun i => d i ω)
      hδ hσ (fun i => hd i ω) (fun i => hdδ i ω) (fun i => hS i ω) (hSum ω))


lemma iid_head_coordinate_potential_sum {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hr₀ : 0 < cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {B σ η : ℝ}
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hηcfg : ∀ t,cfg.headStep t=η)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ x,Integrable (oracle x) p) (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=grad x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (T : ℕ) (j : Fin h)
    (hGB : ∀ (z : ℕ → Ω) (t : ℕ),t ≤ T →
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B) :
    let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
    let q := fun ω t => grad (x ω t) (.inr j)
    let r := fun ω t => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
    (∑ t ∈ Finset.range T,∫ ω,q ω t*(x ω (t+1)-x ω t) (.inr j) ∂P)+
      η/4*(∑ t ∈ Finset.range T,∫ ω,(q ω t)^2/r ω t ∂P) ≤
      η/(2*cfg.r₀)*(grad x₀ (.inr j))^2+
      3*η/2*(∑ t ∈ Finset.range T,∫ ω,(q ω t-q ω (t-1))^2/r ω t ∂P)+η*σ^2/(2*cfg.r₀) := by
  let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
  let q := fun ω t => grad (x ω t) (.inr j)
  let r := fun ω t => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
  let U := fun t => ∫ ω,q ω t*(x ω (t+1)-x ω t) (.inr j) ∂P
  let A := fun t => ∫ ω,(q ω t)^2/r ω t ∂P
  let C := fun t => ∫ ω,(q ω t-q ω (t-1))^2/r ω t ∂P
  let V := fun t => ∫ ω,(q ω (t-1))^2/r ω t ∂P
  let R := fun t => ∫ ω,1/r ω t ∂P
  have hj : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
  have hrm (t) : Measurable (fun ω => r ω t) :=
    (hj.comp (run_core_measurable cfg x₀ seed ho hs.measurable t).2.2).sqrt
  have hrb (ω) (t) : cfg.r₀ ≤ r ω t := by
    have hv := run_head_accumulator_lower cfg x₀ seed (fun k x => oracle x (ξ k ω)) t j
    exact (Real.le_sqrt hr₀.le ((sq_nonneg cfg.r₀).trans hv)).mpr hv
  have hri (t) : Integrable (fun ω => 1/r ω t) P := by
    apply (show MemLp (fun ω => 1/r ω t) 1 P from MemLp.of_bound
      (measurable_const.div (hrm t)).aestronglyMeasurable (1/cfg.r₀) ?_).integrable (by norm_num)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (by norm_num) (hr₀.le.trans (hrb ω t)))]
    exact one_div_le_one_div_of_le hr₀ (hrb ω t)
  have hstep (t) (ht : t<T) : U t ≤ -η/4*A t+η/2*(V t-V (t+1))+
      3*η/2*C t+η*σ^2/2*(R t-R (t+1)) := by
    have hh := iid_head_descent_step cfg hr₀ x₀ seed a hB ho hg hi hmean hni hσ hs t j
      (by rw [hηcfg]; exact hη) (fun z => hGB z t ht.le)
      (fun z => hGB z (t-1) ((Nat.sub_le _ _).trans ht.le))
    dsimp only at hh
    simp only [hηcfg] at hh
    have hrec := integral_sub (hri t) (hri (t+1))
    change (∫ ω,q ω t*((x ω (t+1)) (.inr j)-(x ω t) (.inr j)) ∂P) ≤
      -η/4*A t+η/2*(V t-(∫ ω,(q ω t)^2/r ω (t+1) ∂P))+
      3*η/2*C t+η*σ^2/2*(∫ ω,1/r ω t-1/r ω (t+1) ∂P) at hh
    rw [hrec] at hh
    simpa [U,A,V,C,R,Nat.add_sub_cancel] using hh
  have hv0 : 0 ≤ V T := integral_nonneg fun ω => div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hr0 : 0 ≤ R T := integral_nonneg fun ω => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hh := head_potential_sum U A C V R T hη hv0 hr0 hstep
  have hV0 : V 0=(grad x₀ (.inr j))^2/cfg.r₀ := by
    simp [V,q,x,r,run,initial,Real.sqrt_sq hr₀.le]
  have hR0 : R 0=1/cfg.r₀ := by
    simp [R,r,run,initial,Real.sqrt_sq hr₀.le]
  rw [hV0,hR0] at hh
  dsimp only
  change (∑ t ∈ Finset.range T,U t)+η/4*(∑ t ∈ Finset.range T,A t) ≤ _
  convert hh using 1
  ring


lemma integral_head_gradient_change_energy {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {b h : ℕ} {x y : Ω → Point b h} {r : Fin h → Ω → ℝ}
    {grad : Point b h → Point b h} {L r₀ : ℝ}
    (hx : Measurable x) (hy : Measurable y) (hrm : ∀ j,Measurable (r j)) (hgm : Measurable grad)
    (hL : 0 ≤ L) (hr₀ : 0 < r₀) (hg : ∀ u v,‖grad u-grad v‖ ≤ L*‖u-v‖)
    (hr : ∀ j ω,r₀ ≤ r j ω) (hm : Integrable (fun ω => ‖x ω-y ω‖^2) P) :
    (∀ j : Fin h,Integrable (fun ω => (grad (x ω) (.inr j)-grad (y ω) (.inr j))^2/r j ω) P) ∧
      (∑ j : Fin h,∫ ω,(grad (x ω) (.inr j)-grad (y ω) (.inr j))^2/r j ω ∂P) ≤
        L^2/r₀*(∫ ω,‖x ω-y ω‖^2 ∂P) := by
  let A := fun (j : Fin h) ω => (grad (x ω) (.inr j)-grad (y ω) (.inr j))^2/r j ω
  have hA0 (j) (ω) : 0 ≤ A j ω := div_nonneg (sq_nonneg _) (hr₀.le.trans (hr j ω))
  have hAm (j) : Measurable (A j) := by
    have hc : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
    exact (((hc.comp (hgm.comp hx)).sub (hc.comp (hgm.comp hy))).pow_const 2).div (hrm j)
  have hb (ω) : (∑ j,A j ω) ≤ L^2/r₀*‖x ω-y ω‖^2 := by
    calc
      _ ≤ ∑ j : Fin h,(grad (x ω) (.inr j)-grad (y ω) (.inr j))^2/r₀ :=
        Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_left (sq_nonneg _) hr₀ (hr j ω)
      _ = (∑ j : Fin h,(grad (x ω) (.inr j)-grad (y ω) (.inr j))^2)/r₀ := (Finset.sum_div _ _ _).symm
      _ ≤ (L^2*‖x ω-y ω‖^2)/r₀ := div_le_div_of_nonneg_right (head_gradient_change_sq hL hg (x ω) (y ω)) hr₀.le
      _ = _ := by ring
  have hAi (j) : Integrable (A j) P := (hm.const_mul (L^2/r₀)).mono' (hAm j).aestronglyMeasurable (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hA0 j ω)]
    exact (Finset.single_le_sum (fun i _ => hA0 i ω) (Finset.mem_univ j)).trans (hb ω))
  have hh := integral_mono (integrable_finsetSum _ (fun j _ => hAi j)) (hm.const_mul (L^2/r₀)) hb
  rw [integral_finsetSum _ (fun j _ => hAi j),integral_const_mul] at hh
  exact ⟨hAi,hh⟩


lemma expected_objective_increment_sum {Ω E : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : E → ℝ} {x : Ω → ℕ → E} {x₀ : E} {Δ : ℝ}
    (hinit : ∀ ω,x ω 0=x₀) (hgap : ∀ z,f x₀-f z ≤ Δ)
    (hi : ∀ t,Integrable (fun ω => f (x ω t)) P) (T : ℕ) :
    -Δ ≤ ∑ t ∈ Finset.range T,∫ ω,f (x ω (t+1))-f (x ω t) ∂P := by
  let F := fun t => ∫ ω,f (x ω t) ∂P
  have he (t) : (∫ ω,f (x ω (t+1))-f (x ω t) ∂P)=F (t+1)-F t := integral_sub (hi (t+1)) (hi t)
  have hsum (N) : (∑ t ∈ Finset.range N,(F (t+1)-F t))=F N-F 0 := by
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ,ih]; ring
  have hF0 : F 0=f x₀ := by simp [F,hinit]
  have hb := integral_mono (integrable_const (f x₀-Δ)) (hi T) (fun ω => by linarith [hgap (x ω T)])
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hb
  simp_rw [he]
  rw [hsum,hF0]
  dsimp [F]
  linarith

lemma run_expected_objective_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {f : Point b h → ℝ}
    {ξ : ℕ → Ξ → Ω} {B L Δ : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (ho : Measurable (Function.uncurry oracle)) (hgm : Measurable grad)
    (hg : ∀ x,HasGradientAt f (grad x) x)
    (hlip : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hξ : ∀ k,Measurable (ξ k)) (T : ℕ)
    (hGB : ∀ (z : ℕ → Ω) (t : ℕ),t<T → ∀ (j : Fin b ⊕ Fin h),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) j| ≤ B) :
    let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
    (-Δ) ≤ (∑ t ∈ Finset.range T,∑ j : Fin b,∫ ω,grad (x ω t) (.inl j)*(x ω (t+1)-x ω t) (.inl j) ∂P)+
      (∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,grad (x ω t) (.inr j)*(x ω (t+1)-x ω t) (.inr j) ∂P)+
      L/2*(∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
  let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
  have hx (t) : Measurable (fun ω => x ω t) := (run_core_measurable cfg x₀ seed ho hξ t).1
  have hfi (t) : Integrable (fun ω => f (x ω t)) P :=
    objective_integrable_of_bounded_displacement hg hlip hL
      (Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _) hgap (hx t)
      (fun ω => run_displacement_sum cfg hα hβ hδ x₀ seed (fun k x => oracle x (ξ k ω)) t)
  have hlower := expected_objective_increment_sum (fun ω => rfl) hgap hfi T
  have hstep (t) (ht : t<T) := run_expected_block_smoothness (P := P) cfg hα hβ hδ x₀ seed hB hL ho hgm hg hlip hgap hξ t
    (fun z j => hGB z t ht j)
  have hsum := Finset.sum_le_sum (s := Finset.range T) (fun t ht => hstep t (Finset.mem_range.mp ht))
  dsimp only at hsum
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  exact hlower.trans hsum



lemma iid_head_total_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (hr₀ : 0 < cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {B σ η L : ℝ}
    (hB : 0 ≤ B) (hη : 0 ≤ η) (hηcfg : ∀ t,cfg.headStep t=η) (hL : 0 ≤ L)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖)
    (hi : ∀ x,Integrable (oracle x) p) (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=grad x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (T : ℕ)
    (hGB : ∀ (z : ℕ → Ω) (t : ℕ),t ≤ T → ∀ (j : Fin h),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B) :
    let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
    let r := fun ω t j => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
    (∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,grad (x ω t) (.inr j)*(x ω (t+1)-x ω t) (.inr j) ∂P)+
      η/4*(∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(grad (x ω t) (.inr j))^2/r ω t j ∂P) ≤
      η/(2*cfg.r₀)*‖grad x₀‖^2+
      (3*η*L^2/(2*cfg.r₀))*(∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P)+η*h*σ^2/(2*cfg.r₀) := by
  let x := fun ω t => (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point
  let r := fun ω t j => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
  let U := fun t (j : Fin h) => ∫ ω,grad (x ω t) (.inr j)*(x ω (t+1)-x ω t) (.inr j) ∂P
  let A := fun t (j : Fin h) => ∫ ω,(grad (x ω t) (.inr j))^2/r ω t j ∂P
  let C := fun t (j : Fin h) => ∫ ω,(grad (x ω t) (.inr j)-grad (x ω (t-1)) (.inr j))^2/r ω t j ∂P
  have hper (j : Fin h) : (∑ t ∈ Finset.range T,U t j)+η/4*(∑ t ∈ Finset.range T,A t j) ≤
      η/(2*cfg.r₀)*(grad x₀ (.inr j))^2+3*η/2*(∑ t ∈ Finset.range T,C t j)+η*σ^2/(2*cfg.r₀) :=
    iid_head_coordinate_potential_sum cfg hr₀ x₀ seed a hB hη hηcfg ho hg hi hmean hni hσ hs T j
      (fun z t ht => hGB z t ht j)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hper j)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at hsum
  have heU : (∑ j : Fin h,∑ t ∈ Finset.range T,U t j)=∑ t ∈ Finset.range T,∑ j : Fin h,U t j := Finset.sum_comm
  have heA : (∑ j : Fin h,∑ t ∈ Finset.range T,A t j)=∑ t ∈ Finset.range T,∑ j : Fin h,A t j := Finset.sum_comm
  have heC : (∑ j : Fin h,∑ t ∈ Finset.range T,C t j)=∑ t ∈ Finset.range T,∑ j : Fin h,C t j := Finset.sum_comm
  rw [heU,heA,heC] at hsum
  have hx (t) : Measurable (fun ω => x ω t) := (run_core_measurable cfg x₀ seed ho hs.measurable t).1
  have hj (j : Fin h) : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
  have hrm (t) (j : Fin h) : Measurable (fun ω => r ω t j) :=
    ((hj j).comp (run_core_measurable cfg x₀ seed ho hs.measurable t).2.2).sqrt
  have hrb (ω) (t) (j : Fin h) : cfg.r₀ ≤ r ω t j := by
    have hv := run_head_accumulator_lower cfg x₀ seed (fun k x => oracle x (ξ k ω)) t j
    exact (Real.le_sqrt hr₀.le ((sq_nonneg cfg.r₀).trans hv)).mpr hv
  have hm (t s) : Integrable (fun ω => ‖x ω t-x ω s‖^2) P := by
    simpa only [x,run_point] using (trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hs.measurable t s P).integrable_sq
  have hc (t) : (∑ j : Fin h,C t j) ≤ L^2/cfg.r₀*(∫ ω,‖x ω t-x ω (t-1)‖^2 ∂P) :=
    (integral_head_gradient_change_energy (hx t) (hx (t-1)) (hrm t) hg hL hr₀ hgrad
      (fun j ω => hrb ω t j) (hm t (t-1))).2
  have hCsum : (∑ t ∈ Finset.range T,∑ j : Fin h,C t j) ≤
      L^2/cfg.r₀*(∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T,L^2/cfg.r₀*(∫ ω,‖x ω t-x ω (t-1)‖^2 ∂P) := Finset.sum_le_sum fun t _ => hc t
      _ = L^2/cfg.r₀*(∑ t ∈ Finset.range T,∫ ω,‖x ω t-x ω (t-1)‖^2 ∂P) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (expected_preceding_path_energy_le x T (fun t => hm (t+1) t)) (by positivity)
  have hinit := mul_le_mul_of_nonneg_left (sum_head_sq_le_norm_sq (grad x₀)) (show 0 ≤ η/(2*cfg.r₀) by positivity)
  have hcharge := mul_le_mul_of_nonneg_left hCsum (show 0 ≤ 3*η/2 by positivity)
  dsimp only
  change (∑ t ∈ Finset.range T,∑ j : Fin h,U t j)+η/4*(∑ t ∈ Finset.range T,∑ j : Fin h,A t j) ≤ _
  convert hsum.trans (add_le_add_left (add_le_add hinit hcharge) ((h : ℝ)*(η*σ^2/(2*cfg.r₀)))) using 1
  ring



lemma iid_body_lagged_descent_step {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {L B : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (t k : ℕ) (hk : 2 ≤ k) (hkt : k ≤ t) (j : Fin b)
    (hGB : ∀ (z : ℕ → Ω) (u : ℕ),u ≤ t →
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B)
    (hsym : ∀ x,(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j))) (hη : 0 ≤ cfg.bodyStep t) :
    let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
    let δₜ := cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let A := fun ω => (grad (x (t-k) ω) (.inl j))^2/
      (δₜ+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p)))
    Integrable A P ∧
      (∫ ω,grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) ∂P) ≤
        -(cfg.bodyStep t)/3000*(∫ ω,A ω ∂P)+
        10*cfg.bodyStep t*(∫ ω,bodyWindowError cfg x₀ seed oracle grad δₜ (t-k) (t-k+1) k j (fun r => ξ r ω) ∂P)+
        80*cfg.bodyStep t*L*(∫ ω,‖x t ω-x (t-k) ω‖ ∂P) := by
  have ht : (t-k+1)+(k-2)+1=t := by omega
  have hn : k-2+2=k := by omega
  have hh := iid_body_descent_step (m := t-k+1) (n := k-2) cfg hα hβ hδ x₀ seed a ho hg hi hgrad hL hB hs
    (t-k) (by omega) j (fun z => hGB z (t-k) (Nat.sub_le _ _))
    (fun z => by simpa only [ht] using hGB z t le_rfl) hsym (by simpa only [ht] using hη)
  dsimp only at hh ⊢
  simp only [ht,hn] at hh
  let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
  let δₜ := cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let A := fun ω => (grad (x (t-k) ω) (.inl j))^2/
    (δₜ+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p)))
  let Ψ := fun ω => (grad (x (t-k) ω) (.inl j))^2/
    (90*(δₜ+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))))
  have he (ω) : A ω=90*Ψ ω := by
    dsimp [A,Ψ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hAi : Integrable A P := (hh.2.1.const_mul 90).congr (Filter.Eventually.of_forall fun ω => (he ω).symm)
  have hI : (∫ ω,A ω ∂P)=90*(∫ ω,Ψ ω ∂P) := by
    rw [show A=(fun ω => 90*Ψ ω) from funext he,integral_const_mul]
  refine ⟨hAi,?_⟩
  change (∫ ω,grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) ∂P) ≤
    -(cfg.bodyStep t)/3000*(∫ ω,A ω ∂P)+
    10*cfg.bodyStep t*(∫ ω,bodyWindowError cfg x₀ seed oracle grad δₜ (t-k) (t-k+1) k j (fun r => ξ r ω) ∂P)+
    80*cfg.bodyStep t*L*(∫ ω,‖x t ω-x (t-k) ω‖ ∂P)
  rw [hI]
  convert hh.2.2 using 1
  ring



lemma run_body_descent_upper {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {ξ : ℕ → Ξ → Ω} {B : ℝ} (hB : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hξ : ∀ k,Measurable (ξ k)) (t : ℕ)
    (hGB : ∀ (z : ℕ → Ω) (j : Fin b),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inl j)| ≤ B) :
    (∑ j : Fin b,∫ ω,
      grad (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point (.inl j)*
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (t+1)).point-
        (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point) (.inl j) ∂P) ≤
      80*b*|cfg.bodyStep t| * B := by
  have hp (j : Fin b) : (∫ ω,
      grad (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point (.inl j)*
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) (t+1)).point-
        (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point) (.inl j) ∂P) ≤ B*(80*|cfg.bodyStep t|) := by
    have hi := run_gradient_increment_integrable (P := P) cfg hα hβ hδ x₀ seed hB ho hg hξ t (.inl j) (fun z => hGB z j)
    have he := integral_mono hi (integrable_const (B*(80*|cfg.bodyStep t|))) (fun ω => by
      have h1 : |grad (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).point (.inl j)| ≤ B := by
        simpa only [run_point] using hGB (fun k => ξ k ω) j
      have h2 := run_body_increment cfg hα hβ hδ x₀ seed (fun k x => oracle x (ξ k ω)) t j
      exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) hB))
    simpa using he
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
  convert he using 1
  ring



lemma sum_late_range_shift (F : ℕ → ℝ) (T k : ℕ) :
    (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),F t)=
      ∑ s ∈ Finset.range (T-k),F (s+k) := by
  apply Finset.sum_bij (fun t _ => t-k)
  · intro t ht
    simp only [Finset.mem_filter,Finset.mem_range] at ht ⊢
    omega
  · intro t ht u hu he
    simp only [Finset.mem_filter,Finset.mem_range] at ht hu
    omega
  · intro s hs
    refine ⟨s+k,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_range] at hs ⊢
      omega
    · omega
  · intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    rw [Nat.sub_add_cancel ht']

lemma expected_late_windows_root_sum {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} (x : Ω → ℕ → E) (T k r : ℕ) (hr : r ≤ k)
    (hm : ∀ t s,Integrable (fun ω => ‖x ω t-x ω s‖^2) P) :
    (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),
      Real.sqrt (∫ ω,‖x ω (t-k+r)-x ω (t-k)‖^2 ∂P)) ≤
      k*Real.sqrt T*Real.sqrt (∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
  by_cases hk : k ≤ T
  · rw [sum_late_range_shift]
    simp only [Nat.add_sub_cancel]
    have hh := expected_path_windows_root_sum x (T-k) r (fun t => hm (t+r) t) (fun t => hm (t+1) t)
    have hsum : (∑ t ∈ Finset.range (T-k+r),∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) ≤
        ∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro t ht hnot
      exact integral_nonneg fun ω => sq_nonneg _
    have hkr : (r : ℝ) ≤ k := by exact_mod_cast hr
    have hTk : Real.sqrt (T-k : ℕ) ≤ Real.sqrt T := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le T k)
    exact hh.trans (mul_le_mul (mul_le_mul hkr hTk (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
      (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _) (by positivity))
  · have he : (Finset.range T).filter (fun t => k ≤ t)=∅ := by
      ext t
      simp only [Finset.mem_filter,Finset.mem_range,Finset.notMem_empty,iff_false]
      omega
    rw [he,Finset.sum_empty]
    positivity

lemma expected_late_windows_norm_sum {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {P : Measure Ω} [IsProbabilityMeasure P]
    (x : Ω → ℕ → E) (T k : ℕ)
    (hm : ∀ t s,Integrable (fun ω => ‖x ω t-x ω s‖^2) P) :
    (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),
      ∫ ω,‖x ω t-x ω (t-k)‖ ∂P) ≤
      k*Real.sqrt T*Real.sqrt (∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
  have hb := expected_late_windows_root_sum x T k k le_rfl hm
  refine le_trans (Finset.sum_le_sum (fun t ht => ?_)) hb
  have ht' := (Finset.mem_filter.mp ht).2
  rw [Nat.sub_add_cancel ht']
  have he := (integral_sqrt_le_sqrt_integral (hm t (t-k)) (fun ω => sq_nonneg _)).2
  simpa only [Real.sqrt_sq (norm_nonneg _)] using he

lemma expected_weighted_late_windows {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [Fintype ι] {P : Measure Ω}
    (x : Ω → ℕ → E) (T k : ℕ) (r : ι → ℕ) (w : ι → ℝ) {C : ℝ}
    (hr : ∀ i,r i ≤ k) (hw : ∀ i,0 ≤ w i) (hC : ∑ i,w i ≤ C)
    (hm : ∀ t s,Integrable (fun ω => ‖x ω t-x ω s‖^2) P) :
    (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ i,
      w i*Real.sqrt (∫ ω,‖x ω (t-k+r i)-x ω (t-k)‖^2 ∂P)) ≤
      C*k*Real.sqrt T*Real.sqrt (∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have he := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (expected_late_windows_root_sum x T k (r i) (hr i) hm) (hw i))
  have hb := mul_le_mul_of_nonneg_right hC
    (show 0 ≤ k*Real.sqrt T*Real.sqrt (∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P) by positivity)
  rw [← Finset.sum_mul] at he
  exact he.trans (by nlinarith [hb])



lemma iid_body_window_tracking_sum {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h m n : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hcfgδ : 0 < cfg.δ)
    (x₀ : Point b h) (a : Ω) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {K : Ω → ℝ}
    {L μ B δ : ℝ} (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-grad x) (.inl j)-(oracle y ω-grad y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hμ : (∫ ω,K ω ∂p) ≤ μ)
    (hL : 0 ≤ L) (hB : 0 ≤ B) (hδ : 0 < δ) (s : ℕ) (hs : s ≤ m)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hGB : ∀ (z : ℕ → Ω) (j : Fin b),|grad (trajectory cfg x₀ (fun k x => oracle x (z k)) s) (.inl j)| ≤ B)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    {V : ℝ}
    (hVi : Integrable (fun ω => ∑ j : Fin b,Real.sqrt
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) m).accumulator (.inl j))) P)
    (hV : (∫ ω,∑ j : Fin b,Real.sqrt
      ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) m).accumulator (.inl j)) ∂P) ≤ V) :
    Integrable (fun ω => ∑ j : Fin b,bodyWindowError cfg x₀ seed oracle grad δ s m (n+1) j (fun k => ξ k ω)) P ∧
    (∑ j : Fin b,∫ ω,bodyWindowError cfg x₀ seed oracle grad δ s m (n+1) j (fun k => ξ k ω) ∂P) ≤
      16*((L+μ)*127*b*(∑ i : Fin (n+1),Real.sqrt ((1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))*
        Real.sqrt (∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) (m+i.rev)-
          trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) s‖^2 ∂P))+b*B*((n+1)*(1/2 : ℝ)^n))+
      16*(127*Real.sqrt ((999/1000 : ℝ)^(n+1))*V+b*B*(1/2 : ℝ)^(n+1)) := by
  have hm (j : Fin b) : Measurable (fun ω =>
      (run cfg x₀ seed (fun k x => oracle x (ξ k ω)) m).accumulator (.inl j)) := by
    have hj : Measurable (fun z : Point b h => z (.inl j)) := by fun_prop
    exact hj.comp (run_core_measurable cfg x₀ seed ho hsamples.measurable m).2.2
  have hroots := integrable_scaled_coordinate_roots (show 0 ≤ (999/1000 : ℝ)^(n+1) by positivity) hm hVi hV
  have hp (j : Fin b) := iid_body_window_tracking cfg hα hβ hcfgδ x₀ a seed ho hg hgrad hnoise hK hK0 hμ
    hL hB hδ s hs j (fun x => hsym x j) (fun z => hGB z j) hsamples (hroots.1 j)
  refine ⟨integrable_finsetSum _ (fun j _ => (hp j).1),?_⟩
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hp j).2)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at he
  have hb := mul_le_mul_of_nonneg_left hroots.2 (show (0 : ℝ) ≤ 16*127 by norm_num)
  nlinarith [he,hb]



lemma iid_body_total_tracking {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ} (cfg : Config)
    (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hcfgδ : 0 < cfg.δ)
    (x₀ : Point b h) (a : Ω) (seed : Fin (cfg.lastIndex+1))
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {K : Ω → ℝ}
    {L μ B σ : ℝ} (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-grad x) (.inl j)-(oracle y ω-grad y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hμ : (∫ ω,K ω ∂p) ≤ μ)
    (hL : 0 ≤ L) (hM : 0 ≤ μ) (hB : 0 ≤ B) (hσ0 : 0 ≤ σ) (T n : ℕ)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hGB : ∀ (z : ℕ → Ω) (t : ℕ),t<T → ∀ j : Fin b,
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inl j)| ≤ B)
    (hσ : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-grad x) (.inl j)| ∂p) ≤ σ)
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) :
    let x := fun ω t => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    (∑ t ∈ (Finset.range T).filter (fun t => n+1 ≤ t),∑ j : Fin b,
      ∫ ω,bodyWindowError cfg x₀ seed oracle grad (δₜ t) (t-(n+1)) (t-(n+1)+1) (n+1) j (fun k => ξ k ω) ∂P) ≤
      130048*(L+μ)*b*(n+1)*Real.sqrt T*
        Real.sqrt (∑ t ∈ Finset.range T,∫ ω,‖x ω (t+1)-x ω t‖^2 ∂P)+
      16*b*B*T*((n+1)*(1/2 : ℝ)^n+(1/2 : ℝ)^(n+1))+
      130048*Real.sqrt ((999/1000 : ℝ)^(n+1))*T*(b*B+σ) := by
  let x := fun ω t => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t
  let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let w := fun i : Fin (n+1) => Real.sqrt ((1-(999/1000 : ℝ))*(999/1000 : ℝ)^(i : ℕ))
  let D := fun t => ∑ i : Fin (n+1),w i*Real.sqrt (∫ ω,‖x ω (t-(n+1)+(i.rev+1))-x ω (t-(n+1))‖^2 ∂P)
  let W := fun t => ∑ j : Fin b,∫ ω,bodyWindowError cfg x₀ seed oracle grad (δₜ t)
    (t-(n+1)) (t-(n+1)+1) (n+1) j (fun k => ξ k ω) ∂P
  let C := 16*b*B*((n+1)*(1/2 : ℝ)^n+(1/2 : ℝ)^(n+1))+
    130048*Real.sqrt ((999/1000 : ℝ)^(n+1))*(b*B+σ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hper (t) (ht : t<T) (htn : n+1 ≤ t) : W t ≤ 16*(L+μ)*127*b*D t+C := by
    have hmle : t-(n+1)+1 ≤ t := by omega
    have hv := iid_body_accumulator_sum_root_moment cfg hβ x₀ seed a ho hi
      (show 0 ≤ (b : ℝ)*B+σ by positivity) hσ hsamples (t-(n+1)+1)
      (fun u hu z j => hGB z u (by omega) j)
    have hδt : 0 < δₜ t := mul_pos hcfgδ (Real.sqrt_pos.mpr (default_bias_parameters t).2.1)
    have he := (iid_body_window_tracking_sum (m := t-(n+1)+1) (n := n) cfg hα hβ hcfgδ x₀ a seed
      ho hg hgrad hnoise hK hK0 hμ hL hB hδt (t-(n+1)) (by omega) hsym
      (fun z j => hGB z (t-(n+1)) (by omega) j) hsamples hv.1 hv.2).2
    have hi' (i : Fin (n+1)) : t-(n+1)+1+i.rev=t-(n+1)+(i.rev+1) := by omega
    simp only [hi'] at he
    change W t ≤ 16*((L+μ)*127*b*D t+b*B*((n+1)*(1/2 : ℝ)^n))+
      16*(127*Real.sqrt ((999/1000 : ℝ)^(n+1))*(64*(b*B+σ))+b*B*(1/2 : ℝ)^(n+1)) at he
    dsimp only [C]
    nlinarith [he]
  have hm (t s) : Integrable (fun ω => ‖x ω t-x ω s‖^2) P :=
    (trajectory_displacement_memLp cfg hα hβ hcfgδ x₀ ho hsamples.measurable t s P).integrable_sq
  have hw : (∑ i : Fin (n+1),w i) ≤ 64 :=
    (LongTails.Proofs.AdaptiveHistoryFinite.geometric_root_sum_le (n+1)
      (by norm_num : (0 : ℝ) ≤ 999/1000) (by norm_num : (999/1000 : ℝ) < 1)).trans
      LongTails.Proofs.AdaptiveHistoryFinite.default_geometric_root_constant
  have hD := expected_weighted_late_windows x T (n+1) (fun i : Fin (n+1) => i.rev+1) w
    (fun i => by have hh := i.rev.isLt; omega) (fun i => Real.sqrt_nonneg _) hw hm
  have he := Finset.sum_le_sum (s := (Finset.range T).filter (fun t => n+1 ≤ t))
    (fun t ht => hper t (Finset.mem_range.mp (Finset.mem_filter.mp ht).1) (Finset.mem_filter.mp ht).2)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at he
  have hc : (((Finset.range T).filter (fun t => n+1 ≤ t)).card : ℝ) ≤ T := by
    exact_mod_cast (Finset.card_filter_le (Finset.range T) (fun t => n+1 ≤ t)).trans_eq (Finset.card_range T)
  have hc' := mul_le_mul_of_nonneg_right hc hC
  have hd' := mul_le_mul_of_nonneg_left hD (show 0 ≤ 16*(L+μ)*127*b by positivity)
  dsimp only
  change (∑ t ∈ (Finset.range T).filter (fun t => n+1 ≤ t),W t) ≤ _
  dsimp only [D] at he
  dsimp [C] at hc'
  push_cast at he hc' hd' ⊢
  nlinarith [he,hc',hd']



lemma iid_body_total_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {L B B₀ η : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (T k : ℕ) (hk : 2 ≤ k)
    (hGB : ∀ (z : ℕ → Ω) (u : ℕ),u<T → ∀ j : Fin b,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B)
    (hGB₀ : ∀ (z : ℕ → Ω) (u : ℕ),u<min k T → ∀ j : Fin b,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B₀)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hη : 0 ≤ η) (hηcfg : ∀ t,cfg.bodyStep t=η) :
    let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let A := fun t => ∑ j : Fin b,∫ ω,(grad (x (t-k) ω) (.inl j))^2/
      (δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))) ∂P
    let W := fun t => ∑ j : Fin b,∫ ω,bodyWindowError cfg x₀ seed oracle grad (δₜ t) (t-k) (t-k+1) k j (fun r => ξ r ω) ∂P
    (∑ t ∈ Finset.range T,∑ j : Fin b,∫ ω,grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) ∂P)+
      η/3000*(∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),A t) ≤
      80*b*η*B₀*(min k T : ℕ)+10*η*(∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),W t)+
        80*η*b*L*(∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∫ ω,‖x t ω-x (t-k) ω‖ ∂P) := by
  let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
  let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let A := fun t => ∑ j : Fin b,∫ ω,(grad (x (t-k) ω) (.inl j))^2/
    (δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))) ∂P
  let W := fun t => ∑ j : Fin b,∫ ω,bodyWindowError cfg x₀ seed oracle grad (δₜ t) (t-k) (t-k+1) k j (fun r => ξ r ω) ∂P
  let D := fun t => ∫ ω,‖x t ω-x (t-k) ω‖ ∂P
  let U := fun t => ∑ j : Fin b,∫ ω,grad (x t ω) (.inl j)*(x (t+1) ω (.inl j)-x t ω (.inl j)) ∂P
  have hearly (t) (ht : t<T) (htk : t<k) : U t ≤ 80*b*η*B₀ := by
    have he := run_body_descent_upper (P := P) cfg hα hβ hδ x₀ seed hB₀ ho hg hs.measurable t
      (fun z j => hGB₀ z t (by omega) j)
    simpa only [U,x,run_point,PiLp.sub_apply,hηcfg,abs_of_nonneg hη] using he
  have hlate (t) (ht : t<T) (htk : k ≤ t) : U t+η/3000*A t ≤ 10*η*W t+80*η*b*L*D t := by
    have hp (j : Fin b) := (iid_body_lagged_descent_step cfg hα hβ hδ x₀ seed a ho hg hi hgrad hL hB hs t k hk htk j
      (fun z u hu => hGB z u (by omega) j) (fun z => hsym z j) (by rw [hηcfg]; exact hη)).2
    have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
    dsimp only at he
    simp only [hηcfg,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at he
    change U t ≤ -η/3000*A t+10*η*W t+80*η*L*((b : ℝ)*D t) at he
    nlinarith [he]
  have he := prefix_late_energy_sum U A (fun t => 10*η*W t+80*η*b*L*D t) T k hearly hlate
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at he
  dsimp only
  change (∑ t ∈ Finset.range T,U t)+η/3000*(∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),A t) ≤ _
  convert he using 1
  ring



lemma iid_hybrid_total_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ) (hr₀ : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {f : Point b h → ℝ} {L B B₀ ηb ηh σ Δ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hf : ∀ x,HasGradientAt f (grad x) x) (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=grad x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2 ∂p) ≤ σ^2)
    (T k : ℕ) (hk : 2 ≤ k)
    (hGB : ∀ (z : ℕ → Ω) (u : ℕ),u ≤ T → ∀ j : Fin b ⊕ Fin h,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) j| ≤ B)
    (hGB₀ : ∀ (z : ℕ → Ω) (u : ℕ),u<min k T → ∀ j : Fin b,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B₀)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hηb : 0 ≤ ηb) (hηbcfg : ∀ t,cfg.bodyStep t=ηb)
    (hηh : 0 ≤ ηh) (hηhcfg : ∀ t,cfg.headStep t=ηh) :
    let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let Ab := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,∫ ω,
      (grad (x (t-k) ω) (.inl j))^2/(δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+
        (∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))) ∂P
    let Ah := ∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(grad (x t ω) (.inr j))^2/
      Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
    let W := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,
      ∫ ω,bodyWindowError cfg x₀ seed oracle grad (δₜ t) (t-k) (t-k+1) k j (fun r => ξ r ω) ∂P
    let D := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∫ ω,‖x t ω-x (t-k) ω‖ ∂P
    let S := ∑ t ∈ Finset.range T,∫ ω,‖x (t+1) ω-x t ω‖^2 ∂P
    ηb/3000*Ab+ηh/4*Ah ≤ Δ+80*b*ηb*B₀*(min k T : ℕ)+10*ηb*W+80*ηb*b*L*D+
      ηh/(2*cfg.r₀)*‖grad x₀‖^2+ηh*h*σ^2/(2*cfg.r₀)+(L/2+3*ηh*L^2/(2*cfg.r₀))*S := by
  have hobj := run_expected_objective_energy (P := P) cfg hα hβ hδ x₀ seed hB hL ho hg hf hgrad hgap hs.measurable T
    (fun z t ht j => hGB z t (Nat.le_of_lt ht) j)
  have hbody := iid_body_total_energy cfg hα hβ hδ x₀ seed a ho hg hi hgrad hL hB hB₀ hs T k hk
    (fun z t ht j => hGB z t (Nat.le_of_lt ht) (.inl j)) hGB₀ hsym hηb hηbcfg
  have hhead := iid_head_total_energy cfg hα hβ hδ hr₀ x₀ seed a hB hηh hηhcfg hL ho hg hgrad hi hmean hni hσ hs T
    (fun z t ht j => hGB z t ht (.inr j))
  dsimp only at hobj hbody hhead ⊢
  simp only [run_point,PiLp.sub_apply] at hobj hhead
  linarith [hobj,hbody,hhead]



lemma iid_preliminary_movement_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (hr : 1 ≤ cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h}
    {B σ H ηb ηh q : ℝ} (hB0 : 0 ≤ B)
    (ho : Measurable (Function.uncurry oracle))
    (hi : ∀ z,Integrable (oracle z) p) (hmean : ∀ z,(∫ ω,oracle z ω ∂p)=grad z)
    (hni : ∀ z,Integrable (fun ω => ∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2) p)
    (hσ : ∀ z,(∫ ω,∑ i : Fin h,((oracle z ω-grad z) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hηb : ∀ t,cfg.bodyStep t=ηb) (hηh : ∀ t,cfg.headStep t=ηh)
    (T : ℕ) (hT : 1 ≤ T) (hHr : 2*H ≤ cfg.r₀) (hσr : 0<h → σ^2 ≤ cfg.r₀)
    (hB : B^2 ≤ 6889*H*T^2)
    (hGB : ∀ (z : ℕ → Ω) (t : ℕ),t<T → ∀ j : Fin h,
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B)
    (hscale : ((b : ℝ)+h)*ηh^2=q^2) (hstep : (T : ℝ)*ηb^2=ηh^2) :
    (∑ t ∈ Finset.range T,∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) (t+1)-
      trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t‖^2 ∂P) ≤ 6500*q^2*Real.log (10*T) := by
  have hr0 : 0 < cfg.r₀ := by linarith
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := by linarith
  have hm (j : Fin h) := iid_head_accumulator_moment cfg x₀ seed a hB0 ho hi hmean hni hσ hs T j
    (fun t ht z => hGB z t ht j)
  have hV (j : Fin h) : (∫ ω,(run cfg x₀ seed (fun k x => oracle x (ξ k ω)) T).accumulator (.inr j) ∂P) ≤
      4000*cfg.r₀^2*T^3 := by
    have he := preliminary_head_accumulator_ratio hr hT' hHr (hσr (by have hh := j.isLt; omega)) hB (hm j).2
    have he' := (div_le_iff₀ (sq_pos_of_pos hr0)).mp he
    nlinarith [he']
  have he := run_expected_movement_energy cfg hα hβ hδ hr0 x₀ seed ho hs.measurable hηb hηh T
    (fun j => (hm j).1) hV
  have hx : 4000*cfg.r₀^2*(T : ℝ)^3/cfg.r₀^2=4000*(T : ℝ)^3 := by field_simp
  rw [hx] at he
  have hl := log_poly_accumulator_bound (show 0 < 4000*(T : ℝ)^3 by positivity) hT' le_rfl
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ (h : ℝ)*ηh^2 by positivity)
  have hten : (1 : ℝ) ≤ Real.log 10 := by
    have hh := Real.le_log_one_add_of_nonneg (by norm_num : (0 : ℝ) ≤ 9)
    norm_num at hh
    linarith
  have hell : (1 : ℝ) ≤ Real.log (10*T) := hten.trans (Real.log_le_log (by norm_num) (by linarith))
  have he' : (∑ t ∈ Finset.range T,∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) (t+1)-
      trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t‖^2 ∂P) ≤
      6400*b*T*ηb^2+12*h*ηh^2*Real.log (10*T) := by
    simp only [run_point] at he
    nlinarith [he,hmul]
  exact preliminary_movement_energy_bound (Nat.cast_nonneg b) (Nat.cast_nonneg h) hell hscale hstep he'



lemma iid_tuned_movement_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a₀ : Ω)
    {oracle : Point b h → Ω → Point b h} {f : Point b h → ℝ} {L Δ σ : ℝ}
    (hL : 0 < L) (hΔ : 0 < Δ) (hd : 0 < b+h)
    (hg : ∀ x,HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hgap : ∀ x,f x₀-f x ≤ Δ)
    (ho : Measurable (Function.uncurry oracle))
    (hi : ∀ z,Integrable (oracle z) p) (hmean : ∀ z,(∫ ω,oracle z ω ∂p)=gradient f z)
    (hni : ∀ z,Integrable (fun ω => ∑ i : Fin h,((oracle z ω-gradient f z) (.inr i))^2) p)
    (hσ : ∀ z,(∫ ω,∑ i : Fin h,((oracle z ω-gradient f z) (.inr i))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (T : ℕ) (hT : 1 ≤ T) (hr : cfg.r₀=1+2*L*Δ+h*σ^2)
    (hηb : ∀ t,cfg.bodyStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))/Real.sqrt T)
    (hηh : ∀ t,cfg.headStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))) :
    (∑ t ∈ Finset.range T,∫ ω,‖trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) (t+1)-
      trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t‖^2 ∂P) ≤ 6500*(Δ/L)*Real.log (10*T) := by
  let B := 83*Real.sqrt (L*Δ)*(T : ℝ)
  have hd' : (0 : ℝ) < (b : ℝ)+h := by exact_mod_cast hd
  rcases hybrid_tuning_identities hL hΔ hd' hT with ⟨ha,hη,hηa,hscale,hstep,hroot,hinit⟩
  have hnoise0 : 0 ≤ (h : ℝ)*σ^2 := by positivity
  have hr1 : 1 ≤ cfg.r₀ := by rw [hr]; nlinarith [mul_pos hL hΔ]
  have hHr : 2*(L*Δ) ≤ cfg.r₀ := by rw [hr]; nlinarith
  have hσr (hh : 0<h) : σ^2 ≤ cfg.r₀ := by
    have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
    have hmul := mul_le_mul_of_nonneg_right hh' (sq_nonneg σ)
    rw [hr]
    nlinarith [mul_pos hL hΔ]
  have hB : B^2 ≤ 6889*(L*Δ)*(T : ℝ)^2 := by
    dsimp only [B]
    rw [mul_pow,mul_pow,Real.sq_sqrt (show 0 ≤ L*Δ by positivity)]
    norm_num
  have hGB (z : ℕ → Ω) (t : ℕ) (ht : t<T) (j : Fin h) :
      |gradient f (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B := by
    have he := (run_tuned_gradient_envelopes cfg hα hβ hδ x₀ seed (fun k x => oracle x (z k))
      hL hΔ hd hg hlip hgap T hT hηb hηh).1 t (Nat.le_of_lt ht)
    have hc := PiLp.norm_apply_le (gradient f (trajectory cfg x₀ (fun k x => oracle x (z k)) t)) (.inr j)
    rw [Real.norm_eq_abs] at hc
    exact hc.trans (by simpa only [run_point] using he)
  have he := iid_preliminary_movement_energy cfg hα hβ hδ hr1 x₀ seed a₀ (show 0 ≤ B by dsimp [B]; positivity)
    ho hi hmean hni hσ hs hηb hηh T hT hHr hσr hB hGB hscale hstep
  simpa only [Real.sq_sqrt (show 0 ≤ Δ/L by positivity)] using he



lemma iid_hybrid_tracking_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ) (hr₀ : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {f : Point b h → ℝ} {K : Ω → ℝ} {L M B B₀ ηb ηh σ σBody Δ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B) (hB₀ : 0 ≤ B₀)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hf : ∀ x,HasGradientAt f (grad x) x) (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=grad x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-grad x) (.inr i))^2 ∂p) ≤ σ^2)
    (hM : 0 ≤ M) (hσBody : 0 ≤ σBody)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-grad x) (.inl j)-(oracle y ω-grad y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hKM : (∫ ω,K ω ∂p) ≤ M)
    (hbodyNoise : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-grad x) (.inl j)| ∂p) ≤ σBody)
    (T k : ℕ) (hk : 2 ≤ k)
    (hGB : ∀ (z : ℕ → Ω) (u : ℕ),u ≤ T → ∀ j : Fin b ⊕ Fin h,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) j| ≤ B)
    (hGB₀ : ∀ (z : ℕ → Ω) (u : ℕ),u<min k T → ∀ j : Fin b,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B₀)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hηb : 0 ≤ ηb) (hηbcfg : ∀ t,cfg.bodyStep t=ηb)
    (hηh : 0 ≤ ηh) (hηhcfg : ∀ t,cfg.headStep t=ηh) :
    let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let Ab := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,∫ ω,
      (grad (x (t-k) ω) (.inl j))^2/(δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+
        (∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))) ∂P
    let Ah := ∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(grad (x t ω) (.inr j))^2/
      Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
    let S := ∑ t ∈ Finset.range T,∫ ω,‖x (t+1) ω-x t ω‖^2 ∂P
    ηb/3000*Ab+ηh/4*Ah ≤ Δ+80*b*ηb*B₀*(min k T : ℕ)+
      (1300480*ηb*(L+M)*b*k+80*ηb*b*L*k)*Real.sqrt T*Real.sqrt S+
      160*ηb*b*B*T*(k*(1/2 : ℝ)^(k-1)+(1/2 : ℝ)^k)+
      1300480*ηb*Real.sqrt ((999/1000 : ℝ)^k)*T*(b*B+σBody)+
      ηh/(2*cfg.r₀)*‖grad x₀‖^2+ηh*h*σ^2/(2*cfg.r₀)+(L/2+3*ηh*L^2/(2*cfg.r₀))*S := by
  have he := iid_hybrid_total_energy cfg hα hβ hδ hr₀ x₀ seed a ho hg hi hgrad hL hB hB₀ hs hf hgap hmean hni hσ
    T k hk hGB hGB₀ hsym hηb hηbcfg hηh hηhcfg
  have hn : k-1+1=k := by omega
  have hnr : ((k-1 : ℕ) : ℝ)+1=k := by exact_mod_cast hn
  have ht := iid_body_total_tracking cfg hα hβ hδ x₀ a seed ho hg hi hgrad hnoise hK hK0 hKM
    hL hM hB hσBody T (k-1) hsym (fun z t ht j => hGB z t (Nat.le_of_lt ht) (.inl j)) hbodyNoise hs
  dsimp only at ht
  simp only [hn,hnr] at ht
  have hm (t s) : Integrable (fun ω => ‖trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t-
      trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) s‖^2) P :=
    (trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hs.measurable t s P).integrable_sq
  have hd := expected_late_windows_norm_sum (fun ω t => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t) T k hm
  have ht' := mul_le_mul_of_nonneg_left ht (show 0 ≤ 10*ηb by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 80*ηb*b*L by positivity)
  dsimp only at he ht' hd' ⊢
  nlinarith [he,ht',hd']



lemma point_norm_le_coordinate_abs {b h : ℕ} (x : Point b h) :
    ‖x‖ ≤ (∑ j : Fin b,|x (.inl j)|)+(∑ j : Fin h,|x (.inr j)|) := by
  have he := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun j : Fin b ⊕ Fin h => |x j|) (fun j _ => abs_nonneg _)
  simp only [sq_abs,← EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type] at he
  have hb : 0 ≤ ∑ j : Fin b,|x (.inl j)| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hh : 0 ≤ ∑ j : Fin h,|x (.inr j)| := Finset.sum_nonneg fun j _ => abs_nonneg _
  nlinarith [norm_nonneg x]

lemma gradient_norm_lag_transfer {b h : ℕ} {grad : Point b h → Point b h} {L : ℝ}
    (hlip : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (x y : Point b h) :
    ‖grad x‖ ≤ (∑ j : Fin b,|grad y (.inl j)|)+(∑ j : Fin h,|grad x (.inr j)|)+b*L*‖x-y‖ := by
  have hp (j : Fin b) : |grad x (.inl j)| ≤ |grad y (.inl j)|+L*‖x-y‖ := by
    have ht := norm_le_norm_sub_add (grad x (.inl j)) (grad y (.inl j))
    have hc := PiLp.norm_apply_le (grad x-grad y) (.inl j)
    simp only [Real.norm_eq_abs,PiLp.sub_apply] at ht hc
    have he := hc.trans (hlip x y)
    linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hn := point_norm_le_coordinate_abs (grad x)
  nlinarith

lemma prefix_late_norm_sum (G B H D : ℕ → ℝ) {C : ℝ} (T k : ℕ)
    (hearly : ∀ t,t<T → t<k → G t ≤ C)
    (hlate : ∀ t,t<T → k ≤ t → G t ≤ B t+H t+D t)
    (hH : ∀ t,0 ≤ H t) :
    (∑ t ∈ Finset.range T,G t) ≤ (min k T : ℕ)*C+
      (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),B t)+
      (∑ t ∈ Finset.range T,H t)+
      ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),D t := by
  have he := LongTails.Proofs.AdaptiveHistoryAlgebra.prefix_late_energy_sum G (fun _ => 0)
    (fun t => B t+H t+D t) (c := 0) T k hearly (fun t ht hk => by simpa using hlate t ht hk)
  simp only [zero_mul,add_zero,Finset.sum_add_distrib] at he
  have hh : (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),H t) ≤ ∑ t ∈ Finset.range T,H t :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t ht hnot => hH t)
  linarith

lemma expected_gradient_norm_lag_transfer {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {b h : ℕ} {x y : Ω → Point b h} {grad : Point b h → Point b h} {L : ℝ}
    (hx : Measurable x) (hg : Measurable grad)
    (hlip : ∀ u v,‖grad u-grad v‖ ≤ L*‖u-v‖)
    (hb : Integrable (fun ω => ∑ j : Fin b,|grad (y ω) (.inl j)|) P)
    (hh : Integrable (fun ω => ∑ j : Fin h,|grad (x ω) (.inr j)|) P)
    (hd : Integrable (fun ω => ‖x ω-y ω‖) P) :
    Integrable (fun ω => ‖grad (x ω)‖) P ∧
      (∫ ω,‖grad (x ω)‖ ∂P) ≤
        (∫ ω,∑ j : Fin b,|grad (y ω) (.inl j)| ∂P)+
        (∫ ω,∑ j : Fin h,|grad (x ω) (.inr j)| ∂P)+b*L*(∫ ω,‖x ω-y ω‖ ∂P) := by
  have hi := (hb.add hh).add (hd.const_mul ((b : ℝ)*L))
  have hpoint (ω) := gradient_norm_lag_transfer hlip (x ω) (y ω)
  have hgi : Integrable (fun ω => ‖grad (x ω)‖) P := hi.mono' (hg.comp hx).norm.aestronglyMeasurable (by
    filter_upwards [] with ω
    simpa only [Pi.add_apply,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hpoint ω)
  refine ⟨hgi,?_⟩
  have he := integral_mono hgi hi hpoint
  have heq := integral_add (hb.add hh) (hd.const_mul ((b : ℝ)*L))
  have heq' := integral_add hb hh
  simp only [Pi.add_apply] at he heq heq'
  rw [heq,heq',integral_const_mul] at he
  exact he



lemma iid_head_gradient_sum_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hr₀ : 0 < cfg.r₀) (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {B σ : ℝ}
    (hB : 0 ≤ B) (hσ0 : 0 ≤ σ)
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad)
    (hi : ∀ z,Integrable (fun ω => ∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2) p)
    (hσ : ∀ z,(∫ ω,∑ j : Fin h,((oracle z ω-grad z) (.inr j))^2 ∂p) ≤ σ^2)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) (T : ℕ)
    (hGB : ∀ (z : ℕ → Ω) (t : Fin T) (j : Fin h),
      |grad (trajectory cfg x₀ (fun k x => oracle x (z k)) t) (.inr j)| ≤ B) :
    let x := fun ω t => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t
    let r := fun ω t j => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
    let A := ∑ t : Fin T,∑ j : Fin h,∫ ω,(grad (x ω t) (.inr j))^2/r ω t j ∂P
    Integrable (fun ω => ∑ t : Fin T,∑ j : Fin h,|grad (x ω t) (.inr j)|) P ∧
      (∫ ω,∑ t : Fin T,∑ j : Fin h,|grad (x ω t) (.inr j)| ∂P) ≤
        Real.sqrt T*Real.sqrt A*Real.sqrt (2*h*cfg.r₀+A+2*Real.sqrt h*σ*Real.sqrt T) := by
  let x := fun ω t => trajectory cfg x₀ (fun k x => oracle x (ξ k ω)) t
  let r := fun ω t j => Real.sqrt ((run cfg x₀ seed (fun k x => oracle x (ξ k ω)) t).accumulator (.inr j))
  let A := ∑ t : Fin T,∑ j : Fin h,∫ ω,(grad (x ω t) (.inr j))^2/r ω t j ∂P
  have hx (t) : Measurable (fun ω => x ω t) := trajectory_measurable cfg x₀ ho hs.measurable t
  have hj (j : Fin h) : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
  have hrm (t) (j : Fin h) : Measurable (fun ω => r ω t j) :=
    ((hj j).comp (run_core_measurable cfg x₀ seed ho hs.measurable t).2.2).sqrt
  have hrb (ω) (t) (j : Fin h) : cfg.r₀ ≤ r ω t j := by
    have hv := run_head_accumulator_lower cfg x₀ seed (fun k x => oracle x (ξ k ω)) t j
    exact (Real.le_sqrt hr₀.le ((sq_nonneg cfg.r₀).trans hv)).mpr hv
  have hAi (t : Fin T) (j : Fin h) : Integrable (fun ω => (grad (x ω t) (.inr j))^2/r ω t j) P :=
    integrable_sq_div_of_lower_bound ((hj j).comp (hg.comp (hx t))) (hrm t j) hB hr₀
      (fun ω => hGB (fun k => ξ k ω) t j) (fun ω => hrb ω t j)
  have hAiSum := integrable_finsetSum Finset.univ (fun t _ => integrable_finsetSum Finset.univ (fun j _ => hAi t j))
  have hR := iid_head_terminal_root_energy cfg hr₀ x₀ seed a hB hσ0 ho hg hi hσ hs T hGB
  have hmono (t : Fin T) (j : Fin h) (ω) : r ω t j ≤ r ω T j :=
    Real.sqrt_le_sqrt (run_head_accumulator_monotone cfg x₀ seed (fun k x => oracle x (ξ k ω)) j (Nat.le_of_lt t.isLt))
  have he := integral_head_time_energy_bound
    (fun (t : Fin T) j => (hj j).comp (hg.comp (hx t)))
    (fun t j ω => hr₀.trans_le (hrb ω t j)) hmono (fun j ω => Real.sqrt_nonneg _) hAiSum hR.1
  have hAeq : (∫ ω,∑ t : Fin T,∑ j : Fin h,(grad (x ω t) (.inr j))^2/r ω t j ∂P)=A := by
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun j _ => hAi t j))]
    simp_rw [integral_finsetSum _ (fun j _ => hAi _ j)]
    rfl
  simp only [Function.comp_def] at he
  rw [hAeq] at he
  refine ⟨he.1,he.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hR.2) (by positivity)



lemma iid_body_late_gradient_sum_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {L B σ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B) (hσ0 : 0 ≤ σ)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (T k : ℕ) (hk : 2 ≤ k)
    (hGB : ∀ (z : ℕ → Ω) (u : ℕ),u<T → ∀ j : Fin b,
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hη : ∀ t,0 ≤ cfg.bodyStep t)
    (hσ : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-grad x) (.inl j)| ∂p) ≤ σ) :
    let x := fun t ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let A := fun t => ∑ j : Fin b,∫ ω,(grad (x (t-k) ω) (.inl j))^2/
      (δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))) ∂P
    let G := fun t ω => ∑ j : Fin b,|grad (x (t-k) ω) (.inl j)|
    let late := (Finset.range T).filter (fun t => k ≤ t)
    (∀ t ∈ late,Integrable (G t) P) ∧
      (∑ t ∈ late,∫ ω,G t ω ∂P) ≤ 66*(∑ t ∈ late,A t)+
        Real.sqrt ((T : ℝ)*(b*cfg.δ+66*σ)*(∑ t ∈ late,A t)) := by
  let x := fun t ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t
  let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let S := fun t j ω => ∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p
  let F := fun t (j : Fin b) ω => (grad (x (t-k) ω) (.inl j))^2/
    (δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+S t j ω))
  let A := fun t => ∑ j : Fin b,∫ ω,F t j ω ∂P
  let G := fun t ω => ∑ j : Fin b,|grad (x (t-k) ω) (.inl j)|
  let late := (Finset.range T).filter (fun t => k ≤ t)
  have hδt (t) : 0 < δₜ t := mul_pos hδ (Real.sqrt_pos.mpr (default_bias_parameters t).2.1)
  have hδle (t) : δₜ t ≤ cfg.δ := by
    have hh := Real.sqrt_le_sqrt (default_bias_parameters t).2.2
    rw [Real.sqrt_one] at hh
    exact (mul_le_mul_of_nonneg_left hh hδ.le).trans_eq (mul_one _)
  have hS0 (t j ω) : 0 ≤ S t j ω := integral_nonneg fun u => abs_nonneg _
  have hF0 (t j ω) : 0 ≤ F t j ω := div_nonneg (sq_nonneg _) (by
    exact add_nonneg (hδt t).le (mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (hS0 t j ω))))
  have hA0 (t) : 0 ≤ A t := Finset.sum_nonneg fun j _ => integral_nonneg (hF0 t j)
  have hN : 0 ≤ (b : ℝ)*cfg.δ+66*σ := by positivity
  have hper (t) (ht : t∈late) : Integrable (G t) P ∧
      (∫ ω,G t ω ∂P) ≤ 66*A t+Real.sqrt (((b : ℝ)*cfg.δ+66*σ)*A t) := by
    have htk : k ≤ t := (Finset.mem_filter.mp ht).2
    have htT : t<T := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have hFi (j : Fin b) : Integrable (F t j) P :=
      (iid_body_lagged_descent_step cfg hα hβ hδ x₀ seed a ho hg hi hgrad hL hB hs t k hk htk j
        (fun z u hu => hGB z u (by omega) j) (fun z => hsym z j) (hη t)).1
    have hx : Measurable (x (t-k)) := trajectory_measurable cfg x₀ ho hs.measurable (t-k)
    have hqm (j : Fin b) : Measurable (fun ω => grad (x (t-k) ω) (.inl j)) := by
      have hj : Measurable (fun z : Point b h => z (.inl j)) := by fun_prop
      exact hj.comp (hg.comp hx)
    have hnoise := (body_coordinate_noise_integrals ho hg hi hσ).2
    have he := integral_body_abs_sum_energy hqm hδ.le hσ0 (fun j ω => hδt t) (fun j ω => hδle t)
      (hS0 t) (fun ω => hnoise (x (t-k) ω)) (integrable_finsetSum _ (fun j _ => hFi j))
    have hAeq : (∫ ω,∑ j : Fin b,F t j ω ∂P)=A t := integral_finsetSum _ (fun j _ => hFi j)
    change Integrable (G t) P ∧ (∫ ω,G t ω ∂P) ≤ 66*(∫ ω,∑ j : Fin b,F t j ω ∂P)+
      Real.sqrt ((Fintype.card (Fin b)*cfg.δ+66*σ)*(∫ ω,∑ j : Fin b,F t j ω ∂P)) at he
    simpa only [hAeq,Fintype.card_fin] using he
  have he := sum_linear_root_energy late hN hA0 (fun t ht => (hper t ht).2)
  have hc : (late.card : ℝ) ≤ T := by
    exact_mod_cast (Finset.card_filter_le (Finset.range T) (fun t => k ≤ t)).trans_eq (Finset.card_range T)
  have hsum : 0 ≤ ∑ t ∈ late,A t := Finset.sum_nonneg fun t _ => hA0 t
  have hr := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hN) hsum)
  refine ⟨fun t ht => (hper t ht).1,?_⟩
  dsimp only
  change (∑ t ∈ late,∫ ω,G t ω ∂P) ≤ _
  linarith [he,hr]



lemma expected_prefix_late_gradient_sum {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {b h : ℕ}
    (x : ℕ → Ω → Point b h) {grad : Point b h → Point b h} {L B₀ : ℝ}
    (hx : ∀ t,Measurable (x t)) (hg : Measurable grad)
    (hlip : ∀ u v,‖grad u-grad v‖ ≤ L*‖u-v‖) (T k : ℕ)
    (hearly : ∀ t,t<min k T → ∀ ω,‖grad (x t ω)‖ ≤ B₀)
    (hb : ∀ t ∈ (Finset.range T).filter (fun t => k ≤ t),
      Integrable (fun ω => ∑ j : Fin b,|grad (x (t-k) ω) (.inl j)|) P)
    (hh : ∀ t,t<T → Integrable (fun ω => ∑ j : Fin h,|grad (x t ω) (.inr j)|) P)
    (hd : ∀ t,t<T → Integrable (fun ω => ‖x t ω-x (t-k) ω‖) P) :
    (∀ t,t<T → Integrable (fun ω => ‖grad (x t ω)‖) P) ∧
      (∑ t ∈ Finset.range T,∫ ω,‖grad (x t ω)‖ ∂P) ≤ (min k T : ℕ)*B₀+
        (∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∫ ω,∑ j : Fin b,|grad (x (t-k) ω) (.inl j)| ∂P)+
        (∑ t ∈ Finset.range T,∫ ω,∑ j : Fin h,|grad (x t ω) (.inr j)| ∂P)+
        b*L*(∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∫ ω,‖x t ω-x (t-k) ω‖ ∂P) := by
  have he (t) (ht : t<T) (htk : t<k) : Integrable (fun ω => ‖grad (x t ω)‖) P ∧
      (∫ ω,‖grad (x t ω)‖ ∂P) ≤ B₀ := by
    have hbound (ω) := hearly t (by omega) ω
    have hi : Integrable (fun ω => ‖grad (x t ω)‖) P :=
      (show MemLp (fun ω => ‖grad (x t ω)‖) 1 P from MemLp.of_bound (hg.comp (hx t)).norm.aestronglyMeasurable B₀
        (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] using hbound ω)).integrable (by norm_num)
    refine ⟨hi,?_⟩
    have he := integral_mono hi (integrable_const B₀) hbound
    simpa using he
  have hl (t) (ht : t<T) (htk : k ≤ t) := expected_gradient_norm_lag_transfer (hx t) hg hlip
    (hb t (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht,htk⟩)) (hh t ht) (hd t ht)
  constructor
  · intro t ht
    by_cases htk : t<k
    · exact (he t ht htk).1
    · exact (hl t ht (by omega)).1
  · have hsum := prefix_late_norm_sum (fun t => ∫ ω,‖grad (x t ω)‖ ∂P)
      (fun t => ∫ ω,∑ j : Fin b,|grad (x (t-k) ω) (.inl j)| ∂P)
      (fun t => ∫ ω,∑ j : Fin h,|grad (x t ω) (.inr j)| ∂P)
      (fun t => (b : ℝ)*L*(∫ ω,‖x t ω-x (t-k) ω‖ ∂P)) T k
      (fun t ht htk => (he t ht htk).2) (fun t ht htk => (hl t ht htk).2)
      (fun t => integral_nonneg fun ω => Finset.sum_nonneg fun j _ => abs_nonneg _)
    rw [← Finset.mul_sum] at hsum
    exact hsum



lemma iid_gradient_sum_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ) (hr₀ : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a : Ω)
    {oracle : Point b h → Ω → Point b h} {grad : Point b h → Point b h} {L B B₀ σ σHead : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable grad) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖grad x-grad y‖ ≤ L*‖x-y‖) (hL : 0 ≤ L) (hB : 0 ≤ B) (hσ0 : 0 ≤ σ) (hσHead : 0 ≤ σHead)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (T k : ℕ) (hk : 2 ≤ k)
    (hGB : ∀ (z : ℕ → Ω) (t : ℕ),t<T →
      ‖grad (trajectory cfg x₀ (fun r x => oracle x (z r)) t)‖ ≤ B)
    (hGB₀ : ∀ (z : ℕ → Ω) (t : ℕ),t<min k T →
      ‖grad (trajectory cfg x₀ (fun r x => oracle x (z r)) t)‖ ≤ B₀)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-grad x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-grad x) (.inl j)))
    (hη : ∀ t,0 ≤ cfg.bodyStep t)
    (hσ : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-grad x) (.inl j)| ∂p) ≤ σ)
    (hni : ∀ x,Integrable (fun ω => ∑ j : Fin h,((oracle x ω-grad x) (.inr j))^2) p)
    (hσh : ∀ x,(∫ ω,∑ j : Fin h,((oracle x ω-grad x) (.inr j))^2 ∂p) ≤ σHead^2) :
    let x := fun t ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let Ab := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,∫ ω,(grad (x (t-k) ω) (.inl j))^2/
      (δₜ t+66*(|grad (x (t-k) ω) (.inl j)|+(∫ u,|(oracle (x (t-k) ω) u-grad (x (t-k) ω)) (.inl j)| ∂p))) ∂P
    let Ah := ∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(grad (x t ω) (.inr j))^2/
      Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
    let S := ∑ t ∈ Finset.range T,∫ ω,‖x (t+1) ω-x t ω‖^2 ∂P
    (∀ t,t<T → Integrable (fun ω => ‖grad (x t ω)‖) P) ∧
      (∑ t ∈ Finset.range T,∫ ω,‖grad (x t ω)‖ ∂P) ≤ (min k T : ℕ)*B₀+66*Ab+
        Real.sqrt ((T : ℝ)*(b*cfg.δ+66*σ)*Ab)+
        Real.sqrt T*Real.sqrt Ah*Real.sqrt (2*h*cfg.r₀+Ah+2*Real.sqrt h*σHead*Real.sqrt T)+
        b*L*k*Real.sqrt T*Real.sqrt S := by
  let x := fun t ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t
  let H := fun t ω => ∑ j : Fin h,|grad (x t ω) (.inr j)|
  have hx (t) : Measurable (x t) := trajectory_measurable cfg x₀ ho hs.measurable t
  have hcoord (z : ℕ → Ω) (t : ℕ) (ht : t<T) (j : Fin b ⊕ Fin h) :
      |grad (trajectory cfg x₀ (fun r x => oracle x (z r)) t) j| ≤ B := by
    have he := PiLp.norm_apply_le (grad (trajectory cfg x₀ (fun r x => oracle x (z r)) t)) j
    rw [Real.norm_eq_abs] at he
    exact he.trans (hGB z t ht)
  have hb := iid_body_late_gradient_sum_energy cfg hα hβ hδ x₀ seed a ho hg hi hgrad hL hB hσ0 hs T k hk
    (fun z t ht j => hcoord z t ht (.inl j)) hsym hη hσ
  have hh := iid_head_gradient_sum_energy cfg hr₀ x₀ seed a hB hσHead ho hg hni hσh hs T
    (fun z t j => hcoord z t t.isLt (.inr j))
  dsimp only at hh
  let A := fun t => ∑ j : Fin h,∫ ω,(grad (x t ω) (.inr j))^2/
    Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
  change Integrable (fun ω => ∑ t : Fin T,H t ω) P ∧
    (∫ ω,∑ t : Fin T,H t ω ∂P) ≤ Real.sqrt T*Real.sqrt (∑ t : Fin T,A t)*
      Real.sqrt (2*h*cfg.r₀+(∑ t : Fin T,A t)+2*Real.sqrt h*σHead*Real.sqrt T) at hh
  have hsumH (ω) : (∑ t : Fin T,H t ω)=∑ t ∈ Finset.range T,H t ω :=
    Fin.sum_univ_eq_sum_range (fun t => H t ω) T
  simp_rw [hsumH,Fin.sum_univ_eq_sum_range A T] at hh
  have hHm (t) : Measurable (H t) := by
    apply Finset.measurable_sum
    intro j hj
    have hc : Measurable (fun z : Point b h => z (.inr j)) := by fun_prop
    simpa only [Function.comp_def,Real.norm_eq_abs] using (hc.comp (hg.comp (hx t))).norm
  have hHi (t) (ht : t<T) : Integrable (H t) P := hh.1.mono' (hHm t).aestronglyMeasurable (by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
    exact Finset.single_le_sum (f := fun s => H s ω)
      (fun s _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_range.mpr ht))
  have hH := hh.2
  rw [integral_finsetSum _ (fun t ht => hHi t (Finset.mem_range.mp ht))] at hH
  have hdm (t s) : Integrable (fun ω => ‖x t ω-x s ω‖^2) P :=
    (trajectory_displacement_memLp cfg hα hβ hδ x₀ ho hs.measurable t s P).integrable_sq
  have hdi (t) : Integrable (fun ω => ‖x t ω-x (t-k) ω‖) P := by
    have he := (integral_sqrt_le_sqrt_integral (hdm t (t-k)) (fun ω => sq_nonneg _)).1
    simpa only [Real.sqrt_sq (norm_nonneg _)] using he
  have hn := expected_prefix_late_gradient_sum x hx hg hgrad T k
    (fun t ht ω => hGB₀ (fun r => ξ r ω) t ht) hb.1 hHi (fun t ht => hdi t)
  have hd := expected_late_windows_norm_sum (fun ω t => x t ω) T k hdm
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ (b : ℝ)*L by positivity)
  refine ⟨hn.1,?_⟩
  dsimp only [A,H] at hb hn hd' hH ⊢
  linarith [hn.2,hb.2,hH,hd']


set_option maxHeartbeats 2000000 in
lemma iid_tuned_hybrid_energy {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ) (hr₀ : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a₀ : Ω)
    {oracle : Point b h → Ω → Point b h} {f : Point b h → ℝ} {K : Ω → ℝ} {L M σ σBody Δ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable (gradient f)) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (hL : 0 < L) (hΔ : 0 < Δ) (hd : 0 < b+h)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hf : ∀ x,HasGradientAt f (gradient f x) x) (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=gradient f x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-gradient f x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-gradient f x) (.inr i))^2 ∂p) ≤ σ^2)
    (hM : 0 ≤ M) (hσBody : 0 ≤ σBody)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-gradient f x) (.inl j)-(oracle y ω-gradient f y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hKM : (∫ ω,K ω ∂p) ≤ M)
    (hbodyNoise : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-gradient f x) (.inl j)| ∂p) ≤ σBody)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-gradient f x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-gradient f x) (.inl j)))
    (T : ℕ) (hT : 1 ≤ T) (hr : cfg.r₀=1+2*L*Δ+h*σ^2)
    (hηb : ∀ t,cfg.bodyStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))/Real.sqrt T)
    (hηh : ∀ t,cfg.headStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))) :
    let R := 1+((b : ℝ)+h)*(L+M)*Real.sqrt (Δ/L)
    let ℓ := Real.log (10*(1+σBody)*T)
    let k := ⌈20000*ℓ⌉₊
    let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
    let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
    let Ab := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,∫ ω,
      (gradient f (x (t-k) ω) (.inl j))^2/(δₜ t+66*(|gradient f (x (t-k) ω) (.inl j)|+
        (∫ u,|(oracle (x (t-k) ω) u-gradient f (x (t-k) ω)) (.inl j)| ∂p))) ∂P
    let Ah := ∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(gradient f (x t ω) (.inr j))^2/
      Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
    Ab/(3000*Real.sqrt T)+Ah/4 ≤ 10000000000000*R*ℓ^2 := by
  let a := Real.sqrt (Δ/(L*((b : ℝ)+h)))
  let R := 1+((b : ℝ)+h)*(L+M)*Real.sqrt (Δ/L)
  let ℓ := Real.log (10*(1+σBody)*T)
  let k := ⌈20000*ℓ⌉₊
  let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
  let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let Ab := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,∫ ω,
    (gradient f (x (t-k) ω) (.inl j))^2/(δₜ t+66*(|gradient f (x (t-k) ω) (.inl j)|+
      (∫ u,|(oracle (x (t-k) ω) u-gradient f (x (t-k) ω)) (.inl j)| ∂p))) ∂P
  let Ah := ∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(gradient f (x t ω) (.inr j))^2/
    Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
  let η := a/Real.sqrt T
  let B := 83*Real.sqrt (L*Δ)*(T : ℝ)
  let B₀ := (2+80*(k : ℝ))*Real.sqrt (L*Δ)
  let S := ∑ t ∈ Finset.range T,∫ ω,‖x (t+1) ω-x t ω‖^2 ∂P
  change Ab/(3000*Real.sqrt T)+Ah/4 ≤ 10000000000000*R*ℓ^2
  have hd' : (0 : ℝ) < (b : ℝ)+h := by exact_mod_cast hd
  rcases hybrid_tuning_identities hL hΔ hd' hT with ⟨ha,hη,hηa,hscale,hstep,hroot,hinit⟩
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rcases logarithmic_argument_bounds hσBody hTr with ⟨hX,hTX,hσX,hℓ,hlog⟩
  rcases logarithmic_window_rounding hℓ with ⟨hk,hklo,hkhi,hsqrt⟩
  change 2 ≤ k at hk
  have hGB (z : ℕ → Ω) (u : ℕ) (hu : u ≤ T) (j : Fin b ⊕ Fin h) :
      |gradient f (trajectory cfg x₀ (fun r x => oracle x (z r)) u) j| ≤ B := by
    have he := (run_tuned_gradient_envelopes cfg hα hβ hδ x₀ seed (fun r x => oracle x (z r))
      hL hΔ hd hf hgrad hgap T hT hηb hηh).1 u hu
    have hc := PiLp.norm_apply_le (gradient f (trajectory cfg x₀ (fun r x => oracle x (z r)) u)) j
    rw [Real.norm_eq_abs] at hc
    exact hc.trans (by simpa only [run_point] using he)
  have hGB₀ (z : ℕ → Ω) (u : ℕ) (hu : u < min k T) (j : Fin b) :
      |gradient f (trajectory cfg x₀ (fun r x => oracle x (z r)) u) (.inl j)| ≤ B₀ := by
    have he := (run_tuned_gradient_envelopes cfg hα hβ hδ x₀ seed (fun r x => oracle x (z r))
      hL hΔ hd hf hgrad hgap T hT hηb hηh).2 u k (by omega)
    have hc := PiLp.norm_apply_le (gradient f (trajectory cfg x₀ (fun r x => oracle x (z r)) u)) (.inl j)
    rw [Real.norm_eq_abs] at hc
    exact hc.trans (by simpa only [run_point] using he)
  have he := iid_hybrid_tracking_energy cfg hα hβ hδ hr₀ x₀ seed a₀ ho hg hi hgrad hL.le
    (show 0 ≤ B by dsimp [B]; positivity) (show 0 ≤ B₀ by dsimp [B₀]; positivity)
    hs hf hgap hmean hni hσ hM hσBody hnoise hK hK0 hKM hbodyNoise T k hk hGB hGB₀ hsym
    hη.le hηb ha.le hηh
  change η/3000*Ab+a/4*Ah ≤ Δ+80*b*η*B₀*(min k T : ℕ)+
    (1300480*η*(L+M)*b*k+80*η*b*L*k)*Real.sqrt T*Real.sqrt S+
    160*η*b*B*T*(k*(1/2 : ℝ)^(k-1)+(1/2 : ℝ)^k)+
    1300480*η*Real.sqrt ((999/1000 : ℝ)^k)*T*(b*B+σBody)+
    a/(2*cfg.r₀)*‖gradient f x₀‖^2+a*h*σ^2/(2*cfg.r₀)+(L/2+3*a*L^2/(2*cfg.r₀))*S at he
  have hSm := iid_tuned_movement_energy cfg hα hβ hδ x₀ seed a₀ hL hΔ hd hf hgrad hgap
    ho hi hmean hni hσ hs T hT hr hηb hηh
  have hS : S ≤ 6500*(Δ/L)*ℓ := hSm.trans
    (mul_le_mul_of_nonneg_left hlog (by positivity))
  have hG : ‖gradient f x₀‖^2 ≤ 2*L*Δ := by
    have hh := initial_gradient_norm hL hf hgrad hgap
    have hs := Real.sq_sqrt (show 0 ≤ 2*L*Δ by positivity)
    nlinarith only [hh,hs,norm_nonneg (gradient f x₀),Real.sqrt_nonneg (2*L*Δ)]
  have hrΔ : 2*L*Δ ≤ cfg.r₀ := by
    rw [hr]
    nlinarith only [show 0 ≤ (h : ℝ)*σ^2 by positivity]
  have hI := hybrid_initial_head_charge ha.le hr₀ hG
    (show 2*L*Δ+(h : ℝ)*σ^2 ≤ cfg.r₀ by rw [hr]; linarith only)
  have hrootT : (Real.sqrt (T : ℝ))^2=T := Real.sq_sqrt (Nat.cast_nonneg T)
  have hrootT0 : 0 < Real.sqrt (T : ℝ) := by positivity
  have hpower := half_power_preceding (show 1 ≤ k by omega)
  have hcoef : (1300480*(L+M)*b*k+80*b*L*k)*Real.sqrt S ≤
      1300560*(b*(L+M))*k*Real.sqrt S := by
    have hh : 0 ≤ (b : ℝ)*M*k*Real.sqrt S := by positivity
    nlinarith only [hh]
  have hn := hybrid_energy_normalization ha hrootT0 (rfl : η=a/Real.sqrt T) hrootT hI
    (show η/3000*Ab+a/4*Ah ≤ Δ+η*(80*b*B₀*(min k T : ℕ))+
      η*Real.sqrt T*((1300480*(L+M)*b*k+80*b*L*k)*Real.sqrt S)+
      η*T*(160*b*B*(k*(1/2 : ℝ)^(k-1)+(1/2 : ℝ)^k)+
        1300480*Real.sqrt ((999/1000 : ℝ)^k)*(b*B+σBody))+
      (a/(2*cfg.r₀)*‖gradient f x₀‖^2+a*h*σ^2/(2*cfg.r₀))+
      (L/2+3*a*L^2/(2*cfg.r₀))*S by convert he using 1; ring)
  have hnorm : (η/3000*Ab+a/4*Ah)/a=Ab/(3000*Real.sqrt T)+Ah/4 := by
    have han : a ≠ 0 := ha.ne'
    dsimp [η]
    field_simp [han]
  rw [hnorm,hpower] at hn
  have ht := logarithmic_energy_bound (E := Ab/(3000*Real.sqrt T)+Ah/4) hd hT hL hM hΔ hσBody hr₀ hrΔ hS
  apply ht
  dsimp only [B₀,B,k,ℓ,a] at hn hcoef ⊢
  simp only [div_eq_mul_inv] at hn ⊢
  nlinarith only [hn,hcoef]

set_option maxHeartbeats 2000000 in
lemma iid_tuned_gradient_sum {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {p : Measure Ω} {P : Measure Ξ}
    [IsProbabilityMeasure p] [IsProbabilityMeasure P] {b h : ℕ}
    (cfg : Config) (hα : cfg.α=9/10) (hβ : cfg.β=999/1000) (hδ : 0 < cfg.δ) (hr₀ : 0 < cfg.r₀)
    (x₀ : Point b h) (seed : Fin (cfg.lastIndex+1)) (a₀ : Ω)
    {oracle : Point b h → Ω → Point b h} {f : Point b h → ℝ} {K : Ω → ℝ} {L M σ σBody Δ : ℝ}
    (ho : Measurable (Function.uncurry oracle)) (hg : Measurable (gradient f)) (hi : ∀ x,Integrable (oracle x) p)
    (hgrad : ∀ x y,‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (hL : 0 < L) (hΔ : 0 < Δ) (hd : 0 < b+h)
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hf : ∀ x,HasGradientAt f (gradient f x) x) (hgap : ∀ x,f x₀-f x ≤ Δ)
    (hmean : ∀ x,(∫ ω,oracle x ω ∂p)=gradient f x)
    (hni : ∀ x,Integrable (fun ω => ∑ i : Fin h,((oracle x ω-gradient f x) (.inr i))^2) p)
    (hσ : ∀ x,(∫ ω,∑ i : Fin h,((oracle x ω-gradient f x) (.inr i))^2 ∂p) ≤ σ^2)
    (hM : 0 ≤ M) (hσBody : 0 ≤ σBody) (hσ0 : 0 ≤ σ)
    (hnoise : ∀ᵐ ω ∂p,∀ x y (j : Fin b),
      |(oracle x ω-gradient f x) (.inl j)-(oracle y ω-gradient f y) (.inl j)| ≤ K ω*‖x-y‖)
    (hK : Integrable K p) (hK0 : ∀ᵐ ω ∂p,0 ≤ K ω) (hKM : (∫ ω,K ω ∂p) ≤ M)
    (hbodyNoise : ∀ x,(∫ ω,∑ j : Fin b,|(oracle x ω-gradient f x) (.inl j)| ∂p) ≤ σBody)
    (hsym : ∀ x (j : Fin b),(p.map (fun ω => (oracle x ω-gradient f x) (.inl j))).map (fun z : ℝ => -z)=
      p.map (fun ω => (oracle x ω-gradient f x) (.inl j)))
    (T : ℕ) (hT : 1 ≤ T) (hr : cfg.r₀=1+2*L*Δ+h*σ^2)
    (hηb : ∀ t,cfg.bodyStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))/Real.sqrt T)
    (hηh : ∀ t,cfg.headStep t=Real.sqrt (Δ/(L*((b : ℝ)+h)))) :
    let N := b*cfg.δ+66*σBody+Real.sqrt h*σ
    let R := 1+((b : ℝ)+h)*(L+M)*Real.sqrt (Δ/L)
    let ℓ := Real.log (10*(1+σBody)*T)
    let x := fun t ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) t
    (∀ t,t<T → Integrable (fun ω => ‖gradient f (x t ω)‖) P) ∧
      (∑ t ∈ Finset.range T,∫ ω,‖gradient f (x t ω)‖ ∂P) ≤
        10000000000000000000*(Real.sqrt (N*R)*ℓ*Real.sqrt T*Real.sqrt (Real.sqrt T)+
          Real.sqrt (R^2+(h*cfg.r₀)*R)*ℓ^2*Real.sqrt T) := by
  let a := Real.sqrt (Δ/(L*((b : ℝ)+h)))
  let R := 1+((b : ℝ)+h)*(L+M)*Real.sqrt (Δ/L)
  let ℓ := Real.log (10*(1+σBody)*T)
  let k := ⌈20000*ℓ⌉₊
  let x := fun u ω => trajectory cfg x₀ (fun r x => oracle x (ξ r ω)) u
  let δₜ := fun t => cfg.δ*Real.sqrt (1-(999/1000 : ℝ)^(t+1))
  let Ab := ∑ t ∈ (Finset.range T).filter (fun t => k ≤ t),∑ j : Fin b,∫ ω,
    (gradient f (x (t-k) ω) (.inl j))^2/(δₜ t+66*(|gradient f (x (t-k) ω) (.inl j)|+
      (∫ u,|(oracle (x (t-k) ω) u-gradient f (x (t-k) ω)) (.inl j)| ∂p))) ∂P
  let Ah := ∑ t ∈ Finset.range T,∑ j : Fin h,∫ ω,(gradient f (x t ω) (.inr j))^2/
    Real.sqrt ((run cfg x₀ seed (fun r x => oracle x (ξ r ω)) t).accumulator (.inr j)) ∂P
  let η := a/Real.sqrt T
  let B := 83*Real.sqrt (L*Δ)*(T : ℝ)
  let B₀ := (2+80*(k : ℝ))*Real.sqrt (L*Δ)
  let S := ∑ t ∈ Finset.range T,∫ ω,‖x (t+1) ω-x t ω‖^2 ∂P
  let N := b*cfg.δ+66*σBody+Real.sqrt h*σ
  let u := Real.sqrt (T : ℝ)
  change (∀ t,t<T → Integrable (fun ω => ‖gradient f (x t ω)‖) P) ∧
    (∑ t ∈ Finset.range T,∫ ω,‖gradient f (x t ω)‖ ∂P) ≤
      10000000000000000000*(Real.sqrt (N*R)*ℓ*u*Real.sqrt u+Real.sqrt (R^2+(h*cfg.r₀)*R)*ℓ^2*u)
  have hd' : (0 : ℝ) < (b : ℝ)+h := by exact_mod_cast hd
  rcases hybrid_tuning_identities hL hΔ hd' hT with ⟨ha,hη,hηa,hscale,hstep,hroot,hinit⟩
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rcases logarithmic_argument_bounds hσBody hTr with ⟨hX,hTX,hσX,hℓ,hlog⟩
  rcases logarithmic_window_rounding hℓ with ⟨hk,hklo,hkhi,hsqrt⟩
  change 2 ≤ k at hk
  have hGB (z : ℕ → Ω) (u : ℕ) (hu : u<T) :
      ‖gradient f (trajectory cfg x₀ (fun r x => oracle x (z r)) u)‖ ≤ B := by
    simpa only [run_point] using (run_tuned_gradient_envelopes cfg hα hβ hδ x₀ seed
      (fun r x => oracle x (z r)) hL hΔ hd hf hgrad hgap T hT hηb hηh).1 u (Nat.le_of_lt hu)
  have hGB₀ (z : ℕ → Ω) (u : ℕ) (hu : u<min k T) :
      ‖gradient f (trajectory cfg x₀ (fun r x => oracle x (z r)) u)‖ ≤ B₀ := by
    simpa only [run_point] using (run_tuned_gradient_envelopes cfg hα hβ hδ x₀ seed
      (fun r x => oracle x (z r)) hL hΔ hd hf hgrad hgap T hT hηb hηh).2 u k (by omega)
  have he := iid_tuned_hybrid_energy cfg hα hβ hδ hr₀ x₀ seed a₀ ho hg hi hgrad hL hΔ hd
    hs hf hgap hmean hni hσ hM hσBody hnoise hK hK0 hKM hbodyNoise hsym T hT hr hηb hηh
  change Ab/(3000*u)+Ah/4 ≤ 10000000000000*R*ℓ^2 at he
  have hn := iid_gradient_sum_energy cfg hα hβ hδ hr₀ x₀ seed a₀ ho hg hi hgrad hL.le
    (show 0 ≤ B by dsimp [B]; positivity) hσBody hσ0 hs T k hk hGB hGB₀ hsym
    (fun t => by rw [hηb]; exact hη.le) hbodyNoise hni hσ
  change (∀ t,t<T → Integrable (fun ω => ‖gradient f (x t ω)‖) P) ∧
    (∑ t ∈ Finset.range T,∫ ω,‖gradient f (x t ω)‖ ∂P) ≤ (min k T : ℕ)*B₀+66*Ab+
      Real.sqrt ((T : ℝ)*(b*cfg.δ+66*σBody)*Ab)+
      u*Real.sqrt Ah*Real.sqrt (2*h*cfg.r₀+Ah+2*Real.sqrt h*σ*u)+b*L*k*u*Real.sqrt S at hn
  have hAb : 0 ≤ Ab := by
    apply Finset.sum_nonneg
    intro t ht
    apply Finset.sum_nonneg
    intro j hj
    apply integral_nonneg
    intro ω
    apply div_nonneg (sq_nonneg _)
    apply add_nonneg (mul_nonneg hδ.le (Real.sqrt_nonneg _))
    apply mul_nonneg (by norm_num)
    exact add_nonneg (abs_nonneg _) (integral_nonneg fun z => abs_nonneg _)
  have hAh : 0 ≤ Ah := Finset.sum_nonneg fun t ht => Finset.sum_nonneg fun j hj =>
    integral_nonneg fun ω => div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hSm := iid_tuned_movement_energy cfg hα hβ hδ x₀ seed a₀ hL hΔ hd hf hgrad hgap
    ho hi hmean hni hσ hs T hT hr hηb hηh
  have hS : S ≤ 6500*(Real.sqrt (Δ/L))^2*ℓ := by
    rw [Real.sq_sqrt (show 0 ≤ Δ/L by positivity)]
    exact hSm.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  rcases hybrid_scale_comparisons hd hL hM hΔ with ⟨hR,hPG,hPQ,hgapR⟩
  have hu : 1 ≤ u := by simpa [u] using Real.sqrt_le_sqrt hTr
  have hPLq : (b : ℝ)*L*Real.sqrt (Δ/L) ≤ R := by
    have hm : 0 ≤ (b : ℝ)*M*Real.sqrt (Δ/L) := by positivity
    nlinarith only [hPQ,hm]
  have hp := output_prefix_charge (hybrid_gradient_scale hd hL hM hΔ)
    (show (1 : ℝ) ≤ k by exact_mod_cast (show 1 ≤ k by omega))
    (show (0 : ℝ) ≤ (min k T : ℕ) by positivity)
    (show ((min k T : ℕ) : ℝ) ≤ k by exact_mod_cast Nat.min_le_left k T) hu hR hℓ hkhi
  have hl := output_lag_charge (show 0 ≤ (b : ℝ)*L by positivity) (Real.sqrt_nonneg _)
    (Nat.cast_nonneg k) (show 0 ≤ u by linarith) hR hℓ hPLq hkhi hS
  have hRest : (min k T : ℕ)*B₀+b*L*k*u*Real.sqrt S ≤ 100000000000*R*ℓ^2*u := by
    dsimp only [B₀]
    nlinarith only [hp,hl,show 0 ≤ R*ℓ^2*u by positivity]
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hNb : (b : ℝ)*cfg.δ+66*σBody ≤ N := by
    dsimp [N]
    exact le_add_of_nonneg_right (by positivity)
  have hNh : Real.sqrt h*σ ≤ N := by
    dsimp [N]
    linarith only [show 0 ≤ (b : ℝ)*cfg.δ+66*σBody by positivity]
  have hu2 : u^2=(T : ℝ) := Real.sq_sqrt (Nat.cast_nonneg T)
  have hNbroot := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hNb (Nat.cast_nonneg T)) hAb)
  have hNhroot := Real.sqrt_le_sqrt (show 2*(h : ℝ)*cfg.r₀+Ah+2*Real.sqrt h*σ*u ≤
      2*(h*cfg.r₀)+Ah+2*N*u by
    have hm := mul_le_mul_of_nonneg_right hNh (show 0 ≤ 2*u by positivity)
    nlinarith only [hm])
  have hNhfull := mul_le_mul_of_nonneg_left hNhroot (show 0 ≤ u*Real.sqrt Ah by positivity)
  refine ⟨hn.1,hybrid_gradient_energy_rate hAb hAh hN (show 0 ≤ (h : ℝ)*cfg.r₀ by positivity)
    hR hℓ hu he hRest ?_⟩
  rw [hu2]
  nlinarith only [hn.2,hNbroot,hNhfull]

end LongTails.Proofs.HeterogeneousAdamDescent
