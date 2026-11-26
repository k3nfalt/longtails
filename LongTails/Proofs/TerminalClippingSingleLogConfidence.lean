import LongTails.Proofs.TerminalClippingSingleLogPathwise
import LongTails.Proofs.TerminalClippingSingleLogTails
import LongTails.Proofs.TerminalClippingSingleLogLocalization

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClippingSingleLog

variable {E Ω Ξ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]

lemma compact_accuracy {T : ℕ} {q M r k C b τ : ℝ} (ht : Tuning T q M r k C b τ)
    {K : Set E} {f : E → ℝ} (hf : ConvexOn ℝ K f) {u x₀ : E} (hu : u ∈ K)
    (hmin : ∀ x ∈ K, f u ≤ f x) (hx₀ : x₀ ∈ K) (hstart : ‖x₀-u‖ ≤ r*T)
    {proj : E → E} (hp : Measurable proj) (hpm : ∀ w, proj w ∈ K)
    (hpv : ∀ w, ∀ v ∈ K, ⟪w-proj w,v-proj w⟫ ≤ 0)
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (ν : ProbabilityMeasure Ω)
    (hgi : ∀ x ∈ K, Integrable (g x) (ν : Measure Ω))
    (hmi : ∀ x ∈ K, Integrable (fun ω => ‖g x ω‖^2) (ν : Measure Ω))
    (hm : ∀ x ∈ K, (∫ ω, ‖g x ω‖^2 ∂(ν : Measure Ω)) ≤ M^2)
    (hsub : ∀ x ∈ K, ∀ y ∈ K, f x-f y ≤ ⟪∫ ω, g x ω ∂(ν : Measure Ω), x-y⟫)
    {P : Measure Ξ} (ξ : ℕ → Ξ → Ω)
    (hlaw : MeasurePreserving (fun a (i : Fin T) => ξ i a) P (Measure.pi fun _ : Fin T => (ν : Measure Ω))) :
    let y := fun a => path g proj k C T x₀ (fun i => ξ i a)
    P {a | ¬ ((∀ j ≤ T, ‖y a j-x₀‖ < 4*(r*T)) ∧
      f (y a T)-f u ≤ 24*(r*T)*M*Real.sqrt (q/T))} ≤
      ENNReal.ofReal (Real.exp (-q)) + ENNReal.ofReal (Real.exp (-q)) := by
  let S := ℕ × K × E
  let m := fun s : S => ((T:ℝ)-s.1)
  let x := fun s : S => (s.2.1 : E)
  let z := fun s : S => s.2.2
  let sample := fun (s : S) ω => g (x s) ω
  let next := fun (s : S) ω => proj (x s-(k*m s) • clip C (sample s ω))
  let adv := fun (s : S) (ω : Ω) => ((s.1+1, ⟨next s ω,hpm _⟩, mix (m s) (z s) (next s ω)) : S)
  let A := fun s : S => clip b (direction (m s) k (x s) (z s))
  have mx : Measurable x := measurable_subtype_coe.comp measurable_snd.fst
  have mz : Measurable z := measurable_snd.snd
  have mm : Measurable m := measurable_const.sub ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp measurable_fst)
  have mg : Measurable (Function.uncurry sample) := hg.comp ((mx.comp measurable_fst).prodMk measurable_snd)
  have mn : Measurable (Function.uncurry next) :=
    hp.comp ((mx.comp measurable_fst).sub (((measurable_const.mul mm).comp measurable_fst).smul
      ((measurable_clip C).comp mg)))
  have ma : Measurable (Function.uncurry adv) := by
    apply Measurable.prodMk ((measurable_of_countable Nat.succ).comp measurable_fst.fst)
    apply Measurable.prodMk mn.subtype_mk
    apply Measurable.add
    · exact ((((mm.sub_const 1).div (mm.add_const 1)).comp measurable_fst).smul (mz.comp measurable_fst))
    · exact (((measurable_const.div (mm.add_const 1)).comp measurable_fst).smul mn)
  have mA : Measurable A := (measurable_clip b).comp
    ((measurable_const.div (mm.add_const 1)).smul (mx.sub mz))
  have hb : 0 ≤ b := by rw [ht.direction_eq]; exact mul_nonneg (mul_nonneg (by norm_num) ht.slope_pos.le) ht.radius.le
  let s₀ : S := (0,⟨x₀,hx₀⟩,u)
  have tail := two_tails ma mg mA ν ht.level_pos ht.multiplier_pos.le ht.small
    (fun s => hmi _ s.2.1.property) (fun s => hm _ s.2.1.property)
    (fun s => norm_clip_le hb _) ξ T hlaw s₀ q
  apply (measure_mono ?_).trans tail
  intro a
  contrapose
  intro hn
  change ¬ (_ ∨ _) at hn
  rw [not_or] at hn
  let s := walk adv s₀ (fun i => ξ i a)
  let y := fun i => x (s i)
  let v := fun i => z (s i)
  let c := fun i => clip C (g (y i) (ξ i a))
  have time (i : ℕ) : (s i).1 = i := by
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg Nat.succ ih
  have meq (i : ℕ) : m (s i) = (T:ℝ)-i := by simp only [m,time]
  have hy (i : ℕ) : y (i+1) = proj (y i-(k*((T:ℝ)-i)) • c i) := by
    change next (s i) _ = _
    simp only [next,meq]; rfl
  have hv (i : ℕ) : v (i+1) = mix ((T:ℝ)-i) (v i) (y (i+1)) := by
    change mix (m (s i)) _ _ = _
    rw [meq]; rfl
  have hk (i : ℕ) : y i ∈ K := (s i).2.1.property
  have hvK (i : ℕ) (hi : i ≤ T) : v i ∈ K := by
    induction i with
    | zero => exact hu
    | succ i ih =>
      have hi' : (i:ℝ)+1 ≤ T := by exact_mod_cast hi
      have hw := mix_weights (show 1 ≤ (T:ℝ)-i by linarith)
      rw [hv]
      exact hf.1 (ih (by omega)) (hk _) hw.1 hw.2.1 hw.2.2
  have hpath (i : ℕ) (hi : i ≤ T) : path g proj k C T x₀ (fun i => ξ i a) i = y i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [path, ih (by omega), hy, Nat.cast_sub (show i ≤ T by omega)]
  have hres := pathwise (x := y) (z := v) (c := c) (u := u) ht hf rfl hmin hk hvK hstart
    (fun i _ => hv i)
    (fun i hi => by rw [hy]; exact TerminalClipping.projection_distance (hpv _ _ (hvK i hi.le)))
    (fun i hi => by
      rw [hy]
      exact TerminalClipping.projection_step (mul_nonneg ht.slope_pos.le (sub_nonneg.mpr (by exact_mod_cast hi.le)))
        (hpv _ _ (hk i)))
    (fun i hi => hsub _ (hk i) _ (hvK i hi.le))
    (fun i _ => TerminalClipping.objective_difference_from_moment (hgi _ (hk _)) (hmi _ (hk _))
      ht.scale.le (hm _ (hk _)) (hsub _ (hk _) _ (hk _)))
    (fun i _ => TerminalClipping.full_moment_clip_bias hg.of_uncurry_left
      (hgi _ (hk i)) (hmi _ (hk i)) ht.level_pos (hm _ (hk i)))
    (fun j hj => le_of_not_gt (fun h => hn.1 ⟨j,hj,h⟩))
    (fun j hj => le_of_not_gt (fun h => hn.2 ⟨j,hj,by
      change _ < ∑ i ∈ Finset.range j, -τ * ⟪c i - ∫ ω, clip C (g (y i) ω) ∂(ν : Measure Ω),
        clip b (direction (m (s i)) k (y i) (v i))⟫
      simpa only [meq] using h⟩))
  apply not_not_intro
  dsimp only
  constructor
  · intro j hj
    rw [hpath j hj]
    exact hres.1 j hj
  · rw [hpath T le_rfl]
    exact hres.2

end OracleTemplate.TerminalClippingSingleLog
