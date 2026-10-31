import LongTails.Proofs.GeneralizedLipschitzSampling
import LongTails.Proofs.GeneralizedLipschitzConvex
import LongTails.Proofs.SgdExecution
import LongTails.Algorithms.GeneralizedLipschitzWarmStart
open scoped RealInnerProductSpace
namespace LongTails.Proofs.GeneralizedLipschitzWarmStart
lemma energy_increment_bound {S q : ℝ} (hS : 0 < S) (hq : 0 ≤ q) :
    q / Real.sqrt (S + q) ≤ 2 * (Real.sqrt (S + q) - Real.sqrt S) := by
  have ht : 0 < Real.sqrt (S + q) := Real.sqrt_pos.mpr (by linarith)
  have hs := Real.sq_sqrt hS.le
  have ht2 := Real.sq_sqrt (show 0 ≤ S + q by linarith)
  apply (div_le_iff₀ ht).mpr
  nlinarith [sq_nonneg (Real.sqrt (S + q) - Real.sqrt S)]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma projected_inner_bound (center z xstar h : E) {D η : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hstar : ‖xstar - center‖ ≤ D) :
    ⟪h, z - xstar⟫ ≤
      (‖z - xstar‖ ^ 2 - ‖center + OracleTemplate.clip D (z - η • h - center) - xstar‖ ^ 2) / (2 * η) +
        η * ‖h‖ ^ 2 / 2 := by
  have hp := OracleTemplate.norm_clip_sub_le hD hstar (z - η • h - center)
  have hp2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
  have he1 : OracleTemplate.clip D (z - η • h - center) - (xstar - center) =
      center + OracleTemplate.clip D (z - η • h - center) - xstar := by abel
  have he2 : z - η • h - center - (xstar - center) = (z - xstar) - η • h := by abel
  rw [he1, he2, norm_sub_sq_real (z - xstar) (η • h), real_inner_smul_right, real_inner_comm,
    norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow] at hp2
  have hmain : ⟪h, z - xstar⟫ ≤
      (‖z - xstar‖ ^ 2 - ‖center + OracleTemplate.clip D (z - η • h - center) - xstar‖ ^ 2 + η ^ 2 * ‖h‖ ^ 2) / (2 * η) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * η)).mpr
    nlinarith
  apply hmain.trans_eq
  field_simp
lemma adagrad_potential_step (center z xstar h : E) {D a b : ℝ}
    (hD : 0 < D) (hb : 0 < b) (hab : a ≤ b) (hsq : b ^ 2 = a ^ 2 + ‖h‖ ^ 2)
    (hz : ‖z - center‖ ≤ D) (hstar : ‖xstar - center‖ ≤ D) :
    let znew := center + OracleTemplate.clip D (z - (2 * D / b) • h - center)
    ⟪h, z - xstar⟫ ≤ b * (3 * D - ‖znew - xstar‖ ^ 2 / (4 * D)) -
      a * (3 * D - ‖z - xstar‖ ^ 2 / (4 * D)) := by
  let znew := center + OracleTemplate.clip D (z - (2 * D / b) • h - center)
  have hproj := projected_inner_bound center z xstar h hD.le (by positivity : 0 < 2 * D / b) hstar
  have he : (‖z - xstar‖ ^ 2 - ‖znew - xstar‖ ^ 2) / (2 * (2 * D / b)) +
      (2 * D / b) * ‖h‖ ^ 2 / 2 =
      b * (‖z - xstar‖ ^ 2 - ‖znew - xstar‖ ^ 2) / (4 * D) + D * (‖h‖ ^ 2 / b) := by
    field_simp
    ring
  change ⟪h, z - xstar⟫ ≤ (‖z - xstar‖ ^ 2 - ‖znew - xstar‖ ^ 2) / (2 * (2 * D / b)) + (2 * D / b) * ‖h‖ ^ 2 / 2 at hproj
  rw [he] at hproj
  have hq : ‖h‖ ^ 2 / b ≤ 2 * (b - a) := by
    apply (div_le_iff₀ hb).mpr
    nlinarith [sq_nonneg (b - a)]
  have hdist : ‖z - xstar‖ ≤ 2 * D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub z center xstar
    rw [norm_sub_rev center xstar] at hh
    linarith
  have hd2 : ‖z - xstar‖ ^ 2 ≤ 4 * D ^ 2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdist 2]
  apply hproj.trans
  change b * (‖z - xstar‖ ^ 2 - ‖znew - xstar‖ ^ 2) / (4 * D) + D * (‖h‖ ^ 2 / b) ≤
    b * (3 * D - ‖znew - xstar‖ ^ 2 / (4 * D)) - a * (3 * D - ‖z - xstar‖ ^ 2 / (4 * D))
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left hq hD.le)).trans
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 4 * D)).mp
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hd2)]
open LongTails.Algorithms.GeneralizedLipschitzWarmStart
lemma update_potential (center xstar : E) {D α : ℝ} (s : State E) (reply : E)
    (hD : 0 < D) (hE : 0 < s.2.2.2) (hz : ‖s.2.2.1 - center‖ ≤ D)
    (hstar : ‖xstar - center‖ ≤ D) :
    ⟪weight α s.1 • reply, s.2.2.1 - xstar⟫ ≤
      Real.sqrt (update center D α s reply).2.2.2 *
        (3 * D - ‖(update center D α s reply).2.2.1 - xstar‖ ^ 2 / (4 * D)) -
      Real.sqrt s.2.2.2 * (3 * D - ‖s.2.2.1 - xstar‖ ^ 2 / (4 * D)) := by
  let h := weight α s.1 • reply
  have he : 0 < s.2.2.2 + ‖h‖ ^ 2 := by positivity
  have hab := Real.sqrt_le_sqrt (show s.2.2.2 ≤ s.2.2.2 + ‖h‖ ^ 2 by nlinarith [sq_nonneg ‖h‖])
  have hsq : (Real.sqrt (s.2.2.2 + ‖h‖ ^ 2)) ^ 2 = (Real.sqrt s.2.2.2) ^ 2 + ‖h‖ ^ 2 := by
    rw [Real.sq_sqrt he.le, Real.sq_sqrt hE.le]
  exact adagrad_potential_step center s.2.2.1 xstar h hD (Real.sqrt_pos.mpr he) hab hsq hz hstar

lemma online_to_batch_step (f : E → ℝ) (prev z xstar g : E) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hsub : ∀ y, f ((1 - α) • prev + α • z) - f y ≤
      ⟪g, (1 - α) • prev + α • z - y⟫) :
    f ((1 - α) • prev + α • z) - f xstar ≤
      (1 - α) * (f prev - f xstar) + α * ⟪g, z - xstar⟫ := by
  let x := (1 - α) • prev + α • z
  have hp := mul_le_mul_of_nonneg_left (hsub prev) (sub_nonneg.mpr hα1)
  have hs := mul_le_mul_of_nonneg_left (hsub xstar) hα
  have he : (1 - α) * ⟪g, x - prev⟫ + α * ⟪g, x - xstar⟫ = α * ⟪g, z - xstar⟫ := by
    calc
      _ = ⟪g, (1 - α) • (x - prev) + α • (x - xstar)⟫ := by simp [inner_add_right, inner_smul_right]
      _ = ⟪g, α • (z - xstar)⟫ := by congr 1; dsimp [x]; module
      _ = _ := inner_smul_right _ _ _
  dsimp [x] at he
  nlinarith

lemma point_mem_ball (center : E) {D α : ℝ} (s : State E)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hx : ‖s.2.1 - center‖ ≤ D) (hz : ‖s.2.2.1 - center‖ ≤ D) :
    ‖point α s - center‖ ≤ D := by
  have he : point α s - center = (1 - α) • (s.2.1 - center) + α • (s.2.2.1 - center) := by
    dsimp [point]
    module
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hα1), abs_of_nonneg hα]
  have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hα1)
  have hz' := mul_le_mul_of_nonneg_left hz hα
  nlinarith
lemma update_invariant (center : E) {D α : ℝ} (s : State E) (reply : E)
    (hD : 0 ≤ D) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hx : ‖s.2.1 - center‖ ≤ D) (hz : ‖s.2.2.1 - center‖ ≤ D) (hE : 0 < s.2.2.2) :
    ‖(update center D α s reply).2.1 - center‖ ≤ D ∧
      ‖(update center D α s reply).2.2.1 - center‖ ≤ D ∧
      0 < (update center D α s reply).2.2.2 := by
  refine ⟨point_mem_ball center s hα hα1 hx hz, ?_, ?_⟩
  · dsimp [update]
    rw [add_sub_cancel_left]
    exact OracleTemplate.norm_clip_le hD _
  · dsimp [update]
    positivity

lemma adagrad_regret (center xstar : E) {D G0 : ℝ} (hD : 0 < D) (hG0 : 0 < G0)
    (z h : ℕ → E) (hstar : ‖xstar - center‖ ≤ D) (hz : ∀ n, ‖z n - center‖ ≤ D)
    (hupdate : ∀ n, z (n + 1) = center + OracleTemplate.clip D
      (z n - (2 * D / Real.sqrt (G0 ^ 2 + ∑ i ∈ Finset.range (n + 1), ‖h i‖ ^ 2)) • h n - center)) (N : ℕ) :
    (∑ i ∈ Finset.range N, ⟪h i, z i - xstar⟫) ≤
      3 * D * G0 + 3 * D * Real.sqrt (∑ i ∈ Finset.range N, ‖h i‖ ^ 2) := by
  let energy := fun n => G0 ^ 2 + ∑ i ∈ Finset.range n, ‖h i‖ ^ 2
  let phi := fun n => Real.sqrt (energy n) * (3 * D - ‖z n - xstar‖ ^ 2 / (4 * D))
  have hepos (n) : 0 < energy n := by dsimp [energy]; positivity
  have hesucc (n) : energy (n + 1) = energy n + ‖h n‖ ^ 2 := by simp [energy, Finset.sum_range_succ, add_assoc]
  have hstep (n) : ⟪h n, z n - xstar⟫ ≤ phi (n + 1) - phi n := by
    have hab : Real.sqrt (energy n) ≤ Real.sqrt (energy (n + 1)) := by
      apply Real.sqrt_le_sqrt
      rw [hesucc]
      nlinarith [sq_nonneg ‖h n‖]
    have hsq : (Real.sqrt (energy (n + 1))) ^ 2 = (Real.sqrt (energy n)) ^ 2 + ‖h n‖ ^ 2 := by
      rw [Real.sq_sqrt (hepos _).le, Real.sq_sqrt (hepos _).le, hesucc]
    have hp := adagrad_potential_step center (z n) xstar (h n) hD (Real.sqrt_pos.mpr (hepos _)) hab hsq (hz n) hstar
    dsimp only at hp
    dsimp [phi]
    rw [hupdate n]
    exact hp
  have hsum (n) : (∑ i ∈ Finset.range n, ⟪h i, z i - xstar⟫) ≤ phi n - phi 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [hstep n]
  have hdist : ‖z 0 - xstar‖ ≤ 2 * D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (z 0) center xstar
    rw [norm_sub_rev center xstar] at hh
    linarith [hz 0]
  have hphi0 : 0 ≤ phi 0 := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    have hd : ‖z 0 - xstar‖ ^ 2 / (4 * D) ≤ D := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * D)).mpr
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdist 2]
    linarith
  have hphiN : phi N ≤ 3 * D * Real.sqrt (energy N) := by
    have hh := mul_nonneg (Real.sqrt_nonneg (energy N))
      (div_nonneg (sq_nonneg ‖z N - xstar‖) (by positivity : 0 ≤ 4 * D))
    dsimp [phi]
    nlinarith
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, ‖h i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsqrt : Real.sqrt (energy N) ≤ G0 + Real.sqrt (∑ i ∈ Finset.range N, ‖h i‖ ^ 2) := by
    have he := Real.sq_sqrt (hepos N).le
    have hh := Real.sq_sqrt hsum0
    have hn := Real.sqrt_nonneg (energy N)
    have hm := Real.sqrt_nonneg (∑ i ∈ Finset.range N, ‖h i‖ ^ 2)
    dsimp [energy] at he
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 3 * D)
  linarith [hsum N]

lemma weighted_gap_telescope {α : ℝ} (hα1 : α < 1)
    (gap cost : ℕ → ℝ) (hstep : ∀ n, gap (n + 1) ≤ (1 - α) * gap n + α * cost n) (N : ℕ) :
    ((1 - α)⁻¹) ^ N * gap N ≤ gap 0 + ∑ i ∈ Finset.range N, weight α i * cost i := by
  have hbase : 0 < 1 - α := sub_pos.mpr hα1
  have hlocal (n : ℕ) : ((1 - α)⁻¹) ^ (n + 1) * gap (n + 1) ≤
      ((1 - α)⁻¹) ^ n * gap n + weight α n * cost n := by
    have he : ((1 - α)⁻¹) ^ (n + 1) * (1 - α) = ((1 - α)⁻¹) ^ n := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ hbase.ne', mul_one]
    calc
      _ ≤ ((1 - α)⁻¹) ^ (n + 1) * ((1 - α) * gap n + α * cost n) :=
        mul_le_mul_of_nonneg_left (hstep n) (by positivity)
      _ = _ := by rw [mul_add, ← mul_assoc, he]; dsimp [weight]; ring
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ]; linarith [hlocal N]

section Trajectory
variable {Ω : Type}
lemma trajectory_time (center : E) (D G0 α : ℝ) (oracle : E → Ω → E) (ξ : ℕ → Ω) (n : ℕ) :
    (trajectory center D G0 α oracle ξ n).1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [trajectory, update] using congrArg Nat.succ ih
lemma trajectory_energy (center : E) (D G0 α : ℝ) (oracle : E → Ω → E) (ξ : ℕ → Ω) (n : ℕ) :
    (trajectory center D G0 α oracle ξ n).2.2.2 = G0 ^ 2 +
      ∑ i ∈ Finset.range n, ‖weight α i • oracle (point α (trajectory center D G0 α oracle ξ i)) (ξ i)‖ ^ 2 := by
  induction n with
  | zero => simp [trajectory, initial]
  | succ n ih =>
    change (trajectory center D G0 α oracle ξ n).2.2.2 +
      ‖weight α (trajectory center D G0 α oracle ξ n).1 •
        oracle (point α (trajectory center D G0 α oracle ξ n)) (ξ n)‖ ^ 2 = _
    rw [ih, trajectory_time, Finset.sum_range_succ, add_assoc]
lemma trajectory_invariant (center : E) {D G0 α : ℝ} (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (oracle : E → Ω → E) (ξ : ℕ → Ω) (n : ℕ) :
    ‖(trajectory center D G0 α oracle ξ n).2.1 - center‖ ≤ D ∧
      ‖(trajectory center D G0 α oracle ξ n).2.2.1 - center‖ ≤ D ∧
      0 < (trajectory center D G0 α oracle ξ n).2.2.2 := by
  induction n with
  | zero => simpa only [trajectory, initial, sub_self, norm_zero] using And.intro hD (And.intro hD (sq_pos_of_pos hG0))
  | succ n ih => exact update_invariant center _ _ hD hα hα1 ih.1 ih.2.1 ih.2.2
lemma trajectory_regret (center xstar : E) {D G0 α : ℝ} (hD : 0 < D) (hG0 : 0 < G0)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hstar : ‖xstar - center‖ ≤ D)
    (oracle : E → Ω → E) (ξ : ℕ → Ω) (N : ℕ) :
    let s := trajectory center D G0 α oracle ξ
    let h := fun i => weight α i • oracle (point α (s i)) (ξ i)
    (∑ i ∈ Finset.range N, ⟪h i, (s i).2.2.1 - xstar⟫) ≤
      3 * D * G0 + 3 * D * Real.sqrt (∑ i ∈ Finset.range N, ‖h i‖ ^ 2) := by
  let s := trajectory center D G0 α oracle ξ
  let h := fun i => weight α i • oracle (point α (s i)) (ξ i)
  apply adagrad_regret center xstar hD hG0 (fun i => (s i).2.2.1) h hstar
  · intro n
    exact (trajectory_invariant center hD.le hG0 hα hα1 oracle ξ n).2.1
  · intro n
    have he := trajectory_energy center D G0 α oracle ξ (n + 1)
    change (s (n + 1)).2.2.2 = G0 ^ 2 + ∑ i ∈ Finset.range (n + 1), ‖h i‖ ^ 2 at he
    rw [← he]
    dsimp [s, trajectory, update, h]
    rw [trajectory_time]
end Trajectory

section Execution
variable {Ω : Type}
open OracleTemplate.StochasticGradient
lemma advance_trajectory (center : E) (D G0 α : ℝ) (oracle : E → Ω → E) (ξ : ℕ → Ω) (n k : ℕ) :
    advance (fun j s => update center D α s (oracle (point α s) (ξ j))) n k
      (trajectory center D G0 α oracle ξ k) = trajectory center D G0 α oracle ξ (k + n) := by
  induction n generalizing k with
  | zero => simp [advance]
  | succ n ih =>
    change advance (fun j s => update center D α s (oracle (point α s) (ξ j))) n (k + 1)
      (trajectory center D G0 α oracle ξ (k + 1)) = _
    rw [ih]
    congr 1
    omega
lemma output_eq_trajectory [MeasurableSpace Ω] (center : E) (D G0 α : ℝ)
    (oracle : E → Ω → E) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω)) (N : ℕ) (ξ : ℕ → Ω) :
    output center D G0 α N
      { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => oracle x ω } ξ =
      (trajectory center D G0 α oracle ξ N).2.1 := by
  apply (execute_advance P oracle (algorithm center D G0 α) N () ξ).trans
  have h := advance_trajectory center D G0 α oracle ξ N 0
  simpa only [algorithm, trajectory, Nat.zero_add] using congrArg (fun s => s.2.1) h
end Execution

section Measurable
open MeasureTheory
variable {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
lemma measurable_point (α : ℝ) : Measurable (point (E := E) α) :=
  (measurable_snd.fst.const_smul (1 - α)).add (measurable_snd.snd.fst.const_smul α)
lemma measurable_update_family (D α : ℝ) :
    Measurable (fun w : E × State E × E => update w.1 D α w.2.1 w.2.2) := by
  let h := fun w : E × State E × E => weight α w.2.1.1 • w.2.2
  have hw : Measurable (fun w : E × State E × E => weight α w.2.1.1) :=
    (measurable_from_nat (f := weight α)).comp measurable_snd.fst.fst
  have hh : Measurable h := hw.smul measurable_snd.snd
  have he : Measurable (fun w : E × State E × E => w.2.1.2.2.2 + ‖h w‖ ^ 2) :=
    measurable_snd.fst.snd.snd.snd.add (hh.norm.pow_const 2)
  have hη : Measurable (fun w : E × State E × E => 2 * D / Real.sqrt (w.2.1.2.2.2 + ‖h w‖ ^ 2)) :=
    measurable_const.div he.sqrt
  have hz : Measurable (fun w : E × State E × E => w.1 + OracleTemplate.clip D
      (w.2.1.2.2.1 - (2 * D / Real.sqrt (w.2.1.2.2.2 + ‖h w‖ ^ 2)) • h w - w.1)) :=
    measurable_fst.add ((OracleTemplate.measurable_clip D).comp
      ((measurable_snd.fst.snd.snd.fst.sub (hη.smul hh)).sub measurable_fst))
  have hn : Measurable (fun w : E × State E × E => w.2.1.1 + 1) :=
    (measurable_from_nat (f := fun n : ℕ => n + 1)).comp measurable_snd.fst.fst
  exact hn.prodMk (((measurable_point α).comp measurable_snd.fst).prodMk (hz.prodMk he))
lemma measurable_trajectory_family (D G0 α : ℝ) {oracle : E → Ω → E}
    (ho : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) => trajectory w.1 D G0 α oracle w.2 n) := by
  induction n with
  | zero => exact measurable_const.prodMk (measurable_fst.prodMk (measurable_fst.prodMk measurable_const))
  | succ n ih =>
    have hr : Measurable (fun w : E × (ℕ → Ω) =>
        oracle (point α (trajectory w.1 D G0 α oracle w.2 n)) (w.2 n)) :=
      ho.comp (((measurable_point α).comp ih).prodMk ((measurable_pi_apply n).comp measurable_snd))
    exact (measurable_update_family D α).comp (measurable_fst.prodMk (ih.prodMk hr))
end Measurable

lemma local_gap_refined (f : E → ℝ) (g x y xstar : E) (G0 G : ℝ)
    (hminy : f xstar ≤ f y)
    (hsub : f y - f x ≤ ⟪g, y - x⟫)
    (hgrad : ‖g‖ ≤ G0 + G * (f y - f xstar))
    (hsmall : G * ‖y - x‖ ≤ 1 / 4) (hG0 : 0 ≤ G0) :
    f y - f xstar ≤ (3 / 2 : ℝ) * (f x - f xstar) + 2 * G0 * ‖y - x‖ := by
  have h1 := LongTails.Proofs.GeneralizedLipschitzConvex.gap_le_norm_mul_distance f g y x hsub
  have h2 := mul_le_mul_of_nonneg_right hgrad (norm_nonneg (y - x))
  have h3 := mul_le_mul_of_nonneg_right hsmall (sub_nonneg.mpr hminy)
  nlinarith [mul_nonneg hG0 (norm_nonneg (y - x))]

lemma inverse_weight_power_bound {α : ℝ} (hα1 : α < 1) (n : ℕ)
    (hsmall : (n : ℝ) * α ≤ 1 / 2) : ((1 - α)⁻¹) ^ n ≤ 2 := by
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -α by linarith) n
  have hpow : (1 / 2 : ℝ) ≤ (1 - α) ^ n := by
    simp only [mul_neg, sub_eq_add_neg] at *
    linarith
  rw [inv_pow, inv_eq_one_div]
  apply (div_le_iff₀ (by positivity : 0 < (1 - α) ^ n)).mpr
  linarith
lemma weight_shift_bound {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (i n : ℕ)
    (hsmall : (n : ℝ) * α ≤ 1 / 2) : weight α (i + n) ≤ 2 * weight α i := by
  have hp := inverse_weight_power_bound hα1 n hsmall
  have he : weight α (i + n) = weight α i * ((1 - α)⁻¹) ^ n := by
    unfold weight
    rw [show i + n + 1 = (i + 1) + n by omega, pow_add]
    ring
  rw [he]
  have hw : 0 ≤ weight α i := by unfold weight; positivity
  nlinarith [mul_le_mul_of_nonneg_left hp hw]

section Movement
variable {Ω : Type}
lemma point_movement (center : E) {D α : ℝ} (s : State E) (hα : 0 ≤ α)
    (hx : ‖s.2.1 - center‖ ≤ D) (hz : ‖s.2.2.1 - center‖ ≤ D) :
    ‖point α s - s.2.1‖ ≤ 2 * α * D := by
  have he : point α s - s.2.1 = α • (s.2.2.1 - s.2.1) := by dsimp [point]; module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have hd : ‖s.2.2.1 - s.2.1‖ ≤ 2 * D := by
    have hh := norm_sub_le_norm_sub_add_norm_sub s.2.2.1 center s.2.1
    rw [norm_sub_rev center s.2.1] at hh
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hd hα]
lemma trajectory_movement (center : E) {D G0 α : ℝ} (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (oracle : E → Ω → E) (ξ : ℕ → Ω) (n : ℕ) :
    ‖(trajectory center D G0 α oracle ξ (n + 1)).2.1 -
      (trajectory center D G0 α oracle ξ n).2.1‖ ≤ 2 * α * D := by
  have hi := trajectory_invariant center hD hG0 hα hα1 oracle ξ n
  exact point_movement center _ hα hi.1 hi.2.1
lemma trajectory_distance (center : E) {D G0 α : ℝ} (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (oracle : E → Ω → E) (ξ : ℕ → Ω) (i n : ℕ) :
    ‖(trajectory center D G0 α oracle ξ (i + n)).2.1 -
      (trajectory center D G0 α oracle ξ i).2.1‖ ≤ n * (2 * α * D) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := norm_sub_le_norm_sub_add_norm_sub
      (trajectory center D G0 α oracle ξ (i + (n + 1))).2.1
      (trajectory center D G0 α oracle ξ (i + n)).2.1
      (trajectory center D G0 α oracle ξ i).2.1
    have hm := trajectory_movement center hD hG0 hα hα1 oracle ξ (i + n)
    rw [show i + (n + 1) = i + n + 1 by omega] at hh
    rw [show i + (n + 1) = i + n + 1 by omega]
    push_cast
    linarith
end Movement

lemma finite_l2_uniform_bound {ι : Type} (S : Finset ι) (x : ι → ℝ) {T U V : ℝ}
    (hT : 0 ≤ T) (hU : 0 ≤ U) (hV : 0 ≤ V) (hcard : (S.card : ℝ) ≤ 2 * T)
    (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 3 * U + 16 * V) :
    Real.sqrt (∑ i ∈ S, (x i) ^ 2) ≤ Real.sqrt T * (5 * U + 23 * V) := by
  have hsum0 : 0 ≤ ∑ i ∈ S, (x i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ i ∈ S, (x i) ^ 2) ≤ (S.card : ℝ) * (3 * U + 16 * V) ^ 2 := by
    calc _ ≤ ∑ _i ∈ S, (3 * U + 16 * V) ^ 2 := Finset.sum_le_sum (fun i hi => pow_le_pow_left₀ (hx i hi).1 (hx i hi).2 2)
         _ = _ := by simp [nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right hcard (sq_nonneg (3 * U + 16 * V))
  have hpoly : 2 * (3 * U + 16 * V) ^ 2 ≤ (5 * U + 23 * V) ^ 2 := by
    nlinarith [sq_nonneg U, sq_nonneg V, mul_nonneg hU hV]
  have ht := mul_le_mul_of_nonneg_left hpoly hT
  have hsq : (Real.sqrt T * (5 * U + 23 * V)) ^ 2 = T * (5 * U + 23 * V) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hT]
  have hp : 0 ≤ Real.sqrt T * (5 * U + 23 * V) := by positivity
  nlinarith [Real.sq_sqrt hsum0, Real.sqrt_nonneg (∑ i ∈ S, (x i) ^ 2)]
lemma finite_block_average {ι : Type} (S : Finset ι) (b : ι → ℝ) {T L : ℝ}
    (hT : 0 < T) (hL : 0 ≤ L) (hcard : T ≤ (S.card : ℝ))
    (hb : ∀ j ∈ S, L ≤ Real.sqrt T * b j) :
    L ≤ (∑ j ∈ S, b j) / Real.sqrt T := by
  have hsum := Finset.sum_le_sum hb
  have hh : (S.card : ℝ) * L ≤ Real.sqrt T * ∑ j ∈ S, b j := by
    simpa only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum] using hsum
  have ht : T * L ≤ Real.sqrt T * ∑ j ∈ S, b j :=
    (mul_le_mul_of_nonneg_right hcard hL).trans hh
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  apply (le_div_iff₀ hs).mpr
  apply (mul_le_mul_iff_left₀ hs).mp
  calc
    L * Real.sqrt T * Real.sqrt T = T * L := by
      rw [mul_assoc, ← sq, Real.sq_sqrt hT.le, mul_comm]
    _ ≤ Real.sqrt T * ∑ j ∈ S, b j := ht
    _ = _ := mul_comm _ _
lemma block_weighted_l2 {ι : Type} (S : Finset ι) (w gap : ι → ℝ) {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C) (hlo : T ≤ (S.card : ℝ)) (hhi : (S.card : ℝ) ≤ 2 * T)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hg : ∀ i ∈ S, 0 ≤ gap i)
    (hweight : ∀ i ∈ S, ∀ j ∈ S, w i ≤ 2 * w j)
    (hgap : ∀ i ∈ S, ∀ j ∈ S, gap i ≤ (3 / 2 : ℝ) * gap j + 8 * C) :
    Real.sqrt (∑ i ∈ S, (w i * gap i) ^ 2) ≤
      (5 / Real.sqrt T) * (∑ i ∈ S, w i * gap i) +
        (23 * C / Real.sqrt T) * (∑ i ∈ S, w i) := by
  have hb (j) (hj : j ∈ S) : Real.sqrt (∑ i ∈ S, (w i * gap i) ^ 2) ≤
      Real.sqrt T * (5 * (w j * gap j) + 23 * (w j * C)) := by
    apply finite_l2_uniform_bound S (fun i => w i * gap i) hT.le
      (mul_nonneg (hw j hj) (hg j hj)) (mul_nonneg (hw j hj) hC) hhi
    intro i hi
    refine ⟨mul_nonneg (hw i hi) (hg i hi), ?_⟩
    have h := mul_le_mul (hweight i hi j hj) (hgap i hi j hj) (hg i hi) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hw j hj))
    nlinarith
  have ha := finite_block_average S (fun j => 5 * (w j * gap j) + 23 * (w j * C))
    hT (Real.sqrt_nonneg _) hlo hb
  apply ha.trans_eq
  have he : (∑ j ∈ S, (5 * (w j * gap j) + 23 * (w j * C))) =
      5 * (∑ j ∈ S, w j * gap j) + 23 * C * (∑ j ∈ S, w j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

lemma weight_monotone {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) : Monotone (weight α) := by
  have hinv : 1 ≤ (1 - α)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (sub_pos.mpr hα1)).mpr
    linarith
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hinv (Nat.add_le_add_right hij 1)) hα
lemma weight_pair_bound {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (i j n : ℕ)
    (hij : i ≤ j + n) (hsmall : (n : ℝ) * α ≤ 1 / 2) : weight α i ≤ 2 * weight α j :=
  ((weight_monotone hα hα1) hij).trans (weight_shift_bound hα hα1 j n hsmall)
section PairDistance
variable {Ω : Type}
lemma trajectory_pair_distance (center : E) {D G0 α : ℝ} (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (oracle : E → Ω → E) (ξ : ℕ → Ω)
    (i j n : ℕ) (hij : i ≤ j + n) (hji : j ≤ i + n) :
    ‖(trajectory center D G0 α oracle ξ i).2.1 -
      (trajectory center D G0 α oracle ξ j).2.1‖ ≤ n * (2 * α * D) := by
  have hstep : 0 ≤ 2 * α * D := by positivity
  rcases le_total i j with h | h
  · have hd := trajectory_distance center hD hG0 hα hα1 oracle ξ i (j - i)
    rw [show i + (j - i) = j by omega, norm_sub_rev] at hd
    have hn : ((j - i : ℕ) : ℝ) ≤ n := by exact_mod_cast (show j - i ≤ n by omega)
    exact hd.trans (mul_le_mul_of_nonneg_right hn hstep)
  · have hd := trajectory_distance center hD hG0 hα hα1 oracle ξ j (i - j)
    rw [show j + (i - j) = i by omega] at hd
    have hn : ((i - j : ℕ) : ℝ) ≤ n := by exact_mod_cast (show i - j ≤ n by omega)
    exact hd.trans (mul_le_mul_of_nonneg_right hn hstep)
end PairDistance

lemma sqrt_add_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
lemma global_weighted_l2 (T : ℕ) (hT : 0 < T) {C : ℝ} (hC : 0 ≤ C) :
    ∀ N, T ≤ N → ∀ w gap : ℕ → ℝ,
    (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ gap i) →
    (∀ i j, i ≤ j + 2 * T → w i ≤ 2 * w j) →
    (∀ i j, i ≤ j + 2 * T → j ≤ i + 2 * T → gap i ≤ (3 / 2 : ℝ) * gap j + 8 * C) →
    Real.sqrt (∑ i ∈ Finset.range N, (w i * gap i) ^ 2) ≤
      (5 / Real.sqrt T) * (∑ i ∈ Finset.range N, w i * gap i) +
        (23 * C / Real.sqrt T) * (∑ i ∈ Finset.range N, w i) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hN w gap hw hg hweight hgap
    have hTr : (0 : ℝ) < T := by exact_mod_cast hT
    have hb (m : ℕ) (hlo : T ≤ m) (hhi : m ≤ 2 * T) :
        Real.sqrt (∑ i ∈ Finset.range m, (w i * gap i) ^ 2) ≤
          (5 / Real.sqrt T) * (∑ i ∈ Finset.range m, w i * gap i) +
          (23 * C / Real.sqrt T) * (∑ i ∈ Finset.range m, w i) := by
      apply block_weighted_l2 (Finset.range m) w gap hTr hC
      · simpa only [Finset.card_range] using (show (T : ℝ) ≤ m by exact_mod_cast hlo)
      · simpa only [Finset.card_range, Nat.cast_mul, Nat.cast_ofNat] using (show (m : ℝ) ≤ (2 * T : ℕ) by exact_mod_cast hhi)
      · exact fun i _ => hw i
      · exact fun i _ => hg i
      · intro i hi j hj
        exact hweight i j (by simp only [Finset.mem_range] at hi hj; omega)
      · intro i hi j hj
        exact hgap i j (by simp only [Finset.mem_range] at hi hj; omega) (by simp only [Finset.mem_range] at hi hj; omega)
    by_cases hsmall : N ≤ 2 * T
    · exact hb N hN hsmall
    · let M := N - T
      have hM : T ≤ M := by dsimp [M]; omega
      have hMN : M < N := by dsimp [M]; omega
      have htail := ih M hMN hM (fun i => w (T + i)) (fun i => gap (T + i))
        (fun i => hw (T + i)) (fun i => hg (T + i))
        (fun i j hij => hweight (T + i) (T + j) (by omega))
        (fun i j hij hji => hgap (T + i) (T + j) (by omega) (by omega))
      have hfirst := hb T le_rfl (by omega)
      have hsum (f : ℕ → ℝ) : (∑ i ∈ Finset.range N, f i) =
          (∑ i ∈ Finset.range T, f i) + ∑ i ∈ Finset.range M, f (T + i) := by
        simpa only [show T + M = N by dsimp [M]; omega] using Finset.sum_range_add f T M
      rw [hsum (fun i => (w i * gap i) ^ 2), hsum (fun i => w i * gap i), hsum w]
      have hroot := sqrt_add_bound
        (Finset.sum_nonneg (fun i (_ : i ∈ Finset.range T) => sq_nonneg (w i * gap i)))
        (Finset.sum_nonneg (fun i (_ : i ∈ Finset.range M) => sq_nonneg (w (T + i) * gap (T + i))))
      linarith

section OracleStability
open MeasureTheory LongTails.Setups.StochasticGeneralizedLipschitzConvex LongTails.Proofs.GeneralizedLipschitzSampling
variable {Ω : Type} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
lemma trajectory_local_gap (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {D G G0 G1 α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (T : ℕ) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (ξ : ℕ → Ω) (i j : ℕ) (hij : i ≤ j + 2 * T) (hji : j ≤ i + 2 * T) :
    f (trajectory center D G0 α oracle ξ i).2.1 - f xstar ≤
      (3 / 2 : ℝ) * (f (trajectory center D G0 α oracle ξ j).2.1 - f xstar) + 8 * α * T * D * G0 := by
  let x := (trajectory center D G0 α oracle ξ j).2.1
  let y := (trajectory center D G0 α oracle ξ i).2.1
  have hd := trajectory_pair_distance center hD hG0 hα hα1 oracle ξ i j (2 * T) hij hji
  change ‖y - x‖ ≤ (2 * T : ℕ) * (2 * α * D) at hd
  push_cast at hd
  have hdist : G * ‖y - x‖ ≤ 1 / 4 := by
    have hh := mul_le_mul_of_nonneg_left hd hG
    nlinarith
  have hgm := (oracle_moment_bounds ho hG0.le y).1
  have hg : ‖∫ ω, oracle y ω ∂p‖ ≤ G0 + G * (f y - f xstar) := by
    have hh := mul_le_mul_of_nonneg_right hGG (sub_nonneg.mpr (hmin y))
    linarith
  have hl := local_gap_refined f (∫ ω, oracle y ω ∂p) x y xstar G0 G
    (hmin y) (ho.subgradient y x) hg hdist hG0.le
  have hnoise := mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hG0.le)
  change f y - f xstar ≤ (3 / 2 : ℝ) * (f x - f xstar) + 8 * α * T * D * G0
  nlinarith
lemma trajectory_weighted_l2 (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {D G G0 G1 α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (hα : 0 ≤ α) (hα1 : α < 1) (T : ℕ) (hT : 0 < T) (hκ : 1 ≤ D * G) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (ξ : ℕ → Ω) (N : ℕ) (hN : T ≤ N) :
    let gap := fun i => f (trajectory center D G0 α oracle ξ (i + 1)).2.1 - f xstar
    Real.sqrt (∑ i ∈ Finset.range N, (weight α i * gap i) ^ 2) ≤
      (5 / Real.sqrt T) * (∑ i ∈ Finset.range N, weight α i * gap i) +
        (23 * Real.sqrt T * α * D * G0) * (∑ i ∈ Finset.range N, weight α i) := by
  let gap := fun i => f (trajectory center D G0 α oracle ξ (i + 1)).2.1 - f xstar
  have hw (i) : 0 ≤ weight α i := by unfold weight; positivity
  have hg (i) : 0 ≤ gap i := sub_nonneg.mpr (hmin _)
  have hαT : α * T ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left hκ (mul_nonneg hα (Nat.cast_nonneg T))
    nlinarith
  have hpair : ((2 * T : ℕ) : ℝ) * α ≤ 1 / 2 := by push_cast; nlinarith
  have hweights (i j : ℕ) (hij : i ≤ j + 2 * T) : weight α i ≤ 2 * weight α j :=
    weight_pair_bound hα hα1 i j (2 * T) hij hpair
  have hgaps (i j : ℕ) (hij : i ≤ j + 2 * T) (hji : j ≤ i + 2 * T) :
      gap i ≤ (3 / 2 : ℝ) * gap j + 8 * (α * T * D * G0) := by
    have h := trajectory_local_gap (center := center) p ho hD hG0 hG hGG hmin hα hα1.le T hsmall ξ (i + 1) (j + 1) (by omega) (by omega)
    dsimp [gap]
    nlinarith
  have hc : 0 ≤ α * T * D * G0 := by positivity
  have hb := global_weighted_l2 T hT hc N hN (weight α) gap hw hg hweights hgaps
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTr
  have he : 23 * (α * T * D * G0) / Real.sqrt T = 23 * Real.sqrt T * α * D * G0 := by
    field_simp
    rw [Real.sq_sqrt hTr.le]
    ring
  rw [he] at hb
  exact hb

lemma trajectory_initial_gap (p : Measure Ω) [IsProbabilityMeasure p]
    {f : E → ℝ} {oracle : E → Ω → E} {xstar center : E} {D G G0 G1 α : ℝ}
    (ho : IsOracle p f xstar oracle G0 G1) (hD : 0 ≤ D) (hG0 : 0 < G0)
    (hG : 0 ≤ G) (hGG : G1 ≤ G) (hmin : ∀ x, f xstar ≤ f x)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (T : ℕ) (hκ : 1 ≤ D * G) (hsmall : α * T * (D * G) ≤ 1 / 16)
    (hinit : f center - f xstar ≤ 64 * D * G0) (ξ : ℕ → Ω) (n : ℕ) (hn : n ≤ 2 * T) :
    f (trajectory center D G0 α oracle ξ n).2.1 - f xstar ≤ 100 * D * G0 := by
  have h := trajectory_local_gap (center := center) p ho hD hG0 hG hGG hmin hα hα1 T hsmall ξ n 0 (by omega) (by omega)
  have he : (trajectory center D G0 α oracle ξ 0).2.1 = center := rfl
  rw [he] at h
  have hαT : α * T ≤ 1 / 16 := by
    have hh := mul_le_mul_of_nonneg_left hκ (mul_nonneg hα (Nat.cast_nonneg T))
    nlinarith
  have heps := mul_le_mul_of_nonneg_right hαT (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hD) hG0.le)
  nlinarith [mul_nonneg hD hG0.le]

end OracleStability

lemma weight_difference {α : ℝ} (hα1 : α < 1) (n : ℕ) :
    weight α n = ((1 - α)⁻¹) ^ (n + 1) - ((1 - α)⁻¹) ^ n := by
  have hr := inv_mul_cancel₀ (sub_pos.mpr hα1).ne'
  have he : α * (1 - α)⁻¹ = (1 - α)⁻¹ - 1 := by nlinarith
  unfold weight
  rw [pow_succ]
  calc α * (((1 - α)⁻¹) ^ n * (1 - α)⁻¹) = ((1 - α)⁻¹) ^ n * (α * (1 - α)⁻¹) := by ring
       _ = _ := by rw [he]; ring
lemma weight_sum {α : ℝ} (hα1 : α < 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, weight α i) = ((1 - α)⁻¹) ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, weight_difference hα1]; ring
lemma weight_square_sum {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (N : ℕ) :
    (∑ i ∈ Finset.range N, (weight α i) ^ 2) ≤ α * (((1 - α)⁻¹) ^ N) ^ 2 := by
  induction N with
  | zero => simpa using hα
  | succ N ih =>
    rw [Finset.sum_range_succ]
    apply (add_le_add ih le_rfl).trans
    have he : ((1 - α)⁻¹) ^ N = ((1 - α)⁻¹) ^ (N + 1) * (1 - α) := by
      rw [pow_succ, mul_assoc, inv_mul_cancel₀ (sub_pos.mpr hα1).ne', mul_one]
    have hc : (1 - α) ^ 2 + α ≤ 1 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hα (sq_nonneg (((1 - α)⁻¹) ^ (N + 1))))
    rw [he, weight, mul_pow]
    nlinarith

lemma self_sum_comparison {c : ℝ} (hc : 0 ≤ c) (hc1 : c < 1)
    (z U a : ℕ → ℝ)
    (hz : ∀ n, z n ≤ a n + c * ∑ i ∈ Finset.range (n + 1), z i)
    (hU : ∀ n, a n + c * ∑ i ∈ Finset.range (n + 1), U i ≤ U n) :
    ∀ n, z n ≤ U n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hs : (∑ i ∈ Finset.range n, z i) ≤ ∑ i ∈ Finset.range n, U i :=
      Finset.sum_le_sum (fun i hi => ih i (Finset.mem_range.mp hi))
    have hm := mul_le_mul_of_nonneg_left hs hc
    have hz' := hz n
    have hU' := hU n
    rw [Finset.sum_range_succ] at hz' hU'
    nlinarith
lemma weighted_power_sum {α : ℝ} (hα1 : α < 1) (N : ℕ) :
    α * (∑ i ∈ Finset.range N, ((1 - α)⁻¹) ^ (i + 1)) = ((1 - α)⁻¹) ^ N - 1 := by
  simpa only [LongTails.Algorithms.GeneralizedLipschitzWarmStart.weight, Finset.mul_sum] using weight_sum hα1 N
lemma recurrence_supersolution {α F β : ℝ} (hα1 : α < 1)
    (hβ : 0 ≤ β) (N : ℕ) :
    F + β * ((1 - α)⁻¹) ^ N + (α / 4) *
      (∑ i ∈ Finset.range N, (F * ((1 - α / 4)⁻¹) ^ (i + 1) +
        (4 * β / 3) * ((1 - α)⁻¹) ^ (i + 1))) ≤
      F * ((1 - α / 4)⁻¹) ^ N + (4 * β / 3) * ((1 - α)⁻¹) ^ N := by
  have hq := weighted_power_sum (show α / 4 < 1 by linarith) N
  have hr := weighted_power_sum hα1 N
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hqF := congrArg (fun t => F * t) hq
  have hrβ := congrArg (fun t => β * t) hr
  nlinarith [hqF, hrβ]

lemma recurrence_geometric {α F β : ℝ} (hα : 0 < α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (z : ℕ → ℝ)
    (hz : ∀ k, z k ≤ F + β * ((1 - α)⁻¹) ^ k + (α / 4) *
      (∑ i ∈ Finset.range k, z (i + 1))) (N : ℕ) :
    z N ≤ F * ((1 - α / 4)⁻¹) ^ N + (4 * β / 3) * ((1 - α)⁻¹) ^ N := by
  have h := self_sum_comparison (show 0 ≤ α / 4 by positivity) (show α / 4 < 1 by linarith)
    (fun n => z (n + 1))
    (fun n => F * ((1 - α / 4)⁻¹) ^ (n + 1) + (4 * β / 3) * ((1 - α)⁻¹) ^ (n + 1))
    (fun n => F + β * ((1 - α)⁻¹) ^ (n + 1))
    (fun n => hz (n + 1)) (fun n => recurrence_supersolution hα1 hβ (n + 1))
  cases N with
  | zero => have hh := hz 0; simp only [pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at hh ⊢; linarith
  | succ n => exact h n
lemma recurrence_exponential {α F β : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hF : 0 ≤ F) (hβ : 0 ≤ β) (z : ℕ → ℝ)
    (hz : ∀ k, z k ≤ F + β * ((1 - α)⁻¹) ^ k + (α / 4) *
      (∑ i ∈ Finset.range k, z (i + 1))) (N : ℕ) :
    (1 - α) ^ N * z N ≤ F * Real.exp (-3 * α * N / 4) + 4 * β / 3 := by
  have hbase : 0 < 1 - α := sub_pos.mpr hα1
  have hden : 0 < 1 - α / 4 := by linarith
  have hr : (1 - α) / (1 - α / 4) ≤ Real.exp (-3 * α / 4) := by
    calc (1 - α) / (1 - α / 4) ≤ 1 - 3 * α / 4 := by
          apply (div_le_iff₀ hden).mpr
          nlinarith [sq_nonneg α]
         _ ≤ _ := by linarith [Real.add_one_le_exp (-3 * α / 4)]
  have hrpow := pow_le_pow_left₀ (div_nonneg hbase.le hden.le) hr N
  have hexp : (Real.exp (-3 * α / 4)) ^ N = Real.exp (-3 * α * N / 4) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hrpow
  have hh := mul_le_mul_of_nonneg_left (recurrence_geometric hα hα1 hβ z hz N)
    (pow_nonneg hbase.le N)
  have hid : (1 - α) ^ N * ((1 - α)⁻¹) ^ N = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hbase.ne', one_pow]
  have he : (1 - α) ^ N * (F * ((1 - α / 4)⁻¹) ^ N + (4 * β / 3) * ((1 - α)⁻¹) ^ N) =
      F * ((1 - α) / (1 - α / 4)) ^ N + 4 * β / 3 := by
    simp only [div_eq_mul_inv, mul_pow, inv_pow] at hid ⊢
    nlinarith [congrArg (fun t => (4 * β / 3) * t) hid]
  rw [he] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hrpow hF) le_rfl)


lemma warm_raw_coefficients {D G G0 α : ℝ} (hD : 0 ≤ D)
    (hG0 : 0 ≤ G0) (hα : 0 ≤ α) (T : ℕ) (hT : 0 < T)
    (hlarge : 60 * D * G ≤ Real.sqrt T) :
    15 * D * G / Real.sqrt T ≤ 1 / 4 ∧
    69 * Real.sqrt T * α * D ^ 2 * G * G0 ≤ 192 * T * α * D * G0 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hTr
  refine ⟨(div_le_iff₀ hs).mpr (by nlinarith), ?_⟩
  have hκ : D * G ≤ Real.sqrt T := by nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hm := mul_le_mul_of_nonneg_left hκ hs.le
  rw [Real.mul_self_sqrt hTr.le] at hm
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 69 * α * D * G0 by positivity)
  have hpos : 0 ≤ (T : ℝ) * α * D * G0 := by positivity
  nlinarith

lemma warm_recurrence_from_raw {D G G0 α A : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hG0 : 0 ≤ G0) (hα : 0 ≤ α) (hα1 : α < 1) (T : ℕ) (hT : 0 < T)
    (hlarge : 60 * D * G ≤ Real.sqrt T) (hA : A ≤ 64 * D * G0)
    (z : ℕ → ℝ) (hz : ∀ k, 0 ≤ z k)
    (hearly : ∀ k, k < T → z k ≤ 200 * D * G0)
    (hraw : ∀ k, T ≤ k → z k ≤ A + 3 * D * G0 +
      3 * D * G0 * Real.sqrt α * ((1 - α)⁻¹) ^ k +
      (15 * D * G / Real.sqrt T) * α * (∑ i ∈ Finset.range k, z (i + 1)) +
      (69 * Real.sqrt T * α * D ^ 2 * G * G0) *
        (∑ i ∈ Finset.range k, LongTails.Algorithms.GeneralizedLipschitzWarmStart.weight α i)) (N : ℕ) :
    z N ≤ 512 * D * G0 + (D * G0 * (3 * Real.sqrt α + 192 * T * α)) * ((1 - α)⁻¹) ^ N +
      (α / 4) * (∑ i ∈ Finset.range N, z (i + 1)) := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, z (i + 1) := Finset.sum_nonneg (fun i _ => hz (i + 1))
  have hpi : 0 ≤ ((1 - α)⁻¹) ^ N := pow_nonneg (inv_nonneg.mpr (sub_pos.mpr hα1).le) N
  have hDG0 : 0 ≤ D * G0 := mul_nonneg hD hG0
  by_cases hN : T ≤ N
  · have hr := hraw N hN
    rw [weight_sum hα1] at hr
    have hc := warm_raw_coefficients hD hG0 hα T hT hlarge
    have hs := mul_le_mul_of_nonneg_right hc.1 (mul_nonneg hα hsum)
    have hq := mul_le_mul_of_nonneg_right hc.2 hpi
    have hq0 : 0 ≤ 69 * Real.sqrt T * α * D ^ 2 * G * G0 := by positivity
    nlinarith
  · have he := hearly N (by omega)
    have hb : 0 ≤ (D * G0 * (3 * Real.sqrt α + 192 * T * α)) * ((1 - α)⁻¹) ^ N := by positivity
    have hs := mul_nonneg (show 0 ≤ α / 4 by positivity) hsum
    nlinarith


lemma warm_step_tuning {D G G0 ε : ℝ} (hD : 0 < D) (hG : 0 < G)
    (hG0 : 0 < G0) (hε : 0 < ε) (T : ℕ) (hT : 0 < T) (hκ : 1 ≤ D * G) :
    let α := min (1 / (16 * T * (D * G)))
      (min ((ε / (24 * D * G0)) ^ 2) (ε / (1536 * T * D * G0)))
    0 < α ∧ α < 1 ∧ α * T * (D * G) ≤ 1 / 16 ∧
      D * G0 * (3 * Real.sqrt α + 192 * T * α) ≤ ε / 4 := by
  let α := min (1 / (16 * T * (D * G)))
    (min ((ε / (24 * D * G0)) ^ 2) (ε / (1536 * T * D * G0)))
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hα : 0 < α := by dsimp [α]; positivity
  have h1 : α ≤ 1 / (16 * T * (D * G)) := min_le_left _ _
  have h2 : α ≤ (ε / (24 * D * G0)) ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : α ≤ ε / (1536 * T * D * G0) := (min_le_right _ _).trans (min_le_right _ _)
  have hs : α * T * (D * G) ≤ 1 / 16 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 16 * T * (D * G))).mp h1
    nlinarith
  have hα1 : α < 1 := by
    have hm := mul_le_mul hT1 hκ (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg T)
    have hm' := mul_le_mul_of_nonneg_left hm hα.le
    nlinarith
  refine ⟨hα, hα1, hs, ?_⟩
  have hroot : Real.sqrt α ≤ ε / (24 * D * G0) := (Real.sqrt_le_iff).mpr ⟨by positivity, h2⟩
  have hn := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 3 * D * G0 by positivity)
  have he : 3 * D * G0 * (ε / (24 * D * G0)) = ε / 8 := by
    field_simp
    ring
  rw [he] at hn
  have hd := (le_div_iff₀ (by positivity : 0 < 1536 * T * D * G0)).mp h3
  nlinarith
lemma warm_block_tuning {D G : ℝ} (hD : 0 < D) (hG : 0 < G) :
    let T := ⌈(96 * D * G) ^ 2⌉₊
    0 < T ∧ 60 * D * G ≤ Real.sqrt T := by
  have hb : (96 * D * G) ^ 2 ≤ (⌈(96 * D * G) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have hTp : (0 : ℝ) < (⌈(96 * D * G) ^ 2⌉₊ : ℝ) := lt_of_lt_of_le (by positivity) hb
  refine ⟨by exact_mod_cast hTp, ?_⟩
  have hs := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq (by positivity)] at hs
  nlinarith [mul_pos hD hG]

lemma warm_horizon_bound {α F β ε : ℝ} (hα : 0 < α) (hF : 0 ≤ F)
    (hε : 0 < ε) (hβ : β ≤ ε / 4) :
    let K := ⌈(2 / α) * Real.log (max 2 (2 * F / ε))⌉₊
    F * Real.exp (-3 * α * K / 4) + 4 * β / 3 ≤ ε := by
  let t := max 2 (2 * F / ε)
  let K := ⌈(2 / α) * Real.log t⌉₊
  have ht2 : 2 ≤ t := le_max_left _ _
  have ht : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hK : (2 / α) * Real.log t ≤ (K : ℝ) := Nat.le_ceil _
  have hm := mul_le_mul_of_nonneg_left hK hα.le
  have he : α * ((2 / α) * Real.log t) = 2 * Real.log t := by field_simp
  rw [he] at hm
  have hx : Real.exp (-3 * α * K / 4) ≤ t⁻¹ := by
    calc Real.exp (-3 * α * K / 4) ≤ Real.exp (-Real.log t) := Real.exp_le_exp.mpr (by nlinarith)
         _ = t⁻¹ := by rw [Real.exp_neg, Real.exp_log ht]
  have hf : F * t⁻¹ ≤ ε / 2 := by
    have hratio : 2 * F / ε ≤ t := le_max_right _ _
    have hf' := (div_le_iff₀ hε).mp hratio
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ ht).mpr
    nlinarith
  have hh := (mul_le_mul_of_nonneg_left hx hF).trans hf
  change F * Real.exp (-3 * α * K / 4) + 4 * β / 3 ≤ ε
  nlinarith


end LongTails.Proofs.GeneralizedLipschitzWarmStart
