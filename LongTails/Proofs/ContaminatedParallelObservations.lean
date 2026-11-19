import LongTails.Proofs.ContaminatedParallelSampling
import LongTails.Proofs.ContaminatedParallelTrajectory

namespace LongTails.Proofs.ContaminatedParallelObservations

open MeasureTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms
open ContaminatedParallelSampling ContaminatedParallelEstimator ContaminatedParallelTrajectory
open OracleTemplate.RobustGradient

noncomputable def replies (p : Params) (q : ℕ) (g : Fin p.n → Point p → p.Ω → Point p)
    (x : Point p) (s : Samples p) (i : Fin p.n) : List (Point p) :=
  (List.range (batch p q i)).map (fun k => g i x (s i k))

lemma local_estimate (p : Params) (q : ℕ) (g : Fin p.n → Point p → p.Ω → Point p)
    (x : Point p) (s : Samples p) (i : Fin p.n) :
    estimate p q i (replies p q g x s i) =
      ((freshCount p q i : ℝ)⁻¹) • ∑ j : Fin (freshCount p q i),
        centeredClip (radius p q i) (centers p q g x s i) (g i x (s i (pilotCount p q+j))) := by
  have h1 (j : Fin (pilotCount p q)) : j.val < (batch p q i : ℕ) := by
    change j.val < pilotCount p q + freshCount p q i
    omega
  have h2 (j : Fin (freshCount p q i)) : pilotCount p q + j.val < (batch p q i : ℕ) :=
    Nat.add_lt_add_left j.isLt _
  simp only [estimate, replies, List.getElem?_map, List.getElem?_range (h1 _),
    List.getElem?_range (h2 _), Option.map_some, Option.getD_some, centers]

noncomputable def localAverage (p : Params) (q : ℕ) (g : Fin p.n → Point p → p.Ω → Point p)
    (x : Point p) (s : Samples p) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, estimate p q i (replies p q g x s i)

lemma average_error (p : Params) (q : ℕ) (g : Fin p.n → Point p → p.Ω → Point p)
    (f : Functions p) (hf : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (x : Point p) (s : Samples p) :
    localAverage p q g x s - gradient (objective p f) x = sampledError p q g f x s := by
  have he : gradient (objective p f) x = (p.n : ℝ)⁻¹ • ∑ i, gradient (f i) x :=
    (OracleTemplate.FiniteSum.objective_gradient (f := f)
      (oracle := fun ix : Fin p.n × Point p => gradient (f ix.1) ix.2) hf x).gradient
  rw [he, localAverage, ← smul_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  unfold sampledError centeredSum
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have hm : 0 < freshCount p q i := by unfold freshCount; omega
  rw [local_estimate]
  let V (j : Fin (freshCount p q i)) := centeredClip (radius p q i) (centers p q g x s i)
    (g i x (s i (pilotCount p q+j)))
  change (p.n : ℝ)⁻¹ • (((freshCount p q i : ℝ)⁻¹) • ∑ j, V j - gradient (f i) x) =
    ∑ j, ((p.n : ℝ) * freshCount p q i)⁻¹ • (V j - gradient (f i) x)
  have hmean := finite_mean_centered (X := V) (gradient (f i) x) (freshCount p q i) hm id
  simp only [one_div, id_eq] at hmean
  rw [hmean, smul_smul, ← Finset.smul_sum, mul_inv_rev, mul_comm]

lemma measurable_local {A : Type*} [MeasurableSpace A] (p : Params) (q : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (x : A → Point p) (hx : Measurable x) (s : A → Samples p)
    (hm : ∀ i k, k < (batch p q i : ℕ) → Measurable (fun a => s a i k)) (i : Fin p.n) :
    Measurable (fun a => estimate p q i (replies p q g (x a) (s a) i)) := by
  simp_rw [local_estimate]
  apply Measurable.fun_const_smul
  apply Finset.measurable_fun_sum
  intro j _
  have hc := measurable_centers p q g hg x hx s (fun i k hk => hm i k (by
    change k < pilotCount p q + freshCount p q i; omega))
  have hf := (hg i).comp (hx.prodMk (hm i _ (Nat.add_lt_add_left j.isLt _)))
  exact measurable_centeredClip_joint.comp (measurable_const.prodMk (((measurable_pi_apply i).comp hc).prodMk hf))

lemma measurable_average {A : Type*} [MeasurableSpace A] (p : Params) (q : ℕ)
    (g : Fin p.n → Point p → p.Ω → Point p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (x : A → Point p) (hx : Measurable x) (s : A → Samples p)
    (hm : ∀ i k, k < (batch p q i : ℕ) → Measurable (fun a => s a i k)) :
    Measurable (fun a => localAverage p q g (x a) (s a)) :=
  (Finset.measurable_fun_sum _ (fun i _ => measurable_local p q g hg x hx s hm i)).fun_const_smul _

noncomputable def freshSamples (p : Params) (u : Fin p.n → ℕ) := LeonAdaptiveSampling.shifted (network p) u

noncomputable def noise (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (u : Fin p.n → ℕ) (m : Model p) (op : Operation) (s : Samples p) : ℝ :=
  ‖localAverage p (op.precision p) g (location p m op) (freshSamples p u s) -
    gradient (objective p f) (location p m op)‖

lemma rounding_error (p : Params) (hε : 0 < p.ε) (g : Fin p.n → Point p → p.Ω → Point p)
    (f : Functions p) (u : Fin p.n → ℕ) (m : Model p) (op : Operation) (s : Samples p) :
    ‖reference p m op + Algorithms.LeonAggregate.displacement p.n (LeonTuning.spacing (network p))
      (rawCodes (ContaminatedParallelTrajectory.read p g s u m op)) - gradient (objective p f) (location p m op)‖ ≤
      LeonTuning.resolution (network p) + noise p g f u m op s := by
  let r := ContaminatedParallelTrajectory.read p g s u m op
  let a := reference p m op
  let v (i) := estimate p (op.precision p) i (r.values i)
  let old : LeonTrajectory.Model (network p) := ⟨location p m op,fun _ => a,[]⟩
  have hm (i) : LeonTrajectory.mean (network p) [v i] = v i := by simp [LeonTrajectory.mean]
  have he : LeonTrajectory.totalCodes (network p) old op.level (fun i => [v i]) = rawCodes r := by
    funext j
    simp only [LeonTrajectory.totalCodes, hm]
    rfl
  have hh := LeonRounding.raw_error (network p) hε old op.level (fun i => [v i])
  rw [he] at hh
  simp only [hm] at hh
  exact (norm_sub_le_norm_sub_add_norm_sub _ (localAverage p (op.precision p) g (location p m op)
    (freshSamples p u s)) _).trans (add_le_add_left hh _)

end LongTails.Proofs.ContaminatedParallelObservations
