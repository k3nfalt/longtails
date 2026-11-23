import LongTails.Proofs.ContaminatedTrainingDescent
import LongTails.Proofs.ContaminatedTrainingProbability

namespace LongTails.Proofs.ContaminatedTrainingHistory

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonCalendar (levels)
open LongTails.Algorithms.LeonTuning (resolution height iterations)
open LongTails.Algorithms
open ContaminatedParallelHistory ContaminatedParallelFailures ContaminatedTrainingGeometry ContaminatedTrainingDescent
open ContaminatedTreeProbability
open scoped Classical
variable {p : Params}

noncomputable abbrev count (p : Params) := (levels (height (network p))).length
noncomputable abbrev snapshot (D : Data p) (s : Samples p) := model D s (count p)
noncomputable abbrev point (D : Data p) (s : Samples p) (j : ℕ) := saved p (snapshot D s) j

lemma length (D : Data p) (s : Samples p) : (snapshot D s).training.history.length = iterations (network p) := by
  simpa [count,iterations,LeonCalendar.leaf_count] using history_count D s (count p) le_rfl

lemma gradient_sum (D : Data p) (s : Samples p)
    (hm : mass (fun t => weight p (level p t)) (bad D (trainOp p)) (count p) s < 1) :
    (∑ j : Fin (iterations (network p)), ‖D.G (point D s j)‖) ≤
      35 * (iterations (network p):ℝ) * resolution (network p) := by
  let a := resolution (network p)
  let K := (iterations (network p):ℝ)
  let η := a / p.L
  have hL := D.valid.2.1
  have ha : 0 < a := LeonBatchTuning.resolution_pos (network p) D.valid.2.2.2.1
  have hη : 0 < η := div_pos ha hL
  have hηL : η*p.L = a := div_mul_cancel₀ _ hL.ne'
  have hcost : p.L/2*η^2 = η*a/2 := by nlinarith only [congrArg (fun y => η*y) hηL]
  have hk := (div_le_iff₀ (sq_pos_of_pos ha)).mp (LeonBatchTuning.iterations_lower (network p))
  have hgap : p.Δ ≤ K*(η*a)/2 := by
    apply le_of_mul_le_mul_left (a := p.L) _ hL
    change 2*p.L*p.Δ ≤ K*a^2 at hk
    nlinarith only [hk,congrArg (fun y => K*y*a) hηL]
  have hh := total_error D s hm
  unfold ContaminatedTreeTracking.leafMass at hh
  rw [ContaminatedTreeMass.total_range] at hh
  have hd := descent D s (count p)
  dsimp only at hd
  have hl := length D s
  change (hist D s (count p)).length = iterations (network p) at hl
  rw [hl,LeonReturnedPoint.sum_get _ _ hl] at hd
  have he (i : Fin (iterations (network p))) :
      point D s i = ((hist D s (count p))[i.val]'(by rw [hl]; exact i.isLt)).1 := by
    simp [point,saved,List.getElem?_eq_getElem (show i.val < (hist D s (count p)).length by rw [hl]; exact i.isLt)]
  simp_rw [he]
  let S := ∑ i ∈ Finset.range (count p), if level p i = 0 then err D s i else 0
  change S ≤ 17*K*a at hh
  change η * _ ≤ _ - _ + 2*η*S + K*(p.L/2*η^2) at hd
  rw [hcost] at hd
  obtain ⟨lo,hlo,h₀⟩ := D.gap
  have hg : objective p D.f p.x0 - objective p D.f (x D s (count p)) ≤ p.Δ := by
    linarith only [h₀,hlo (x D s (count p))]
  apply le_of_mul_le_mul_left (a := η) _ hη
  change η*_ ≤ η*(35*K*a)
  linarith only [hd,hg,hgap,mul_le_mul_of_nonneg_left hh hη.le]

def regular {A : Type*} [SeminormedAddCommGroup A] (base : A) (a : ℝ) (ls : List A) : Prop :=
  ∀ i j : ℕ, i ≤ j → j < ls.length → ‖ls[i]?.getD base - ls[j]?.getD base‖ ≤ (j-i:ℕ)*a

lemma prepend {A : Type*} [SeminormedAddCommGroup A] {base u v : A} {a : ℝ} {xs : List A}
    (h : regular base a (u::xs)) (hm : ‖v-u‖ ≤ a) : regular base a (v::u::xs) := by
  intro i j hij hj
  cases i with
  | zero =>
    cases j with
    | zero => simp
    | succ j =>
      have hh := h 0 j (Nat.zero_le _) (by simpa using hj)
      simp only [List.getElem?_cons_zero,Option.getD_some,Nat.sub_zero] at hh
      simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Nat.sub_zero,Nat.cast_succ]
      linarith only [norm_sub_le_norm_sub_add_norm_sub v u ((u::xs)[j]?.getD base),hm,hh]
  | succ i =>
    cases j with
    | zero => omega
    | succ j =>
      simpa only [List.getElem?_cons_succ,Nat.succ_sub_succ_eq_sub] using
        h i j (by omega) (by simpa using hj)

lemma path (D : Data p) (s : Samples p) (t : ℕ) :
    let xs := (hist D s t).map (fun z => D.G z.1)
    let a := resolution (network p)
    regular (D.G p.x0) a (D.G (x D s t) :: xs) ∧
      ∀ y ∈ D.G (x D s t) :: xs, ‖y‖ ≤ ‖D.G p.x0‖ + (hist D s t).length * a := by
  induction t with
  | zero =>
    change regular _ _ [_] ∧ ∀ y ∈ [D.G p.x0], ‖y‖ ≤ ‖D.G p.x0‖ + (0:ℕ)*_
    constructor
    · intro i j hij hj
      simp only [List.length_singleton] at hj
      obtain rfl : j = 0 := by omega
      obtain rfl : i = 0 := by omega
      simp
    · simp
  | succ t ih =>
    dsimp only at ih ⊢
    by_cases hz : level p t = 0
    · have hh : hist D s (t+1) = (x D s t,‖v D s t‖) :: hist D s t := by
        unfold hist; rw [step]; simp [LeonTrajectory.applyEstimate,hz]
      have h := mul_le_mul_of_nonneg_left (one_move D s t) D.valid.2.1.le
      rw [ite_eq_left hz,mul_comm p.L (resolution (network p) / p.L),div_mul_cancel₀ _ D.valid.2.1.ne'] at h
      have hm : ‖D.G (x D s (t+1))-D.G (x D s t)‖ ≤ resolution (network p) := (D.smooth _ _).trans h
      rw [hh,List.map_cons,List.length_cons]
      refine ⟨prepend ih.1 hm,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · have hp := ih.2 _ List.mem_cons_self
        push_cast
        linarith only [hp,hm,norm_le_norm_sub_add (D.G (x D s (t+1))) (D.G (x D s t))]
      · have hp := ih.2 _ hy
        push_cast
        linarith only [hp,(LeonBatchTuning.resolution_pos (network p) D.valid.2.2.2.1).le]
    · have hh : hist D s (t+1) = hist D s t := by unfold hist; rw [step]; simp [LeonTrajectory.applyEstimate,hz]
      have hx : x D s (t+1) = x D s t := by unfold x; rw [step]; simp [LeonTrajectory.applyEstimate,hz]
      simpa only [hh,hx] using ih

end LongTails.Proofs.ContaminatedTrainingHistory
