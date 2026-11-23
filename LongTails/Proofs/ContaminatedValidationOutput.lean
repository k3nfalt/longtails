import LongTails.Proofs.ContaminatedValidationState

namespace LongTails.Proofs.ContaminatedValidationOutput

open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms.LeonTuning (resolution height iterations)
open ContaminatedParallelHistory ContaminatedParallelFailures ContaminatedTrainingGeometry
open ContaminatedTrainingHistory ContaminatedValidationCalendar ContaminatedValidationState
open scoped Classical
variable {p : Params}

def eligible (p : Params) (b : Point p × ℝ) := 0 ≤ b.2 ∧ b.2 ≤ p.ε/2+2*resolution (network p)

lemma choice (D : Data p) (b : Point p × ℝ) (x y : Point p)
    (hs : 0 ≤ b.2 → ‖D.G b.1‖ ≤ b.2 + 2*resolution (network p))
    (hy : ‖y-D.G x‖ ≤ 2*resolution (network p)) :
    let b' := if 0 ≤ b.2 ∧ b.2 ≤ ‖y‖ then b else (x,‖y‖)
    (0 ≤ b'.2 → ‖D.G b'.1‖ ≤ b'.2 + 2*resolution (network p)) ∧
      ((eligible p b ∨ ‖D.G x‖ ≤ p.ε/2) → eligible p b') := by
  dsimp only
  have h₁ := norm_le_norm_sub_add y (D.G x)
  have h₂ := norm_le_norm_sub_add (D.G x) y
  rw [norm_sub_rev (D.G x)] at h₂
  split_ifs with h
  · refine ⟨hs,?_⟩
    rintro (h₀|h₀)
    · exact h₀
    · exact ⟨h.1,by linarith only [h₁,h.2,hy,h₀]⟩
  · refine ⟨fun _ => by dsimp only; linarith only [h₂,hy],?_⟩
    rintro (h₀|h₀)
    · exact ⟨norm_nonneg _,(le_of_not_ge (fun hb => h ⟨h₀.1,hb⟩)).trans h₀.2⟩
    · exact ⟨norm_nonneg _,by dsimp only; linarith only [h₀,h₁,hy]⟩

lemma validate (D : Data p) (s : Samples p) (z : Seed p)
    (xs : List (Fin (iterations (network p)))) (prior : Option (Fin (iterations (network p)))) (t : ℕ)
    (hset : (run D s z t).training = (snapshot D s).training)
    (hsched : ∀ i < xs.length, ops p z (t+i) = atOp (validationOps (height (network p)) (prior.map Fin.val) xs) i)
    (hgood : ∀ i < xs.length, s ∉ bad D (ops p z) (t+i))
    (hsort : xs.Pairwise (· ≤ ·))
    (hprior : match prior with
      | none => (run D s z t).anchor = 0
      | some k => (∀ j ∈ xs, k ≤ j) ∧ ‖(run D s z t).anchor-D.G (point D s k)‖ ≤ 2*resolution (network p))
    (hsound : 0 ≤ (run D s z t).best.2 → ‖D.G (run D s z t).best.1‖ ≤ (run D s z t).best.2+2*resolution (network p))
    (hfound : eligible p (run D s z t).best ∨ ∃ j ∈ xs, ‖D.G (point D s j)‖ ≤ p.ε/2) :
    ‖D.G (run D s z (t+xs.length)).best.1‖ ≤ p.ε := by
  let a := resolution (network p)
  have ha : 0 ≤ a := (LeonBatchTuning.resolution_pos _ D.valid.2.2.2.1).le
  induction xs generalizing prior t with
  | nil =>
    simp only [List.not_mem_nil,false_and,exists_false,or_false] at hfound
    simp only [List.length_nil,Nat.add_zero]
    have h := hsound hfound.1
    have h₂ := hfound.2
    unfold resolution at h h₂
    linarith only [h,h₂,D.valid.2.2.2.1]
  | cons j xs ih =>
    let l := (prior.map Fin.val).elim (height (network p)) (fun k => Nat.clog 4 (1+(j.val-k)))
    have ho : ops p z t = .validate j.val l := by simpa [atOp,validationOps,l] using hsched 0 (by simp)
    let m := run D s z t
    let op := ops p z t
    let y := ContaminatedParallelTrajectory.decoded
      (ContaminatedParallelTrajectory.read p D.g s (used p (ops p z) t) m op)
    have hx : location p m op = point D s j := by
      dsimp only [op]; rw [ho]; change (m.training.history[j.val]?.getD _).1 = _
      rw [show m.training = _ from hset]; rfl
    have hr : reference p m op = m.anchor := by dsimp only [op]; rw [ho]; rfl
    have hl : op.level = l := by dsimp only [op]; rw [ho]; rfl
    have hstep : run D s z (t+1) = advance p m (.validate j.val l) y := by
      change advance p m op y = _
      exact congrArg (fun o => advance p m o y) ho
    have hy : ‖y-D.G (point D s j)‖ ≤ 2*a := by
      rw [← hx]
      apply decode_accurate D (ops p z) s t (by simpa using hgood 0 (by simp))
      change ‖reference p m op - D.G (location p m op)‖ + 2*a ≤ Algorithms.LeonTuning.radius (network p) op.level
      rw [hr,hx,hl]
      unfold Algorithms.LeonTuning.radius
      cases prior with
      | none =>
        change m.anchor = 0 at hprior
        rw [hprior,zero_sub,norm_neg]
        change _ ≤ 8*(4:ℝ)^height (network p)*a
        have h₁ := initial_scale D s j
        change _ ≤ 2*(4:ℝ)^height (network p)*a at h₁
        linarith only [h₁,mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4) (n := height (network p))) ha,ha]
      | some k =>
        obtain ⟨hk,hold⟩ := hprior
        have hh := gap_scale D s k j (hk j List.mem_cons_self)
        have hn := norm_sub_le_norm_sub_add_norm_sub m.anchor (D.G (point D s k)) (D.G (point D s j))
        let b := j.val-k.val
        have hp : (1:ℝ)+(b:ℝ) ≤ (4:ℝ)^Nat.clog 4 (1+b) := by exact_mod_cast Nat.le_pow_clog (by decide : 1<4) (1+b)
        change _ ≤ 8*(4:ℝ)^Nat.clog 4 (1+b)*a
        change ‖m.anchor-_‖ ≤ 2*a at hold
        change _ ≤ (b:ℝ)*a at hh
        nlinarith only [hn,hold,hh,mul_le_mul_of_nonneg_right hp ha,ha,show 0 ≤ (b:ℝ)*a by positivity]
    have he : (run D s z (t+1)).best =
        (if 0 ≤ m.best.2 ∧ m.best.2 ≤ ‖y‖ then m.best else (point D s j,‖y‖)) := by
      rw [hstep]; change (if _ then _ else (location p m (.validate j.val l),_)) = _
      have hr' : location p m (.validate j.val l) = point D s j := by rw [← ho]; exact hx
      rw [hr']
    obtain ⟨hs,hc⟩ := choice D m.best _ y hsound hy
    rw [← he] at hs hc
    obtain ⟨hord,hrest⟩ := List.pairwise_cons.mp hsort
    have hnew : eligible p (run D s z (t+1)).best ∨ ∃ k ∈ xs, ‖D.G (point D s k)‖ ≤ p.ε/2 := by
      rcases hfound with hb | ⟨k,hk,hk'⟩
      · exact Or.inl (hc (Or.inl hb))
      · rcases List.mem_cons.mp hk with rfl | hk
        · exact Or.inl (hc (Or.inr hk'))
        · exact Or.inr ⟨k,hk,hk'⟩
    have hh := ih (some j) (t+1) (by rw [hstep]; exact hset) (fun i hi => by
      have h := hsched (i+1) (by simp only [List.length_cons]; omega)
      simpa only [validationOps,atOp,List.getElem?_cons_succ,Option.map_some, Nat.add_right_comm t 1 i, ← Nat.add_assoc] using h)
      (fun i hi => by have h := hgood (i+1) (by simp only [List.length_cons]; omega); simpa [Nat.add_assoc,Nat.add_comm 1] using h)
      hrest (by refine ⟨hord,?_⟩; rw [hstep]; exact hy) hs hnew
    simpa only [List.length_cons,Nat.add_right_comm t 1 xs.length, ← Nat.add_assoc] using hh

end LongTails.Proofs.ContaminatedValidationOutput
