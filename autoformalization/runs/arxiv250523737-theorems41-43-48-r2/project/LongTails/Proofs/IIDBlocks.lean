import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.FiniteVariance

lemma infinite_block_law {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p) (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun k : ℕ => fun i : Fin n => ξ (k*n+i.val))
      P (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p) := by
  let index : ℕ × Fin n → ℕ := fun v => v.1*n+v.2.val
  have hinj : Function.Injective index := by
    intro a b h
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) a.2.isLt
    have hd := congrArg (fun t => t / n) h
    dsimp only [index] at hd h
    rw [Nat.mul_comm a.1, Nat.mul_comm b.1, Nat.mul_add_div hn, Nat.mul_add_div hn,
      Nat.div_eq_of_lt a.2.isLt, Nat.div_eq_of_lt b.2.isLt] at hd
    simp only [Nat.add_zero] at hd
    have hs : a.2 = b.2 := Fin.ext (by rw [hd] at h; exact Nat.add_left_cancel h)
    exact Prod.ext hd hs
  have hf : MeasurePreserving (fun ξ : ℕ → Ω => fun v : ℕ × Fin n => ξ (index v))
      P (Measure.infinitePi fun _ : ℕ × Fin n => p) := by
    refine ⟨by fun_prop, ?_⟩
    have h := (iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun v => measurable_pi_apply (index v))).mp (hind.precomp hinj)
    simpa only [hmarg] using h
  have hc : MeasurePreserving (MeasurableEquiv.curry ℕ (Fin n) Ω)
      (Measure.infinitePi fun _ : ℕ × Fin n => p)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => p) := by
    refine ⟨(MeasurableEquiv.curry ℕ (Fin n) Ω).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin n) => p))
  exact hc.comp hf

lemma paired_stream_law {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (hind : iIndepFun (fun k (ξ : ℕ → Ω) => ξ k) P)
    (hmarg : ∀ k, P.map (fun ξ => ξ k) = p) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun k : ℕ => (ξ (k*2), ξ (k*2+1)))
      P (Measure.infinitePi fun _ : ℕ => p.prod p) := by
  have hp : MeasurePreserving (fun ω : ℕ → (Fin 2 → Ω) => fun k => (ω k 0, ω k 1))
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin 2 => p)
      (Measure.infinitePi fun _ : ℕ => p.prod p) := by
    refine ⟨by fun_prop, ?_⟩
    have hf := measurePreserving_finTwoArrow p
    change (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin 2 => p).map
      (fun ω k => MeasurableEquiv.finTwoArrow (ω k)) = _
    rw [Measure.infinitePi_map_pi (fun _ : ℕ => Measure.pi fun _ : Fin 2 => p) (fun _ => hf.measurable)]
    simp only [hf.map_eq]
  have h := hp.comp (infinite_block_law p P hind hmarg 2)
  simpa [Function.comp_def] using h

end OracleTemplate.FiniteVariance
