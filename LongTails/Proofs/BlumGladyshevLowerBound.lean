import LongTails.Proofs.BlumGladyshevOracle
import LongTails.TemplateLowerBound

open MeasureTheory ProbabilityTheory OracleTemplate OracleTemplate.CountdownMarkov
open LongTails.Proofs.BlumGladyshevMask LongTails.Proofs.BlumGladyshevTesting
open LongTails.Proofs.BlumGladyshevHardInstance
open LongTails.Setups.InterpolatedDistanceGrowingSubgradient (spec)
open LongTails.Setups.TerminalClippingConvex (Public Query)
open scoped RealInnerProductSpace

namespace LongTails.Proofs.BlumGladyshevLowerBound

lemma successful_tail {p : Public} (hR : 0 < p.R) (hε : 0 < p.ε) {e w : E p}
    (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (hew : ⟪e,w⟫ = 0)
    (A : Algorithm (Query p) (E p) (E p)) (q : unitInterval) (n : ℕ)
    (hs : spec.successful p (instanceOf p e w)
      (fun z : A.Seed × (ℕ → Bool) => execute (oracle p e w q) A (fun _ => n) z.1 z.2)
      ⟨(A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool)), inferInstance⟩) :
    ((A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool)))
      {z | p.ε < objective p e w (execute (oracle p e w q) A (fun _ => n) z.1 z.2)} ≤
      ENNReal.ofReal p.δ := by
  obtain ⟨_, _, u, _, hmin, hb⟩ := hs
  have hlu : objective p e w u ≤ objective p e w (point p e w) := hmin (Set.mem_univ _)
  obtain ⟨hc, ht⟩ := point_zero p hR he hw hew
  have hz : objective p e w u = 0 := by
    rw [show objective p e w (point p e w) = 0 by simp [objective,hc,ht]] at hlu
    exact le_antisymm hlu (objective_nonneg p hε e w u)
  change ((A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool)))
    {z | p.ε < objective p e w (execute (oracle p e w q) A (fun _ => n) z.1 z.2) - objective p e w u} ≤
    ENNReal.ofReal p.δ at hb
  simpa only [hz, sub_zero] using hb

lemma exists_failure (p : Public) (hp : spec.valid p)
    (A : Algorithm (Query p) (E p) (E p)) (n : ℕ)
    (hn : (n : ℝ) ≤ p.R^2*(p.G^2+p.B^2*p.R^2)*Real.log (1/p.δ)/(2^28*p.ε^2)) :
    ∃ I O, spec.admissible p I O ∧
      ¬ spec.successful p I
        (fun z : A.Seed × ((k : ℕ) → O.Seed k) =>
          execute O A (fun _ => n) z.1 z.2)
        ⟨(A.law : Measure A.Seed).prod (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩ := by
  obtain ⟨hd, _, hG, hR, hε, hscale, hδ, hδ'⟩ := hp
  obtain ⟨hpos,hqmax⟩ := mask_bounds hG hR hε hscale
  let q : unitInterval := ⟨probability p.G p.B p.R p.ε, hpos.le, by linarith⟩
  let i : Fin p.d := ⟨0, by omega⟩
  let j : Fin p.d := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  let e : E p := EuclideanSpace.single i 1
  let w : E p := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hw : ‖w‖ = 1 := by simp [w]
  have hew : ⟪e,w⟫ = 0 := by
    simp [e, w, EuclideanSpace.inner_single_left, hij]
  have hw' : ‖-w‖ = 1 := by simpa using hw
  have hew' : ⟪e,-w⟫ = 0 := by simp [hew]
  let out := fun (v : E p) (z : A.Seed × (ℕ → Bool)) =>
    execute (oracle p e v q) A (fun _ => n) z.1 z.2
  let P : ProbabilityMeasure (A.Seed × (ℕ → Bool)) :=
    ⟨(A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool)), inferInstance⟩
  have hprefix : 2*p.δ < (1-(q:ℝ))^(n+1) := prefix_failure hpos (by linarith)
    hδ hδ' (budget_times_probability hG hR hε hn)
  have hc : ∀ x, responses p e w q x false = responses p e (-w) q x false := by
    intro x
    cases x <;> simp [responses, field]
  have hnot := incompatible_success (responses p e w q) (responses p e (-w) q) q hc A n
    (objective p e w) (objective p e (-w)) hδ.le (objective_separation p hε e w) hprefix
  by_cases h : spec.successful p (instanceOf p e w) (out w) P
  · refine ⟨instanceOf p e (-w), oracle p e (-w) q,
      model_admissible p hG hR hε hscale he hw' hew' q rfl, ?_⟩
    exact fun h' => hnot ⟨successful_tail hR hε he hw hew A q n h,
      successful_tail hR hε he hw' hew' A q n h'⟩
  · exact ⟨instanceOf p e w, oracle p e w q,
      model_admissible p hG hR hε hscale he hw hew q rfl, h⟩

end LongTails.Proofs.BlumGladyshevLowerBound
