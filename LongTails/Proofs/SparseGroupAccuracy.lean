import LongTails.Proofs.SparseGroupCertificate
import LongTails.Proofs.SparseGroupEmpirical
import LongTails.Proofs.SparseGroupCounts

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SparseGroupAccuracy

open LongTails.Setups.OptimumGapGroupDro LongTails.Algorithms.SparseGroupSampling
open SparseGroupGeometry SparseGroupChoices SparseGroupEmpirical SparseGroupCertificate

lemma upper_eq_empirical (q : Public) (s : State q) (ω : Reservoir q)
    (ht : ∀ i h, s.2.1 i h = ∑ k ∈ Finset.range (s.1 i), q.loss h.val (ω k i)) :
    ∀ i h, upper q s i h = upperRisk q ω s.1 i h.val := by
  intro i h
  simp only [upper, upperRisk, empirical, ht]

lemma mesh_objective_le (q : Public) (p : ProbabilityMeasure (Rows q)) (s : State q)
    (ω : Reservoir q)
    (ht : ∀ i h, s.2.1 i h = ∑ k ∈ Finset.range (s.1 i), q.loss h.val (ω k i))
    (hc : ∀ i, ∀ h : PrimalIndex q,
      |empirical q ω i (s.1 i) h.val - risk q p i h.val| ≤ radius q (s.1 i)) :
    objective q p (primalChoice q s).val ≤
      upper q s (finiteMaximizer (fun i => upper q s i (primalChoice q s))) (primalChoice q s) := by
  apply ciSup_le
  intro i
  have h := hc i (primalChoice q s)
  have hlo := neg_le_abs (empirical q ω i (s.1 i) (primalChoice q s).val -
    risk q p i (primalChoice q s).val)
  have hu : risk q p i (primalChoice q s).val ≤ upper q s i (primalChoice q s) := by
    rw [upper_eq_empirical q s ω ht]
    unfold upperRisk
    linarith
  exact hu.trans (le_finiteMaximizer (fun i => upper q s i (primalChoice q s)) i)

lemma state_certificate (q : Public) (p : ProbabilityMeasure (Rows q)) (s : State q)
    (ω : Reservoir q) (xstar : Space q.d) (Δ : Fin q.K → ℝ)
    (hε : 0 < q.ε) (hG : 0 ≤ q.G) (hx0 : q.x0 ∈ q.domain)
    (hbound : ∀ x ∈ q.domain, ‖x - q.x0‖ ≤ q.R) (hQ : Convex ℝ q.domain)
    (hm : Measurable (Function.uncurry q.loss))
    (hconv : ∀ z, ConvexOn ℝ q.domain (fun x => q.loss x z))
    (hb : ∀ z, ∀ x ∈ q.domain, 0 ≤ q.loss x z ∧ q.loss x z ≤ 1)
    (hl : ∀ z, ∀ x ∈ q.domain, ∀ y ∈ q.domain,
      |q.loss x z - q.loss y z| ≤ q.G * ‖x - y‖)
    (hxstar : xstar ∈ q.domain)
    (hmin : IsMinOn (objective q p) q.domain xstar)
    (hΔ : ∀ i, Δ i ≤ objective q p xstar - risk q p i xstar)
    (ht : ∀ i h, s.2.1 i h = ∑ k ∈ Finset.range (s.1 i), q.loss h.val (ω k i))
    (hc : ∀ i, ∀ h : PrimalIndex q,
      |empirical q ω i (s.1 i) h.val - risk q p i h.val| ≤ radius q (s.1 i)) :
    (∑ i, (dualChoice q s).val i * Δ i) ≤
        2 * ∑ i, (dualChoice q s).val i * radius q (s.1 i) + q.ε / (8 * (q.d + 1 : ℝ)) ∧
    objective q p (primalChoice q s).val - objective q p xstar ≤
        2 * ∑ i, (dualChoice q s).val i * radius q (s.1 i) -
          (∑ i, (dualChoice q s).val i * Δ i) + q.ε / (8 * (q.d + 1 : ℝ)) := by
  let w := (dualChoice q s).val
  let V := upper q s (finiteMaximizer (fun i => upper q s i (primalChoice q s))) (primalChoice q s)
  let ρ := (q.d + 1 : ℝ) * coordinateScale q
  let E := 4 * q.G * ρ + q.ε / (64 * (q.d + 1 : ℝ)) + 2 * q.K * dualMeshRadius q
  have hw := (dualMesh_valid q hε).2.1 w (dualChoice q s).property
  have hsad := state_saddle_bound q s (upperRisk q ω s.1) hε hG hx0 hbound hQ
    (fun i => upperRisk_convex q ω s.1 i hQ hconv)
    (fun i _ hx _ hy => upperRisk_lipschitz q ω s.1 i hG hl hx hy)
    (by intro i x hx; rw [abs_of_nonneg (upperRisk_bounds q ω s.1 i hx hb).1]; exact (upperRisk_bounds q ω s.1 i hx hb).2)
    (upper_eq_empirical q s ω ht) xstar hxstar
  have hu : ∀ i, upperRisk q ω s.1 i xstar ≤ risk q p i xstar + 2 * radius q (s.1 i) + 2 * q.G * ρ :=
    fun i => confidence_extension q p ω s.1 hε hG hx0 hbound hm hb hl hc i hxstar
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hu i) (hw.1 i))
  have hsumEq : (∑ i, w i * (risk q p i xstar + 2 * radius q (s.1 i) + 2 * q.G * ρ)) =
      (∑ i, w i * (risk q p i xstar + 2 * radius q (s.1 i))) + 2 * q.G * ρ := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hw.2.1, one_mul]
  rw [hsumEq] at hsum
  have hsad' : V ≤ (∑ i, w i * (risk q p i xstar + 2 * radius q (s.1 i))) + E := by
    change V ≤ (∑ i, w i * upperRisk q ω s.1 i xstar) + _ at hsad
    dsimp [E, ρ]
    dsimp [ρ] at hsum
    linarith
  have hcert := SparseConfidenceCertificate.certificate_of_upper_risks w
    (fun i => radius q (s.1 i)) (fun i => risk q p i xstar)
    (fun i => risk q p i xstar + 2 * radius q (s.1 i)) V (objective q p xstar) E
    hw.1 hw.2.1 (fun _ => le_rfl) hsad'
  have hgap := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (hΔ i) (hw.1 i))
  have hE := discretization_error_le q hε hG
  change E ≤ q.ε / (8 * (q.d + 1 : ℝ)) at hE
  have hobj := mesh_objective_le q p s ω ht hc
  change objective q p (primalChoice q s).val ≤ V at hobj
  have hfeas := (primalMesh_valid q hε hG hx0 hbound).2.2.1
    (primalChoice q s).val (primalChoice q s).property
  have hopt : objective q p xstar ≤ objective q p (primalChoice q s).val := hmin hfeas
  constructor <;> dsimp only [w] at * <;> linarith

lemma certified_gap_le (q : Public) (s : State q) (Δ : Fin q.K → ℝ) (gap : ℝ)
    (hε : 0 < q.ε) (hΔ : ∀ i, 0 ≤ Δ i) (hs : certified q s)
    (hgap : gap ≤ 2 * ∑ i, (dualChoice q s).val i * radius q (s.1 i) -
      (∑ i, (dualChoice q s).val i * Δ i) + q.ε / (8 * (q.d + 1 : ℝ))) :
    gap ≤ q.ε := by
  have hw := (dualMesh_valid q hε).2.1 (dualChoice q s).val (dualChoice q s).property
  obtain ⟨S, hcard, hsupp⟩ := hw.2.2
  apply SparseConfidenceCertificate.output_gap_bound (dualChoice q s).val
    (fun i => radius q (s.1 i)) Δ S (q.ε / (4 * (q.d + 1 : ℝ))) q.ε gap
    (q.ε / (8 * (q.d + 1 : ℝ))) hΔ hw.1 hsupp
  · intro i _
    exact (le_finiteMaximizer (uncertainty q s) i).trans hs
  · have hc : (S.card : ℝ) ≤ q.d + 1 := by exact_mod_cast hcard
    have hsp : (0 : ℝ) < q.d + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hc
      (div_nonneg hε.le (by positivity : 0 ≤ 4 * (q.d + 1 : ℝ)))
    have he : (q.d + 1 : ℝ) * (q.ε / (4 * (q.d + 1 : ℝ))) = q.ε / 4 := by field_simp
    rw [he] at hmul
    have hsmall : q.ε / (8 * (q.d + 1 : ℝ)) ≤ q.ε / 8 := by
      apply div_le_div_of_nonneg_left hε.le (by norm_num)
      have := Nat.cast_nonneg (α := ℝ) q.d
      linarith
    linarith
  · exact hgap

lemma uncertified_selected_count (q : Public) (s : State q) (Δ : Fin q.K → ℝ)
    (hε : 0 < q.ε) (hΔ : ∀ i, 0 ≤ Δ i) (hL : 0 ≤ confidenceLog q)
    (hs : ¬ certified q s)
    (hc : (∑ i, (dualChoice q s).val i * Δ i) ≤
      2 * ∑ i, (dualChoice q s).val i * radius q (s.1 i) + q.ε / (8 * (q.d + 1 : ℝ))) :
    (s.1 (selectedGroup q s) : ℝ) ≤
      128 * (q.d + 1 : ℝ) ^ 2 * confidenceLog q / max (Δ (selectedGroup q s)) q.ε ^ 2 := by
  have hw := (dualMesh_valid q hε).2.1 (dualChoice q s).val (dualChoice q s).property
  obtain ⟨S, hcard, hsupp⟩ := hw.2.2
  have hr := SparseGroupCounts.selected_radius_bound (dualChoice q s).val
    (fun i => radius q (s.1 i)) Δ S (selectedGroup q s) (q.d + 1 : ℝ) q.ε
    (q.ε / (8 * (q.d + 1 : ℝ))) (by have := Nat.cast_nonneg (α := ℝ) q.d; linarith)
    hε (by exact_mod_cast hcard) hw.1 hw.2.1 (fun i => radius_nonneg q (s.1 i)) hΔ hsupp
    (le_finiteMaximizer (uncertainty q s)) hc le_rfl (lt_of_not_ge hs)
  exact SparseGroupCounts.radius_count_bound q _ _ (hε.trans_le (le_max_right _ _)) hL hr

end LongTails.Proofs.SparseGroupAccuracy
