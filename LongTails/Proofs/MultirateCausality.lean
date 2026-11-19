import LongTails.Proofs.MultiratePackets
import LongTails.Proofs.LeonSampling

namespace LongTails.Proofs.MultirateCausality

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Algorithms
open MultirateSchedule MultirateTrajectory MultiratePackets

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p)

abbrev Index (p : Params) := (i : Fin p.n) × Fin (batch p i)
abbrev Coord (p : Params) := Fin p.n × ℕ

noncomputable def coord (k : ℕ) (z : Index p) : Coord p :=
  (z.1, block p z.1 k * (batch p z.1 : ℕ) + z.2)

noncomputable def release (z : Coord p) : ℕ :=
  (z.2 / (batch p z.1 : ℕ)) * (period p z.1 : ℕ)

lemma release_coord (k : ℕ) (a : Index p) :
    release (coord k a) = block p a.1 k * (period p a.1 : ℕ) := by
  simp only [coord,release]
  rw [Nat.mul_comm (block _ _ _), Nat.mul_add_div (batch p a.1).pos, Nat.div_eq_of_lt a.2.isLt, Nat.add_zero]

lemma release_le (k : ℕ) (a : Index p) : release (coord k a) ≤ k := by
  rw [release_coord]; exact Nat.div_mul_le_self _ _

lemma anchor_release (k : ℕ) (a : Index p) : anchor p a.1 (block p a.1 k) ≤ release (coord k a) := by
  rw [release_coord]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

lemma coord_inj (k : ℕ) : Function.Injective (coord (p := p) k) := by
  rintro ⟨i,u⟩ ⟨j,w⟩ h
  obtain rfl : i = j := congrArg Prod.fst h
  congr 1
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Prod.snd h)

noncomputable def atCoord (a : Coord p) (s : Samples p) := s a.1 a.2

lemma mean_eq (s : Samples p) (k : ℕ) (i : Fin p.n) :
    LeonTrajectory.mean (network p) (replies g s k i) =
      ((batch p i : ℝ)⁻¹) • ∑ u : Fin (batch p i), g i (x g s (anchor p i (block p i k)))
        (atCoord (coord k ⟨i,u⟩) s) := by
  simp [replies,values,LeonTrajectory.mean,LeonAdaptiveSampling.list_range_sum,coord,atCoord]

variable {Y : Type*} [MeasurableSpace Y] (s : Y → Samples p)
  (hg : ∀ i, Measurable (Function.uncurry (g i)))

include hg in
lemma estimate_measurable (k : ℕ)
    (hx : ∀ i, Measurable fun y => x g (s y) (anchor p i (block p i k)))
    (hs : ∀ a : Index p, Measurable fun y => atCoord (coord k a) (s y)) :
    Measurable fun y => v g (s y) k := by
  have hm (i) : Measurable (fun y => LeonTrajectory.mean (network p) (replies g (s y) k i)) := by
    simp_rw [mean_eq]
    apply Measurable.fun_const_smul
    exact Finset.measurable_sum _ (fun u _ => (hg i).comp ((hx i).prodMk (hs ⟨i,u⟩)))
  have hr : Measurable (fun y => raw p (replies g (s y) k)) := by
    apply Measurable.of_eval
    intro j
    unfold raw LeonTrajectory.totalCodes
    apply Finset.measurable_sum
    intro i _
    have hcode := (DashaQuantization.measurable_indices p.d false (LeonTuning.spacing (network p))).comp
      (((hm i).sub (measurable_const (a := (0 : Point p)))).prodMk (measurable_const (a := fun _ : Fin p.d => (0 : ℝ))))
    exact (measurable_pi_apply j).comp hcode
  have hv := LeonMeasurability.measurable_decode (network p) (level p) _ _ (measurable_const (a := (0 : Point p))) hr
  convert hv using 1
  funext y
  change estimate p (packets g (s y) k) = _
  rw [show packets g (s y) k = _ from funext (packet_eq g (s y) k),decode_raw]
  rfl

include hg in
lemma point_measurable (t : ℕ)
    (hs : ∀ k < t, ∀ a : Index p, Measurable fun y => atCoord (coord k a) (s y)) :
    Measurable fun y => x g (s y) t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => exact measurable_const
    | succ k =>
      have hprev (j : ℕ) (hj : j ≤ k) := ih j (by omega) (fun k' hk' a => hs k' (by omega) a)
      have hv := estimate_measurable g s hg k (fun i => hprev _ (anchor_bounds (p := p) i k).1)
        (hs k (by omega))
      simp_rw [x_step]
      exact (hprev k le_rfl).sub ((measurable_const.div hv.norm).smul hv)

noncomputable abbrev others (a : Coord p) : MeasurableSpace (Samples p) :=
  ⨆ j ∈ ({a}ᶜ : Set (Coord p)), MeasurableSpace.comap (atCoord j) p.measurableΩ

lemma coord_measurable (j : Coord p) : Measurable (atCoord j) := by unfold atCoord; fun_prop

lemma other_measurable {j a : Coord p} (h : j ≠ a) :
    Measurable[others a] (atCoord j) :=
  Measurable.of_comap_le (le_iSup_of_le j (le_iSup_of_le h le_rfl))

include hg in
lemma point_without (a : Coord p) (t : ℕ) (ht : t ≤ release a) :
    Measurable[others a] (fun s => x g s t) := by
  apply @point_measurable p g (Samples p) (others a) id hg t
  intro k hk z
  apply other_measurable
  intro he
  have h := release_le k z
  rw [he] at h
  omega

lemma independent_other (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hi : ∀ i, IID (fun k (s : Samples p) => s i k) (μ i : Measure _) P)
    (a : Coord p) (Z : Samples p → Y) (hZ : Measurable[others a] Z) :
    IndepFun Z (atCoord a) P := by
  let m := fun j : Coord p => MeasurableSpace.comap (atCoord j) p.measurableΩ
  have hind : iIndep m P := DistributedSampling.independent_coordinates (network p) P μ hw hi
  have he := indep_iSup_of_disjoint (fun j => (coord_measurable (p := p) j).comap_le) hind
    (show Disjoint ({a}ᶜ : Set (Coord p)) {a} from disjoint_compl_left)
  apply indep_of_indep_of_le he hZ.comap_le
  exact le_iSup_of_le a (le_iSup_of_le (Set.mem_singleton a) le_rfl)

end LongTails.Proofs.MultirateCausality
