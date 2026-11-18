import LongTails.Algorithms.DistributedNormalizedProtocol
import LongTails.Proofs.DistributedNormalizedCompression
import LongTails.Proofs.DistributedRandomRounding

namespace LongTails.Proofs.DistributedNormalizedProtocol

open DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink
open LongTails.Algorithms.DistributedNormalizedProtocol

lemma uplink_message_length (p : Params) (cfg : Config) (D : Draws p)
    (k : ℕ) (i : Fin p.n) (v : Point p) :
    (uplinkMessage p cfg D k i v).length = uplinkPayload p cfg := by
  unfold uplinkMessage uplinkPayload
  cases cfg.fullUplink <;> simp only [Bool.false_eq_true, ↓reduceIte,
    DistributedRandomRounding.message_length, DistributedNormalizedCompression.sparse_message_length]

lemma downlink_message_length (p : Params) (cfg : Config) (D : Draws p)
    (k : ℕ) (i : Fin p.n) (x u : Point p) :
    (downlinkMessage p cfg D k i x u).length = downlinkPayload p cfg k := by
  unfold downlinkMessage downlinkPayload
  cases refresh cfg k <;> simp only [Bool.false_eq_true, ↓reduceIte,
    DistributedRandomRounding.message_length, DistributedNormalizedCompression.sparse_message_length]

lemma uplink_receive_frame (p : Params) (cfg : Config) (D : Draws p)
    (k : ℕ) (i : Fin p.n) (v : Point p) (padding : List Bool) :
    uplinkReceive p cfg D k i (uplinkMessage p cfg D k i v ++ padding) =
      uplinkReceive p cfg D k i (uplinkMessage p cfg D k i v) := by
  have hfull (w : Point p) (u : Fin p.d → ℝ) :
      LongTails.Algorithms.DistributedNormalizedCompression.fullReceive p.d cfg.uplinkWidth cfg.uplinkSpacing
        (LongTails.Algorithms.DistributedRandomRounding.message p.d cfg.uplinkWidth cfg.uplinkSpacing w u ++ padding) =
      LongTails.Algorithms.DistributedNormalizedCompression.fullReceive p.d cfg.uplinkWidth cfg.uplinkSpacing
        (LongTails.Algorithms.DistributedRandomRounding.message p.d cfg.uplinkWidth cfg.uplinkSpacing w u) := by
    rw [DistributedNormalizedCompression.full_receive_message]
    simpa only [List.append_nil] using
      (DistributedNormalizedCompression.full_receive_message p.d cfg.uplinkWidth cfg.uplinkSpacing w u []).symm
  unfold uplinkReceive uplinkMessage
  cases cfg.fullUplink
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [DistributedNormalizedCompression.sparse_receive_message]
    simpa only [List.append_nil] using
      (DistributedNormalizedCompression.sparse_receive_message cfg.uplinkWidth cfg.uplinkCount cfg.uplinkSpacing
        (OracleTemplate.clip cfg.clipRadius v) (fun q => (D (2 * k) i q.val).1)
          (fun q => (D (2 * k) i q.val).2) []).symm
  · simp only [↓reduceIte]
    exact hfull _ _

lemma downlink_receive_frame (p : Params) (cfg : Config) (D : Draws p)
    (k : ℕ) (i : Fin p.n) (x u previous : Point p) (padding : List Bool) :
    downlinkReceive p cfg D k i previous (downlinkMessage p cfg D k i x u ++ padding) =
      downlinkReceive p cfg D k i previous (downlinkMessage p cfg D k i x u) := by
  unfold downlinkReceive downlinkMessage
  cases refresh cfg k
  · simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1
    rw [DistributedNormalizedCompression.sparse_receive_message]
    simpa only [List.append_nil] using
      (DistributedNormalizedCompression.sparse_receive_message cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing
        u (fun q => (D (2 * k + 1) i q.val).1) (fun q => (D (2 * k + 1) i q.val).2) []).symm
  · simp only [↓reduceIte]
    congr 1
    rw [DistributedNormalizedCompression.full_receive_message]
    simpa only [List.append_nil] using
      (DistributedNormalizedCompression.full_receive_message p.d cfg.downlinkWidth cfg.refreshSpacing
        (x - p.x0) (fun j => (D (2 * k + 1) i j.val).2) []).symm

noncomputable def workerMessage (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) (k : ℕ) (i : Fin p.n) : List Bool :=
  uplinkMessage p cfg D k i (batchMean p cfg g samples k i ((trajectory p cfg D g samples k).workers i))

noncomputable def rootMessage (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) (k : ℕ) (i : Fin p.n) : List Bool :=
  downlinkMessage p cfg D k i (trajectory p cfg D g samples (k + 1)).root
    (increment cfg (estimator p cfg D g samples k (trajectory p cfg D g samples k)))

lemma receive_rootMessage (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) (k : ℕ) (i : Fin p.n)
    (padding : List Bool) :
    downlinkReceive p cfg D k i ((trajectory p cfg D g samples k).workers i)
      (rootMessage p cfg D g samples k i ++ padding) = (trajectory p cfg D g samples (k + 1)).workers i := by
  unfold rootMessage
  rw [downlink_receive_frame]
  rfl

structure RootPoints (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p) : Prop where
  draws : s.draws = D
  point : s.point = (trajectory p cfg D g samples s.iteration).root
  index : s.outputIndex = selected.val
  selected_point : s.selected =
    if selected.val ≤ s.iteration then (trajectory p cfg D g samples selected.val).root else p.x0

structure RootData (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p) : Prop extends RootPoints p cfg D g samples selected s where
  accumulator : s.accumulator = ∑ i ∈ s.arrived,
    uplinkReceive p cfg D s.iteration i (workerMessage p cfg D g samples s.iteration i)

lemma initial_root_data (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) :
    RootData p cfg D g samples selected
      { draws := D, point := p.x0, selected := p.x0, outputIndex := selected.val } := by
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ?_⟩
  · dsimp only
    split_ifs with h
    · have hi : selected.val = 0 := Nat.eq_zero_of_le_zero h
      rw [hi]
      rfl
    · rfl
  · simp only [Finset.sum_empty]

lemma finish_root_points (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p) (aggregate : Point p)
    (hs : RootPoints p cfg D g samples selected s)
    (haggregate : (p.n : ℝ)⁻¹ • aggregate = estimator p cfg D g samples s.iteration
      (trajectory p cfg D g samples s.iteration)) :
    RootPoints p cfg D g samples selected (finish p cfg s aggregate) := by
  have hx : s.point + increment cfg ((p.n : ℝ)⁻¹ • aggregate) =
      (trajectory p cfg D g samples (s.iteration + 1)).root := by
    rw [hs.point, haggregate]
    rfl
  refine ⟨hs.draws, hx, hs.index, ?_⟩
  change (if s.iteration + 1 = s.outputIndex then s.point + increment cfg ((p.n : ℝ)⁻¹ • aggregate) else s.selected) =
    if selected.val ≤ s.iteration + 1 then (trajectory p cfg D g samples selected.val).root else p.x0
  by_cases he : s.iteration + 1 = s.outputIndex
  · rw [ite_eq_left he]
    have hi : selected.val = s.iteration + 1 := (he.trans hs.index).symm
    rw [hi, ite_eq_left le_rfl]
    exact hx
  · rw [ite_eq_right he, hs.selected_point]
    have hi := hs.index
    by_cases hle : selected.val ≤ s.iteration
    · rw [ite_eq_left hle, ite_eq_left (by omega)]
    · rw [ite_eq_right hle, ite_eq_right (by omega)]

lemma completed_aggregate (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p) (i : Fin p.n)
    (hs : RootData p cfg D g samples selected s) (hi : i ∉ s.arrived)
    (hall : insert i s.arrived = Finset.univ) :
    (p.n : ℝ)⁻¹ • (s.accumulator + uplinkReceive p cfg D s.iteration i
      (workerMessage p cfg D g samples s.iteration i)) =
      estimator p cfg D g samples s.iteration (trajectory p cfg D g samples s.iteration) := by
  rw [hs.accumulator]
  unfold estimator
  congr 1
  have he := Finset.sum_insert hi (f := fun j => uplinkReceive p cfg D s.iteration j
    (workerMessage p cfg D g samples s.iteration j))
  rw [hall] at he
  simp only [workerMessage] at he ⊢
  rw [he]
  abel

lemma accept_root_data (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p) (i : Fin p.n) (padding : List Bool)
    (hs : RootData p cfg D g samples selected s) (hi : i ∉ s.arrived)
    (hk : s.iteration < cfg.iterations) :
    RootData p cfg D g samples selected
      (accept p cfg s i.succ (workerMessage p cfg D g samples s.iteration i ++ padding)) := by
  have hframe : uplinkReceive p cfg D s.iteration i
      (workerMessage p cfg D g samples s.iteration i ++ padding) =
      uplinkReceive p cfg D s.iteration i (workerMessage p cfg D g samples s.iteration i) := by
    unfold workerMessage
    exact uplink_receive_frame p cfg D s.iteration i _ padding
  unfold accept
  simp only [Fin.cases_succ]
  rw [ite_eq_left ⟨hi, hk⟩, hs.draws, hframe]
  by_cases hall : insert i s.arrived = Finset.univ
  · rw [ite_eq_left hall]
    refine ⟨finish_root_points p cfg D g samples selected s _ hs.toRootPoints
      (completed_aggregate p cfg D g samples selected s i hs hi hall), ?_⟩
    simp only [finish, Finset.sum_empty]
  · rw [ite_eq_right hall]
    refine ⟨⟨rfl, hs.point, hs.index, hs.selected_point⟩, ?_⟩
    change s.accumulator + uplinkReceive p cfg D s.iteration i
      (workerMessage p cfg D g samples s.iteration i) = ∑ j ∈ insert i s.arrived,
        uplinkReceive p cfg D s.iteration j (workerMessage p cfg D g samples s.iteration j)
    rw [Finset.sum_insert hi, hs.accumulator]
    abel

structure WorkerData (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (i : Fin p.n) (s : State p) : Prop where
  draws : s.draws = D
  point : s.point = (trajectory p cfg D g samples s.iteration).workers i
  count : s.samples ≤ cfg.batch
  accumulator : s.accumulator = ∑ j ∈ Finset.range s.samples,
    g i s.point (samples i (s.iteration * cfg.batch + j))

lemma initial_worker_data (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (i : Fin p.n) :
    WorkerData p cfg D g samples i
      { draws := D, point := p.x0, selected := p.x0, outputIndex := selected.val } := by
  refine ⟨rfl, rfl, Nat.zero_le _, ?_⟩
  simp only [Finset.range_zero, Finset.sum_empty]

lemma receive_worker_data (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (s : State p) (i : Fin p.n) (padding : List Bool) (hs : WorkerData p cfg D g samples i s) :
    WorkerData p cfg D g samples i
      (receive p cfg s i (rootMessage p cfg D g samples s.iteration i ++ padding)) := by
  refine ⟨hs.draws, ?_, Nat.zero_le _, ?_⟩
  · change downlinkReceive p cfg s.draws s.iteration i s.point
      (rootMessage p cfg D g samples s.iteration i ++ padding) = _
    rw [hs.draws, hs.point]
    exact receive_rootMessage p cfg D g samples s.iteration i padding
  · simp only [receive, Finset.range_zero, Finset.sum_empty]

lemma computed_worker_data (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (s : State p) (i : Fin p.n) (hs : WorkerData p cfg D g samples i s)
    (hcount : s.samples < cfg.batch) :
    WorkerData p cfg D g samples i
      { s with
        accumulator := s.accumulator + g i s.point (samples i (s.iteration * cfg.batch + s.samples))
        samples := s.samples + 1
        pending := false } := by
  refine ⟨hs.draws, hs.point, Nat.succ_le_of_lt hcount, ?_⟩
  change s.accumulator + g i s.point (samples i (s.iteration * cfg.batch + s.samples)) = _
  rw [Finset.sum_range_succ, hs.accumulator]

lemma worker_data_message (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (s : State p) (i : Fin p.n) (hs : WorkerData p cfg D g samples i s)
    (hcount : s.samples = cfg.batch) :
    uplinkMessage p cfg s.draws s.iteration i ((cfg.batch : ℝ)⁻¹ • s.accumulator) =
      workerMessage p cfg D g samples s.iteration i := by
  rw [hs.draws, hs.accumulator, hcount, hs.point]
  rfl

lemma finish_root_message (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p) (aggregate : Point p)
    (hs : RootPoints p cfg D g samples selected s)
    (haggregate : (p.n : ℝ)⁻¹ • aggregate = estimator p cfg D g samples s.iteration
      (trajectory p cfg D g samples s.iteration)) (i : Fin p.n) :
    (finish p cfg s aggregate).outbox i = rootMessage p cfg D g samples s.iteration i := by
  change downlinkMessage p cfg s.draws s.iteration i
    (s.point + increment cfg ((p.n : ℝ)⁻¹ • aggregate))
    (increment cfg ((p.n : ℝ)⁻¹ • aggregate)) = _
  rw [hs.draws, hs.point, haggregate]
  rfl

lemma root_selected_complete (p : Params) (cfg : Config) (D : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (selected : Fin cfg.iterations) (s : State p)
    (hs : RootPoints p cfg D g samples selected s) (hk : s.iteration = cfg.iterations) :
    s.selected = output p cfg D g samples selected := by
  rw [hs.selected_point, ite_eq_left (by rw [hk]; exact selected.isLt.le)]
  rfl

end LongTails.Proofs.DistributedNormalizedProtocol
