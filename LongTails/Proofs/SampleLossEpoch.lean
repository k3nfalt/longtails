import LongTails.Proofs.SampleLossFrame

open scoped RealInnerProductSpace BigOperators
open LongTails.Setups.NonnegativeSmoothSampleLossEuclidean
open LongTails.Proofs.SampleLossFrame LongTails.Proofs.SampleLossChain
open LongTails.Proofs.SampleLossRadial LongTails.Proofs.SampleLossFrontier
open LongTails.Proofs.SampleLossMixture

namespace LongTails.Proofs.SampleLossEpoch

variable {n m d : ℕ}

def exposedRows (ξ : ℕ → Fin m) (length k : ℕ) : Finset (Fin m) :=
  (Finset.range length).image (fun s => ξ (k*length+s))

def exposed (ξ : ℕ → Fin m) (length k : ℕ) : Finset (Fin n × Fin m) :=
  Finset.univ.filter (fun p => p.1.val < k ∨ p.1.val = k ∧ p.2 ∈ exposedRows ξ length k)

lemma exposed_mono (ξ : ℕ → Fin m) (length : ℕ) {k l : ℕ} (h : k ≤ l) :
    exposed (n:=n) ξ length k ⊆ exposed ξ length l := by
  rcases h.eq_or_lt with rfl | h
  · exact fun _ hi => hi
  · intro p hp
    simp only [exposed,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
    rcases hp with h'|⟨h',_⟩ <;> exact Or.inl (by omega)

lemma exposed_active (ξ : ℕ → Fin m) {length : ℕ} (hl : 0 < length) (s : ℕ) :
    ξ s ∈ exposedRows ξ length (s/length) := by
  apply Finset.mem_image.mpr
  exact ⟨s%length, Finset.mem_range.mpr (Nat.mod_lt _ hl), by rw [Nat.div_add_mod']⟩

lemma signed_prefix_congr (π ρ : Table n m d) (i : Fin m) {k : ℕ} (hk : k<n)
    (hp : ∀ j : Fin n, j.val < k → ∀ l, π (j,l) = ρ (j,l))
    (hi : π (⟨k,hk⟩,i) = ρ (⟨k,hk⟩,i)) (M : ℝ) :
    frontier (proj (n:=n)) (direction π) (payload π i) (row π i k) M n k =
      frontier proj (direction ρ) (payload ρ i) (row ρ i k) M n k := by
  have hb (j : ℕ) (hj : j<k) (l : Fin m) : basis π j l = basis ρ j l := by
    simp [basis,lt_trans hj hk,hp ⟨j,lt_trans hj hk⟩ hj l]
  have hu (j : ℕ) (hj : j<k) : direction π j = direction ρ j := by
    simp [direction,hb j hj]
  have hs (j : ℕ) (hj : j<k) (x : Space n m d) : signal proj (direction π) j x = signal proj (direction ρ) j x := by
    simp [signal,hu j hj]
  have ha (j : ℕ) (hj : j≤k) (x : Space n m d) : incoming proj (direction π) j x =
      incoming proj (direction ρ) j x := by
    cases j with
    | zero => rfl
    | succ j => simp [incoming,hs j (by omega)]
  have hw (j : ℕ) (hj : j<k) : payload π i j = payload ρ i j := by simp [payload,hu j hj,row,hb j hj i]
  have hr : row π i k = row ρ i k := by simp [row,basis,hk,hi]
  funext x
  have hpert (t : ℕ) (ht : t ≤ k) :
      perturbation proj (direction π) (payload π i) t x = perturbation proj (direction ρ) (payload ρ i) t x := by
    induction t with
    | zero => rfl
    | succ t ih =>
      change blend (incoming proj (direction π) t x)
        (perturbation proj (direction π) (payload π i) t x) (signal proj (payload π i) t x) =
        blend (incoming proj (direction ρ) t x)
          (perturbation proj (direction ρ) (payload ρ i) t x) (signal proj (payload ρ i) t x)
      rw [ih (by omega), ha t (by omega)]
      simp [signal,hw t (by omega)]
  have hbase : base proj (direction π) k x = base proj (direction ρ) k x := by
    unfold base
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp [link, hs j (Finset.mem_range.mp hj),ha j (Finset.mem_range.mp hj).le]
  simp [SampleLossFrontier.frontier,hr,ha k le_rfl,hpert k le_rfl,hbase]

noncomputable def reply (π : Table n m d) (i : Fin m) (k : ℕ) (r c : ℝ) (x : Space n m d) :=
  c • gradient (frontier proj (direction π) (payload π i) (row π i k) (1+Real.sqrt m) n k) (r • x)

lemma reply_stable (π ρ : Table n m d) (ξ : ℕ → Fin m) {length : ℕ} (hl : 0 < length)
    (s : ℕ) (hk : s/length < n) (he : ∀ l ∈ exposed ξ length (s/length), π l = ρ l)
    (r c : ℝ) (x : Space n m d) :
    reply π (ξ s) (s/length) r c x = reply ρ (ξ s) (s/length) r c x := by
  unfold reply
  rw [signed_prefix_congr π ρ (ξ s) hk (fun j hj l => he (j,l) (by simp [exposed,hj]))
    (he _ (by simp [exposed,exposed_active ξ hl s]))]

end LongTails.Proofs.SampleLossEpoch
