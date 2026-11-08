import LongTails.Proofs.BirchRoutedTime
import LongTails.Proofs.BirchPowerTime

namespace LongTails.Proofs.BirchResourceRepetition

open Finset Set LongTails.Setups

lemma same_phase {T t : ℝ} (hT : 0 ≤ T) {i j : ℕ}
    (hi : t ∈ Ico ((i : ℝ) * T) ((i + 1 : ℕ) * T))
    (hj : t ∈ Ico ((j : ℝ) * T) ((j + 1 : ℕ) * T)) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hb : ((i + 1 : ℕ) : ℝ) * T ≤ j * T :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt h)) hT
    exact False.elim (not_lt_of_ge hj.1 (hi.2.trans_le hb))
  · exact h
  · have hb : ((j + 1 : ℕ) : ℝ) * T ≤ i * T :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt h)) hT
    exact False.elim (not_lt_of_ge hi.1 (hj.2.trans_le hb))

def routeJob {Route I : Type*} (jobs : I → BirchRoutedTime.Job Route) (T : ℝ)
    (label : ℕ × I) : BirchRoutedTime.Job Route :=
  ⟨(jobs label.2).route, label.1 * T + (jobs label.2).launch⟩

lemma route_active {Route Device I : Type*} [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (jobs : I → BirchRoutedTime.Job Route) (T : ℝ)
    (j : ℕ × I) (v : Device) (t : ℝ) :
    (routeJob jobs T j).active p v t ↔ (jobs j.2).active p v (t - j.1 * T) := by
  unfold routeJob BirchRoutedTime.Job.active
  simp only [Set.mem_Ico]
  constructor <;> rintro ⟨h, ha, hb⟩ <;> exact ⟨h, by linarith only [ha], by linarith only [hb]⟩

lemma routes_legal {Route Device I : Type*} [DecidableEq Device]
    (p : BirchRoutedTime.Profile Route Device) (hp : ∀ i, 0 ≤ p.duration i)
    (jobs : I → BirchRoutedTime.Job Route) (s : Finset I) (H : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hl : BirchRoutedTime.Legal p jobs s)
    (ht : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + BirchRoutedTime.latency p (jobs j).route ≤ T) :
    BirchRoutedTime.Legal p (routeJob jobs T) ((range H) ×ˢ s) := by
  intro v t j hj k hk hjact hkact
  have hj' := mem_product.mp hj
  have hk' := mem_product.mp hk
  have window (i : ℕ × I) (hi : i.2 ∈ s) (ha : (routeJob jobs T i).active p v t) :
      t ∈ Ico ((i.1 : ℝ) * T) ((i.1 + 1 : ℕ) * T) := by
    obtain ⟨hlat, ha'⟩ := (route_active p jobs T i v t).mp ha
    have hb := LongTails.Proofs.BirchRoutedTime.offset_bounds p hp _ v hlat
    have hc := ht i.2 hi
    push_cast
    exact ⟨by linarith only [ha'.1, hb.1, hc.1], by linarith only [ha'.2, hb.2, hc.2]⟩
  have he := same_phase hT (window j hj'.2 hjact) (window k hk'.2 hkact)
  have hj'' := (route_active p jobs T j v t).mp hjact
  have hk'' := (route_active p jobs T k v t).mp hkact
  rw [he] at hj''
  exact Prod.ext he (hl v (t - k.1 * T) _ hj'.2 _ hk'.2 hj'' hk'')

def powerJob {Mode I : Type*} (jobs : I → BirchPowerTime.Job Mode) (T : ℝ)
    (label : ℕ × I) : BirchPowerTime.Job Mode :=
  ⟨(jobs label.2).mode, label.1 * T + (jobs label.2).launch⟩

lemma power_active {Mode Device I : Type*}
    (p : BirchPowerTime.Profile Mode Device) (jobs : I → BirchPowerTime.Job Mode) (T : ℝ)
    (j : ℕ × I) (t : ℝ) :
    (powerJob jobs T j).active p t ↔ (jobs j.2).active p (t - j.1 * T) := by
  unfold powerJob BirchPowerTime.Job.active
  simp only [Set.mem_Ico]
  constructor <;> rintro ⟨ha, hb⟩ <;> exact ⟨by linarith only [ha], by linarith only [hb]⟩

lemma power_legal {Mode Device I : Type*}
    (p : BirchPowerTime.Profile Mode Device) (jobs : I → BirchPowerTime.Job Mode)
    (s : Finset I) (H : ℕ) (T : ℝ) (hT : 0 ≤ T) (hcap : 0 ≤ p.cap)
    (hl : BirchPowerTime.Legal p jobs s)
    (ht : ∀ j ∈ s, 0 ≤ (jobs j).launch ∧ (jobs j).launch + p.duration (jobs j).mode ≤ T) :
    BirchPowerTime.Legal p (powerJob jobs T) ((range H) ×ˢ s) := by
  classical
  intro t
  have window (i : ℕ × I) (hi : i.2 ∈ s) (ha : (powerJob jobs T i).active p t) :
      t ∈ Ico ((i.1 : ℝ) * T) ((i.1 + 1 : ℕ) * T) := by
    have ha' := (power_active p jobs T i t).mp ha
    have hc := ht i.2 hi
    push_cast
    exact ⟨by linarith only [ha'.1, hc.1], by linarith only [ha'.2, hc.2]⟩
  constructor
  · intro j hj k hk hjact hkact hd
    have hj' := (mem_product.mp hj).2
    have hk' := (mem_product.mp hk).2
    have he := same_phase hT (window j hj' hjact) (window k hk' hkact)
    have hj'' := (power_active p jobs T j t).mp hjact
    have hk'' := (power_active p jobs T k t).mp hkact
    rw [he] at hj''
    exact Prod.ext he ((hl (t - k.1 * T)).1 _ hj' _ hk' hj'' hk'' hd)
  · by_cases he : ∃ j ∈ ((range H) ×ˢ s), (powerJob jobs T j).active p t
    · obtain ⟨j, hj, ha⟩ := he
      let v := fun i : ℕ × I =>
        if (powerJob jobs T i).active p t then p.power (powerJob jobs T i).mode else 0
      change (∑ i ∈ (range H) ×ˢ s, v i) ≤ p.cap
      rw [sum_product]
      rw [sum_eq_single_of_mem j.1 (mem_product.mp hj).1]
      · have he' (i : I) : v (j.1, i) =
            if (jobs i).active p (t - j.1 * T) then p.power (jobs i).mode else 0 := by
          unfold v
          rw [power_active]
          rfl
        simp_rw [he']
        exact (hl (t - j.1 * T)).2
      · intro k _ hk
        apply sum_eq_zero
        intro i hi
        have hn : ¬(powerJob jobs T (k, i)).active p t := fun hb =>
          hk (same_phase hT (window (k, i) hi hb) (window j (mem_product.mp hj).2 ha))
        simp [v, hn]
    · push Not at he
      have hz : (∑ j ∈ (range H) ×ˢ s,
        if (powerJob jobs T j).active p t then p.power (powerJob jobs T j).mode else 0) = 0 :=
        sum_eq_zero (fun j hj => ite_eq_right (he j hj))
      rwa [hz]

end LongTails.Proofs.BirchResourceRepetition
