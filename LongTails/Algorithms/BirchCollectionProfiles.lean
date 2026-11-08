import LongTails.Setups.BirchCollections

namespace LongTails.Algorithms.BirchCollectionProfiles

open LongTails.Setups.BirchCollections

def divisor (upper window : ℕ) : ℕ := upper + 4 * window

noncomputable def controls (lower upper window waste : ℕ) : Controls where
  lowerMass := (lower : ℝ) / divisor upper window
  upperMass := (upper : ℝ) / divisor upper window
  massRatio := (upper : ℝ) / lower
  amplification := divisor upper window
  initialization := 0
  waste

noncomputable def packetControls (lower upper window waste factor : ℕ) : Controls :=
  { controls lower upper window waste with amplification := (divisor upper window : ℝ) * factor }

def resetOrdering (o : LongTails.Setups.BirchCollections.Ordering) :
    LongTails.Setups.BirchCollections.Ordering :=
  { o with anchor := id, scale := fun _ _ => 1, renewalFrontier := fun _ _ => 0 }

end LongTails.Algorithms.BirchCollectionProfiles
