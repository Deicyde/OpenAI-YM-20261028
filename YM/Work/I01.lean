import YM.Bid.Fuels
import YM.Corona.Fit

/-!
# Support price for separated markers

Use the short traversal of the centers of a minimizing cover. It need not
visit the markers themselves: distinct markers already force a gap between
the traversal times of their respective covering centers. (All distances in
this proof are native torus max-distance.)
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.I01

open Lattice

theorem answer : YM.Bid.I01 := by
  intro n V _ _ f B hB F hsep hcard H hsub
  classical
  obtain ⟨D, hD, hprice⟩ := coverNumber_realized B H
  obtain ⟨N, hN, R, hstep, hvisits⟩ :=
    Corona.ring_path _ (Corona.halo_ship B hD.2)
  -- Pick a time for each marker in F, within B of it.
  have hpick (i : V) (hi : i ∈ F) :
      ∃ k, k ≤ N ∧ separation (R k) (f i) ≤ B := by
    obtain ⟨c, hc, hdist⟩ :=
      halo_spec.mp (hD.1 (hsub (Finset.mem_image_of_mem f hi)))
    obtain ⟨k, hk, he⟩ := hvisits c hc
    exact ⟨k, hk, he.symm ▸ hdist⟩
  choose! t ht hnear using hpick
  let gap := B^2 - 2*B
  have hsq : 8*B ≤ B^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_right B hB
  have hpos : 0 < gap := by dsimp [gap]; omega
  -- A gap in distance forces a gap in time, paying two radii.
  have apart (i : V) (hi : i ∈ F) (j : V) (hj : j ∈ F) (hne : i ≠ j)
      (hij : t i ≤ t j) : t i + gap ≤ t j := by
    have hspan := Corona.path_span hstep (t i) (t j) hij (ht j hj)
    have h1 := separation_triangle (f i) (R (t i)) (f j)
    have h2 := separation_triangle (R (t i)) (R (t j)) (f j)
    rw [separation_comm (f i) (R (t i))] at h1
    have := hnear i hi
    have := hnear j hj
    have := hsep i hi j hj hne
    dsimp [gap]
    omega
  let bucket := fun i => t i / gap
  have later (i : V) (hi : i ∈ F) (j : V) (hj : j ∈ F) (hne : i ≠ j)
      (hij : t i ≤ t j) : bucket i < bucket j := by
    have h := Nat.div_le_div_right (c := gap) (apart i hi j hj hne hij)
    rw [Nat.add_div_right (t i) hpos] at h
    exact h
  -- At most one marker per bucket, including the bucket containing N.
  have hpack : F.card ≤ N/gap + 1 := by
    let I := Finset.range (N/gap + 1)
    calc
      F.card ≤ I.card := by
        apply Finset.card_le_card_of_injOn bucket
        · intro i hi
          exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (c := gap) (ht i hi)))
        · intro i hi j hj heq
          by_contra hne
          rcases le_total (t i) (t j) with hij | hji
          · exact (later i hi j hj hne hij).ne heq
          exact (later j hj i hi (Ne.symm hne) hji).ne heq.symm
      _ = N/gap + 1 := Finset.card_range _
  have hm : (F.card-1)*gap ≤ N := (Nat.le_div_iff_mul_le hpos).mp (by omega)
  rw [← hprice]
  apply Nat.le_of_mul_le_mul_left (c := B) _ (by omega)
  calc
    B * (B * F.card) = F.card * B^2 := by ring
    _ ≤ (2*(F.card-1)) * (2*gap) :=
      Nat.mul_le_mul (by omega) (by dsimp [gap]; omega)
    _ = 4*((F.card-1)*gap) := by ring
    _ ≤ 4*N := Nat.mul_le_mul_left _ hm
    _ ≤ 4*(D.card*((B+B+1)+(B+B+1))) := Nat.mul_le_mul_left _ hN
    _ ≤ 4*(D.card*(16*B)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = B*(64*D.card) := by ring

end YM.Work.I01
