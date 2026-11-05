import YM.MergeProof.Paddle
import YM.Work.I01
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Connectors
/-! # Moderated separation intermediate for regroup

See YM/Work/I01.lean and YM/Primitives/CONNECTED_GAUSSIAN_CUMULANTS/Connectors.lean
for the argument. Uses line native, earns only `w` in the mint; conversely now can
actually afford the regroup geometry at servicing this *failure* scale.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Finset Lattice Corona RG
open scoped Topology BigOperators
variable {V:Type} [DecidableEq V] {n : Side}
theorem separatedMarks (F:Finset V)(f:V→Site n){B w:ℕ}
    (hsep: ∀ i∈F,∀ j∈F,i ≠ j→B*w ≤ separation (f i) (f j))
    (hw:8≤w)(hB:1≤B)(hcard:2≤F.card)(H:Support n)(hsub:F.image f⊆ H) : w*F.card≤ 64*coverNumber B H := by
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
  let gap := B*w - 2*B
  have hsq : 8*B ≤ B*w := by
    rw [mul_comm _ w]; exact Nat.mul_le_mul_right B hw
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
    B * (w * F.card) = F.card*(B*w) := by ring
    _ ≤ (2*(F.card-1)) * (2*gap) :=
      Nat.mul_le_mul (by omega) (by dsimp [gap]; omega)
    _ = 4*((F.card-1)*gap) := by ring
    _ ≤ 4*N := Nat.mul_le_mul_left _ hm
    _ ≤ 4*(D.card*((B+B+1)+(B+B+1))) := Nat.mul_le_mul_left _ hN
    _ ≤ 4*(D.card*(16*B)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = B*(64*D.card) := by ring


lemma link (x y : Site n) (B : ℕ) : coverNumber B ({x,y}:Support n) ≤ separation x y / (B+1)+2 := by
  let k := B+1; let t := separation x y/k + 1; let f b := line x y (k*b)
  let U := range (t+1); let s := U.image f
  have he (j : ℕ) (h : j≤t) : f j∈s := mem_image_of_mem _ (mem_range.mpr (by omega))
  have hh : f 0=x := by simp [f]
  have hd : f t=y := line_end x y (le_of_lt (Nat.lt_mul_div_succ (separation x y) (Nat.succ_pos B)))
  have hi : Ships s (B+B+1) := by
    have he' i (hi : i≤t) : Relation.ReflTransGen (Touch s (B+B+1)) (f 0) (f i) := by
      refine line_path _ _ (fun i h => he _ (h.trans hi)) (fun j hj => ?_)
      unfold f
      apply (line_dist x y _ _ ?_).trans
      · rw [Nat.mul_add,Nat.mul_one,Nat.add_sub_cancel_left]; unfold k; omega
      exact Nat.mul_le_mul_left _ (by omega)
    intro a ha b hb
    rcases mem_image.mp ha with ⟨i,hi,rfl⟩
    rcases mem_image.mp hb with ⟨j,hj,rfl⟩
    exact (Corona.sym (he' i (by have := mem_range.mp hi; omega))).trans (he' j (by have := mem_range.mp hj; omega))
  have hg : covers B ({x,y}:Support n) s := by
    refine ⟨?_, Corona.ship_halo B hi⟩
    refine (Finset.insert_subset ?_ (singleton_subset_iff.mpr ?_)).trans (halo_subset B s)
    · exact hh ▸ he 0 (Nat.zero_le t)
    exact hd ▸ he t le_rfl
  exact (list_cost B hg).trans (card_image_le.trans (by simp [k,t,U]))

lemma moderateRadius (x y : Site n) (B w:ℕ) (h:separation x y≤ B*w) : coverNumber B ({x,y}:Support n) ≤ w+2:=by
    have hp : separation x y/(B+1) ≤ w:=by
       refine Nat.div_le_of_le_mul (h.trans ?_)
       nlinarith
    exact (link ..).trans (Nat.add_le_add_right hp _)
structure Moderate (f : V→Site n)(B w:ℕ) : Prop where
   wide : ∀ i j:V, i ≠ j → B*w ≤ separation (f i) (f j)
variable [Fintype V] {W W': V→ℝ} {K : Marker.Census V}{f:V→Site n}{b w:ℕ}
open MergeProof Accent Marker Extra.Multi Push GridApprox.Nil Local Extra.Trajectories
omit [Fintype V] in
lemma Moderate.pegs (h:Moderate f b w)(he:∀ i,W' i≤ W i*mintK w)(hp:∀ i,0<W' i)(hq:∀ i,0<W i)(hb:1≤b)(hw:8≤w): Repegs f b W W' (1/2) 1 K:=by
   intro i hi X hX; have ht := separatedMarks i.val f (fun i _ j _=> h.wide i j) hw hb hi X hX
   rw [one_mul]; unfold Poly.toll
   refine (Finset.prod_le_prod (fun i _=>hp i|>.le) (fun i _=>he i)).trans ?_
   rw [Finset.prod_mul_distrib,prod_const]; apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _=> hq i|>.le); unfold mintK; rw [← Real.exp_nat_mul]
   have ht':(w:ℝ)*i.val.card ≤ 64*(coverNumber b X :ℝ):= by exact_mod_cast ht
   apply Real.exp_monotone; linarith only [ht']
end YM.OPE.Log
