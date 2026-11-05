import YM.Corona.Fill

/-! Halo enlargements pay pre-scale cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Lattice.Corona
open Relation
variable {n : Side}

lemma cover_mono {D X : Support n} (hx : D⊆X) (M : ℕ) : coverNumber M D ≤ coverNumber M X := by
  obtain ⟨A,h1,h2⟩ := coverNumber_realized M X
  exact (list_cost M (D := A) (X:=D) ⟨fun _ hh ↦ h1.1 (hx hh),h1.2⟩).trans_eq h2

lemma meets_sum {D X : Support n} {x} (hx : x∈D) (hh : x∈X) (M : ℕ) : coverNumber M (D∪X) ≤ coverNumber M D+coverNumber M X := by
  obtain ⟨A,⟨a1,a2⟩,ha⟩ := coverNumber_realized M D
  obtain ⟨B,⟨b1,b2⟩,hb⟩ := coverNumber_realized M X
  have la : halo M A ⊆ halo M (A∪B) := halo_mono le_rfl (fun i hi => Finset.mem_union_left B hi)
  have lb : halo M B ⊆ halo M (A∪B) := halo_mono le_rfl (fun i hi => Finset.mem_union_right A hi)
  have h (i) (hi : i∈halo M (A∪B)) : ReflTransGen (Touch _ 1) x i :=
    show ReflTransGen (Touch (halo M (A∪B)) 1) x i from by
      obtain ⟨j,hj,hz⟩ := halo_spec.mp hi
      rcases Finset.mem_union.mp hj with he|he
      · exact grow la (a2 _ (a1 hx) _ (halo_spec.mpr ⟨_,he,hz⟩))
      exact grow lb (b2 _ (b1 hh) _ (halo_spec.mpr ⟨_,he,hz⟩))
  apply le_trans _ (le_trans (Finset.card_union_le A B) (ha ▸ hb ▸ le_rfl))
  apply list_cost
  refine ⟨fun i hi => ?_, fun i hi j hj => (sym (h _ hi)).trans (h _ hj)⟩
  rcases Finset.mem_union.mp hi with he|he
  · exact la (a1 he)
  exact lb (b1 he)

private lemma combine (D : Support n) (b k : ℕ) (hk : ∀ i∈D, coverNumber b (halo k {i}) ≤ (k/b+k/b+1)^4)
    (ht : Ships D (k+k)) : coverNumber b (halo k D) ≤ D.card * (k/b+k/b+1)^4 := by
  classical
  by_cases ha : D.Nonempty
  · choose! X hx hcard using fun i : Site n => coverNumber_realized b (halo k {i})
    have hun (i) (hi : i∈D) : halo b (X i) ⊆ halo b (D.biUnion X) :=
      halo_mono le_rfl (fun v hv => Finset.mem_biUnion.mpr ⟨i,hi,hv⟩)
    have he (i) (hi : i ∈ D) (j) (hj : j∈halo b (X i)) : ReflTransGen (Touch (halo b (D.biUnion X)) 1) i j :=
      grow (hun _ hi) ((hx i).2 i ((hx i).1 (halo_subset k {i} (by simp))) j hj)
    obtain ⟨a,ha⟩ := ha
    have hy (i) (hi : i∈D) : ReflTransGen (Touch (halo b (D.biUnion X)) 1) a i := by
      induction ht a ha i hi with
      | refl => exact .refl
      | @tail i j _ hh ih =>
        let m := line i j k
        have hw : separation i m ≤ k := by simpa only [line_home, Nat.sub_zero] using line_dist i j 0 k (Nat.zero_le _)
        have hw' := line_dist i j k (k+k) (by omega)
        rw [line_end i j hh.2.2, Nat.add_sub_cancel_right,separation_comm] at hw'
        exact ((ih hh.1).trans (he _ hh.1 m ((hx i).1 (halo_spec.mpr ⟨i,by simp,hw⟩)))).trans (sym (he _ hh.2.1 m ((hx j).1 (halo_spec.mpr ⟨j,by simp,hw'⟩))))
    have h' (x) (hh : x∈ halo b (D.biUnion X)) : ReflTransGen (Touch (halo b (D.biUnion X)) 1) a x := by
      obtain ⟨y,h1,h2⟩ := halo_spec.mp hh
      obtain ⟨i,h3,h4⟩ := Finset.mem_biUnion.mp h1
      exact (hy _ h3).trans (he _ h3 x (halo_spec.mpr ⟨y,h4,h2⟩))
    calc
      _ ≤ (D.biUnion X).card := list_cost b ⟨fun x h ↦ (by
          obtain ⟨i,h1,h2⟩ := halo_spec.mp h
          exact hun _ h1 ((hx i).1 (halo_spec.mpr ⟨i,by simp,h2⟩))),fun i hi j hj ↦ (sym (h' _ hi)).trans (h' _ hj)⟩
      _ ≤ _ := by
        refine (Finset.card_biUnion_le).trans ?_
        simp_rw [hcard]; simpa using Finset.sum_le_sum hk
  rw [Finset.not_nonempty_iff_eq_empty.mp ha]
  have he : ∀ b : ℕ,halo (n:=n) b ∅=∅ := fun b => by ext; simp [halo_spec]
  simpa only [Finset.card_empty, zero_mul] using list_cost b (X:=halo k (∅:Support n)) (D:=∅) (by unfold covers; simp [he])

lemma tile (x : Site n) (k b : ℕ) (h : 0<b) : coverNumber b (halo (k*b) {x}) ≤ (k+k+1)^4 := by
  let f := fun p : Cover => x+wrap n (b • p)
  let D := (box k).image f
  have H : 0 < (b:ℤ) := by exact_mod_cast h
  have hx : coverNumber b (halo (k*b) {x}) ≤ D.card := by
    apply list_cost
    refine ⟨fun i hi => ?_, ship_halo _ (fun i hi j hj => ?_)⟩
    · obtain ⟨a,ha,hpr⟩ := halo_spec.mp hi; obtain rfl := Finset.mem_singleton.mp ha
      rw [separation_comm,separation] at hpr
      let p : Cover := lift (i-a)
      let r : Cover := fun j => p j / b
      have hh : r ∈ box k := by
        have ht (j : Axis) : -(k:ℤ) ≤ r j ∧ r j ≤ k := by
          have hu : (p j).natAbs ≤ k*b := (component_le (i-a) j).trans hpr
          have hw : p j ≤ k*b := by exact le_trans (by omega : p j ≤ ↑(p j).natAbs) (by exact_mod_cast hu)
          have he : -(p j) ≤ k*b := by exact le_trans (by omega : -(p j) ≤ ↑(p j).natAbs) (by exact_mod_cast hu)
          refine ⟨(Int.le_ediv_iff_mul_le H).mpr (by nlinarith only [he]), Int.ediv_le_of_le_mul (by omega) ?_⟩
          exact hw
        exact box_test.mpr ⟨fun j => (ht j).1,fun j => (ht j).2⟩
      apply halo_spec.mpr; refine ⟨_,Finset.mem_image_of_mem f hh, ?_⟩
      have hb : wrap n p=i-a := wrap_lift _
      rw [separation_comm,separation,show i-f r = wrap n (p-b • r) by
        unfold f; rw [map_sub,hb]; abel]
      apply Finset.sup_le; intro j _
      apply (lap ..).trans; change (p j- (b • r : Cover) j).natAbs ≤ b
      rw [Pi.smul_apply]; change (p j - (b:ℤ)*(p j/b)).natAbs ≤ b
      have H1 := Int.emod_add_mul_ediv (p j) b; have H2 := Int.emod_nonneg (p j) H.ne'; have H3 := Int.emod_lt_of_pos (p j) H
      omega
    obtain ⟨v,h1,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w,h2,rfl⟩ := Finset.mem_image.mp hj
    let P := fun m : ℕ => fun i : Axis => max (v i-(m:ℤ)) (min (v i+(m:ℤ)) (w i))
    obtain ⟨ht,hu⟩ := box_test.mp h1; obtain ⟨hr,hs⟩ := box_test.mp h2
    have he : P (k+k) = w := by ext i; dsimp [P]; specialize ht i; specialize hu i; specialize hr i; specialize hs i; omega
    have he' : P 0 = v := by ext i; simp [P]
    rw [← he',← he]; apply line_path (F:=f ∘ P)
    · intro i _
      refine Finset.mem_image_of_mem _ (box_test.mpr ⟨fun j => ?_, fun j => ?_⟩)
      all_goals dsimp [P]; specialize ht j; specialize hu j; specialize hs j; specialize hr j; omega
    intro i _
    dsimp only [Function.comp_apply,f]
    rw [separation, add_sub_add_left_eq_sub, ← map_sub,← smul_sub]
    refine (show pdist (wrap n _) ≤ b from ?_).trans (by omega)
    apply Finset.sup_le; intro j _
    apply (lap ..).trans
    rw [Pi.smul_apply,nsmul_eq_mul, Pi.sub_apply, Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left b (show ((P i j)-(P (i+1) j)).natAbs ≤ 1 by dsimp [P]; omega)).trans (by rw [mul_one])
  apply hx.trans
  exact (Finset.card_image_le).trans (by rw [box_size])

lemma tiling {D X : Support n} {m b : ℕ} (hb : 0<b) (hh : covers (m*b) X D) :
    coverNumber b X ≤ D.card * ((m+1)+(m+1)+1)^4 := by
  let a := (m+1)*b
  have ht : Ships D (a+a) := by
    intro i hi j hj
    refine ReflTransGen.mono (r:=Touch D (m*b+m*b+1)) (p:=Touch D _) ?_ i j (halo_ship _ hh.2 _ hi _ hj)
    intro x y h; obtain ⟨h1,h2,h3⟩ := h
    exact ⟨h1,h2,by dsimp [a]; rw [Nat.add_mul,one_mul]; omega⟩
  have hy : X⊆halo a D := fun _ hx => halo_mono (by dsimp [a]; gcongr; omega) (Finset.Subset.refl D) (hh.1 hx)
  apply (cover_mono hy b).trans
  simpa only [a, Nat.mul_div_cancel _ hb] using combine D b a (fun i _ => by simpa only [a, Nat.mul_div_cancel _ hb] using tile i (m+1) b hb) ht
end YM.Lattice.Corona
