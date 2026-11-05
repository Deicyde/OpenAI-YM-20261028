import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Clock
/-!
 # Face weights polynomial in w. charge orientations unsigned before cancellation.
 kernels fiber includes every Position. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c C L:Side} {Z D w m:ℕ}
section cast
variable (h:C.val=2*w) (ht:2*Z≤ w)
include h
lemma counted (x:ℕ) (hp:x≤w): #((univ:Finset (Per C)).filter (fun i=> Slide.point w i=x))=if x=0 ∨ x=w then 1 else 2:= by
  let t:Per C:=x
  have he := Slide.centerDown (i:=x) h.ge hp; have hv : point w (-t)=x:=by rw [Slide.reflected h]; exact he
  have hx : (univ.filter (fun i:Per C=> point w i=x))={t,-t}:= by
    ext i; simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]; constructor
    · intro hp; have hk:= Slide.untwist h i; rw [hp] at hk; exact hk
    rintro (rfl|rfl); exact he; exact hv
  rw [hx]; split
  next hk=> suffices hh:t=-t from (by rw [← hh]; simp)
            rcases hk with hk|hk; · simp [t,hk]
            have hk : t+t=0:= by
              change ↑x+(x:Per C)=_; rw [← Nat.cast_add,show x+x=C.val from (by omega)]; exact ZMod.natCast_self _
            exact eq_neg_of_add_eq_zero_left hk
  next hk=>
    have hx : t≠-t:= by
      intro he; have hu : t+t=0:= eq_neg_iff_add_eq_zero.mp he
      change ↑x+(x:Per C)= _ at hu; rw [← Nat.cast_add] at hu
      have hh : (t+t).val=(0:ℕ):= (ZMod.val_eq_zero _).2 (by nth_rw 1 [he]; group)
      have hb := congr_arg ZMod.val hu; rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hb; omega
    simp [hx]
include ht
omit h
lemma urban (x:ℕ) (hp:x≤w): bud w Z x=none ↔ Z≤x∧x≤w-Z:= by
  unfold Slide.bud; split
  · simp; omega
  split <;> simp <;> omega
omit ht
lemma bottom (x:ℕ) (i:Fin Z): bud w Z x=some (false,i) ↔ i.val=x:= by
  unfold bud; split; next=> simp [Fin.ext_iff, eq_comm (a:=x)]
  next h=> have hx:i.val≠x:= by omega
           split<;>simp [hx]
include ht
lemma apex (x:ℕ) (hp:x≤w) (i:Fin Z): bud w Z x=some (true,i) ↔ x=w-i.val:= by
  unfold bud; split
  next h=> suffices ht:x≠ w-i.val from (by simp [ht]); omega
  split; next h=> simp only [Option.some.injEq,Prod.mk.injEq,Fin.ext_iff, true_and]; omega
  next h=> suffices ht:x≠w-i.val from (by simp [ht]); omega
-- w-2*Z proved nonneg only where used

def coins (i:Fin Z) : ℕ := if i.val=0 then 1 else 2
def dinners (w:ℕ) (i: Rose Z) : ℕ:= match i with
  | none => 2*(w-2*Z+1)
  | some (_,i)=> Slide.coins i
include h
lemma curt (hp:0< Z) (i:Rose Z): #((univ:Finset (Per C)).filter fun k=> Slide.tag w Z k=i)=dinners w i:= by
  rcases i with _|⟨b,i⟩
  · let v:= fun x:Per C=> Slide.point w x
    let s:= Icc Z (w-Z)
    let t(x):= (Finset.univ:Finset (Per C)).filter fun k=>v k=x
    have he:(univ.filter fun k:Per C=> Slide.tag w Z k=none)=s.biUnion t:= by
      ext k; simp only [mem_filter,mem_univ,true_and,mem_biUnion]
      simp only [s,t,v,mem_filter,mem_univ,true_and,mem_Icc]; change Slide.bud w Z (Slide.point w k)=_ ↔ _; rw [urban ht (Slide.point w k) (Slide.stopped _)]; constructor; · exact fun h=> ⟨_,h,rfl⟩
      rintro ⟨k',h,rfl⟩; exact h
    have hd : Set.PairwiseDisjoint ↑s t:= fun i hi j hj he=> Finset.disjoint_left.mpr fun k hp hk=>he ((mem_filter.mp hp).2.symm.trans (mem_filter.mp hk).2)
    have hh i (hi:i∈s): #(t i)= (2:ℕ):= by have hv:=mem_Icc.mp hi; rw [show #(t i)=_ from counted h i (by omega : i≤w),if_neg (by omega)]
    rw [he, Finset.card_biUnion hd, sum_congr rfl hh]; change _=2*_; unfold s; rw [sum_const,Nat.card_Icc]; change _ * (2:ℕ) = _; omega
  cases b
  · let t:=univ.filter fun k:Per C=> Slide.point w k=i.val
    have he i' : Slide.tag w Z i' = some (false,i)↔ (point w i'=i.val : Prop):= (bottom (w:=w) (point w (C:=C) _) i).trans eq_comm
    have hz := i.isLt; rw [show (univ.filter fun k:Per C=> _)=t from (by unfold t; ext j; simp [he] ),show #t=_ from counted h i.val (by omega: i.val≤w)]; simp only [dinners,coins]; split_ifs <;> omega
  let t:=univ.filter fun k:Per C=> Slide.point w k=w-i.val
  have he i' : Slide.tag w Z i' = some (true,i)↔point w (C:=C) i'=w-i.val:= apex ht _ (Slide.stopped _) i
  have hz := i.isLt
  rw [show (univ.filter fun k:Per C=> _)=t from (by unfold t; ext j; simp [he] ),show #t=_ from counted h (w-i.val) (by omega: w-i.val≤w)]; simp only [dinners,coins]; split_ifs <;> omega
lemma weighted (hp:0< Z) (i: Petals Z): #((univ:Finset (Site C)).filter fun k=> Slide.charm w Z k=i)=∏ j, Slide.dinners w (i j):= by
  let f j := (univ:Finset (Per C)).filter fun k=> Slide.tag w Z k=i j
  rw [show (univ.filter fun k:Site C=> _)=Fintype.piFinset f from ?_, Fintype.card_piFinset]; · exact Finset.prod_congr rfl fun j _=> curt h ht hp _
  ext k; simp [f,Slide.charm,funext_iff] -- pattern goal ? check
lemma presents (hp:0< Z) (i : Petals Z): ∃ x:Site C,charm w Z x=i := by
  have hv : ∀ i: Rose Z,0 < dinners w i:= by
    rintro (_|⟨j,z⟩); · change 0<2*(w-2*Z+1); omega
    simp only [dinners,coins]; split<;>omega
  have hp:= Finset.card_pos.mp (show 0< #((univ:Finset (Site C)).filter fun k=>charm w Z k=i) from by rw [weighted h ht hp]; exact Finset.prod_pos fun j _=> hv (i j))
  obtain ⟨x,hx⟩:= hp; exact ⟨x,(mem_filter.mp hx).2⟩
end cast
end YM.PhysicalNext.Repeat.Slide
