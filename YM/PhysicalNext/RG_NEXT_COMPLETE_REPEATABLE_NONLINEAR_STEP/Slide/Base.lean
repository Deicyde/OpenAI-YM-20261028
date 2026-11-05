import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Range
/-!
 # Coordinates clamp and exact retention. Many periods from any realized. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck  Greenbelt
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C c : Side} {Z D:ℕ}
-- coords flavor ZMod
abbrev point (w:ℕ) (i:Per C):ℕ:= if i.val≤w then i.val else 2*w-i.val
lemma upnext (v:Per C): (v+1).val=(v.val+1)%C.val:= by rw [show v+1=↑(v.val+1) by simp]; exact ZMod.val_natCast ..
def cognac {w : ℕ} (h:2*w≤C.val): Track C := {
    pos i:= point w i
    step v:= by
      have ht:=ZMod.val_lt v; unfold Slide.point; rw [upnext]; by_cases he:v.val+1<C.val
      · rw [Nat.mod_eq_of_lt he]; split_ifs <;> omega
      · rw [show v.val+1=C.val from (by omega),Nat.mod_self]; split_ifs <;> omega
}
-- def. radius influence gates commons
lemma stopped {w:ℕ} (v:Per C) : point w v≤w:= by unfold point; split<;>omega
lemma centerDown {w i:ℕ} (h:2*w ≤ C.val) (hp : i ≤ w): point w (i:Per C)=i:= by
  have hi:i<C.val:= by have he:=C.pos; omega
  unfold point; rw [ZMod.val_natCast_of_lt hi,if_pos hp]
abbrev crystal (w:ℕ) : Finset Cover:= Finset.Icc 0 (fun _=> (w:ℤ))
lemma cryst {w:ℕ} (i:Cover): i ∈ crystal w↔ (∀ j,0 ≤ i j)∧∀ j,i j ≤ w:= mem_Icc
lemma crystal_le (w : ℕ): crystal w ⊆Lattice.box w:= by intro i hi; rw [cryst] at hi; exact Lattice.box_test.mpr ⟨fun k=> by have hh:=hi.1 k; omega, hi.2⟩
lemma stamp {w:ℕ} (h:2*w≤C.val) (i : Site C): Slide.stage (cognac h) i∈ crystal w:= (Slide.cryst _).mpr ⟨fun _ => Int.natCast_nonneg _,fun k=> Int.ofNat_le.mpr (stopped (i k))⟩
lemma rock {w:ℕ} (h:2*w≤ C.val) (i : Cover) (hi:i∈crystal w): Slide.stage (Slide.cognac h) (wrap C i)=i:= by
  funext k; have he' := (Slide.cryst i).mp hi; change (point w (↑(i k): Per C):ℤ)=_
  let a := (i k).toNat; have ha : (a:ℤ) = i k:=Int.toNat_of_nonneg (he'.1 k); have hE:= he'.2 k
  rw [←ha,Int.cast_natCast,centerDown h (by omega)]
lemma current {w:ℕ} (h:2*w≤ C.val) (i:Cover) (hi:i∈crystal w) (k:Axis) (hk:i+step k∈crystal w): grade (Slide.cognac h) (wrap C i,k)=1:= by
  have hv:stage (Slide.cognac h) (wrap C i+step k)=i+step k:= by rw [← Lattice.wrap_step C, ← map_add]; exact rock h _ hk
  rw [tops, rock h _ hi] at hv; have hE:= congr_fun (add_left_cancel hv) k; simpa using hE
lemma vested {w:ℕ} (h:2*w≤ C.val) (i:Cover) (hi:i∈crystal w) (k:Axis) (hk:i+step k∈crystal w) (V: Config G c) (o:Site c): shape (Slide.cognac h) o V (wrap C i,k)=V (wrap c i+o,k):= by unfold shape sites; rw [if_pos (current h i hi k hk),rock h _ hi]
lemma sep (i:Cover) (x:Site c) (hi:i∈Lattice.box Z) : separation x (wrap c i+x) ≤ Z:= Work.E08.separation_box_add x hi -- edit
lemma village {w:ℕ} (h:2*w≤ C.val) (o:Site c) (i:Site C): separation o (sites (Slide.cognac h) o i) ≤ w:= Slide.sep _ _ (crystal_le _ (stamp h i))

section activate
variable {Z:ℕ}
lemma emboss (x y: Site c) (h : separation x y ≤ Z): ∃ p : Cover, p∈Lattice.box Z∧ y=wrap c p+x:= by
  let i:=lift (y-x); refine ⟨i,?_,by unfold i; simp⟩; rw [separation_comm] at h
  have ht j : (i j).natAbs ≤ Z:= (component_le ..).trans h
  exact Lattice.box_test.mpr ⟨fun j=> by have hh:= ht j; omega,fun j=> by have hh:= ht j; omega⟩
lemma tilt_down (x y: Site c) (h : separation x y≤Z) (z:Cover) (he:wrap c z+x=y) (hk:z∈Lattice.box (Z+1)) (hz:2*(Z+1) <c.val): z∈Lattice.box Z:= by
  obtain ⟨p,hp,hq⟩:= emboss x y h; have hh:= add_right_cancel (he.trans hq)
  refine (wrap_injOn _ ?_ ?_ hh).symm ▸ hp
  · obtain ⟨h,h'⟩:= box_test.mp hk; intro i; have hw:= h i; have hp:= h' i; omega
  obtain ⟨h,h'⟩:= box_test.mp hp; intro i; have hw:= h i; have hp:= h' i; omega
-- Along neighbors ball BOTH endpoints. Vertical matching storage.
lemma readNear (x:Site c) (h:2*(Z+1)<c.val) {U V: Config G c} (he:Agrees (Lattice.box Z) (expandAt x U) (expandAt x V)): Agrees (neighbors Z x) U V:= by
  rintro ⟨p,i⟩ hp hk; obtain ⟨v,hv,hy⟩:= emboss x p ((neighbors_mem ..).1 hp)
  have hn:v+step i∈Lattice.box (Z+1):= by
    obtain ⟨hz,hv⟩:= box_test.mp hv; apply box_test.mpr; constructor <;> intro j <;> have hh:= hz j <;> have hy:= hv j <;> simp only [Pi.add_apply, step_apply] <;> split <;> omega
  have hQ : v+step i∈ Lattice.box Z := tilt_down x (p+step i) ((neighbors_mem ..).1 hk) _ (by simp only [map_add,wrap_step]; rw [hy]; abel) hn h
  change U (p,i)= _; rw [hy]; exact he (v,i) hv hQ

end activate
end YM.PhysicalNext.Repeat.Slide
