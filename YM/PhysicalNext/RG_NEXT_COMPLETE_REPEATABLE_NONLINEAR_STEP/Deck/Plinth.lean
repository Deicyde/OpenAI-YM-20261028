import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Infinitesimal
import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Mixed
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.RoofTile
import YM.Further.STRONG_STARTUP_CREDIT.Launch
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.GaussianTarget
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Instruments
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Plot
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Dome
import YM.Planned.ATOM_GUARDED_LAYOUT.Orbit
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Algebra
import YM.Primitives.SMALL_FIELD_EXTERIOR.Identity

/-! # The cover & labelled window congruence. Build-on-F933.Tracery. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window
open Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology BigOperators Classical
variable {c f C F K m: Side} {S : StepData c f} {V : StepData C F} {p : Patch} {M : ℕ} {G : Gauge}

section course
variable (h : c.val∣ C.val)
local notation "Uq" => (Macrame.splitter h)
include h
lemma less (x y : Site C) : separation (Macrame.splitter h x) (Uq y)≤ separation x y:= by
  unfold separation; rw [← map_sub]; let i:=x-y; rw [show Uq i= wrap c (lift i) from Eq.trans (by rw [wrap_lift i] : Uq i=Uq (wrap C (lift i))) (branch ..)]
  unfold pdist; exact Finset.sup_le fun j _=> (Lattice.Corona.lap ..).trans (component_le ..)
def rise (x : Site C) (y : Site c) := x + wrap C (lift (y-Uq x))
lemma dawns (x : Site C) (y : Site c): Uq (rise h x y)=y := by rw [rise,map_add,branch,wrap_lift,add_sub_cancel]
lemma climb (x : Site C) (y : Site c): separation x (rise h x y)=separation (Macrame.splitter h x) y:= by
  let z:= rise h x y
  have hx := less h x z; rw [dawns h x y] at hx
  refine Nat.le_antisymm ?_ hx
  rw [separation_comm,separation_comm (Macrame.splitter h x), rise, separation,add_sub_cancel_left]; unfold pdist; exact Finset.sup_le fun j _=> (Lattice.Corona.lap ..).trans (component_le ..)
lemma tiniest {x y : Site C} (he : Uq x=Uq y) (hh : separation x y < c.val): x=y:= by by_contra hn; exact Nat.not_lt_of_le ((blocks_at_floor h).apart x y he hn) hh
lemma boost (x : Site C) (i : Site C) (hp : 2*separation x i < c.val): rise h x (Uq i)=i:= by
  apply tiniest h (dawns ..); apply Nat.lt_of_le_of_lt (separation_triangle _ x _) ?_; rw [separation_comm (rise h x (Uq i)), climb]; have hx:= less h x i; omega
lemma teaches (x : Site C) (i : Site C) (hp : 2*separation x i < c.val): separation x i=separation (Macrame.splitter h x) (Uq i):= by have h := climb h x (Uq i); rwa [boost (by assumption) x i hp] at h
lemma usual (s : Signed) (i : Site C) : s.act (Uq i)=Uq (s.act i):= by
  obtain ⟨x,rfl⟩ : ∃ x, wrap C x=i:= ⟨_,wrap_lift _⟩
  rw [branch,wrap_signed,wrap_signed,branch]

-- a carrier (location) for labels at any shift; arbitrary asymmetric footprints individually, not requiring canonical coordinates across covers
variable {I J : Type*} (p : J→ I) (root : J→ Site C) (u : I→ Site c) -- name conflict rename
structure Nest : Prop where
  footing i : (splitter h) (root i)=u (p i)
  extend x i (hx:u i=Macrame.splitter h x) : ∃ j,p j=i ∧ root j=x
  firm (i j:J) : p i=p j→ root i=root j → i=j
namespace Nest
variable {root u h p}
variable (H : Nest h p root u)
include H
lemma esc (x : Site C) (i:I) : ∃ j,p j=i ∧ separation x (root j)=separation (Macrame.splitter h x) (u i) := by
  obtain ⟨j,hp,hL⟩:= H.extend (rise h x (u i)) i (dawns ..).symm; exact ⟨j,hp,hL ▸ climb ..⟩
lemma point {k:ℕ} (hx:2*k<c.val) (x:Site C) (i j) (he:separation x (root i)≤k) (hg:separation x (root j)≤k) (hp:p i=p j) : i=j:= by
  apply H.firm i j hp (tiniest h _ _)
  · rw [H.footing,H.footing,hp]
  apply lt_of_le_of_lt (separation_triangle _ x _); rw [separation_comm (root i)]; omega
lemma charge (x : Site C) (i) (hp : 2*separation x (root i) < c.val) : separation x (root i)= separation (Macrame.splitter h x) (u (p i)):= by rw [teaches h _ _ hp,H.footing]
lemma all (k : ℕ) (x:Site C) {Y: Type*} [AddCommMonoid Y] [Fintype I] [Fintype J] (hk : 2*k < c.val) (f : J→ Y) (g:I→Y) (hf : ∀ j, ¬separation x (root j) ≤ k → f j=0) (hg : ∀ i, ¬separation (Macrame.splitter h x) (u i) ≤ k → g i=0) (hv : ∀ j,separation x (root j)≤k→ f j=g (p j)) : (∑ i,f i)=∑ i,g i:= by
  let U := univ.filter fun i=>separation x (root i)≤k; let V:= univ.filter fun i=> separation (Macrame.splitter h x) (u i)≤k
  have he i (hi:i∈U):= (Finset.mem_filter.mp hi).2
  have hx : (∑ i,f i)=U.sum f := Eq.symm (sum_subset (subset_univ _) fun i hi hj=> hf i fun hh=> hj (mem_filter.mpr ⟨hi,hh⟩))
  have hy : (∑ i,g i)= V.sum g:= Eq.symm (sum_subset (subset_univ _) fun i hi hj=> hg i fun hh=> hj (mem_filter.mpr ⟨hi,hh⟩))
  rw [hx,hy]; apply sum_bij (fun i _=>p i) (fun i hi=> mem_filter.mpr ⟨mem_univ _,?_⟩) (fun i hi j hj=> H.point hk x i j (he i hi) (he j hj)) _ (fun i hi=>hv _ (he i hi))
  swap
  · have ht := (he i hi); rw [← H.footing]; exact (less h ..).trans ht
  intro i hi; obtain ⟨j,hj,hk⟩:= H.esc x i; exact ⟨j,mem_filter.mpr ⟨mem_univ _,hk ▸ (mem_filter.mp hi).2⟩,hj⟩
lemma pr {E : Type*} : Nest h (Prod.map p (id:E→ E)) (fun i=>root i.1) (fun i=>u i.1) := by
  refine ⟨(fun i=> H.footing _),fun x i hh=>?_,fun i j hh h=>Prod.ext (H.firm _ _ (congr_arg Prod.fst hh) h) (congr_arg (fun y : I×E=>y.snd) hh)⟩; obtain ⟨z,hz,hT⟩:= H.extend x i.1 hh; exact ⟨(z,i.2),Prod.ext hz rfl,hT⟩
lemma sum {E F : Type*} {p' : F→ E} {v : F→ Site C} {d : E→ Site c} (K : Nest h p' v d): Nest h (Sum.map p p') (Sum.elim root v) (Sum.elim u d) := by
  refine ⟨(fun z=> by rcases z with z|z; exact H.footing _; exact K.footing _),fun x i hh=>?_,fun i j hh he=>?_⟩
  · rcases i with i|i
    · obtain ⟨j,hq,hj⟩:= H.extend x i hh; exact ⟨.inl j,congr_arg Sum.inl hq,hj⟩
    obtain ⟨j,hq,hj⟩:= K.extend x i hh; exact ⟨.inr j,congr_arg Sum.inr hq,hj⟩
  rcases i with i|i <;> rcases j with j|j <;> simp only [Sum.map_inl,Sum.map_inr,Sum.inl.injEq,Sum.inr.injEq,reduceCtorEq] at hh ⊢
  all_goals first| exact False.elim hh | exact H.firm i j hh he| exact K.firm i j hh he
end Nest
end course
section phy
variable {P:Patch} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {M : ℕ} {G : Gauge} (hC : C.val=c.val*M) (he : 2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
include hC he
lemma onfloor : Nest (show c.val∣C.val from ⟨M,hC⟩) ((L).low.cut) id id:= ⟨(fun _=>rfl),(fun _x _i hi=>⟨_,hi.symm,rfl⟩),(fun _ _ _ he=>he)⟩
lemma footing : Nest (show c.val ∣ C.val from ⟨M,hC⟩) ((L).high.cut) (decreed H).parent (decreed h).parent:= by
  let V:= L; refine ⟨(fun _=> (V.position _).symm),fun x i hx=>?_,fun i j hi hh=>?_⟩
  · let r:=(decreed h).residue i; let y:=(decreed H).assemble (x,r); refine ⟨y,?_,Ratio.assemble_parent ..⟩; unfold y; rw [V.regions,show V.low.cut x=_ from hx.symm]; exact V.r.unpack_at i
  have hp := (V.room i).symm; rw [hi,V.room] at hp; have he' := V.R.unpack_at j; rw [← hp, ← hh] at he'; exact (V.R.unpack_at i).symm.trans he'
end phy
end YM.PhysicalNext.Repeat.Deck
