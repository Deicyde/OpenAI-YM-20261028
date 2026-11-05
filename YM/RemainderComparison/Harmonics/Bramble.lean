import YM.RemainderComparison.Harmonics.Spindle
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Harmonics
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Deck.Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
variable {hC he I I' V U}
variable (D : Youth (p:=p) hC he I I' V U)
include D
namespace Youth
-- all tags
variable {S' : StepData c f}
def Seedless (P:Molecule S'):=∀ i∈P,(∃ j:Music c f,i=Mint.disc S' j)∨ ∃ j:ℕ,i=Opacity.key S' j
lemma candida : Seedless V ∧ Seedless U:=by
    constructor
    · intro i hi; by_cases h:i∈ I'.signs Y
      · obtain ⟨j,hj,rfl⟩:= mem_image.mp h; obtain ⟨p,hp,-⟩:=D.lands' ⟨j,hj⟩; exact Or.inr ⟨p,(congr_arg (fun x:Wing=> x.badge Y) hp)⟩
      rcases D.verbal ⟨i, Finset.mem_sdiff.mpr ⟨hi,h⟩⟩ with ⟨j,h,-⟩|⟨j,p,h,-⟩; exact Or.inl ⟨_,h⟩; exact Or.inr ⟨_,h⟩
    intro i hi; by_cases h:i∈I.signs S
    · obtain ⟨j,hj,rfl⟩:=mem_image.mp h; obtain ⟨p,h,h',h''⟩:=D.lands' (D.branch.symm ⟨j,hj⟩); rw [Equiv.apply_symm_apply] at h''; exact Or.inr ⟨h',congr_arg (fun x:Wing=> x.badge S) h''⟩
    rcases D.verbal (D.west.symm ⟨i,Finset.mem_sdiff.mpr ⟨hi,h⟩⟩) with ⟨j,h,h',-⟩|⟨j,p,h,h',-⟩ <;> rw [Equiv.apply_symm_apply] at h'
    · exact Or.inl ⟨_,h'⟩
    exact Or.inr ⟨_,h'⟩
omit D
namespace Seedless
lemma rises {Q:Molecule S'} (h:Seedless Q) : Q.toLeft=∅ ∧ Matter.own Q=∅:=by
   constructor <;> ext p <;> simp only [Matter.own,mem_toLeft,mem_toRight,notMem_empty,iff_false]
   · intro hq; rcases h _ hq with ⟨j,h⟩|⟨j,h⟩
     · unfold disc at h; injection h
     cases h
   intro hq; rcases h _ hq with ⟨j,h⟩|⟨j,h⟩
   · unfold disc at h; injection h with he; injection he
   cases h
lemma whiteG {Q:Molecule S'}(h:Seedless Q): roster Q=⟨∅,∅,∅⟩:=by
   unfold roster; rw [h.rises.1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩
lemma untraced {P:Molecule S'} (h:Seedless P) (T:Tube G S') (R: RG.Rep G f) (i j:ℕ) : troupe T R i j P:=by
   unfold troupe; rw [h.whiteG,h.rises.1,h.rises.2]
   constructor
   · constructor
     · simp
     · simp
     simp [Packets.seeds]
   constructor
   · intro _ h; exact False.elim (notMem_empty _ h)
   intro _ h; exact False.elim (notMem_empty _ h)
end Seedless
include D ht
-- induce Spark across Umbrellas
-- sums over subtype
set_option maxRecDepth 4000 in
lemma imperials : ∃ f: Head Y→Head S, U= V.image f ∧ Set.InjOn f V ∧∀ i∈V, c'.supportP (f i)=(C'.supportP i).image (L).low.cut:=by
   let td:= fun j: ↥I'.own=>j.val.turn.badge Y; let sd:= fun j: ↥I.own=>j.val.turn.badge S
   have hS {c f:Side} (S'':StepData c f) {R:RG.Rep G f} (I:Team R): Bijective fun j: ↥I.own=> (show ↥(I.signs S'') from ⟨j.val.turn.badge S'',mem_image_of_mem _ j.2⟩):=
       ⟨fun i j hj=> Subtype.ext (I.alone i.2 j.2 (Team.badged _ (congr_arg Subtype.val hj))), fun i=> by obtain ⟨j,hj,h⟩:=mem_image.mp i.2; exact ⟨⟨j,hj⟩,Subtype.ext h⟩⟩
   let L':=Equiv.ofBijective _ (hS Y I'); let L₁:=Equiv.ofBijective _ (hS S I); let v:= L'.symm.trans (D.branch.trans L₁)
   let w i:Head S:= if h:i∈I'.signs Y then (v ⟨i,h⟩).val else if h:i∈V\ I'.signs Y then (D.west ⟨i,h⟩).val else Opacity.key S 0
   have hw i: w (td i)=sd (D.branch i):=by
       unfold w; rw [dif_pos (show td i∈ I'.signs Y from (L' i).2)]; change (L₁ (D.branch (L'.symm (L' i)))).val=_; rw [Equiv.symm_apply_apply]; rfl
   have hu (i:↥(V\I'.signs Y)) : w i.val=(D.west i).val:=by unfold w; rw [dif_neg (Finset.mem_sdiff.mp i.2).2,dif_pos i.2]
   have hm i: w (td i)∈I.signs S:= hw i ▸ (L₁ (D.branch i)).prop
   have hp i : w (i:↥(V\I'.signs Y)).val∉ I.signs S:=hu i ▸ (mem_sdiff.mp (D.west i).prop).2
   have ht (i:Head Y)(hi:i∈V): (∃ j,i=td j) ∨ ∃ j:↥(V\I'.signs Y), i=j.val:=by
       by_cases h:i∈I'.signs Y; · refine Or.inl ⟨L'.symm ⟨i,h⟩,?_⟩; exact (congr_arg Subtype.val (L'.apply_symm_apply ⟨i,h⟩)).symm
       exact Or.inr ⟨⟨i,Finset.mem_sdiff.mpr ⟨hi,h⟩⟩,rfl⟩
   refine ⟨w,?_,?_,fun i hi=>?_⟩
   · ext i; constructor
     · intro hi; by_cases h:i∈I.signs S
       · let j:= D.branch.symm (L₁.symm ⟨i,h⟩)
         refine mem_image.mpr ⟨td j,D.asked (L' j).prop,?_⟩; rw [hw]; unfold j; rw [Equiv.apply_symm_apply]; exact congr_arg Subtype.val (L₁.apply_symm_apply ⟨i,h⟩)
       let j:=D.west.symm ⟨i,Finset.mem_sdiff.mpr ⟨hi,h⟩⟩; refine mem_image.mpr ⟨j.val, (Finset.mem_sdiff.mp j.prop).1, (hu j).trans (congr_arg Subtype.val (D.west.apply_symm_apply _))⟩
     intro hi'; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi'; rcases ht i hi with ⟨j,rfl⟩|⟨j,rfl⟩; exact D.inSquare (hm j); rw [hu]; exact (Finset.mem_sdiff.mp (D.west j).prop).1
   · intro i hi j hj hk; rcases ht i hi with ⟨i,rfl⟩|⟨i,rfl⟩<;> rcases ht j hj with ⟨j,rfl⟩|⟨j,rfl⟩
     · rw [hw,hw] at hk; exact congr_arg _ (D.branch.injective (L₁.injective (Subtype.ext hk)))
     · exact (hp j (hk ▸ hm i)).elim
     · exact (hp i (hk ▸ hm j)).elim
     rw [hu,hu] at hk; exact congr_arg Subtype.val (D.west.injective (Subtype.ext hk))
   have ha := c'.laws.data.room.buys; have hh:c.val≤f.val:= h ▸ Nat.le_mul_of_pos_right _ P.L.property
   rcases ht i hi with ⟨j,rfl⟩|⟨j,rfl⟩
   · rw [hw]; exact mold hC he T T' (D.branch j).val.turn _ (R:=R) (R':=R') (D.left j) (by omega) J.halo (radiusB p)
   rw [hu]; rcases D.verbal j with ⟨b,h,h',-⟩|⟨b,B',h,h',hh,-⟩
   · rw [h,h']; exact (Meadow.contempt hC he (by assumption) b).2
   rw [h,h']; exact mold hC he T T' (Wing.logKey B') (Wing.logKey b) (R:=R) (R':=R') hh (by omega) J.halo _
lemma mantle (hZ:2*n<c.val) (hp:C'.unionP V⊆neighbors n Z) : Ac.Spark C'.supportP V↔ Ac.Spark c'.supportP U :=by
   obtain ⟨f,rfl,hv,hf⟩:= imperials C' c' ht D
   let p:= Equiv.ofBijective (fun i:↥V=> (show ↥(V.image f) from ⟨f i.val, mem_image_of_mem f i.2⟩))
     ⟨fun i j h=>Subtype.ext (hv i.2 j.2 (congr_arg Subtype.val h)), fun i=> by obtain ⟨x,hx,h⟩:=mem_image.mp i.2; exact ⟨⟨x,hx⟩,Subtype.ext h⟩⟩
   have hs i (hi:i∈C'.unionP V): reverts hC Z ((L).low.cut i)=i:=same_site hC Z _ hZ hp i hi
   apply Meadow.capitates C'.supportP c'.supportP _ _ p; intro i j; change (∃ p∈C'.supportP j.val, p∈C'.supportP i.val)↔ ∃ z∈ c'.supportP (f j.val),z∈ c'.supportP (f i.val)
   rw [hf i.val i.2,hf j.val j.2]; constructor
   · rintro ⟨x,h,h'⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ h'⟩
   rintro ⟨x,h,h'⟩; obtain ⟨i',hi,rfl⟩:= mem_image.mp h'; obtain ⟨j',hj,hh⟩:=mem_image.mp h
   have h:j'=i':= ((hs j' (mem_biUnion.mpr ⟨_,j.2,hj⟩)).symm.trans ((congr_arg _ hh).trans (hs i' (mem_biUnion.mpr ⟨_,i.2,hi⟩))))
   exact ⟨i',h ▸ hj, hi⟩
lemma foldCount : c'.unionP U=(C'.unionP V).image (L).low.cut:=by
   obtain ⟨f,rfl,hv,hf⟩:= imperials C' c' ht D; ext i; constructor
   · intro hi; obtain ⟨j,hj',h⟩:= Finset.mem_biUnion.mp hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hj'; rw [hf j hj] at h; obtain ⟨x,hx,rfl⟩:=mem_image.mp h; exact mem_image_of_mem _ (mem_biUnion.mpr ⟨j,hj,hx⟩)
   intro hi; obtain ⟨z,hz,rfl⟩:=mem_image.mp hi; obtain ⟨j,hj,h⟩:= Finset.mem_biUnion.mp hz; refine mem_biUnion.mpr ⟨f j,mem_image_of_mem _ hj,?_⟩; rw [hf j hj]; exact mem_image_of_mem _ h
end Youth
end YM.RemainderComparison.Harmonics
