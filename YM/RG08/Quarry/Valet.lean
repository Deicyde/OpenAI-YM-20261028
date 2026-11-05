import YM.RG08.Quarry.Paws
/-! # All-period lazy external interpretation (the cover tests themselves are sparse,
 so no summability or transformer decay demands for this calculus). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Quarry
open Gallery Forms Function Filter Lattice Laurent Room Camera Glyph Finset Prism Pert.Bulk Isles
open scoped Classical ContDiff BigOperators Topology PowerSeries ENNReal
variable {I J L:Type}[Fintype I][Fintype J][Fintype L]
/-- local transformation from Market logs J to Market logs L through template germs.
 Finite head type I may repeat slots, offsets depend on L. -/
structure Loom (I J L : Type)[Fintype I] where
 offset: L → I → Market J
 fare: L → Still I
 fit:∀ j,Pace (fare j)
 origin:∀ j,fare j 0=0
variable (V:Loom I J L)

def jab (i:Market L)(p:I):Market J := (i.1+(V.offset i.2 p).1,(V.offset i.2 p).2)
def dodge {c:Side}(i:Cove c L)(p:I): Cove c J := (i.1+wrap c (V.offset i.2 p).1,(V.offset i.2 p).2)
private def rubble (s:Finset (Market J))(k:L)(a:I):Finset (Market L):=s.image (fun j:Market J=>(j.1-(V.offset k a).1,k))

def portrait (s:Tray (Market J)):Tray (Market L) where
 base:=univ.biUnion fun k:L=> univ.biUnion fun a:I=>rubble V s.base k a
 get i:=breath (s.get ∘ jab V i) (eye (V.fare i.2))
 shut i hi:=by
    rw [show s.get ∘ jab V i=0 from ?_,dark]
    funext p; exact s.shut _ (by
      intro he; apply hi; refine Finset.mem_biUnion.mpr ⟨i.2,mem_univ _,Finset.mem_biUnion.mpr ⟨p,mem_univ _,?_⟩⟩;apply Finset.mem_image.mpr; refine ⟨jab V i p,he,?_⟩
      simp [jab])

def reachLog (c:Side)(x:Cove c J)(s:Tray (Market J)):= (Gallery.native c s).get x
omit [Fintype I][Fintype J][Fintype L] in
private lemma across (s: Tray (Market J))(u:Market J){N:ℕ→Side}(hN:Tendsto (fun j=>(N j).val) atTop atTop):∀ᶠ k in atTop,∀ i:Site (N k),reachLog (N k) (i+wrap _ u.1,u.2) s=s.get (lift i+u.1,u.2):=by
 let Δ (j: Market J):Market J:=(j.1-u.1,j.2)
 filter_upwards [moving hN s.base, moving hN (s.base.image Δ)] with k _ hV
 let c:= N k
 intro i
 let b:=Isles.reach (P:=c) (i+wrap c u.1,u.2)
 let d:Market J:=(lift i+u.1,u.2)
 change s.get b=s.get d
 by_cases h:b∈s.base
 · have he :=congrArg Prod.fst (hV _ (mem_image_of_mem Δ h));
   have hx :wrap c (b.1-u.1)=i:=by simp [Isles.reach,b]
   change lift (wrap c (b.1-u.1))= b.1-u.1 at he;rw [hx] at he;refine congrArg s.get (Prod.ext (x:=b) (y:=d) ?_ rfl);change b.1= lift i+u.1;rw [he];exact (sub_add_cancel _ _).symm
 by_cases hj:d∈s.base
 · rename_i hB
   have he:=hB _ hj
   have hh:b=Isles.reach (port c d):=by simp [Isles.reach,b,port,d]
   rw [hh,he]
 rw [s.shut _ h,s.shut _ hj]
omit [Fintype J] in
lemma rear (s:Tray (Market J)){N:ℕ→Side}(hN:Tendsto (fun j=>(N j).val) atTop atTop):
 ∀ᶠ k in atTop,∀ i:Cove (N k) L, (Gallery.native (N k) (portrait V s)).get i=breath ((Gallery.native (N k) s).get ∘ dodge V i) (eye (V.fare i.2)):=by
 filter_upwards [(eventually_all.mpr (fun l:L=>eventually_all.mpr (fun a:I=> across s (V.offset l a) hN)))] with k hx
 intro i;unfold Gallery.native portrait;dsimp only;congr 2;funext p;exact (hx i.2 p i.1).symm

omit [Fintype J] in
lemma leading (s:Tray (Market J))(i:Market L): (Demo.flat (portrait V s)).play i=fderiv ℝ (V.fare i.2) 0 ((Demo.flat s).play ∘ jab V i):=lead _ _

/-- Merge two attitudes, all couplings. -/
def art (x:Tray (Market L))(u:Tray (Market J)):Tray (Market (L⊕J)) where
 base:= x.base.image (fun i=>(i.1,Sum.inl i.2))∪u.base.image (fun i=> (i.1,Sum.inr i.2))
 get i:=i.2.elim (fun p=>x.get (i.1,p)) (fun p=>u.get (i.1,p))
 shut:=by rintro ⟨i,p|p⟩ h; exact x.shut _ (fun ht=>h (mem_union_left _ (mem_image_of_mem (fun i=> (i.1, Sum.inl i.2):Market L→Market (L⊕J)) ht)));exact u.shut _ (fun ht=>h (mem_union_right _ (mem_image_of_mem (fun i=>(i.1,Sum.inr i.2): Market J→ Market (L⊕J)) ht)))
end YM.RG08.Quarry
