import YM.OPE.Replicas.Corn
/-!
# License collapse along all fibers of a grouping

Generalizing `Focal` (YM/MergeProof/North) from pair to arbitrary finite families. Use
for simultaneous events so that families with many close pairs don't have to spend
several extra exponent reserves at the same step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J S₀ : Type*} [DecidableEq V] [DecidableEq S₀][Fintype V][Fintype S₀]
structure Fibers (U V : Type*) where
   bunch : U→V
   twig : V→U
   sectioned : LeftInverse bunch twig
namespace Fibers
variable (L : Fibers S₀ V)

def span (i:(Bud S₀).Mode) : (Bud V).Mode:= ⟨i.val.image L.bunch,mem_univ _⟩
def contents (v:V) : Finset S₀ := univ.filter (fun i => L.bunch i=v)
lemma focuses (i:S₀) (v:V) : i∈L.contents v ↔ L.bunch i=v := by simp [contents]

def plena (b:(Bud V).Mode) : (Bud S₀).Mode:= ⟨b.val.biUnion L.contents,mem_univ _⟩
def Pays (i:(Bud S₀).Mode) := i=L.plena (L.span i)
lemma spans (i:(Bud S₀).Mode)(j) : j∈(L.span i).val ↔ ∃ k∈L.contents j,k∈i.val:=by
   simp only [span,mem_image,focuses]; tauto
lemma reaped (b : (Bud V).Mode) (a) : a∈(L.plena b).val ↔ L.bunch a∈b.val:=by simp [plena, focuses, eq_comm]
lemma reband (b:(Bud V).Mode) : L.span (L.plena b)=b:=by
   apply Subtype.ext; ext i; rw [L.spans]; constructor
   · rintro ⟨k,hk,ht⟩; rw [← (L.focuses ..).1 hk]; exact (L.reaped ..).1 ht
   intro h
   exact ⟨L.twig i,(L.focuses ..).2 (L.sectioned _),(L.reaped ..).2 (L.sectioned i|>.symm ▸ h)⟩
lemma worth_iff (i:(Bud S₀).Mode) : L.Pays i↔ ∀ j∈ (L.span i).val,∀ k ∈ L.contents j,k∈i.val:=by
   constructor
   · intro h j hj k hk; change i=_ at h; nth_rw 1 [h]; exact mem_biUnion.mpr ⟨j,hj,hk⟩
   intro h; apply Subtype.ext; ext k; refine ⟨fun hx=> (L.reaped ..).2 (mem_image_of_mem _ hx),fun hh=>?_⟩
   obtain ⟨v,hv,hk⟩:= mem_biUnion.mp hh; exact h _ hv _ hk

def reap : Poly (Bud S₀)→L[ℂ] Poly (Bud V):= LinearMap.toContinuousLinearMap ({
    toFun:=fun p=>Poly.inject fun s=> p.part (L.plena s)
    map_add':= by intro a x; ext1 s; rfl
    map_smul':= by intro a x; ext1 s; rfl } : Poly (Bud S₀) →ₗ[ℂ] Poly (Bud V))
lemma harvest (i:(Bud S₀).Mode)(a:ℂ) : (Fibers.reap L) (Poly.send i a)=if L.Pays i then Poly.send (L.span i) a else 0:=by
   ext1 s; change (Poly.send i a).part (L.plena s)=_; rw [Poly.part_send]; split
   next h=> rw [← h,L.reband, if_pos (show L.Pays (L.plena s) from (by unfold Pays; rw [L.reband])),Poly.part_send,if_pos rfl]
   next h=> split
            next he=> rw [Poly.part_send, if_neg (fun (ht:s=L.span i)=> h (ht.symm ▸ he.symm))]
            rfl
lemma combines {q:I→(Bud S₀).Mode} {s:Finset I}(h:Fits q s): (L.span (unionTag _ _ h)).val=s.biUnion (fun i=>(L.span (q i)).val):=by
   ext; simp only [L.spans,unionTag,mem_biUnion]; tauto
lemma disjoint_c (x y:V)(hx:x≠y) : Disjoint (L.contents x) (L.contents y) := disjoint_left.mpr
  (fun {k} p hp => hx (((L.focuses _ _).1 p).symm.trans ((L.focuses _ _).1 hp)))
lemma prod_plena {A : Type*} [CommMonoid A] (b:(Bud V).Mode) (f:S₀→A):
    ∏ i∈(L.plena b).val,f i = ∏ j∈b.val,∏ i∈L.contents j,f i := prod_biUnion (fun _ _ _ _ h=> L.disjoint_c _ _ h)
lemma afford (i:(Bud S₀).Mode)(h:L.Pays i)(w:S₀→ℝ)(u:V→ℝ)(ht:∀ i, u i=∏ j∈L.contents i,w j): Poly.toll w i=Poly.toll u (L.span i):=by
   nth_rw 1 [show i=L.plena (L.span i) from h]; unfold Poly.toll; rw [L.prod_plena]; simp_rw [← ht]
lemma recomp {q:I→(Bud S₀).Mode}{s:Finset I}(h:∀ i∈s,L.Pays (q i))(A:I→ℂ): (Fibers.reap L) (∏ i∈s,Poly.send (q i) (A i))=∏ i∈s,Poly.send (L.span (q i)) (A i):=by
   by_cases hv:Fits q s
   · have hp:Fits (fun i=>L.span (q i)) s:=by
        refine ⟨fun i hi j hj hz=> disjoint_left.mpr fun k hk he=>?_,mem_univ _⟩
        have hK : L.twig k∈ L.contents k:= (L.focuses ..).2 (L.sectioned _)
        exact disjoint_left.mp (hv.1 hi hj hz) ((L.worth_iff _).mp (h _ hi) _ hk _ hK) ((L.worth_iff _).mp (h _ hj) _ he _ hK)
     have hx:L.Pays (unionTag _ _ hv):=by
        rw [L.worth_iff,L.combines]; intro i hi j hj; obtain ⟨k,hk,hz⟩:=mem_biUnion.mp hi; exact mem_biUnion.mpr ⟨k,hk,(L.worth_iff _).mp (h k hk) i hz j hj⟩
     rw [tagged_prod _ s hv,L.harvest,if_pos hx,tagged_prod _ _ hp]; exact congr_arg (fun p=> Poly.send p _) (Subtype.ext (L.combines hv))
   rw [show (∏ i∈s,Poly.send (q i) (A i))=0 from Classical.byContradiction (fun h=> hv (fits_of_tagged_prod _ h)),map_zero]; symm; by_contra hh
   have hp:= fits_of_tagged_prod (fun i=> L.span (q i)) hh; exact hv ⟨fun i hi j hj hz=> disjoint_left.mpr fun k hx he=> disjoint_left.mp (hp.1 hi hj hz) (mem_image_of_mem L.bunch hx) (mem_image_of_mem L.bunch he),mem_univ _⟩
end Fibers
end YM.MergeProof.Ribbons
