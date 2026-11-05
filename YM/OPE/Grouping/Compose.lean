import YM.OPE.Grouping.Fibers
/-! # Composition of the grouping projection -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V U X Y : Type*} [DecidableEq U][Fintype U][DecidableEq V][Fintype V]
 [DecidableEq X][Fintype X][DecidableEq Y][Fintype Y]

def same (U : Type*) : Fibers U U := ⟨id,id, fun _=>rfl⟩
def comp (A:Fibers U V)(B:Fibers V X) : Fibers U X :=
    ⟨B.bunch ∘ A.bunch,A.twig ∘ B.twig,fun i=> by rw [comp_apply,comp_apply,A.sectioned,B.sectioned]⟩
def similar (A B:Fibers U V) : Prop:= A.bunch=B.bunch
lemma same_plena (s:(Bud U).Mode) : (same U).plena s=s:=Subtype.ext (by ext1 i; rw [reaped]; rfl)
lemma same_reap (p:Poly (Bud U)) : reap (same U) p=p:= by ext s; change p.part _=p.part _; rw [same_plena]
lemma comp_plena (A:Fibers U V)(B:Fibers V X)(p:(Bud X).Mode): A.plena (B.plena p)=(A.comp B).plena p:=Subtype.ext (by ext1 i; rw [reaped,reaped,reaped]; rfl)
lemma comp_reap (A:Fibers U V)(B:Fibers V X)(p:Poly (Bud U)) : reap B (reap A p)= reap (A.comp B) p:= by ext s; change p.part _=p.part _; rw [comp_plena]
lemma similar_plena {A B:Fibers U V}(he:similar A B)(p:(Bud V).Mode) : A.plena p=B.plena p:= by apply Subtype.ext; ext i; rw [reaped,reaped,show A.bunch=B.bunch from he]
lemma similar_reap {A B:Fibers U V}(he:similar A B)(p:Poly (Bud U)): reap A p=reap B p:=by ext s; change p.part _=p.part _; rw [similar_plena he]
end YM.MergeProof.Ribbons.Fibers
