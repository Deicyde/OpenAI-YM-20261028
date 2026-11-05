import YM.MergeProof.North.Fermi

/-!
# Many slots per cell: port of YM/MergeProof/North/Fermi.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Extra.Histories Push Push.Local Motion
abbrev Names (V : Type*) (Z : Type*) [DecidableEq V][Fintype V][DecidableEq Z][Fintype Z] := Stock.census (V×Z)
def homes (i:(Names V slotsZ).Mode) : (Bud V).Mode:= ⟨i.val.image Prod.fst,mem_univ _⟩
variable (b: Equiv.Perm V)
def nome : Equiv.Perm ((V×slotsZ)):= Equiv.prodCongr b (Equiv.refl _)
def drum := pars (nome (slotsZ:=slotsZ) b)
lemma recall (i:(Names V slotsZ).Mode): homes (drum b i)=pars b (homes i):=Subtype.ext (by unfold homes; simp only [drum,pares,image_image];rfl)
def Focused (v:V)(p:(Names V slotsZ).Mode):Prop:= (homes p).val⊆ {v}
lemma going (v:V)(p:(Names V slotsZ).Mode): Focused v p ↔ Focused (b v) (drum b p):=by
    unfold Focused; rw [recall,pares,← image_singleton b]; exact (Finset.image_subset_image_iff b.injective).symm
lemma go_one (p:(V×slotsZ)) : drum b ((Names V slotsZ).fire p)=(Names V slotsZ).fire (nome b p):= Subtype.ext (by unfold drum; rw [pares];exact image_singleton ..)
lemma which (v:V)(p:(V×slotsZ)):Focused v ((Names V slotsZ).fire p) ↔ p.1=v:=by simp [Focused,Census.fire,homes]

end YM.MergeProof.Ribbons.ManyCopies
