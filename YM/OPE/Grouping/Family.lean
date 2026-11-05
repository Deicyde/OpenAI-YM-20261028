import YM.MergeProof.North.Fermi
import YM.MergeProof.North.Harbor
import YM.OPE.Grouping.Stator
/-!
# Keep the precise transformation per cell

The predicate in `Family.kin/jets` is applied to all parts within that focus, not just
unit and one. Generalizes `YM/MergeProof/North/Fermi`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J X₀ : Type*} [DecidableEq V][Fintype V][DecidableEq X₀][Fintype X₀]
 {n:Side}{G:Gauge}{B:Census V}{Δ:Fibers X₀ V}
open Extra.Histories Push Push.Local Motion

def Focus (Δ:Fibers X₀ V) (s:Set V) (p:(Bud X₀).Mode) := ((Δ.span p).val : Set V)⊆ s

structure Permutes (Δ:Fibers X₀ V)(a:Equiv.Perm X₀) (b:Equiv.Perm V) : Prop where
  run (x) : Δ.bunch (a x)= b (Δ.bunch x)
  pin (x) : Δ.twig (b x)=a (Δ.twig x)
variable (Z: Salt V X₀ Δ G n)
variable {a : Equiv.Perm X₀} {b:Equiv.Perm V}

namespace Permutes
variable (h : Permutes Δ a b) (p:(Bud X₀).Mode)
include h
lemma recalls : Δ.span (pars a p)=pars b (Δ.span p):= by
  apply Subtype.ext; unfold span; simp only [pares,image_image]; exact Finset.image_congr fun i _=>h.run i
lemma garner : Δ.Pays p ↔ Δ.Pays (pars a p):=by
  have he (x:(Bud V).Mode): Δ.plena (pars b x)=pars a (Δ.plena x):=by
    apply Subtype.ext; ext1 z; obtain ⟨y,rfl⟩ := a.surjective z
    rw [pares a (Δ.plena x), Ribbons.mem_image_of_injective _ a.injective,← L_fix,Δ.reaped,h.run,pares, Ribbons.mem_image_of_injective _ b.injective]
  unfold Pays; rw [h.recalls,he,(pars a).apply_eq_iff_eq]
where L_fix (x:(Bud V).Mode)(y:X₀): Δ.bunch y∈x.val ↔ y∈ (Δ.plena x).val:=(Δ.reaped ..).symm
-- check syntax mem_image lemma
end Permutes
lemma focus_fire (s:Set V) (x:X₀) : Focus Δ s ((Bud X₀).fire x) ↔ Δ.bunch x∈s:=by simp [Focus,Census.fire,Fibers.span]
lemma fires (a:Equiv.Perm V)(x:V) : (Bud V).fire (a x)=pars a ((Bud V).fire x):=by apply Subtype.ext; rw [pares]; simp [Census.fire]

structure CopyFamily (z : ℝ) (m:Motion)(x:Site n)(v u:Set V) (a:Equiv.Perm X₀)(b:Equiv.Perm V) : Prop where
   groups : Permutes Δ a b
   who (i) : b i ∈ u ↔ i∈v
   ways i : Δ.bunch i∈v → Z.grain (a i) = affine m.1 x (Z.grain i)
   debut i: Δ.bunch i∈v → Z.pepper (a i)= scalar m (Z.pepper i)
   kin p (hp:Focus Δ v p) i U: (Z.air (MergeProof.sky m x i) U).part (pars a p)=scalar m ((Z.air i (pull m.1 x U)).part p)
   jets p (hp:Focus Δ v p) i U:(Z.river (puff m x i) U).part (pars a p)= scalar m ((Z.river i (pull m.1 x U)).part p)
variable {t:ℝ}{m: Motion}{x:Site n}{v u:Set V}
namespace CopyFamily
variable {Z} (h : CopyFamily Z t m x v u a b)
include h
lemma moves (i:V)(hi:i∈v) : Z.focus (b i)=affine m.1 x (Z.focus i) := by
  unfold Salt.focus; rw [h.groups.pin]; exact h.ways _ (Δ.sectioned i|>.symm ▸ hi)
lemma goes (p:(Bud X₀).Mode) : Focus Δ v p ↔ Focus Δ u (pars a p) := by
  unfold Focus; rw [h.groups.recalls,pares]
  simp only [coe_image,Set.image_subset_iff,show b ⁻¹' u=v from Set.ext h.who]
lemma homes (i:(Bud X₀).Mode)(hp:Focus Δ v i)(p:Support n) : i.val.image Z.grain⊆ p↔ (pars a i).val.image Z.grain ⊆ sky m x p:=by
   have he:(pars a i).val.image Z.grain=(i.val.image Z.grain).image (turnSites m.1 x):=by
      rw [pares,image_image,image_image]; apply Finset.image_congr; intro k hk; exact h.ways _ (hp (show Δ.bunch k ∈ (Δ.span i).val from mem_image_of_mem Δ.bunch hk))
   rw [he,shading]; exact (Finset.image_subset_image_iff (turnSites m.1 x).injective).symm
lemma kilo (i:(Bud X₀).Mode)(hp:Focus Δ v i)(p:Support n): Z.kiln (sky m x p) (pars a i)=sky m x (Z.kiln p i):=by
    unfold Salt.kiln; rw [h.groups.recalls,pares,shading,shading,image_union,image_image,image_image]; refine congr_arg (_ ∪ ·) (Finset.image_congr ?_); intro k hi; exact h.moves k (hp hi)
end CopyFamily
end YM.MergeProof.Ribbons.Fibers
