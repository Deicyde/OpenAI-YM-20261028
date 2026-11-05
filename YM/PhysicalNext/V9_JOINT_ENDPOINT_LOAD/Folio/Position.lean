import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind

/-! # The full physical address convention for charging (not a sector alphabet per table)

We still include *all* position labels of the Z-ratio even when some sites
aren't active, and don't price a forest, tag, branch, Y draw or color choice
per (re)visit. Color products go INSIDE the term. No result here produces
the remaining physical letters, their supports, assignment or re-log data,
nor allows discarding flags/stencils after some replacement of their values
on a given field!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure Further.GaussianScalar
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching
open AnalyticBridge.NonflatCovarianceLocality.Full (point)
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I J : Type} {c f : Side} {G : Gauge}

def rename (L : I → J) (p : Full I) : Full J := p.map L (fun ⟨n,⟨i,j⟩,h⟩ => ⟨n,(L i,L j),L ∘ h⟩)
def clues (p : Full I) : Finset I := p.elim (fun i=>{i}) (fun ⟨_,⟨i,j⟩,h⟩=> insert i (insert j (Finset.univ.image h)))

lemma tracks_inj {L : I→J} (h : Injective L) : Injective (rename L) := by
  rintro (i|⟨n,⟨i,j⟩,f⟩) (u|⟨m,⟨u,v⟩,g⟩) ht <;> simp only [rename,Sum.map,Sum.elim,Function.comp_apply,Sum.inl.injEq,reduceCtorEq,Sum.inr.injEq,Sigma.mk.injEq] at ht ⊢
  · exact h ht
  · obtain ⟨rfl,ht⟩ := ht; obtain ⟨⟨h₁,h₂⟩,h₃⟩ := Prod.mk.inj (eq_of_heq ht) |>.imp_left Prod.mk.inj
    obtain rfl := h h₁; obtain rfl := h h₂; obtain rfl := h.comp_left h₃; exact ⟨rfl,HEq.rfl⟩
lemma preorder (p : Full I) (L : I → J) : clues (rename L p) = (clues p).image L := by
  rcases p with i|⟨n,⟨i,j⟩,h⟩ <;> simp [clues,rename,Finset.image_image,Function.comp_def]



abbrev Paper f := Full (Bond f)
variable {S : StepData c f} {A B : Stores S} {F H : Forest S.ratio} {T : Tube G S} {x : ℝ} {q : Chi} {d g : ℝ} {U : Config G c} {P : Teller G}

abbrev home (S : StepData c f) (j : Bond f) := S.ratio.parent j.1
abbrev castEdge (A : Stores S) (F : Forest S.ratio) (x : ℝ) (j : Active A x F) : Bond f := j.val.val
lemma cast_inj : Injective (castEdge A F x) := fun _ _ he=> Subtype.ext (Subtype.ext he)
abbrev upwards (A : Stores S) (F : Forest S.ratio) (x : ℝ) := rename (castEdge A F x)
lemma upwards_inj : Injective (upwards A F x) := tracks_inj cast_inj





def spread (S : StepData c f) (r : ℕ) (p : Paper f) : Support c := halo r ((clues p).image (home S))
lemma belongs (i) (p : Paper f) (r : ℕ) : i∈spread S r p ↔ ∃ j∈ clues p, separation (home S j) i ≤ r := by
  simp [spread,halo_spec]










namespace Bulletin
variable (b : Bulletin x P T) (k : S.Choices)
include b



end Bulletin
end YM.PhysicalNext.JointLoad.Folio
