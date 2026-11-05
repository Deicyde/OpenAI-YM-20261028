import YM.UVExtension.Fallow.Utah
import YM.MergeProof.Canyon
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d p n N : ℕ}

variable (R : Weave G)
private lemma additiveH (I : Finset (Fin n)) (f : Fin n→Pre G) {r m : ℕ} (hf : ∀ i∈I,Continuous (f i))
    (h : ∀ i∈I,MicroAt (f i) r m) : MicroAt (∑ i∈I,f i) r m := by
  induction I using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact MicroAt.zero G r m
  | insert i s hi ih=>
    rw [Finset.sum_insert hi]
    let a := Finset.mem_insert_self i s
    have he : Continuous (∑ j∈s,f j) := by
      rw [funext (fun x : CoverConfig G=> Finset.sum_apply x s f)]
      exact continuous_finsetSum _ fun j hj=> hf j (Finset.mem_insert_of_mem hj)
    apply (h i a).add _ (hf i a) he
    exact ih (fun i hi=>hf i (Finset.mem_insert_of_mem hi)) (fun i hi=>h i (Finset.mem_insert_of_mem hi))

lemma radiusH {B : Frame G d} {H : Hol G} (X : SectionData B) (he : Portfolio H X (R d)) :
    ∃ r m : ℕ,∀ x : Label G d,x∈Maxwell.equationIdeal G d → MicroAt (X.evaluate (B.coords (R d x))) r m := by
  let S := Maxwell.equationIdeal G d
  have hp {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (P : Submodule ℂ V) :
      Module.Free ℂ P ∧ Module.Finite ℂ P := ⟨inferInstance,inferInstance⟩
  haveI := (hp S).1; haveI := (hp S).2
  let E := Module.finBasis ℂ S
  let f : S →ₗ[ℂ] Pre G := ((X.eval_linear).mk' X.evaluate).comp
    (B.coords.toLinearMap.comp ((R d).toLinearMap.comp S.subtype))
  choose r m h using fun i=> (he.rank (E i).1 (E i).2).2
  let M := Finset.univ.sup m
  let A := Finset.univ.sup r
  refine ⟨A,M,fun x hx=>?_⟩
  let z : S := ⟨x,hx⟩
  change MicroAt (f z) _ _
  rw [← E.sum_repr z,map_sum]; simp_rw [map_smul]
  refine additiveH _ _ ?_ ?_
  · intro i _; apply Continuous.const_smul; exact (he.rank (E i).1 (E i).2).1
  intro i hi; exact ((h i).mono (Finset.le_sup (s:=Finset.univ) (f:=r) hi) (Finset.le_sup (s:=Finset.univ) (f:=m) hi)).scale (E.repr z i)
end YM.Push.Mark
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Fallow
open Finset Filter Function MeasureTheory Set Lattice Wilson RG Cells Extraction Push GridApprox Hearth
open Lease Dash Bid MergeProof RelayDifference Opening Local Next.Foundations Source
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}(hG:G.Simple)(H:Vintage.YM.Family.Makes C)(B:Stock.Tabs C.path.levels){W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (h:Scrim C W u ψ φ δ ζ r D) (hF:Fridge C u ζ) {d N p:ℕ}
open Extra.Histories Motion
variable (V:SectionData (C.labels.level d))(he: V.Sound C.params)(x:ℕ→ C.label d)
def badge (p:ℕ): Stem C p:= fun N=>initial V C.path N p (x N) 0
include he
lemma marked (p:ℕ): Pasted (badge V x p):=by
   let c:= V.stencil; let k:= c.sup (fun x=>Finset.univ.sup (fun i=> (x i).natAbs))
   refine ⟨k,Eventually.of_forall fun N=>?_⟩; unfold badge initial; let z:=(C.labels.level d).scaled (C.path.levels.budget N).threshold⁻¹ (x N); let o:Site (C.side N p):=0; let T:=V.places z o
   have hp :Interior (V.footprint o) T:=⟨V.placed_invariant he o z,(V.continuous_places ..).measurable, V.placed_local o z,(V.continuous_places z o).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩
   exact (hp.enlarges (K:=V.footprint o) (M:=GridApprox.window o k) fun t hx => by
      obtain ⟨y,hy,rfl⟩:= Finset.mem_image.mp hx
      have he i:(y i).natAbs ≤ k:=le_trans (Finset.le_sup (f:=fun i=> (y i).natAbs) (Finset.mem_univ i)) (Finset.le_sup (f:=fun x:Cover=> Finset.univ.sup (fun i=> (x i).natAbs)) hy)
      exact ⟨y,box_test.mpr ⟨fun i=> by have := he i;omega,fun i=> by have:=he i;omega⟩,rfl⟩).scale (((C.S.a N:ℂ)^d)⁻¹)
omit he
open Mark
variable (R:Mark.Weave G)(hV:Mark.Portfolio C.params V (R d))
include H hV
lemma paper (hx: ∀ᶠ N in atTop,(C.factory d N p).terminal (x N)∈ Mark.carrier C R d N p): Cloud C (badge V x p) :=by
   refine ⟨marked V hV.valid x p,?_⟩
   obtain ⟨r,M,h⟩:= radiusH R V hV
   refine ⟨r,?_⟩; filter_upwards [hx,lengths C.S M] with N hn hm o X he
   let W:Rowe C d:=fun j=>x N; obtain ⟨y,hY,h0⟩:= Mark.obtained R _ hn -- argument
   have ht : bloom ((badge V x p) N) o=((C.S.a N:ℂ)^d)⁻¹ • (V.evaluate ((C.labels.level d).coords (R d y)) ∘ expandAt o):=by
      have hg: bloom ((badge V x p) N) o= initial V C.path N p (x N) o:=by funext U; unfold bloom badge initial; simp
      rw [hg]; unfold initial
      unfold Mark.embedTo at h0; simp only [LinearEquiv.trans_apply] at h0; rw [show x N=_ from (C.factory d N p).terminal.injective h0]
      let F:=C.labels.level d; let j:= C.path.levels.clock.threshold N; rw [show ∀ w:C.label d,F.scaled j⁻¹ (Mark.tied C d N w)=w from (Mark.tied C d N).left_inv]; rfl
   rw [ht]; have hv :0 < C.beta N p:= (half_pos (zero_lt_one.trans (C.path.levels.fits.delayed _))).trans_le ( (Vintage.YM.RG.History.Selected.represents (Vintage.YM.Family.Makes.wilson H) N p N le_rfl).band.1)
   exact ((h y hY).scale (((C.S.a N:ℂ)^d)⁻¹)) (C.side N p) (hm p) o (C.beta N p) hv.ne' X he.localSites (GridApprox.cylinder_env he)
end YM.UVExtension.Fallow
