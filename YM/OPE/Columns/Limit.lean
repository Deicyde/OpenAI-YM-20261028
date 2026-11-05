import YM.OPE.Columns.ExtensionCost
import YM.OPE.Columns.Reannounce
import YM.Next.UV_STRESS.Vary

/-!
# Membership in the true physical filtration

A sublimit of a bounded output assembled from the plane, along the SAME ordered tails
as above, lies in the e-filtration of the *actual* hierarchy. Not a claim about bare
label lifts or the transfer matrices converging on those tails.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Columns
open Function Set Filter MeasureTheory Analysis Wilson MergeProof Labels Source
open Bid Push.RelayDifference Extraction Next.Extract Dash
open Work.G08 Extra.Histories
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {W r D} (T : TableTickets C W r D) {d e : ℕ} (hG : G.Simple)
  {f : Extraction.Order} {A S : Table C.book} {V : DiffPlan S} {M : ℕ → Table C.book} {R : Bin A} {X : DiffPlan S}
  -- NOTE we allow X different from the witnessing V.
  (L : Base C f A M R S V) (h : X.Inclusions S)
set_option quotPrecheck false
local notation "F" => C.labels.level d
local notation "K!" => fun i : Cutoffs => (C.factory d i.1 i.2).terminal

include T hG L h
lemma belongs (v : Rowe C d) (x : C.label d) {b : Filter Cutoffs} [b.NeBot] {z : ℝ}
    (he : e < d) (hp : b ≤ f.fuse)
    (hz : ∀ᶠ i in f.fuse, ‖v i‖ ≤ z) (hw : ∀ᶠ i in f.fuse,
      low F e (((K!) i).symm (v i))=((K!) i).symm (v i))
    (hx : Tendsto v b (𝓝 x)) : S.project d x ∈ LinearMap.range (X.rise he.le) := by
  have hm := onions L.family T.tabs T.system hG T.reissue (Bid.upper C v)
    (reannounce T L.family hG v hz hw he) (Stencilled.upper L.family v)
    (Eventually.of_forall fun i => C.continuousO ..)
  let P (i : Shot C.book) := Shot.core i (d:=d) A L.arrives.born x
  have ht (i : Shot C.book) :
      Tendsto (uncurry (targetB (Bid.upper C v) i)) b (𝓝 (P i)) := by
    refine (arcing ((i.ready L.arrives.born L.arrives.census.integral d).mono_left hp) hx).congr ?_
    rintro ⟨N,p⟩; exact (ExtensionCost.upper_scan ..).symm
  obtain ⟨y,hy⟩ := ExtensionCost.matched hp Work.D01.answer Work.D02.answer L.family L.center R (L.carries e)
    (ExtensionCost.sober_upper v) hm ht
  obtain ⟨u,-,hu⟩ := brace (fun i => snapshots i e) (fun i => Shot.core i A L.arrives.born)
    (((L.pinned.p e).slides).mono_left hp)
    (Bin.exactC R L.arrives.census.integral (L.pinned.p e) (L.pinned.q e))
    (fun i => (i.ready L.arrives.born L.arrives.census.integral _).mono_left hp) y hy
  refine ⟨S.project e u, S.field_ext L.kernel.laws.toSymmetric ?_⟩
  intro n v s hs
  rw [h.kernels _ (S.project e u) hs]
  simp_rw [MonitorOps.head S L.kernel.laws.toSymmetric _ v hs]
  let w : Fin n → C.book.Token := fun i => ⟨(v i).1, S.representative _ (v i).2⟩
  let q (z : C.book.Token) (s : Points (n+1)) := S.read s (Fin.cons z w)
  apply (Test.unique_kernel (K:=q ⟨e,u⟩) (P:=q ⟨d,x⟩)
    ((S.smooth_read L.clean.smooth _).continuousOn) ((S.smooth_read L.clean.smooth _).continuousOn)).1 ?_ hs
  intro t
  let p := Shot.mk _ 0 (Fin.cons (α:=fun _ => C.book.Token) ⟨d,x⟩ w) t
  have he (z : C.book.Token) : update (Fin.cons (α:=fun _ => C.book.Token) ⟨d,x⟩ w) 0 z=Fin.cons z w := by simp
  have hx:=hu p
  change t.applyTo (fun x => A.read x (update _ 0 (⟨e,u⟩:C.book.Token))) = t.applyTo
    (fun a => A.read a (update _ 0 ⟨d,x⟩)) at hx
  rw [he,he] at hx; simp_rw [faithful L.clean.sharp] at hx; exact hx

lemma limit_lower (v : Rowe C d) (x : C.label d) {b : Filter Cutoffs} [b.NeBot]
    (he : e < d) (hp : b ≤ f.fuse)
    (hw : ∀ᶠ i in b, low F e (((K!) i).symm (v i))=((K!) i).symm (v i))
    (hx : Tendsto v b (𝓝 x)) : S.project d x ∈ LinearMap.range (X.rise he.le) := by
  classical
  let z := ‖x‖ + 1
  let P := fun i : Cutoffs => ‖v i‖ ≤ z ∧ low F e (((K!) i).symm (v i))=((K!) i).symm (v i)
  let w : Rowe C d := fun i => if P i then v i else 0
  have heq(i):‖w i‖ ≤ z ∧ low F e (((K!) i).symm (w i))=((K!) i).symm (w i):= by
    dsimp only [w]; split
    next h => exact h
    simp; exact add_nonneg (norm_nonneg _) zero_le_one
  apply belongs T hG L h w x he hp (Eventually.of_forall fun i=>(heq i).1)
    (Eventually.of_forall fun i=>(heq i).2)
  exact hx.congr' ((hw.and (hx.norm.eventually (ge_mem_nhds (by dsimp only [z]; simp : ‖x‖<z)))).mono
    fun i hi => Eq.symm (if_pos (show P i from hi.symm)))
end YM.OPE.Columns
