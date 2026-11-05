import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Mom
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Stereo


set_option warningAsError false

/-! Pullback valuation and first-order identification. No new analysis
assumptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Mom
open Function Filter Finset Tensor Work Set MeasureTheory RG Wilson Lattice Labels Source Drops Analysis
open Powers Mediator Next.Foundations Pattern Broadcast
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {d m : ℕ} {n : Side} (o : Site n) (X : Support n)

set_option maxHeartbeats 420000 in
lemma centered (x : Edge (Site n)) (v : Fin m → Slate G n d) : (iteratedFDeriv ℝ m (optic X o) 0 v) x=
    if needed X x then (iteratedFDeriv ℝ m (stereo G d) 0) (fun i => runway o x (v i)) else 0 := by
  let L : Directions G n →L[ℝ] G.Color := ContinuousLinearMap.proj x
  have hx := L.iteratedFDeriv_comp_left (n:=ω) (i:=m) (osmotic (d:=d) X o).1 le_top
  have ht := (show _ = L ((iteratedFDeriv ℝ m (optic X o (G:=G) (d:=d)) 0) v) from congrArg (fun f => (f : Tensor.T (Slate G n d) G.Color m) v) hx)
  change _= (iteratedFDeriv ℝ m (optic X o (G:=G) (d:=d)) 0 v) x at ht
  rw [← ht]
  by_cases h:needed X x
  · rw [if_pos h,show L ∘ optic X o=stereo G d ∘ runway o x from ?_];
    have hw := jets_linear (k:=m) (runway (G:=G) (d:=d) o x) ((scripts G d).1.of_le le_top)
    exact congrArg (fun f => (f : Tensor.T (Slate G n d) G.Color m) v) hw
    funext s; change optic X o _ x=_; rw [optic,if_pos h]; rfl
  rw [if_neg h,show L ∘ optic X o= (fun _ => 0) from funext (fun i => by change optic X o i x=_; rw [optic,if_neg h]),iteratedFDeriv_fun_zero]; rfl

lemma transmitted (x : Edge (Site n)) (v : Slate G n d) : fderiv ℝ (optic X o) 0 v x=
    if needed X x then (access v.2 (lift (x.1-o),x.2)) + (v.1 x.1-v.1 (x.1+Lattice.step x.2)) else 0 := by
  have he := centered o X x (fun _ : Fin 1 => v)
  rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply] at he
  rw [he, first]
  split; swap; rfl
  unfold access; rw [humming]
  change _- (v.1 _-v.1 x.1) = _+(v.1 x.1-v.1 _); dsimp [runway,stamp]; abel

lemma along (hn : 2 ≤ n.val) (h : Nonwrapping X o) : Mediator.curry (fun i => (Sites o X i (G:=G) (d:=d) : Set _)) (fun i => (Maps o X i (G:=G) : Set _))
    m (optic X o (G:=G) (d:=d)) := by
  intro m hm a u hx
  choose p hp hP using fun i => ((hx.1 i).2).1
  let f (x : Axis) (y : E4) := (iteratedFDeriv ℝ m (stereo G d) 0) (fun i => sight y x (p i) (u i).2)
  refine Exists.intro f ⟨fun j => channel m j p (fun i => (u i).2) a hp (fun i t hi => ((hx.1 i).2).2 t hi) (fun i => (hx.1 i).1), fun y => ?_⟩
  rw [centered]; split; swap; rfl
  next hY =>
    apply congrArg ((iteratedFDeriv ℝ m (stereo G d) 0) ·)
    funext i; unfold sight
    have ht : stamp o (y.1+Lattice.step y.2)=stamp o y.1+basis y.2 := by
      unfold stamp; rw [lift_end hn h y.1 hY.1,Pattern.xyz_step]
    change ((u i).1 y.1, (u i).1 (y.1+Lattice.step y.2)-(u i).1 y.1, _) = _
    rw [hP i _ hY.1,hP i _ hY.2,ht]
end YM.MultiNext.SignedSource.Mom
