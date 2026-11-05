import YM.FullVolume.Stage.Freak
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
import YM.FullVolume.Arc

/-!
# First retainer purchase at finite cutoff and use for calibration

Attach `Arc` to the *same* Nest and calendar. Future analyticity
bounds must enforce uniqueness (not just along the surviving arc) with
the same startup & moving rules on a purchased family. This first purchase
is only onto-ness and trajectory data along the entire retained forward
range. Even one-off forward curve existence without a tie to an
actual construction would not give the latter
with Mark/Move certificates on other trajectories on an actual RG family!
-/

set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Filter Set MeasureTheory Lattice Wilson RG Shoot Input Supply
open AnalyticBridge VerifiedReset UVNext.CouplingReset
open Org PhysicalNext.Repeat Graces Roost Mallow Progress.DirectedRecipe
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {M: Metals G} {L : Rolls M.p} {A : Alloy M L}

lemma rodB (X : Factor A){ξ t τ a:ℝ} {V:Roof.Lyrics X t t}(Φ : Muse.Plato V ξ a a τ) :∃ T : Bolt A, Nonempty (Chosen X T) ∧ ∀ N n, Competes V.tunes n N 0 (T.history N n):=by
  have h:= Φ.SimpleR
  let C (p N:ℕ): Arc V.tunes p N 0:= Classical.choice (Arc.bought p N (V.supplier Φ.SimpleR) Φ.SimpleR Φ.firm 0 (Nat.zero_le _))
  let E (p N):Arc (still X) p N 0:= ⟨_,_,_,(C p N).nonempty,fun x hx=> V.disappears ((C p N).trials x hx),(C p N).top,(C p N).priced,(C p N).lower,(C p N).upper⟩; let B:=A.B
  have hv (p N) : B.a.clock.bar ∈ _ := (E p N).covers (interior_subset (centers A.B.a))
  choose k hx hz using fun p N=> show ∃ z∈ Icc (E p N).left (E p N).right, ((E p N).replay z 0).beta=B.a.clock.bar from hv p N
  let Y N p:= (E p N).replay (k p N)
  have hp N p : Competes (still X) p N 0 (Y N p):= (E p N).trials _ (hx p N)
  have hg N p m (hv : m<N): A.B.Move N m p (Y N p m) (Y N p (m+1)) := ((hp N p).persists _ (Nat.zero_le _) hv).continues.1
  have he : A.B.bake.Stays Y := by intro N p; have hf:= (hp N p).fromTop; exact ⟨fun i hi hj=> ⟨(lives ..).1 ((hp N p).prices i hi hj).1,((hp N p).prices i hi hj).2⟩,⟨hf.scalars,hf.raw,hf.inits.1⟩,fun i hi hi'=>A.B.links hi' (hg N p i hi')⟩
  let U:=A.B.bake.make Y
  have hw N p m (hm:m ≤ N):Lives A.B.bake N m p (Y N p m) := ((he N p).prices m (Nat.zero_le _) hm).1
  have hP (N p m) (hm:m<N):U.Transfer N p m:= ⟨(hg N p m hm).ident,(A.B.links hm (hg N p m hm)).drift⟩
  have hd : U.Selected:= {
    path_shared := fun N p q m hm ↦ (hw N p m hm).path.trans (hw N q m hm).path.symm
    represents := fun N p m hm ↦ ⟨(hw N p m hm).point, (hw N p m hm).clip,(hw N p m hm).valid, ((he N p).prices m (Nat.zero_le _) hm).2⟩
    starts := fun N p ↦ ⟨(he N p).fromTop.scalars,(he N p).fromTop.raw⟩
    steps := hP
    reaches := fun N p=> hz p N
    running := trajectory U (fun N p=>hz p N) hP }
  exact ⟨⟨X.worksNow h,Y,he,hd,fun N m p=> hg N p m⟩,
    ⟨E,k,hx,fun _ _=> rfl, ⟨fun N p=> (hp N p).fromTop.inits.2,fun N m p hm=> ((hp N p).persists _ (Nat.zero_le _) hm).continues.2⟩⟩,fun N p=> (C p N).trials (k p N) (hx p N)⟩
end YM.FullVolume
