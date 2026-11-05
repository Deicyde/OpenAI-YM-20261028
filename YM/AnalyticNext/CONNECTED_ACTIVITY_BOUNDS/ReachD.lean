import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Birthday
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tangent


/-!
# The D stencil even before seeing the tree, and the orientation footprints
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Function Matrix Lattice RG Wilson Pressure Pressure.Stores Precision Tree Exterior Turn
open Push.SectorMeasure Push.SectorMeasure.Oriented Work.F03 Progress.StationaryScenes
open Push.AbsoluteSums Next.Fluctuations
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def home (S : StepData c f) (p : Bond f) := S.ratio.parent p.1
def base (S : StepData c f) (i : Pos S) := i.1.act (center S i.2)

theorem pin_origin (S : StepData c f) (p : Bond f) : home S p∈points S p :=
  Finset.mem_image_of_mem _ (Finset.mem_insert_self ..)

theorem pin_radius (p : Bond f) (j : Site c) (h : j∈points S p) : separation (home S p) j ≤ 1 := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
  rcases Finset.mem_insert.mp hy with H|H
  · rw [H]; simp [home]
  rw [Finset.mem_singleton.mp H]; exact Work.E03.parent_step S p.1 p.2

lemma points_turn (s : Signed) (p : Bond f) : points S (edgeP s p) = (points S p).image s.act := by
  unfold points; rw [pin_map,Finset.image_image,Finset.image_image]; congr 1; funext x
  exact S.ratio.parent_signed S.patch.odd_side x s

lemma to_home (s : Signed) (S : StepData c f) (p : Bond f) :
    separation (s.act (home S p)) (home S (edgeP s p)) ≤ 1 := by
  rw [separation_comm]
  apply pin_radius; rw [points_turn]; exact Finset.mem_image_of_mem _ (pin_origin ..)

lemma along_home (s : Signed) (y : Site c) (S : StepData c f) (i : Bond f) :
    separation (s.act y) (home S (edgeP s i)) ≤ separation y (home S i)+1 := by
  refine le_trans (separation_triangle _ (s.act (home S i)) _) (Nat.add_le_add ?_ (to_home ..))
  rw [separation_signed]

lemma trunc_range (x : Site f) (s : Slot) :
    separation (S.ratio.parent x) (S.ratio.parent (slotFace s x).1) ≤ s.walk.length := by
  have hv : stop x s.walk = (slotFace s x).1 := by
    unfold slotFace Slot.offset; rw [wrap_stop_cover, map_zero, add_comm]; dsimp only
    exact (by simpa using (Work.E03.stop_add_left x (0:Site f) s.walk))
  rw [← hv]; exact Work.E03.sep_walk _ (Work.E03.parent_step S) x s.walk

/-- Gates on untransformed directions can be slightly larger; here
`v` is already in the normal physical orientation. -/
lemma pull_cost (s : Pos S) (V : Config G c) (v : Directions G f) (i : Bond f) :
    ‖untwine S s V v i‖=‖v (edgeP s.1 i)‖ := by unfold untwine rotateG; rw [G.norm_adjoint,maps_cost]

lemma pull_dep (s : Pos S) (V : Config G c) (v u : Directions G f) (i : Bond f)
    (h : v (edgeP s.1 i)=u (edgeP s.1 i)) : untwine S s V v i = untwine S s V u i := by
  simp only [untwine,rotateG,maps_apply,h]

lemma curl_range (S : StepData c f) (p : Cell f) (x y : Directions G f)
    (h : ∀ i : Bond f, separation (S.ratio.parent p.1) (home S i) ≤ 1 → x i=y i) : curl p x=curl p y := by
  simp only [curl_chain,chain]
  have hf j k := h (p.1+Lattice.step j,k) (Work.E03.parent_step S p.1 j)
  have hc j := h (p.1,j) (by simp [home]); rw [hf,hc,hf,hc]

lemma slot_range (T : Tube G S) (R : ℕ) (p : Pos S) (i : Twin f) (hi : p.2=Sum.inl i)
    (V : Config G c) (l : ℕ) (x y : Directions G f) (h : ∀ j : Bond f,
      separation (base S p) (home S j) ≤ (T.up.row i.1.2 l).2.length → x j=y j) :
    bandTerm T R i.1 l (untwine S p V x)=bandTerm T R i.1 l (untwine S p V y) := by
  let t := (T.up.row i.1.2 l).2
  let a := slotFace t i.1.1
  unfold bandTerm; split
  · refine congr_arg _ (curl_range S a _ _ ?_)
    intro j hj; apply pull_dep; apply h
    unfold base; rw [hi]
    have h1 := trunc_range (S:=S) i.1.1 t
    have h2 := separation_triangle (S.ratio.parent i.1.1) (S.ratio.parent a.1) (home S j)
    have h3 := along_home p.1 (S.ratio.parent i.1.1) S j
    change separation _ _ ≤ 1 at hj
    apply h3.trans
    change separation _ (S.ratio.parent a.1) ≤ t.walk.length at h1
    change _ ≤ t.walk.length + 4; omega
  rfl

lemma z_range (hb : S.patch.Branches S.kernel G) (i : Bond c) (x y : Directions G f)
    (h : ∀ j : Bond f,separation i.1 (home S j)≤predReach S.patch → x j=y j) :
    zLin S (form x) 0 i=zLin S (form y) 0 i := by
  let k : S.Choices := Classical.ofNonempty
  have he := zTest_deriv (S:=S) hb k i (form x,0)
  have hf := zTest_deriv (S:=S) hb k i (form y,0)
  apply HasDerivAt.unique _ hf
  refine he.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  unfold zTest; dsimp only [Prod.smul_mk,smul_zero]
  unfold Tube.Z
  rw [prediction_near_eq hb _ (represent (t • form x)) _ i ?_]
  intro j hh
  have hx := h j hh
  unfold represent increment
  change G.lieExp (t • collect G (form y) j)*_ = G.lieExp (t • collect G (form x) j)*_
  simp only [collect_form,hx]

def stencilD (D : RG.Patch) (R : ℕ) := R+predReach D+2

/-- Dependence on `x` (not the full record/readout; price those
also before declaring independence). -/
lemma derivative_range (T : Tube G S) (R : ℕ) (p : Pos S) (V : Config G c) (hb : S.patch.Branches S.kernel G)
    (x y : Directions G f) (h : ∀ i : Bond f, separation (base S p) (home S i) ≤ stencilD S.patch R → x i=y i) :
    derivative T R p V x = derivative T R p V y := by
  rcases p with ⟨s,i|i⟩
  · let p : Pos S := (s,Sum.inl i)
    unfold derivative; dsimp only [Sum.elim_inl]; unfold level; split
    next hi =>
      apply tsum_congr; intro l
      by_cases H : (T.up.row i.1.2 l).2.length ≤ R
      · exact slot_range T R p i rfl V l x y fun j hj => h j (hj.trans (H.trans (by unfold stencilD; omega)))
      simp [H]
    next hi =>
      refine congr_arg _ (curl_range S _ _ _ ?_)
      intro j hj; apply pull_dep; apply h
      exact (along_home s (S.ratio.parent i.1.1) S j).trans (by unfold stencilD; omega)
  unfold derivative; dsimp only [Sum.elim_inr]; refine z_range hb _ _ _ (fun j hj => ?_)
  apply pull_dep; apply h
  exact (along_home s i.1 S j).trans (by unfold stencilD; omega)

lemma lie_basis (i : Vars G f) (z : Bond f) (h : i.1≠z) : lie (Pi.single i 1) z=(0:G.Color) := by
  rcases i with ⟨p,l⟩
  ext k; simp [lie, Ne.symm h]

lemma tangent_support (T : Tube G S) {P : Teller G} (hT : P.Funds S T) (x : ℝ) (V : Config G c)
    (p : Ix G S) (i : Vars G f) (h : stencilD S.patch (till x)<separation (base S p.1) (home S i.1)) :
    scale T x V p i = 0 := by
  have hv : derivative T (till x) p.1 V (0:Directions G f) = 0 := map_zero (elongate x V p.1 hT)
  unfold scale; rw [Matrix.of_apply,derivative_range T _ _ _ (Push.SectorMeasure.funds_branch hT) _ 0 ?_,hv]; simp
  intro j hj; apply lie_basis i j
  rintro H; rw [← H] at hj; omega
end YM.AnalyticNext.ConnectedActivity.Aff
