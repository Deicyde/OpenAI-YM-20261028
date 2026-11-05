import YM.Push.FREE_RESOLVENT.Layout
import YM.Push.FREE_RESOLVENT.PatchComparison


/-!
# Stencil views in lifted working patches

Physical positive-coordinate alignment, on relative coarse displacements
with *all* fine residues and colors. No gauging chosen here independently
across roles. On overlapping views the same B,a axes are required. Use true
step (scale, odd L and P etc) unchanged. This component also works at small
tori/wrapping (subject to natural >1 coarse for the replica condition). To
instantiate a shared-coordinate injective patch for comparison later require
its own spatial room explicitly.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open Work.E03 Work.F08 Lifted
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c f' c' : Side} {S : StepData c f} {r : ℕ} {σ V A : ℝ}

namespace View

def addr (o : Site c) (z : Cover) := o+wrap c z

def bottom (S : StepData c f) (o : Site c) (z : Cover) (w : Site S.patch.L) := S.ratio.assemble (addr o z,w)

def coarseAt (o : Site c) (z : Cover) (t : PAC G r) : Slot G c r := (addr o z,t)

def fineAt (S : StepData c f) (o : Site c) (z : Cover) (t : Co S.patch.L (PAC G r)) : Slot G f r :=
  (bottom S o z t.1,t.2)

/-- In an oriented channel one uses *actual transformed locations*.
The PAC components in this view are interpreted in that row basis. -/
def fineHere (S : StepData c f) (s : Signed) (o : Site c) (z : Cover) (t : Co S.patch.L (PAC G r)) : Slot G f r :=
  ((StepData.sendSites s (0:Site f)).symm (bottom S o z t.1),t.2)

def coarseHere (s : Signed) (o : Site c) (z : Cover) (t : PAC G r) : Slot G c r :=
  ((StepData.sendSites s (0:Site c)).symm (addr o z),t)

lemma bottom_pp (S : StepData c f) (o : Site c) (z : Cover) (w : Site S.patch.L) :
    S.ratio.parent (bottom S o z w)=addr o z := S.ratio.assemble_parent _
lemma bottom_pr (S : StepData c f) (o : Site c) (z : Cover) (w : Site S.patch.L) :
    S.ratio.residue (bottom S o z w)=(w : Site S.patch.L) := S.ratio.assemble_res _
lemma home_addr (S : StepData c f) (o : Site c) (z : Cover) (t : Co S.patch.L (PAC G r)) :
    home S (fineAt S o z t)=addr o z := bottom_pp ..

lemma coarse_here (s : Signed) (o : Site c) (z : Cover) (t : PAC G r) :
    namedCo s (coarseHere s o z t)=addr o z := (StepData.sendSites ..).apply_symm_apply _
lemma bottom_adv (S : StepData c f) (o : Site c) (z : Cover) (w : Site S.patch.L) (v : Cover) :
    bottom S o z w+wrap f v=bottom S o (z+carry w v) (arrives w v) := by
  rw [moves_site S.ratio, bottom_pp,bottom_pr]
  unfold bottom addr; rw [map_add, ← add_assoc]; rfl
lemma wrap_walk (d : Step) : size (d.vec:Cover) ≤ 1 := by
  have he (i : Axis) : size (step i:Cover) = 1 := by simp [size,apply_ite Int.natAbs]
  rcases d with ⟨i,g|g⟩; · exact (he i).le
  change size (-(step i:Cover)) ≤ 1; rw [size_neg,he]
lemma bottom_root (S : StepData c f) (o : Site c) (z : Cover) :
    bottom S o z 0=S.ratio.embed (addr o z) := by
  change _ + wrap f (lift 0)=_
  rw [show lift (0: Site S.ratio.count) = 0 from funext fun _ => ZMod.valMinAbs_zero _, map_zero, add_zero]

lemma shift_adv (S : StepData c f) (o : Site c) (z : Cover) (w : Site S.patch.L) (d : Step) :
    bottom S o z w+d.vec=bottom S o (z+carry w d.vec) (arrives w d.vec) := by rw [← bottom_adv,wrap_vec]
lemma shift_neg (S : StepData c f) (o : Site c) (z : Cover) (w : Site S.patch.L) (i : Axis) :
    bottom S o z w-step i=bottom S o (z+carry w (negDir i).vec) (arrives w (negDir i).vec) := by
  rw [← shift_adv S]; rw [Step.vec_neg,← sub_eq_add_neg]
lemma size_adv {n : Side} (z : Cover) (w : Site n) (d : Step) :
    size (z+carry w d.vec) ≤ size z+1 := le_trans (size_add ..) (Nat.add_le_add_left ((carry_size ..).trans (wrap_walk _)) _)
lemma echo (o : Site c) (z v : Cover) : addr (addr o z) v=addr o (z+v) := by simp [addr,map_add,add_assoc]
lemma separation_view (o : Site c) (z : Cover) : separation o (addr o z) ≤ size z := by
  have hh := le_trans (native_le_taxi o (addr o z)) (wrap_bound o z)
  change ((separation _ _):ℝ) ≤ ((size z):ℝ) at hh; exact_mod_cast hh

-- Read agreement across periods.
section across
variable {P : Patch} {K : KernelChoices}
variable {h : f.val = c.val*P.L.val} {h' : f'.val = c'.val*P.L.val}

abbrev sees (p : Vec G c r) (q : Vec G c' r) (o : Site c) (o' : Site c') (R : ℕ) := ∀ z : Cover, size z ≤ R →
    ∀ i : PAC G r, p (coarseAt o z i)=q (coarseAt o' z i)
-- ts.count etc
abbrev sync (p : Vec G f r) (q : Vec G f' r) (h : f.val=c.val*P.L.val) (h' : f'.val=c'.val*P.L.val)
    (K : KernelChoices) (o : Site c) (o' : Site c') (R : ℕ) := ∀ z : Cover, size z ≤ R →
    ∀ i : Co P.L (PAC G r), p (fineAt (data h K) o z i)=q (fineAt (data h' K) o' z i)

/-- Require actual p,B,a coincide near the tested patch on all siblings. -/
structure Reads (p : pair G c f) (p' : pair G c' f') (h : f.val=c.val*P.L.val) (h' : f'.val=c'.val*P.L.val)
    (K : KernelChoices) (o : Site c) (o' : Site c') (R : ℕ) : Prop where
  front : sees p.1 p'.1 o o' R
  middle : sync p.2 p'.2 h h' K o o' R

variable {p : pair G c f} {p' : pair G c' f'} {o : Site c} {o' : Site c'} {R : ℕ}
lemma Reads.lower (H : Reads p p' h h' K o o' R) {r : ℕ} (hp : r ≤ R) : Reads p p' h h' K o o' r :=
  ⟨fun _ hh => H.front _ (hh.trans hp),fun _ hh => H.middle _ (hh.trans hp)⟩
lemma Reads.blank (H : Reads p p' h h' K o o' R) : Reads (G:=G) (p.1,0) (p'.1,0) h h' K o o' R :=
  ⟨H.front, fun _ _ _ => rfl⟩
lemma Reads.move (H : Reads p p' h h' K o o' R) {v : Cover} {r : ℕ} (he : size v+r ≤ R) :
    Reads p p' h h' K (addr o v) (addr o' v) r := by
  have hr (z : Cover) (hz : size z ≤ r) : size (v+z) ≤ R :=
    (size_add _ _).trans ((Nat.add_le_add_left hz _).trans he)
  refine ⟨fun z hz i => ?_,fun z hz i => ?_⟩
  · unfold coarseAt; rw [echo,echo]; exact H.front _ (hr z hz) _
  unfold fineAt bottom; rw [echo,echo]; exact H.middle _ (hr z hz) i

lemma next_step {x : Site c} (j : Axis) (hc : 1 < c.val) : x+step j≠x := by
  letI : Fact (1 < c.val) := ⟨hc⟩
  intro h
  have he : (step j:Site c) = 0 := add_left_cancel (h.trans (add_zero _).symm)
  have hi := congr_fun he j; simp at hi

lemma Reads.copy (H : Reads p p' h h' K o o' R) (hc : 1<c.val) (hc' : 1<c'.val)
    (z : Cover) (hz : size z ≤ R) (w : Site P.L) (i : Axis) :
    backdrop (data h K) p.1 (bottom (data h K) o z w,i)=backdrop (data h' K) p'.1 (bottom (data h' K) o' z w,i) := by
  unfold backdrop replica; rw [Ratio.parents_hop _ P.odd_side, Ratio.parents_hop _ P.odd_side]
  simp only
  erw [bottom_pr, bottom_pr,bottom_pp, bottom_pp]
  split <;> rename_i Hq
  · erw [if_pos Hq]; rw [if_neg (next_step _ hc), if_neg (next_step _ hc'),Work.F03.represent_link,Work.F03.represent_link]
    congr 1; ext l; exact H.front _ hz _
  erw [if_neg Hq]; simp
lemma Reads.enter (H : Reads p p' h h' K o o' R) (hc : 1<c.val) (hc' : 1<c'.val)
    (z : Cover) (hz : size z ≤ R) (w : Site P.L) (i : Axis) :
    unwrapped (data h K) p (bottom (data h K) o z w,i)=unwrapped (data h' K) p' (bottom (data h' K) o' z w,i) := by
  unfold unwrapped increment; rw [H.copy hc hc' z hz w i]
  congr 2; ext l; exact H.middle _ hz (w,coord i,l)
lemma Reads.march (H : Reads p p' h h' K o o' R) (hc : 1<c.val) (hc' : 1<c'.val) (z : Cover)
    (r : Site P.L) (w : Walk) (hx : size z+w.length ≤ R) :
    travel (unwrapped (data h K) p) (bottom (data h K) o z r) w=
      travel (unwrapped (data h' K) p') (bottom (data h' K) o' z r) w := by
  induction w generalizing z r with
  | nil => rfl
  | cons b w ih =>
    rw [travel, travel,shift_adv, shift_adv]; dsimp only
    have he : size (z+carry r b.vec)+w.length ≤ R := by have := size_adv z r b; simp at hx; omega
    erw [ih (z+carry r b.vec) (arrives r b.vec) he]
    congr 1
    cases b with
    | mk i v =>
      cases v
      · exact H.enter hc hc' _ (by simp at hx; omega) _ _
      rw [show ({dir:=i,neg:=true}:Step) = negDir i from rfl, Step.neg_read, Step.neg_read]
      rw [shift_neg (data h K) o z r i, shift_neg (data h' K) o' z r i]
      exact congr_arg (fun x : G.El => x⁻¹) (H.enter hc hc' _ (Nat.le_trans (Nat.le_add_right ..) he) (arrives r (negDir i).vec) i)


/-- Put channel-face coordinates in common cover positions *after*
including the actual orientation. -/
lemma Reads.reflect (H : Reads p p' h h' K o o' R) (hc : 1<c.val) (hc' : 1<c'.val)
    (s : Signed) (z : Cover) (w : Co P.L (PAC G r)) (W : Walk) (he : size z+W.length ≤ R) :
    travel (rays (data h K) s p) (fineHere (data h K) s o z w).1 W=
      travel (rays (data h' K) s p') (fineHere (data h' K) s o' z w).1 W := by
  unfold rays; rw [travel_pull, travel_pull]
  have hh (S : StepData c f) (w : Co S.patch.L (PAC G r)) : affine s 0 (fineHere S s o z w).1=bottom S o z w.1 :=
    (StepData.sendSites ..).apply_symm_apply _
  rw [hh]; change travel (unwrapped _ p) _ _=travel (unwrapped _ p') (StepData.sendSites s 0 ((StepData.sendSites s _).symm _)) _
  rw [Equiv.apply_symm_apply]; exact H.march hc hc' _ _ _ (by rwa [List.length_map])

lemma Reads.plaquettes (H : Reads p p' h h' K o o' R) (hc : 1<c.val) (hc' : 1<c'.val)
    (s : Signed) (z : Cover) (w : Co P.L (PAC G 2)) (he : size z+4 ≤ R) :
    faces (data h K) s p (fineHere (data h K) s o z w)=faces (data h' K) s p' (fineHere (data h' K) s o' z w) := by
  let i := plaqEquiv.symm w.2.1
  let W := square i.val.1 i.val.2
  have hw := H.reflect hc hc' s z w W he
  exact congr_arg (fun x => G.curvature x w.2.2) hw
end across
end View
end YM.FreeResolvent.Affine
