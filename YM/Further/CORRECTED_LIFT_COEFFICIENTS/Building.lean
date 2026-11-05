import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Collapse
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.PathCost


/-!
# Feed costs with cover constructions on the actual period

Single fit for a potentially very large common cube. No asserting estimates
on masks/final halos/radius of convergence (critical downstream needs!).
At the calibration point supports themselves suffice. Connector paths may
need a larger cube than the H-support cube. Do not drop that from geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Building
open Filter Function Set Lattice Wilson Labels RG Cells Source Source.Drops WilsonStartup
open Work Push.Corrected Push.CutoffProjectors Collapse PathCost Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side}

-- cube for H unmask. stencil padding *for calibration*: all used slots
-- lie within `limitsight` not necessarily `lot`. Keep size costs later.
def lot (n : Side) (m : ℕ) := (box m).image (wrap n)
lemma corner (m : ℕ) (i : Site n) (h : i ∈ lot n m) : separation i 0 ≤ m := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h; unfold separation; rw [sub_zero]; refine Finset.sup_le fun j _ => ?_
  have hh := box_test.mp hv
  apply (Corona.lap v j).trans; exact (by have := hh.1 j; have := hh.2 j; omega)
lemma inside (m : ℕ) (i : Site n) (h : separation i 0 ≤ m) : lift i∈box m := by
  unfold separation at h; rw [sub_zero] at h; rw [box_test]; constructor <;> intro j <;> have := (component_le i j).trans h <;> omega


def wall (m : ℕ) := 8*m+1
def limitsight (m : ℕ) := wall m+6

def distant (n : Side) (m : ℕ) := 20*(limitsight m + 1) ≤ n.val
variable {m : ℕ}
lemma fit (h : distant n m) : Nonwrapping (lot n m) 0 := by
  unfold distant limitsight wall at h; exact fun i hi => by have := corner m i hi; omega

private def door (x : Site n) := route 0 (lift x) 1
private theorem length_route (x : Cover) (h : x ∈ box m) (s : Lattice.Order) :
    (route 0 x s).length ≤ 4*m := by
  have he (w : List Axis) : (axisRoute 0 x w).length ≤ w.length*m := by
    induction w with
    | nil => simp [axisRoute]
    | cons a v ih =>
      have hh := (box_test.mp h).2 a; have hh' := (box_test.mp h).1 a
      change (straight a (x a-(0:Cover) a) ++ axisRoute 0 x v).length ≤ _
      simp only [Pi.zero_apply,sub_zero,List.length_append,straight,List.length_replicate,List.length_cons,add_mul,one_mul]; omega
  simpa only [route,allAxes,List.length_map,List.length_finRange] using he (allAxes s)

def nails (n : Side) (m : ℕ) := (Finset.univ (α:=Edge (Site n))).filter fun e =>
    e.1 ∈ lot n m ∧ e.1 + step e.2 ∈ lot n m
private theorem pounded (A : nails n m) : A.val.1 ∈ lot n m ∧ A.val.1 + step A.val.2 ∈ lot n m :=
    (Finset.mem_filter.mp A.property).2


private def orbit (A : nails n m) :=
    door A.val.1 ++ [posDir A.val.2] ++ Lattice.reverse (door (A.val.1+step A.val.2))
private lemma gated (h : distant n m) (A : nails n m) :
    stop (0:Cover) (door A.val.1 ++ [posDir A.val.2])=stop (0:Cover) (door (A.val.1+step A.val.2)) := by
  have hn : 2 ≤ n.val := by unfold distant limitsight wall at h; omega
  simp only [stop_append,door,route_end,stop,Step.vec_pos]; simpa only [sub_zero] using (lift_end hn (fit h) _ (pounded A).1 A.val.2).symm
private lemma closed (h : distant n m) (A : nails n m) : stop (0:Cover) (orbit A)=0 := by
  unfold orbit; rw [stop_append, gated h A, reverse_stop]
private lemma visited (A : nails n m) : (orbit A).length≤wall m := by
  have hp (x : Site n) (hx : x ∈ lot n m) : (door x).length ≤ 4*m := length_route (lift x) (inside m x (corner m x hx)) _
  have hb := hp _ (pounded A).2; have he := hp _ (pounded A).1
  unfold orbit Lattice.reverse wall; simp only [List.length_append,List.length_map,List.length_reverse,List.length_cons,List.length_nil]; omega
private def sender (U : Config G n) (x : Site n) := travel (expandAt 0 U) 0 (door x)
private theorem sent (h : distant n m) (A : nails n m) (U : Config G n) :
    gauge (sender U) U A.val=travel (expandAt 0 U) 0 (orbit A) := by
  unfold orbit; rw [travel_append,gated h A,travel_append, travel_reverse,door,route_end,travel,travel, mul_one,Lattice.Step.pos_read]; simp [expandAt]; rfl

lemma watches {i : Slot} {r : ℕ} (h : i.walk.length+4 ≤ r) : i.stencil ⊆ box r := by
  intro x hx; rcases Finset.mem_union.mp hx with he|he
  · apply borrow _ r ?_ (passages 0 i.walk (center_box 0) x (List.mem_toFinset.mp he))
    omega
  apply borrow _ r _ (passages _ _ (limit 0 i.walk (center_box 0)) x (List.mem_toFinset.mp he))
  simpa [square] using h
lemma vacancy_at (h : distant n m) (i : Slot) (hx : i.walk.length + 4 ≤ limitsight m) :
    ∀ y∈i.stencil, ∀ j, 20*((y j).natAbs+1) ≤ n.val := by
  intro y hy j
  obtain ⟨h1,h2⟩ := box_test.mp (watches hx hy); specialize h1 j; specialize h2 j; unfold distant at h; omega

-- choose transcripts independent of U. Independent slots per occurrence,
-- to simplify derivative estimates; do not treat as independent in propagation!
variable (G) in
def sill (h : distant n m) (A : nails n m) := (compress (G:=G) _ (closed h A)).choose
lemma load (G : Gauge) (h : distant n m) (A : nails n m) : (sill G h A).length ≤ wall m^2 :=
    (compress (G:=G) _ (closed h A)).choose_spec.1.trans (Nat.pow_le_pow_left (visited A) _)
lemma role (G : Gauge) (h : distant n m) (A : nails n m) (b : Brick) (he : b∈sill G h A) : b.1.walk.length ≤ wall m :=
    ((compress (G:=G) _ (closed h A)).choose_spec.2.1 b he).trans (visited A)
lemma hangs (h : distant n m) : ∀ᶠ U : Config G n in 𝓝 1, ∃ g : Site n → G.El,
    ∀ A : nails n m, gauge g U A.val=((sill G h A).map (lay (expandAt 0 U))).prod := by
  have hv : Tendsto (expandAt (0:Site n)) (𝓝 (1:Config G n)) (𝓝 1) := (continuous_pi (fun i => continuous_apply (wrap n i.1+0,i.2))).tendsto (1:Config G n)
  refine ((Filter.eventually_all.mpr fun A : nails n m => hv.eventually
    (compress (G:=G) _ (closed h A)).choose_spec.2.2)).mono fun U hu => ?_
  exact ⟨sender U,fun A => (sent h A U).trans (hu A)⟩
end YM.Further.CorrectedLift.Building
