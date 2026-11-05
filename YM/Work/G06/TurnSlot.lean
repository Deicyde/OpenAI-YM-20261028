import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.PCalc.Band
import YM.Source.Insertion

/-!
# G06: transport of curvature slots

Step signs in `pull` can send the based positive plaquette to a plaquette
with negative steps, or in reverse orientation. Cycling to the next
corner works for the actual Color readout too, if we append the traversed
link to the transport path. Swapping directions negates the result.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.G06
open Lattice Wilson RG
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge}

/-- `Slot.eval`, allowing a square with arbitrary step orientations. -/
def slanted (w : Walk) (a b : Lattice.Step) (U : CoverConfig G) : G.Color :=
  G.adjoint (travel U 0 w) (G.curvature (travel U (stop 0 w) (oriented a b)))

theorem slot_pos (v : Slot) (U : CoverConfig G) :
    v.eval U = slanted v.walk (posDir v.plaq.val.1) (posDir v.plaq.val.2) U := rfl

theorem slanted_swap (w : Walk) (a b : Lattice.Step) (U : CoverConfig G) :
    slanted w b a U = - slanted w a b U := by
  unfold slanted
  rw [oriented_swap a b, G.curvature_inv, map_neg]

theorem slanted_next (w : Walk) (a b : Lattice.Step) (U : CoverConfig G) :
    slanted (w ++ [a]) b a.rev U = slanted w a b U := by
  unfold slanted
  rw [travel_append, stop_append, stop, stop, oriented_next]
  simp only [travel, mul_one]
  let t := a.read U (stop 0 w)
  have hc (V : G.El) : G.curvature (t⁻¹ * V * t) = G.adjoint t⁻¹ (G.curvature V) := by
    simpa only [inv_inv] using G.curvature_conjugate t⁻¹ V
  rw [hc, ← G.adjoint_mul, mul_inv_cancel_right]

private lemma slanted_positive (w : Walk) {i j : Axis} (h : i ≠ j) :
    ∃ (v : Slot) (r : ℝ), (r = 1 ∨ r = -1) ∧
        ∀ U : CoverConfig G, slanted w (posDir i) (posDir j) U = r • v.eval U := by
  rcases lt_or_gt_of_ne h with h | h
  · refine ⟨⟨w, ⟨(i,j), h⟩⟩, 1, Or.inl rfl, ?_⟩
    intro U; rw [one_smul]; rfl
  refine ⟨⟨w, ⟨(j,i), h⟩⟩, -1, Or.inr rfl, ?_⟩
  intro U
  rw [slanted_swap w (posDir j), neg_smul, one_smul]; rfl

/-- Lower-corner normalization; the sign and path are fixed independently of U. -/
lemma slanted_slot (w : Walk) (a b : Lattice.Step) (h : a.dir ≠ b.dir) :
    ∃ (v : Slot) (r : ℝ), (r = 1 ∨ r = -1) ∧
        ∀ U : CoverConfig G, slanted w a b U = r • v.eval U := by
  rcases a with ⟨i, _|_⟩ <;> rcases b with ⟨j, _|_⟩ <;> change i ≠ j at h
  · exact slanted_positive w h
  · -- positive i, negative j: swap, then append the step to the lower corner
    obtain ⟨v,r,hr,hv⟩ := slanted_positive (G := G) (w ++ [negDir j]) h
    refine ⟨v,-r, ?_, ?_⟩
    · rcases hr with hr|hr <;> simp [hr]
    intro U
    change slanted w (posDir i) (negDir j) U = _
    rw [slanted_swap w (negDir j), ← slanted_next w, Step.rev_neg, hv, neg_smul]
  · obtain ⟨v,r,hr,hv⟩ := slanted_positive (G := G) (w ++ [negDir i]) h.symm
    refine ⟨v,r,hr,?_⟩
    intro U
    change slanted w (negDir i) (posDir j) U = _
    rw [← slanted_next w, Step.rev_neg, hv]
  obtain ⟨v,r,hr,hv⟩ := slanted_positive (G := G) ((w ++ [negDir i]) ++ [negDir j]) h
  refine ⟨v,r,hr,?_⟩
  intro U
  change slanted w (negDir i) (negDir j) U = _
  rw [← slanted_next w, ← slanted_next (w ++ _), Step.rev_neg, Step.rev_neg, hv]

private lemma stop_act (s : Signed) (x : Cover) (w : Walk) :
    s.act (stop x w) = stop (s.act x) (w.map (·.rotate s)) := by
  induction w generalizing x <;> simp_all only [stop,List.map_nil,List.map_cons,
    Step.vec_rotate, Signed.act_add]

theorem slanted_pull (s : Signed) (w : Walk) (a b : Lattice.Step) (U : CoverConfig G) :
    slanted w a b (pull s 0 U) = slanted (w.map (·.rotate s)) (a.rotate s) (b.rotate s) U := by
  unfold slanted
  simp only [travel_pull, affine, Signed.act_zero, add_zero,
    stop_act, oriented, List.map_cons, List.map_nil, Step.rev_rotate]

theorem slot_pull (s : Signed) (v : Slot) :
    ∃ (v' : Slot) (r : ℝ), (r = 1 ∨ r = -1) ∧
      ∀ U : CoverConfig G, v.eval (pull s 0 U) = r • v'.eval U := by
  let a := posDir v.plaq.val.1
  let b := posDir v.plaq.val.2
  obtain ⟨v',r,hr,hv⟩ := slanted_slot (G := G) (v.walk.map (·.rotate s))
    (a.rotate s) (b.rotate s) (s.perm.injective.ne v.plaq.property.ne)
  exact ⟨v', r, hr, fun U => (slanted_pull s v.walk a b U).trans (hv U)⟩

lemma slot_gauge (v : Slot) (t : Cover → G.El) (U : CoverConfig G) :
    v.eval (Lattice.gauge t U) = G.adjoint (t 0) (v.eval U) := by
  unfold Slot.eval Slot.offset
  rw [travel_gauge, face_gauge, G.curvature_conjugate, ← G.adjoint_mul, ← G.adjoint_mul]
  simp

lemma pull_gauge_zero (s : Signed) (t : Cover → G.El) (U : CoverConfig G) :
    pull s 0 (Lattice.gauge t U) = Lattice.gauge (fun x => t (s.act x)) (pull s 0 U) := by
  funext e
  change ((posDir e.2).rotate s).read (Lattice.gauge t U) _ = _
  rw [Step.gauge_read]
  simp only [Lattice.gauge, pull, affine, add_zero, Step.vec_rotate, Step.vec_pos, Signed.act_add]
end YM.Work.G06
