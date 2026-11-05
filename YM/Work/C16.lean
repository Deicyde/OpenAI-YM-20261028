import YM.Analysis.Polydisc
import YM.Axis.Matrix
import YM.Bid.Tar

/-!
# Real Lorentz covariance inside the tube

All arguments (including distribution supports) in absolute coordinates.
The position and frequency transports are `togetherL r` and
`togetherL (Lorentz.dual r)`, respectively, with Euclidean pairing.
The rotated lens pulled back along the frequency transport needn't be the
original lens globally. Compare only near `coneM`, where *both* cuts are
identically one, and use distribution support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C16
open Function Set Filter Distribution Mink Mink.Poincare Boundary Boundary.Surface
open Probe Bid
open scoped Topology InnerProductSpace

lemma rect_mem_tube {n : ℕ} (r : Lorentz) {x : Full n} (hx : x ∈ tube n) :
    rect r x ∈ tube n := by
  change shade x ∈ fields n at hx
  rw [tube, Set.mem_preimage, rect, im_glow]
  simp only [fields, Set.mem_iInter, Set.mem_setOf_eq] at hx ⊢
  intro i j hij
  rw [togetherL_at, togetherL_at, ← map_sub]
  exact (Lorentz.stays r _).2 (hx i j hij)

lemma dual_mem_coneM {n : ℕ} (r : Lorentz) {p : Points n} (hp : p ∈ coneM n) :
    togetherL (Lorentz.dual r) n p ∈ coneM n := by
  rw [coneM, Set.mem_iInter]
  intro k
  let b : Lorentz := Lorentz.dual k * Lorentz.dual r
  have hb := Boundary.present hp (Lorentz.dual b)
  rw [Lorentz.dual_involution] at hb
  rw [Set.mem_preimage]
  have he : togetherL (Lorentz.dual k) n (togetherL (Lorentz.dual r) n p) =
      togetherL b n p := PiLp.ext fun i => by simp only [b, togetherL_at, Lorentz.act_mul]
  rwa [he]

/-- Pull the lens back to the original frequency coordinates. The difference
is a Schwartz test supported in the open complement of the spectral cone. -/
lemma lens_support {G : Gauge} {L : Register G} {S : Table L} (W : Surface S)
    (D : ∀ i, Blanket i) (Y : W.Aurora D) {n : ℕ} (r : Lorentz)
    {x : Full n} (hx : x ∈ tube n) :
    tsupport (Y.lens n x - along (togetherL (Lorentz.dual r) n) (Y.lens n (rect r x))) ⊆
      (coneM n)ᶜ := by
  let A := togetherL (Lorentz.dual r) n
  let U := Y.lens n x - along A (Y.lens n (rect r x))
  change tsupport U ⊆ _
  intro p ht hp
  have hA : A p ∈ coneM n := dual_mem_coneM r hp
  let N := Metric.ball p 1 ∩ (A ⁻¹' Metric.ball (A p) 1)
  have ho : IsOpen N := Metric.isOpen_ball.inter (Metric.isOpen_ball.preimage A.continuous)
  have hn : p ∈ N := ⟨Metric.mem_ball_self zero_lt_one,
    show A p ∈ Metric.ball (A p) 1 from Metric.mem_ball_self zero_lt_one⟩
  have he : Disjoint N (Function.support U) := by
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨hq, hQ⟩ h
    have hc : (D n).cut q = 1 := (D n).immediate q ⟨p, hp, hq⟩
    have hC : (D n).cut (A q) = 1 := (D n).immediate (A q) ⟨A p, hA, hQ⟩
    apply h
    change Y.lens n x q - (along A (Y.lens n (rect r x))) q = 0
    rw [along_at, Y.shape n x hx q, Y.shape n (rect r x) (rect_mem_tube r hx)]
    have phase : plane (A q) (togetherL r n (reality x)) = plane q (reality x) := by
      rw [plane_dot, plane_dot q]
      simp only [plane, A, Boundary.parr]
    simp only [Blanket.lens, Blanket.attenuate, rect, re_glow, im_glow, hc, hC,
      phase, show inner ℝ (togetherL r n (shade x)) (A q) = inner ℝ (shade x) q from
        Boundary.parr r (shade x) q, sub_self]
  exact Set.disjoint_left.1 (he.closure_right ho) hn ht

theorem answer : YM.Bid.C16 := by
  -- Modified and FullBody are kept as in the application; the symmetry itself
  -- already follows for any Aurora from spectral support, shape and URS.
  intro G L S W K D Y F _hc hcone hurs _hb n v r x hx
  let A := togetherL (Lorentz.dual r) n
  let v' := fun i : Fin n => K.rail r (v i)
  let f := Y.lens n (rect r x)
  have he : Distn.fourier (W.W n v) (Y.lens n x) = Distn.fourier (W.W n v) (along A f) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact ((Distn.due _ _ (closedM n)).1 (hcone n v)) _ (lens_support W D Y r hx)
  have hv (z : Joint n) :
      Distn.fourier (W.W n v') (along A.symm z) = Distn.fourier (W.W n v) z := by
    simp only [Distn.fourier_at, A, Boundary.turns]
    exact hurs.rotation n v (hat z) r
  unfold Aurora.emit
  rw [he, ← hv (along A f), Probe.along_inv]

end YM.Work.C16
