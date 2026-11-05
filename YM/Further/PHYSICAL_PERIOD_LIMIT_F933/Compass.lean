import YM.Extra.WEAK_SCALING_ACTLAW.Common
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Bought
import YM.Next.MULTISOURCE.OneRate
import YM.Push.SECTOR_MEASURE.Profile
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Hosted





/-!
# Keep the canonical stress even after selection

One might wonder what of the meter, calibrated to unambiguously chosen
normalization via one sided curves, survives in the literal Final: the
retuned (full O + derivative flux) stress is only specified by Tab and
could well have an identity term, hence may not satisfy its *centering*,
even with the Encore in hand. Show what its centered part has to be on
any Cast with the Encore, fix also its ORIENTATION (since our free κ
is fixed), and then that can demand this actual normalization even
without centering after extraction: all character shell tests made again
by B09 on the **same** phase selection, even when class expectation
differs! Do not rerun anything downstream, Hilbert spaces/unbounded
adjoints etc are identical. This produces a literal Cast with this
canonical choice, also Legs etc now on its final stress, and identifies the
additional scale limit that goes with receipts. All at the E convention
of negative grad-test kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Compass
open Function Filter Set MeasureTheory Lattice Analysis Table Ward Climb Extraction Org Push.Common Snap Next.UVStress Next.Extract UVNext.Grade Work.A15
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {w : Snap C} {u : Upper w} {p : Presentation C} {W : Joint.Comparator C} {I : IR (C:=C) u.T} {Z : Cast u W.a.reads I}
  {X : Scaling u.T} {V : Guests u.T}

section normalize
variable {L : Register G} {T : Table L} (A : Rotation T) {S : DiffPlan T} {h : T.Hierarchy}

lemma raw {J : T.Stress} (ha : A.Laws S h.spin) (hp : Tensorial A J) : RawTensor h.spin J := by -- name shadow
  intro k a b
  rw [← ha.signed]
  exact hp k.ortho a b


end normalize

variable (h : Encore u p V W.a.reads I Z f X)
include h





lemma price (hk : 0 < W.a.T.κ) : 0 < Z.rate := by
  let t := h.stage.estimates.atBase.base.clean
  have ht := Extra.WeakScaling.kappa_sign W.a.reads h.stage.uv.basis.kernel t.ready t.tilt (I:=I) h.stage.uv.planet (h.stage.costs.Γ.sizes 4) h.stage.uv.weak
  change 0 < Z.rate * W.a.T.κ at ht
  exact pos_of_mul_pos_left ht hk.le


section canonical
variable (Z)
def orient : Cast u W.a.reads I := { Z with stress := (↑(Z.rate⁻¹) : ℂ) • I.J }
variable {Z}

-- centered part of tensorial T is also tensorial under rotations that
-- really orient the hierarchy. Can't just commute recenter out of
-- comparisons W.a.T to S, which have different expectations!
variable {L : Register G} {T : Table L}
omit h in
lemma re_tensor {A : Rotation T} (ho : A.Oriented T) {J : T.Stress} (hx : Tensorial A J)
    {D : DiffPlan T} {S : T.RealSpin} (he : A.Laws D S) : Tensorial A (reCenter T J) := by
  intro K i j
  have hk (v : T.Field 4) : expectation T _ (A.act 4 K v) = expectation T _ v := by
    simp_rw [expectation,Work.A01.front_eval]
    have hm : (Fin.cons (α:=fun _ => T.Tag) ⟨4,A.act 4 K v⟩ (blank T)) = A.label K ∘ Fin.cons ⟨4,v⟩ (blank T) := by
      ext1 e; refine Fin.cases rfl (fun l => Fin.elim0 l) e
    have hh := ho 1 (Fin.cons ⟨4,v⟩ (blank T)) 0 conf1 K
    rw [show Points.move K (0:Points 1)=0 by ext1 a; exact K.motion.map_zero] at hh
    rw [hm]; exact hh
  change A.act 4 K (centering T 4 (J i j))=∑ a : Axis,∑ b : Axis,_ • centering T 4 (J a b)
  rw [value_center,map_sub,map_smul,he.identity,← hk, hx]
  simp_rw [map_sum, map_smul,value_center,smul_sub, Finset.sum_sub_distrib, Finset.sum_smul,smul_smul]
  rfl


end canonical









omit h in
lemma shells (hp : Legs f I.J) : Legs f (orient Z).stress := fun l => legRow_scale l.2.1 (hp l) _



open RG Supply Precision Timing Labels Source Spec
variable {κ : ℝ} {hκ : 0 < κ} {J : Timing.OrderBook} {M : Timing.Inception G κ hκ J} {R : Timing.Requests}
  {S : Timing.Layout M R} {U : Timing.Reserves} {L : Timing.Ledger M S U} {n : ℕ → ℕ}
  {β : ℕ → ℝ} {D : Rolls {L.s with floorL:=n}} {P : Timing.Price (L:=L) D} {hG : G.Simple}
omit h
variable (E : Developed (β:=β) L D P hG) (K : Developed.Compiled hG E)
-- auxiliary receipt on the compiled funded context, keeping extraction for use
open Cook
abbrev farm := family (Developed.story hG E) K.run
open Push.Common renaming Snap → Snaps

structure Green (f : Extraction.Order) where
  w : Push.Common.Snap (farm E K)
  u : Upper w
  offers : Guests u.T
  I : IR (C:=farm E K) u.T
  Z : Cast u K.free.a.reads I
  s : Scaling u.T
  x : K.coupons.π.PerLabels
  y : K.coupons.π.Labels
  orientation : Z.stress = (↑(Z.rate⁻¹) : ℂ) • I.J
  encore : Encore u K.crew.presentation offers K.free.a.reads I Z f s
  leg : Legs f Z.stress
  ranks : K.coupons.π.Read f x y

-- Re-export Final, canonical orientation and all orders tuple, heat & adjoint on same calibrated data
open Boundary
example (f : Extraction.Order) (Y : Green E K f) : Calibrated (farm E K) := Y.encore.stage.trajectory



open Push.Corrected
-- reserve along compiled. Also leave correction basis identity; Holder path at post u on plate Q, ties derivative identities in Late.

end YM.Further.PhysicalPeriodLimitF933.Compass
