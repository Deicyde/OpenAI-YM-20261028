import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Shared
import YM.Push.LOCAL_SPLITTING.Direct



set_option warningAsError false

/-!
# All input marker monomials in the common sector calculation

Use `Overlay.Bands` and `Marker.Census`:
ordered/physical copies can have distinct names (even for identical
insertions) but the marker algebra is COMMUTATIVE square-zero, possibly
with forbidden monomials.
Signs of source coefficients are not discarded, entries are complex.
Includes every subword permitted by the census and the constant term;
markers with no local effect (e.g., unit factors), translated inserts, and
spectators in this algebra use the same formulas. No assumption of output
Bands, aperture, separation, or anchor multiplicity bounds.

`Active,Radial` on the INPUT are sufficient, not using small values of an
already summed polynomial in place of address summability. Note Active format
has a padding convention requiring a marker type with at least one name;
empty selection within it is fine, empty name-type handled instead by `fixed`
and `apply_push` (for example on R.eval) or directly in the trajectory
consumer on complete marker coefficients. `mark` evaluated before engineering
rescaling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Marked
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Gaussian Rows YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid
open YM.Push.SectorMeasure YM.Next.Fluctuations.Sector
open YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented Overlay Marker
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {x w : ℝ}
variable {I : Type*} [DecidableEq I] [Fintype I] {R : Rep G f} {B : Census I}

def mark (U : Bands B R) (i : B.Mode) (y : Config G f) := (U.density y).part i

section envelopes
variable {U : Bands B R} {σ n Λ δ l : ℝ}

lemma mark_gauge (h : R.Lawful σ n Λ δ l) (ha : U.Active) (i : B.Mode) : GaugeInvariant (mark U i) := by
  intro k y
  apply congr_arg (fun f : Poly B => f.part i)
  have hr (j : ℕ) : U.ray j (gauge k y) = U.ray j y := by
    unfold Bands.ray; rw [Push.Local.Kernel.mask_gauge _ _ (ha.regular j).symmetry k y]
  have hg (j : ℕ) : U.each j (gauge k y) = U.each j y := by
    unfold Bands.each; simp only [Bands.tagged, ha.invi _ _ k y, h.labels.forced.sym _ k y]
  have hc (s : Finset ℕ) : U.packet s (gauge k y) = U.packet s y := by
    unfold Bands.packet; simp only [Activities.admissible, gauge_flags, hg]; congr
  unfold Bands.density
  simp only [Push.Local.Kernel.exp_invariant h k y, Bands.extra, hr, Bands.cluster, hc]

variable {a b g K : ℝ} {r : I → ℝ}

lemma bill_mark (h : R.Lawful σ n Λ δ l) (hb : 0 ≤ R.beta) (ha : U.Active)
    (hr : U.Radial r a b g K) (i : B.Mode) (y) :
    ‖mark U i y‖ ≤ Real.exp (R.scalar + Bands.fine (Fintype.card I) R a b g K n Λ δ l)/Poly.toll r i := by
  rw [le_div_iff₀ (Poly.worth hr.pure _), mul_comm]
  exact (Poly.member hr.pure i _).trans (U.physical ha hr h hb y)

lemma mark_envelope (h : R.Lawful σ n Λ δ l) (hb : 0 ≤ R.beta) (ha : U.Active)
    (hr : U.Radial r a b g K) (i : B.Mode) : Envelope (mark U i) :=
  ⟨(Poly.part_cont _).measurable.comp (U.density_meas ha h), _, bill_mark h hb ha hr i⟩

end envelopes







variable {T : Tube G S} {F : Forest S.ratio} {D : Allocation G S x w} {q : Chi} {J : ChartRatio G} {d : ℝ}



namespace Bought
variable {a b g K : ℝ} {r : I → ℝ} {U : Bands B R}
  (L : Bought T x R F D q J d)
include L

theorem coefficients (ha : U.Active) (hr : U.Radial r a b g K) (i : B.Mode) :
    Envelope (mark U i) ∧ S.push R.beta (mark U i) = paidSum T x R F D q J d (mark U i) ∧
    ∀ (A : Stores S) (k : S.Choices), (∀ V, Permission T x V k A R (shots S x) F D q J d
        (fog A F T x V k) (meanLog A F T x V k q d) (mark U i)) ∧
      Envelope (amount T x R F D q J d (mark U i) A k) ∧ Envelope (magnitude T x R F D q J d (mark U i) A k) := by
  obtain ⟨σ,n,Λ,δ,l,h⟩ := L.lawful
  have he := mark_envelope h L.beta.le ha hr i
  exact ⟨he,L.apply_push he (mark_gauge h ha i),fun A k => ⟨L.fixedTerm he A k,L.outer he A k⟩⟩


end Bought
end YM.Next.SectorChange.Marked
