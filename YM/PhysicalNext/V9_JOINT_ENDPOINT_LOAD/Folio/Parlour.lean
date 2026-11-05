import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Lit

/-!
# Actual partial-sector local Install

Explicit upstream supplier ports for the Reading. In particular do *not*
call `Notice.meet` or `deltaReached` at local flags and infer use there,
including near a boundary. `Occupied` specifies the true-law alignment and
geometry wanted of the missing dictionary. The whole paths (even intermediate
keys and extra tests) paid; doesn't imply that all other readings of the term
fit in this currency. Nor does a flag test only near the start suffice to
prove Occupied. At a formal extension with wrong flags elsewhere, all actual
ratio coefficient charges still paid before the Clearance use. No
constructing the detector/seed inventories, direction context, row &
ancestor incomes, density/jacket jets or smoothness of held kernels away
from `Station`s domain. Use `Folio.Registration` for exact pricing supports.
The procurement applies to ALL sizes of first selections, but with other
charged poles & their verifications still external. Not invoking in a sum
over *other* fields (θ variables, tags, etc) without paying THEIR common
measurability/domination/eligibility/expansion licenses. Only positivity of
the stated principal *covariance* for the transfer: at partial flags do NOT
apply the normalized-column formulas to a potentially junk whole cloud.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching
open AnalyticBridge.NonflatCovarianceLocality.Placement AnalyticBridge.LocalGaussian Spot Spot.Programme Notice Reading
open MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {Q : Kiosk} {k n : ℕ} {θ E : ℝ} {d : Desk G S} {u : Spot d}
    {A : Stores S} {F : Forest S.ratio} {κ : S.Choices}
    {H R ι α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R]
    {X : Support c} {l : Viewport u X H R ι} {D : u.Slices} {b : Finset ℕ} {q : Programme D b} {z : q.Run α β γ}
    {a : Notice l} {B : Reading a z} {s : Seats l z} {M : Income α β γ (H⊕R)} {o : Site c} {V : Config G c} {Ω : Set (Config G c)}

abbrev glyph (s : Seats l z) (j : s.big) := upwards u.A u.F d.betaHat (s.issued j)
omit [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ] [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] in
lemma glyph_inj : Injective (glyph s) := upwards_inj.comp s.issued_inj

structure Occupied (s : Seats l z) (a : Notice l) (V : Config G c) : Prop where
  reads i : Seen d.betaHat u.A u.F V (l.read i)
  answer j : Known d.betaHat u.A V (glyph s j)
  canvas : a.C V=l.cropped V
  still (Y : LinkArray G u.FrozenKey) : a.m V (Y ∘ l.held) = u.m V Y ∘ l.slot

abbrev LocalNotice (P : Teller G) (d : Desk G S) := Bulletin d.betaHat P d.tube
namespace LocalNotice
variable (b₀ : LocalNotice P d) (h : Day Q θ E k n d) (u₀ : u=spectacle d A F κ)
include b₀ h u₀
omit [DecidableEq β] [DecidableEq γ] [Fintype α] [Fintype β] [DecidableEq H] [DecidableEq R] in
theorem pane (he : Occupied s a V) : (a.C V).PosDef ∧ Peak (a.C V) Q.cap := by
  subst u
  let B := amended d.betaHat A V
  have hr (i : H ⊕ R) : ∃ t : Active B d.betaHat F, t.val.val = l.edges i :=
    ⟨_,b₀.reader_bond (l.read i) (he.reads i)⟩
  choose e hf using hr
  let Y : (H⊕R) × G.ColorIndex → In d.betaHat B F (G:=G) := fun z => (e z.1,z.2)
  have hy (z) : pointer B F (Y z)=pointer A F (l.slot z) := Prod.ext (hf z.1) rfl
  have hy' : Injective Y := by
    intro i j hi; apply ((pointer_injective A F G).comp l.slot_inj).eq_iff.mp
    exact (hy i).symm.trans ((congr_arg _ hi).trans (hy j))
  let C := (fog B F d.tube d.betaHat V κ).submatrix Y Y
  have hC : a.C V=C := by
    rw [he.canvas]; ext i j
    have h₁ : ReadsWithin (AnalyticBridge.NonflatCovarianceLocality.Full.point S (pointer A F (l.slot i))) (settleR d.betaHat) A B F F V V κ κ := completion_reads (he.reads i.1) F κ V
    have h₂ := (cloud_local b₀.priced b₀.geometry).both h₁ (pointer A F (l.slot i)) (by have hh:=b₀.clearance_size; rw [separation_self]; unfold shiftR at hh; omega) (pointer A F (l.slot j))
    exact (b₀.clouds_shared V (l.slot i) (l.slot j)).symm.trans (h₂.1.trans ((congr_arg₂ (clouds d.betaHat d.tube B F V κ) (hy _).symm (hy _).symm).trans (b₀.clouds_shared V _ _)))
  rw [hC]; obtain ⟨hP,hV⟩ := h.capacity B F κ V rfl
  change Peak (fog B F d.tube d.betaHat V κ) Q.cap at hP
  exact ⟨hV.pane.submatrix hy', hP.project ⟨Y,hy'⟩⟩

omit [DecidableEq β] [DecidableEq γ] [Fintype α] [Fintype β] [Fintype H] [Fintype R] [DecidableEq H] [DecidableEq R] h b₀ u₀ in
lemma sites (he : Occupied s a V) (i : s.big) {n : ℕ} {u' v' : H⊕R} {Y : Tracks u.ActiveKey n} (hz : s.place i=.inr ⟨n,(u',v'),Y⟩) (t : Fin (n+1)) : Seen d.betaHat u.A u.F V (Y t) := by
  apply known_upwards (he.answer i); rw [Seats.issued,hz,project,Sum.map_inr]; simp [clues]




end LocalNotice
end YM.PhysicalNext.JointLoad.Folio
