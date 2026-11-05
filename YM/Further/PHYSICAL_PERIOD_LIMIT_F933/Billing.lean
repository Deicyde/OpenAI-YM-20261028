import YM.Next.WARD_BIN.Rays
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Install
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Rainbow
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.COMMON_WITNESSES.RankMatrix
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.CUTOFF_PROJECTORS.Quotient
import YM.Push.FINITE_DETECTION.Test
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free







/-!
# Finite rank bills on the one presentation and Orders

The E.X basis for offers can come from Bel columns BEFORE picking
RBase. Use all estimates on a single Campaign before prolonging f;
`Wears` OR `Rain` (if with whole-orientation averaging) must hold on
the same E as the one on which the signed difference income and lifts
etc. hold. *Not* requesting PhysAct→one W, calibrate→another! -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Billing
open Function Filter Set MeasureTheory Lattice Extraction Around Cells Columns
  Bid Org Climb Push.CutoffProjectors Next.Extract ProjectorNext.Calibration ProjectorNext.Equivariance
  Push.Common Push.Corrected Dash
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {d : ℕ}
  {b : Presentation C} {A : Campaign C} {W : Worth} {f g : Extraction.Order}

/-- Kernel rank, per finite cut on which the calibration is served.
No continuum geometry except the free rank normalization proved once.
Factoring out residual=0 is the right comparison on `Cells.standard C`;
this step is *not* asserting true projection of the physical YM kernel. -/
lemma count (A : Campaign C) (d : ℕ) (i : ℕ × ℕ) (h : Function.Injective (A.packet d i.1 i.2).reference) :
    Module.finrank ℂ (LinearMap.range (A.presentation.step d i).toLinearMap) =
      Module.finrank ℂ ((Cells.standard C).Field d) := by
  let E := A.packet d i.1 i.2
  let α := Maxwell.equationIdeal G d
  let γ := A.presentation.step d i
  let S := Cells.standard C
  have hh := LinearMap.finrank_range_add_finrank_ker γ.toLinearMap
  have hs := Submodule.finrank_quotient_add_finrank (S.null d)
  rw [show LinearMap.ker γ.toLinearMap = E.subspace from A.ker d i.1 i.2,
    LinearMap.finrank_range_of_inj (f:=E.reference.toLinearMap) h, equation_dim] at hh
  have he : Module.finrank ℂ (S.null d) = Module.finrank ℂ α := by
    change Module.finrank ℂ ((Maxwell.freeTable C.book.grid).null d)=_
    rw [← Push.CutoffProjectors.free_null d (Push.FiniteDetection.residual_trivial ..)]; exact equation_dim _
  rw [he] at hs
  exact Nat.add_right_cancel (hh.trans hs.symm)

/-- The finite invoices (equations portion). Supporting ANY service
order under a procured f. We require physical transfers on the SAME
Campaign A used at relay/difference, not `Customs.purchases` on some
potentially changed A'. Averaged version is supplied for the symmetry
interfaces if helpful. d with zero ideal needs no calibration tests or
Account for `count` alone (and its mark rows from A are already trivial,
see later). -/
structure Banked (A : Campaign C) (d : ℕ) (f : Extraction.Order) (W : Worth) : Prop where
  ticket : Module.finrank ℂ (Maxwell.equationIdeal G d) ≠ 0 →
    f.late (fun N p => (A.packet d N p).Compares W) ∧
    ∃ M : Machine C.params d,
      (f.late fun N p => Wears A M N p) ∨ (f.late fun N p => M.Rain A N p)



lemma Banked.pays (H : Banked A d f W) (hp : Bank W C.path.levels) (hB : roomCost C.path.levels W) (hg : G.Simple) :
    ∃ c > (0:ℝ), f.late fun N p => (A.packet d N p).Separation c := by
  let α := Module.finrank ℂ (Maxwell.equationIdeal G d)
  rcases eq_or_ne α 0 with h|h
  · exact ⟨1,one_pos,Eventually.of_forall fun _ => Eventually.of_forall fun _ => (empty_space _ h 0 ∅ 0).2⟩
  obtain ⟨he,M,ht|ht⟩ := H.ticket h
  · obtain ⟨c,hc,H'⟩ := ProjectorNext.Calibration.margin A M hg
    exact ⟨c,hc,(H' W hp hB f).1 ((ht.and he).mono fun _ h => h.1.and h.2)⟩
  obtain ⟨c,hc,H'⟩ := M.signs A hg
  exact ⟨c,hc,H' W hp hB f ((ht.and he).mono fun _ h => h.1.and h.2)⟩

structure Works (A : Campaign C) (d : ℕ) (c : ℝ) (N p : ℕ) : Prop where
  light : (A.packet d N p).ComesFrom (A.box d)
  measure : (A.packet d N p).Separation c
  cardinal : Function.Injective (A.packet d N p).reference
  amount : Module.finrank ℂ (LinearMap.range (A.presentation.step d (N,p)).toLinearMap) =
    Module.finrank ℂ ((Cells.standard C).Field d)

lemma Banked.ready (H : Banked A d f W) (hp : Bank W C.path.levels) (hB : roomCost C.path.levels W) (hg : G.Simple) :
    ∃ c>(0:ℝ), f.late (Works A d c) := by
  obtain ⟨c,hc,K⟩ := H.pays hp hB hg
  refine ⟨c,hc,?_⟩
  refine ((A.auth_late d f).and K).mono fun i hi => (hi.1.and hi.2).mono fun j hj => ?_
  exact ⟨hj.1,hj.2,hj.2.injective,count A d _ hj.2.injective⟩

lemma Banked.receipts (H : ∀ d, Banked A d f W) (hp : Bank W C.path.levels) (hB : roomCost C.path.levels W) (hg : G.Simple) :
    ∃ c : ℕ → ℝ, (∀ d, 0<c d) ∧ (∀ d, f.late (Works A d (c d))) ∧ ∀ d, Persist.Count A.presentation f d := by
  choose c hc H using fun d => (H d).ready hp hB hg
  exact ⟨c,hc,H,fun d => (H d).mono fun _ hi => hi.mono fun _ hj => hj.amount.le⟩

section persistent
variable {T : Table C.book} (π : Push.Corrected.Survey C T) (h : G.Simple)

private def cost (f : Extraction.Order) (H : π.Ready f) (d k : ℕ) : ℝ := ((H d).known k).choose
variable {z : π.PerLabels} {t : π.Labels}

/-- Holder fields literally those from the corrected source work,
basis/detection columns fixed. -/
def support (f : Extraction.Order) (U : Table C.book) (H : π.Ready f) (t : π.Labels) : Offers (C:=C) U :=
    ⟨fun d => retarget (π.X d) U,fun d => Push.Corrected.offered h ((π.Y d).take U) (π.price d) (t d),cost π f H⟩

def holder (f : Extraction.Order) (H : π.Ready f) (U : Table C.book) (z : π.PerLabels) (t : π.Labels) : Holder (C:=C) U :=
  { X := support π h f U H t
    innerLimits := fun i v => z i v.1 v.2 }

variable (H : π.Ready f) (p : ∀ d, Persist.Count b f d) (Z : π.Read f z t)
variable {r : Push.Common.Snap C} {u : Push.Common.Snap.Upper r}

include Z p h in
/-- Keep both stages of limits for Survey and all o (Holder) data.
Income for those precise offers, not ones chosen in another `merge_rank`.
Doesn't ask for `Setup` or an independent physical all-copy-test `CheapBill`.
Predicated on quantitative Survey.Offer (`Known`, all real period mesh;
and `solves`, proper seams & output prices for EVERY subset). -/
lemma income (bH : Risen u b f) : (holder π h f H u.T z t).Income b f := by
  intro d
  let T := u.T
  let Y := (holder π h f H T z t).X.cylinder d
  have hv : Y.Valid f := valid h bH.base ((π.Y d).revoke T _ (H d)) ((π.Y d).carry T _ _ (Z d)) (p d) r.z bH.projections
  let o := (holder π h f H u.T z t).innerLimits d
  have he : Setup Y := ⟨hv.ratios,hv.same_stage,hv.scale_down,hv.conjugate,hv.unit,hv.tuned,hv.seams,hv.generic⟩
  have hr : Response Y f o := by
    refine ⟨fun _ => Eventually.of_forall fun _ => trivial,fun ⟨k,i⟩ p _ => (Z d).rows k i p,fun ⟨k,i⟩ => (Z d).outer k i⟩
  have hk (k) := ((H d).known k).choose_spec
  have ht : ∀ k ε, 0<ε → CheapBill Y f k ε := hv.cheap
  let X := retarget (π.X d) T
  have hc : Module.finrank ℂ ((Cells.standard C).Field d) = X.dim+1 :=
    (Module.finrank_eq_card_basis X.basis).trans (Fintype.card_fin _)
  have hs : SizeBill b f X := (p d).mono fun _ hi => hi.mono fun _ hh => hh.trans hc.le -- maybe field notation Count
  have hp := unselected_prices Y he bH.base.points hr (seamless bH.base.family) ht
  exact ⟨he,fun k => (hk k).1,fun i => by
    rcases i with _ | ⟨(_|_),k,i⟩
    · exact hs
    · exact (hk k).2 i
    exact ht k (toll i) (toll_pos i),hr,hp,(spans Y he bH.base.kernel.laws.toSymmetric hp ((size_pay bH.projections bH.base X).1 hs)).1,hv⟩

omit H in
/- Recover Stock at ANY Risen, without assuming our own earlier Base
choices. Count needed ultimately on that f's fused tail, not `each_p`
if not ordering Compares at each p. -/
lemma solvent_stock (D : Holder (C:=C) T) (hD : D.Income b f) : Push.Common.Stock b T f :=
  ⟨D.X,⟨fun i => (hD i).setup,fun i => (hD i).nonneg⟩,already fun i => (hD i.1).purchases i.2⟩

include H p h in
theorem stock (R : Risen u b f) : Push.Common.Stock b u.T f := by
  obtain ⟨g,v,w,hg⟩ := π.settles H
  let H' := Tails.refine f g
  have hc := income π h (π.tail H' H) (fun d => Persist.further (p d) H') hg (R.upon H')
  obtain ⟨X,hs,r,hr,H⟩ := solvent_stock _ hc
  refine ⟨X,hs,(fun i => g.refine (r i)),fun i => ?_,fun i => ?_⟩
  · obtain ⟨a,h⟩ := hr i; exact ⟨a,by simp_rw [h]; rfl⟩
  obtain ⟨i,h⟩ := H i; exact ⟨i,h⟩

include H p h
lemma detective (hl : ∀ d, RelayCosts b f d) (hr : Snap.First r b f) : Stationed f
    (fun d t => RelayCosts b t d ∧ Detector b t d) := by
  apply OnDemand.stations
  intro d g
  have hg := Tails.refine f g
  obtain ⟨u,z,t,hz⟩ := π.settles (π.tail hg H)
  let K := (f.refine g).refine u
  let hu := Tails.refine (f.refine g) u
  have ht : Tails K f := hu.trans hg
  exact ⟨u,ht.relay (hl d),
    ((Push.Corrected.finish π hr.family (ht.center hr.center) h (ht.raw hr.raw) (ht.projected hr.projections)
      (fun d => ht.relay (hl d)) (π.tail ht H) (fun d => Persist.further (p d) ht) _ _ hz).1 d)⟩

end persistent
end YM.Further.PhysicalPeriodLimitF933.Billing
