import YM.UVExtension.Oasis.Fruition
import YM.UVExtension.Reports.Deviations

/-!
 # Public fixed-volume UV extension and calibration

 * One Family C, non-empty Final on it; even the orders reading the smears
   can use full mesh on that Family (without claiming full infinite-volume
   convergence of any kind; the *period* is still ordered).

 * `Oasis.Floral`: detail of the achievement. Keeps calendar & uses witness
   (hence all lengths, stencil/ref choices, recurrence). `Spring`: includes
   UNIQUE success on it (`Plotted`: only band/recurrence/reach criteria),
   holomorphic coupling and E/K array views on a disk independent of N AND
   period, and full-sequence convergence of all the fixed-level normalized
   vacuum data. Norm completion (finite simultaneous sup-tests representing
   the weighted l1 norms); see `difference_sees`, `deviation_test` for
   comparing in the original labelled deviation with common support addresses.
   Exclude the field-independent `v` in `Rep.eval`.

 * `Shoal`, `Realizes`, `Terrace`: for *these* calibrated cylinder fields,
   kernels using the actual Wilson law. Physical analytic convergence in
   coupling at fixed period (here finite-family/one-order-higher period
   demands). Full mesh working down to ANY fixed separated compact, uniform
   in positions there & in the complex parameter on strict interiors, with
   derivatives, including each announced finite order of positional lattice
   differences (interpolate the differences themselves) converging to the
   corresponding spatial derivatives; no coordinate-projection separation
   needed. Smear limits on the same b-parametrized families. The test
   assertion of `Shoal` uses `suitable`, but the same Shoal proof buys even
   periodic (across seams) tested assertion, `periodic_tests` (and
   `periodic_caps`). Kernels on cover coordinates. Outside `NoHit` only
   padding. No identification with inserting at coincidence.

 `ultraviolet`: combine, only uses order extraction in addition for
 stipulations appearing in the retained baseline `Final`. The limits just
 described already hold along the FULL mesh sequence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Reports
open RG Lattice MeasureTheory Function Filter Extraction Spec Wilson Push
open Topology Precision PhysicalNext PhysicalNext.Repeat Legato Org Input
open Shoot Supply Roost Spire Orchard Camp Mast Harvest Oasis Cellar Beach
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {C : Family G} {hG:G.Simple}

-- The comparison-cell tests of Extraction: not even a rank-minimal
-- period needed in the plain real integrated limit.
lemma full_tests (h:Oasis.Floral (hG:=hG) C) :
    ∃ P:ℕ → Table C.book, Extraction.Order.full.Meshes C P ∧
    ∀ (n p) (u:Fin n→ C.book.Token) (t:Test n), Extraction.suitable C.S p t →
      Integrable (fun x=> t x * (P p).read x u) ∧
         Tendsto (fun i=> Extraction.Order.smears C i p u t) atTop
           (𝓝 (t.applyTo fun x => (P p).read x u)) := by
  obtain ⟨M,B,A,R,S,T,t,K,w,Q,L,H,rfl,-,hc,hB,hQ,-,h⟩:=h
  obtain ⟨_,hx,hP⟩:= hB.sponsors (Mast.roseA S)
  exact Hearth.slaked H L _ hx hB.tithe hP (fun _=> ⟨Orchard.rose0 S,tendsto_const_nhds (x:=(0:ℝ))⟩)

-- mesh-first ordered part of this T. Outer parameters remain the original.
-- Does not change Rank etc. witnesses or use a different C.S.
lemma useFull (h:Oasis.Floral (hG:=hG) C) {f:Extraction.Order} {T:Table C.book}
    (H:Nonempty (Final C f T)) : (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T := by
  obtain ⟨I⟩:=H; obtain ⟨P,hP,hV⟩:= full_tests h
  constructor; intro n u t
  obtain ⟨hx,k,hU,hF⟩:= I.room.ordered.reads n u t
  refine ⟨hx,k,fun p hp=>?_,hF⟩
  have ht:= hV n p u t hp|>.2
  exact (tendsto_nhds_unique (hU p hp) (ht.comp f.mesh.cofinal)) ▸ ht

variable {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {R:Factor A}
    {S:Uses R hG} {t:ℕ→ℕ} {K:ℕ→ℝ} {w:Bid.Worth} {Q:Bandage R K w}
    (L:Cellar S t Q)

-- Keys entries b are offsets from the single calendar bar. Cylinder basis,
-- reference levels etc. from the same Cellar. Makes.U only called literally
-- at center since it hardcodes .reaches; the theorem below clarifies
-- wilson/calibrated type at other offsets.
lemma offset_tests (v : Orchard.Keys S) (N p m : ℕ) (hm:m≤N) :
    let C:= Cellar.yard v L; let b:= (v N p).val; let μ:= C.path
    S.Success b N p (C.beta N p) ∧ μ.β N p 0=A.B.a.clock.bar+b ∧
      μ.levels=A.B.a ∧ μ.rep N p m=S.realBeat b N p m ∧
        (∫ U, (μ.rep N p m).eval U ∂prior G (C.side m p)) = partition G (C.side N p) (C.beta N p) ∧
        Vintage.YM.Family.Makes C ∧ Spec.Calibrated C ∧
        ∀ d,t d ≤ N →(C.factory d N p).Based C.params (C.localSection d) (C.ref d) := by
  intro C b μ; let h:=Cellar.intakeV v L
  refine ⟨?_,S.hits N p (v N p).property,rfl,rfl, Vintage.YM.RG.History.partition_eq μ h.wilson N p m hm,h,L.hardy v,fun d hd=> h.calibrated d N p hd⟩
  rw [Spire.Uses.genuine S b N p]; exact S.terminates N p (v N p).property

lemma analytic_tuning_test (S:Spire.Uses R hG) {Y:Org.Bolt A}
    (H:Upland.Arc R S Y) (b:ℝ) (hb:|b|< Upland.Arc.radius S) (N n:ℕ) :
    S.Success b N n (S.realBeat b N n N).beta ∧
      (∀ r, S.Success b N n r → Complex.ofReal r=Upland.Arc.betaK S N n N b) ∧
      AnalyticOnNhd ℂ (Upland.Arc.betaK S N n N) (Metric.ball (0:ℂ) (Upland.Arc.radius S)) := by
  have h : (b:ℂ) ∈ Broad A.B.a:= mem_ball_zero_iff.mpr ((Complex.norm_real b).trans_lt hb)
  have hv:= Oasis.spring H; obtain ⟨hV,hS,h₁,hQ⟩:= hv.here N n b hb
  exact ⟨(S.genuine ..).mpr (S.terminates N n h),fun r hp=> (hQ r hp).symm,(hv.has_fin N n N le_rfl).1⟩

/-! `bar` is not the parameter `penalty` below! bar, schedule and all
    prescription witnesses picked once. Read Flora after picking C. -/
theorem ultraviolet (G:Gauge) (h:G.Simple) (penalty:ℝ) (hp:0<penalty) :
    ∃ (C : Family G) (f: Extraction.Order) (T:Table C.book),
      Nonempty (Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧
        C.path.levels.clock.kernel.penalty=penalty ∧
        Oasis.Floral (hG:=h) C ∧
        (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
        ∀ d k:ℕ,∀ᶠ n in atTop,
          ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i,(v i).1≤d) →
            ∃ g,Poppy.Margins C r n k v g := by
  obtain ⟨C,hM,hC,F,hW,hs,hQ,H⟩:= Oasis.fruition h penalty hp
  obtain ⟨f,T,g,A,E⟩:= H Extraction.Order.full
  refine ⟨C,_,T,E,hM,hC,hW,F,useFull F E,hQ⟩
end YM.UVExtension.Reports
#check YM.UVExtension.Reports.ultraviolet
#print axioms YM.UVExtension.Reports.ultraviolet
#print axioms YM.UVExtension.Reports.offset_tests
#print axioms YM.UVExtension.deviation_test
#print axioms YM.UVExtension.Beach.periodic_tests
#print axioms YM.UVExtension.Beach.periodic_caps
