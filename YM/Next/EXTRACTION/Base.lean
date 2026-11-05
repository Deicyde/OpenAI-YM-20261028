import YM.Next.EXTRACTION.Detector
import YM.Work.B10
import YM.Work.D01
import YM.Work.D02
import YM.Work.D03
import YM.Work.D04
import YM.Work.D05

/-!
# Common extraction through the normalized continuum base

**Conditional** on explicit estimates. See `Raw`, `Relay`, `Detector` for
these inputs. The application graph for RArrives/RBase should not be read as
saying the premises of D04 follow from those of RRaw. In particular the relay
cost and finite detector assumptions used here still require producers.

Keep every conclusion on exactly the same `C` and extraction `f`. The smooth
table `T` of `Base` has the actual ordered test and point limits after repair
through ties (`Cleaner.mesh`), with exactly the same individual-period tables
as the raw table (no point claim at axis ties). This provides the part of
`Seed` at RBase (i.e. excluding `RankWidths`). The arrival and cleaner
receipts expose all ingredients in the original interfaces; in particular,
`Hierarchy` retains coordinate reflection positivity (points and separated
smears), normalization/unit, H symmetries, homogeneity, and all inverse-power
bounds per test family / derivative, and the plan `W` is on the quotient of
this same `T`. No phase or relativistic statement here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Extract
open Set Filter Function Extraction Bid Dash
open scoped Topology

variable {G : Gauge} {C : Family G} {f g : Order} {S T : Table C.book} {M : ℕ → Table C.book}
variable {R : Bin S} {W : DiffPlan T} {b : Presentation C} {z : ∀ d : ℕ, ℕ → CoordMap C d}

/-- Surface reached by this module, named with the raw and smooth tables and
the particular bin. OneCap here has constants per fixed n, caps and vectors,
independent of spacings and positions; exponents natural, constants
nonnegative, `0 < r ≤ 1`. Capped in Hierarchy has the corresponding all
order bounds. -/
structure Base (C : Family G) (f : Order) (S : Table C.book) (M : ℕ → Table C.book) (R : Bin S)
    (T : Table C.book) (W : DiffPlan T) : Prop where
  family : C.Makes
  center : CenterPort C f
  carries d : RelayBin C R f d
  arrives : Org.Arrives C f S M
  pinned : Spans arrives.born R f
  clean : Org.Cleaner S M T W f
  cap : Bid.OneCap T
  kernel : T.Hierarchy

lemma Tails.spans {H : Live S} (h : Tails g f) (p : Spans H R f) : Spans H R g := by
  have ht (d e : ℕ) (a : C.label d) (m) (he : TestPlan R f d a e m) : TestPlan R g d a e m := by
    obtain ⟨x,hx⟩ := he
    exact ⟨x,fun i => (hx.meets i).mono_left h.fused,fun i => (hx.costly i).mono_left h.fused⟩
  refine ⟨fun d => ?_,p.q,fun _ _ h a => ht _ _ a _ (p.r _ _ h a),fun d k a => ht _ _ a _ (p.t d k a)⟩
  exact ⟨(p.p d).slides.mono_left h.fused,fun i x => ((p.p d).roots i x).mono_left h.fused⟩

lemma Tails.arrives (h : Tails g f) (p : Org.Arrives C f S M) : Org.Arrives C g S M := by
  obtain ⟨R,hR⟩ := p.pin
  exact ⟨h.raw p.census,p.born,R,h.spans hR⟩

lemma Tails.cleaner (h : Tails g f) (p : Org.Cleaner S M T W f) : Org.Cleaner S M T W g :=
  ⟨p.sharp,h.raw p.mesh,p.basic,p.smooth,p.ready,p.tilt⟩

lemma Tails.base (h : Tails g f) (H : Base C f S M R T W) : Base C g S M R T W :=
  ⟨H.family,h.center H.center,fun d => h.relayBin (H.carries d),h.arrives H.arrives,h.spans H.pinned,h.cleaner H.clean,H.cap,H.kernel⟩

lemma Base.points (H : Base C f S M R T W) : f.PointLimits C T := ⟨M,H.clean.mesh.mesh,H.clean.mesh.volume⟩

lemma Base.null (H : Base C f S M R T W) (d) : T.null d = LinearMap.ker (R d).trueP.toLinearMap :=
  Bin.transfer R H.arrives.born H.clean.sharp H.clean.basic.toSymmetric H.clean.smooth d
    (Bin.exactC R H.arrives.census.integral (H.pinned.p d) (H.pinned.q d))

/-- Arrive, get through ties, and assemble at RBase. Here RRaw selection and
projection convergence have already been achieved (e.g. by the proofs herein).
Allows proving finite estimates once that stage has been reached. -/
theorem finish (h : C.Makes) (c : CenterPort C f) (p : RawLimits C f S M) (he : Projected b f R z)
    (hr : ∀ d, RelayCosts b f d) (hd : ∀ d, Detector b f d) :
    ∃ T : Table C.book, ∃ W : DiffPlan T, Base C f S M R T W := by
  have hv : ∀ d, RelayBin C R f d := fun d => he.ready d (hr d)
  have hx (i : Live S) (d : ℕ) : Bin.shortage R i d :=
    shortage_of_detector i p.integral (he.approaches d) (he.same d).symm (hd d)
  have ha := Bid.arriving c h Work.D01.answer Work.D02.answer Work.D03.answer Work.D04.answer M p R hv hx
  have hm : Spans ha.born R f := Work.D04.answer Work.D01.answer Work.D02.answer Work.D03.answer ha.born h c
    p.integral R hv (hx ha.born)
  obtain ⟨T,W,H⟩ := ha.serves h c
  have hp : f.PointLimits C T := ⟨M,H.mesh.mesh,H.mesh.volume⟩
  have ht := Work.D05.answer h c H.smooth hp
  have hh := Work.B10.answer T T W (fun _ => le_rfl) H.smooth H.basic H.ready H.tilt ht
  exact ⟨T,W,h,c,hv,ha,hm,H,ht,H.stay h hh⟩

/-- Include the projection data in the extraction, same limits, then
finish. Again it suffices to prove the listed finite estimates on the given
`f`; even `RelayCosts` transports through the required further extraction. -/
theorem from_raw (h : C.Makes) (c : CenterPort C f) (p : RawLimits C f S M)
    (b : Presentation C) (he : Affordable b f) (hr : ∀ d, RelayCosts b f d) (hd : ∀ d, Detector b f d) :
    ∃ g : Order, ∃ R : Bin S, ∃ z, Projected b (f.refine g) R z ∧
    ∃ T : Table C.book, ∃ W : DiffPlan T, Base C (f.refine g) S M R T W := by
  obtain ⟨g,R,z,hp⟩ := include_projections S b he
  have hg := Tails.refine f g
  exact ⟨g,R,z,hp,finish h (hg.center c) (hg.raw p) hp (fun d => hg.relay (hr d)) (fun d => hg.detects (hd d))⟩

/-- **Main conditional extraction** through RBase. All input on the cutoff
family. Start with any `f` to be refined (in particular can use `Order.full`
to start without any subsequence). Include any given countable bank of fixed
numerical data with the stated bounds, retaining it throughout with genuine
ordered limits, even its mesh limits at all requested periods . May use `from_raw` / `finish` instead if some finite-cutoff estimates
are to be produced only between/after the earlier selection stages. -/
theorem common {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, FirstCountableTopology (X i)] [∀ i, T2Space (X i)] {A : ι → ℕ → Prop} {Y : ∀ i, ℕ → ℕ → X i}
    (h : C.Makes) (c : CenterPort C f) (H : Reserve f A Y)
    (b : Presentation C) (he : Affordable b f) (hr : ∀ d, RelayCosts b f d) (hd : ∀ d, Detector b f d) :
    ∃ g : Order, (∃ u y, Keeps (f.refine g) A Y u y) ∧
    ∃ (S : Table C.book) (M : ℕ → Table C.book) (R : Bin S), (∃ z, Projected b (f.refine g) R z) ∧
    ∃ (T : Table C.book) (W : DiffPlan T), Base C (f.refine g) S M R T W := by
  obtain ⟨g,S,M,hg,u,y,hw⟩ := raw h c H
  have hp := Tails.refine f g
  obtain ⟨a,R,z,hz,T,W,ha⟩ := from_raw h (hp.center c) hg b (hp.affordable he)
    (fun d => hp.relay (hr d)) (fun d => hp.detects (hd d))
  exact ⟨g.refine a,⟨u,y,(Tails.refine _ a).keeps hw⟩,S,M,R,⟨z,hz⟩,T,W,ha⟩
end YM.Next.Extract
