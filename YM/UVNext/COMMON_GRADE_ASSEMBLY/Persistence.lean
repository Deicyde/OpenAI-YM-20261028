import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Post
import YM.Next.UV_STRESS.Across
import YM.Push.COMMON_WITNESSES.Link
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression



/-! # Which B70 / UV receipts transfer to a further common order

Stationed bills before collection are *not* generally persistent (nor can one assume two
suppliers choosing on a given order choose compatible suborders). Paid bills
built from fused/ordered tails often are. Also OnDemand suppliers (ability
to run on **arbitrary inherited orders**) are robust even under Tails.
We do NOT do a diagonal of (N,p) to combine anyone's estimates. Tails compares
mesh and period separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter Extraction Table Ward Climb Org Spec
  Next.Extract Next.UVStress Push.Common
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {S : Table C.book}

/-- A Tail refinement itself might not be an `after`; but it eventually is,
with equality, not merely frequently touching. -/
lemma tail_strict {s t : Sequence} (h : Tail s t) : ∃ a b : Sequence, s.after a = t.after b := by
  obtain ⟨n,hn⟩ := eventually_atTop.mp h
  choose x hx using fun i => hn (n+i) (Nat.le_add_right n i)
  have hm : StrictMono x := by
    intro i j hij
    apply t.monotone.lt_iff_lt.mp
    rw [hx,hx]; exact s.monotone (Nat.add_lt_add_left hij n)
  let a : Sequence := ⟨fun i => n+i,fun i j hij => Nat.add_lt_add_left hij n⟩
  have he : ∀ {u v : Sequence}, u.choose = v.choose → u=v := by
    rintro ⟨u,x⟩ ⟨v,y⟩ (h : u=v); subst h; rfl
  exact ⟨a,⟨x,hm⟩,he (funext fun i => (hx i).symm)⟩

lemma common_strict (h : Tails g f) : ∃ a b : Extraction.Order, g.refine a=f.refine b := by
  obtain ⟨a,b,ha⟩ := tail_strict h.mesh
  obtain ⟨x,y,hx⟩ := tail_strict h.per
  exact ⟨⟨a,x⟩,⟨b,y⟩,congr_arg₂ Extraction.Order.mk ha hx⟩

/-- Thus a true OnDemand supplier preserves its exact port, not just
existence of a new table with the estimates. Doesn't assume that the
estimates themselves have a transport theorem. -/
lemma demand_persists {ι : Type*} {P : ι → Extraction.Order → Prop} (p : OnDemand f P)
    (h : Tails g f) : OnDemand g P := by
  intro i r
  obtain ⟨u,v,he⟩ := common_strict ((Tails.refine g r).trans h)
  obtain ⟨w,hw⟩ := p i v
  rw [← he] at hw
  exact ⟨u.refine w,hw⟩



/-- Tail variants of the UV receipts, compare `Foundation.upon` proofs
for strict refinements. -/
lemma station_persists {a : (Bel C.book).RealSpin} {d n : ℕ} {R ε : ℝ} {X : Station C d}
    (p : X.Admissible f a n R ε) (h : Tails g f) : X.Admissible g a n R ε where
  lift_bound := ⟨_, h.late p.lift_bound.choose_spec⟩
  lift_unit := h.late p.lift_unit
  lift_real := h.late p.lift_real
  lift_signed := h.late p.lift_signed
  short i v hv t ht M he hh η hη := h.late (p.short i v hv t ht M he hh η hη)

lemma stations_persist {a : (Bel C.book).RealSpin} (p : Stations C f a) (h : Tails g f) : Stations C g a where
  arbitrarily d n R ε δ hr he hd := by
    obtain ⟨X,hX,H⟩ := p.arbitrarily d n R ε δ hr he hd
    exact ⟨X,station_persists hX h,H⟩

lemma nodes_persist {d D k l : ℕ} {e ε : ℝ} {J : Axis → Axis → C.book.Ref 4} {V : C.book.Ref d}
    (p : NodeBound C f D l k (d:=d) e ε J V) (h : Tails g f) : NodeBound C g D l k (d:=d) e ε J V where
  live i j m y he := by
    obtain ⟨x,⟨M,hM⟩,hx⟩ := p.live i j m y he
    exact ⟨x,⟨M,h.late hM⟩,fun η hη => h.late (hx _ hη)⟩





end YM.UVNext.Grade
