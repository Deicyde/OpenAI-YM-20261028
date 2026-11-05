import YM.Work.B10
import YM.Work.D05
import YM.Work.D06




/-!
# A single input order for RClose

The global assembly problem is **not** solved by choosing infinitely many
ordered mesh/period limits independently. Here is one positive theorem about
the compatibility it needs. Above explicit common lower data (through an
Order before some of the physics tasks), schedule certain *per-demand*
supplies in further orders, including powers-of-roots estimates and grid
estimates with specific quantifier dependencies, on that same family. Need
supplies at `f.refine p` with **arbitrary** p each time; just receiving one
estimate at some order of the producer's choosing and another separately
doesn't entitle calls to this theorem. But we can ask quite separately: e.g.
a RankWidths set of estimates *for one d* (all k still required); even grid
estimates *per arity and placement* can use further refinements. And Grid
service only need respond when (all-d) Seed already holds.

Choose *nested* stations on requested Order axes. Prove there is a genuine
refinement of the original order retaining all these estimates; no switching
of histories, no auxiliary choices after boundary, no replacement of
`Order.limits` by a diagonal limit. Preserve the old Arrives (S₀ & Bin
interfaces) and Cleaner and prove full `UV`. Nothing proves that these
request-based antecedents will be inhabited -- important research
obligations!
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function
open Extraction
open scoped Topology

/-- `F` after `G`, in the two required axes separately, for purposes of tail
comparisons. Holds also for certain "diagonals" through *towers of Orders*,
even though F need not be literally `G.refine _`. -/
structure Refines (F G : Order) : Prop where
  mesh : Filter.map (fun n => F.mesh n) atTop ≤ Filter.map (fun n => G.mesh n) atTop
  per : Filter.map (fun n => F.per n) atTop ≤ Filter.map (fun n => G.per n) atTop

theorem refine_fits (F G : Order) : Refines (F.refine G) F := by
  constructor
  · intro s h
    change ∀ᶠ i in atTop, F.mesh i∈s at h
    exact G.mesh.cofinal.eventually h
  intro s h
  change ∀ᶠ i in atTop, F.per i∈s at h
  exact G.per.cofinal.eventually h

namespace Refines
variable {f g : Order}
protected theorem cons (h : Refines f g) (t : Order) : Refines (t.refine f) (t.refine g) := by
  constructor
  · simpa only [map_map] using! (map_mono (m:=fun n => t.mesh n) h.mesh)
  simpa only [map_map] using! (map_mono (m:=fun n => t.per n) h.per)

-- Include every usage distinguishing mesh THEN volume.
protected theorem late (h : Refines f g) {A : ℕ → ℕ → Prop} (ht : g.late A) : f.late A := by
  change ∀ᶠ k in Filter.map (fun i => g.per i) atTop, ∀ᶠ j in Filter.map (fun i => g.mesh i) atTop,
    A j k at ht
  exact (ht.filter_mono h.per).mono fun _ he => he.filter_mono h.mesh

protected theorem limits (h : Refines f g) {A : ℕ → Prop} {X : Type*} [TopologicalSpace X] {W : ℕ→ℕ→X}
    {x : X} (H : g.limits A W x) : f.limits A W x := by
  obtain ⟨u, v, hv, hx⟩ := H
  refine ⟨(show ∀ᶠ k in Filter.map (fun i => g.per i) atTop, A k from u).filter_mono h.per, v,
    fun p hp => ?_, ?_⟩
  · intro P hP
    change ∀ᶠ j in Filter.map (fun i => f.mesh i) atTop, W j p∈P
    exact Eventually.filter_mono h.mesh ((hv p hp) hP)
  intro T hT
  change ∀ᶠ k in Filter.map (fun i => f.per i) atTop, v k∈T
  exact Eventually.filter_mono h.per (hx hT)

protected theorem fuse (h : Refines f g) : f.fuse ≤ g.fuse := by
  intro s hs
  change ∀ᶠ k in g.fuse, k∈s at hs
  change ∀ᶠ k in f.fuse, k∈s
  rw [Order.fused] at hs ⊢
  exact h.late hs
end Refines

section diagonal
private lemma one_axis (t : ℕ → Sequence) (H : ∀ i : ℕ, ∃ r : Sequence, t (i+1)=(t i).after r) :
    ∃ g : Sequence, ∀ i : ℕ, Filter.map (fun k => g k) atTop ≤ Filter.map (fun k => t i k) atTop := by
  let g (i : ℕ) := t i i
  have hg : StrictMono g := strictMono_nat_of_lt_succ (fun n => by
    obtain ⟨p, hp⟩ := H n
    change t n n < t (n+1) (n+1)
    rw [hp, Sequence.after_apply]; exact (t n).monotone (p.monotone.id_le (n+1)))
  have he (i j : ℕ) (h : i≤j) : ∃ U : Sequence, t j=(t i).after U := by
    induction j, h using Nat.le_induction with
    | base => exact ⟨Sequence.full, rfl⟩
    | succ j hj ih =>
      obtain ⟨U, hu⟩ := ih
      obtain ⟨V, hv⟩ := H j
      exact ⟨U.after V, by rw [hv, hu]; rfl⟩
  refine ⟨⟨g, hg⟩, fun i => ?_⟩
  intro s hs
  change ∀ᶠ j in atTop, t i j∈s at hs
  obtain ⟨m, hm⟩ := eventually_atTop.mp hs
  change ∀ᶠ j in atTop, t j j∈s
  filter_upwards [eventually_ge_atTop i, eventually_ge_atTop m] with j hj hx
  obtain ⟨U, hu⟩ := he i j hj
  rw [hu]
  exact hm (U j) (hx.trans (U.monotone.id_le j))

/-- Orders through a tower; this lemma alone gives tail comparison. -/
theorem tower (T : ℕ→Order) (h : ∀ n, ∃ p, T (n+1)=(T n).refine p) :
    ∃ g : Order, ∀ n, Refines g (T n) := by
  obtain ⟨a, ha⟩ := one_axis (fun i => (T i).mesh) (fun i => by
    obtain ⟨r, hr⟩ := h i; exact ⟨r.mesh, by rw [hr]; rfl⟩)
  obtain ⟨b, hb⟩ := one_axis (fun i => (T i).per) (fun i => by
    obtain ⟨r, hr⟩ := h i; exact ⟨r.per, by rw [hr]; rfl⟩)
  exact ⟨⟨a, b⟩, fun i => ⟨ha i, hb i⟩⟩

/-- Countable fusion ending at a single **refinement of f**, paying all
requests. Feed producers genuine order refinements; use sides individually
in diagonalization. -/
theorem concert (f : Order) {ι : Type*} [Nonempty ι] [Countable ι] (P : ι → Order → Prop)
    (supply : ∀ i (g : Order), ∃ k : Order, P i ((f.refine g).refine k))
    (stays : ∀ i g k, Refines g k → P i k → P i g) : ∃ g : Order, ∀ i, P i (f.refine g) := by
  choose r hr using supply
  obtain ⟨s, hs⟩ := exists_surjective_nat ι
  let T : ℕ → Order := Nat.rec Order.full fun n g => g.refine (r (s n) g)
  obtain ⟨g, hg⟩ := tower T (fun n => ⟨r (s n) (T n), rfl⟩)
  refine ⟨g, ?_⟩
  intro i
  obtain ⟨n, rfl⟩ := hs i
  exact stays (s n) _ (f.refine (T (n+1))) ((hg (n+1)).cons f) (hr _ (T n))
end diagonal

open Spec Org Cells
variable {G : Gauge} {C : Family G} {f g : Order} {S₀ S : Table C.book} {P : ℕ → Table C.book} {V : DiffPlan S}

lemma keep_seed (H : Seed C f S) (g : Order) : Seed C (f.refine g) S := by
  refine ⟨H.cutoff, Order.upon H.ordered _, Order.point_retained _ _ _ H.generic _,
    H.kernel, Cells.recur H.copies g, fun d => ?_⟩
  obtain ⟨X, T, ht⟩ := H.corrected d
  exact ⟨X, T, Columns.Trials.refresh _ _ ht g⟩

-- Use on mod-finite comparisons too, for fusion of late estimates on
-- specific concrete columns, not replacing their budget guarantees.
theorem Refines.rank (h : Refines g f) {d : ℕ} (X : Columns C S d) {Z : X.Trials}
    (H : Columns.Trials.Valid f Z) : Columns.Trials.Valid g Z where
  ratios := H.ratios
  same_stage := H.same_stage
  scale_down := H.scale_down
  conjugate := H.conjugate
  unit := H.unit
  responds k i := h.limits (H.responds k i)
  bounded k := by
    obtain ⟨A,hA⟩ := H.bounded k
    refine ⟨A, fun p => ?_⟩
    change ∀ᶠ i in Filter.map (fun j => g.mesh j) atTop, ∀ n, ‖Z.lift k i p n‖ ≤ A
    exact Eventually.filter_mono h.mesh (hA p)
  span := H.span
  tuned := H.tuned
  seams := H.seams
  generic := H.generic
  cheap k ε hε := h.late (H.cheap k ε hε)

theorem Refines.plots {n k : ℕ} {v : Fin n → C.book.Token} {x : Fin n → Lattice.Cover} (h : Refines g f)
    {Z : OS.Grid.Covering (C:=C) k v x} (H : OS.Grid.Covering.Works k v x Z f) :
    OS.Grid.Covering.Works k v x Z g := by
  refine ⟨fun a b c => h.late (H.controls a b c), fun a b c e => (H.fillings a b c e).mono ?_⟩
  intro t ht
  exact h.late ht

lemma Refines.bins (H : Refines g f) {h : Dash.Live S} (R : Dash.Bin S) (hs : Dash.Spans h R f) :
    Dash.Spans h R g where
  p d := ⟨(hs.p d).slides.mono_left H.fuse, fun i x => ((hs.p d).roots i x).mono_left H.fuse⟩
  q := hs.q
  r a b p q := by
    obtain ⟨x, hx⟩ := hs.r a b p q
    exact ⟨x, ⟨fun i => (hx.meets i).mono_left H.fuse, fun i => (hx.costly i).mono_left H.fuse⟩⟩
  t a i x := by
    obtain ⟨y, hy⟩ := hs.t a i x
    exact ⟨y, ⟨fun j => (hy.meets j).mono_left H.fuse, fun j => (hy.costly j).mono_left H.fuse⟩⟩

lemma keep_arrives (h : Arrives C f S P) (g : Order) : Arrives C (f.refine g) S P := by
  obtain ⟨T, ht⟩ := h.pin
  exact ⟨copy_down _ _ h.census g, h.born, T, (refine_fits f g).bins T ht⟩

lemma keep_cleaner (h : Cleaner S₀ P S V f) (g : Order) : Cleaner S₀ P S V (f.refine g) :=
  ⟨h.sharp, copy_down _ _ h.mesh g, h.basic, h.smooth, h.ready, h.tilt⟩

/-- **Requires new producers**. Per-weight d `Valid` estimates, in full
including simultaneous over all of that detector family's rows and depths k;
here we need them in some further order each time. -/
def AtRank (C : Family G) (f : Order) (S : Table C.book) : Prop :=
  ∀ (d : ℕ) (p : Order), ∃ (g : Order) (X : Columns C S d) (Z : X.Trials),
    Columns.Trials.Valid ((f.refine p).refine g) Z

/-- Estimate port in Grill, exact for this extraction, weight, grid
station k, arity and generic placement. Not claiming other mixed-approximation
or rotation inputs from this. Only needs
`Grid.Covering.Works` (including plot bounds and the cross expectations,
with the stated eventuality in t and the `late`
filter, and on the actual cutoff measure of C). -/
def PlotBounds (C : Family G) (f : Order) (d k n : ℕ) (x : Fin n → Lattice.Cover) : Prop :=
  Order.grid C k x ∈ YM.generic n →
    ∀ v : Fin n → C.book.Token, (∀ i,(v i).fst ≤ d) → OS.Grid.plain (C:=C) v →
      ∃ P : OS.Grid.Covering (C:=C) k v x, OS.Grid.Covering.Works k v x P f

/-- k cofinal must work for all arities n. However we can ask for each n,
x separately in further Orders (arbitrary refinement supply). No
diagonalization through the continuum of all `v`: require all such v at
that n/x. -/
def AtGrid (C : Family G) (f : Order) (S : Table C.book) : Prop :=
  ∀ p : Order, Seed C (f.refine p) S → ∀ d m : ℕ, ∃ k : ℕ, m≤k ∧ ∃ q : Order,
    ∀ (n : ℕ) (x : Fin n → Lattice.Cover) (g : Order), ∃ r : Order,
      PlotBounds C ((((f.refine p).refine q).refine g).refine r) d k n x

lemma plotted {d k n : ℕ} {x : Fin n → Lattice.Cover} (H : PlotBounds C f d k n x) (h : Refines g f) : PlotBounds C g d k n x := by
  intro hg v hv e
  obtain ⟨X,hX⟩ := H hg v hv e
  exact ⟨X, h.plots hX⟩

lemma rank_count (X : AtRank C f S) : ∃ g : Order, RankWidths C (f.refine g) S := by
  refine concert f (fun d F => ∃ (X : Columns C S d) (Z : X.Trials), Columns.Trials.Valid F Z)
    (fun i j => X i j) ?_
  rintro i F Q h ⟨X, Z, e⟩
  exact ⟨X, Z, h.rank _ e⟩

lemma grid_count (X : AtGrid C f S) (p : Order) (s : Seed C (f.refine p) S) :
    ∃ g : Order, Grill C ((f.refine p).refine g) := by
  let base := f.refine p
  let J := (n : ℕ) × (Fin n → Lattice.Cover)
  letI : Nonempty J := ⟨⟨0, Fin.elim0⟩⟩
  letI : Countable J := by unfold J; infer_instance
  let A := fun d : ℕ×ℕ => fun t : Order => ∃ k ≥ d.2, ∀ x : J, PlotBounds C t d.1 k x.1 x.2
  have he (i : ℕ × ℕ) (g : Order) : ∃ q, A i ((base.refine g).refine q) := by
    obtain ⟨k, hk, q, hq⟩ := X (p.refine g) (keep_seed s g) i.1 i.2
    let F := (base.refine g).refine q
    obtain ⟨Q, hQ⟩ := concert F (fun x : J => fun u : Order => PlotBounds C u i.1 k x.1 x.2)
      (fun j u => hq j.1 j.2 u) (fun _ _ _ H h => plotted h H)
    exact ⟨q.refine Q, k, hk, hQ⟩
  have hh (i : ℕ × ℕ) (F G : Order) (h : Refines G F) (p : A i F) : A i G := by
    obtain ⟨k, hk, hX⟩ := p
    exact ⟨k, hk, fun t => plotted (hX t) h⟩
  obtain ⟨q, hq⟩ := concert base A he (fun _ _ _ h => hh _ _ _ h)
  refine ⟨q, fun d m => ?_⟩
  obtain ⟨k, hv, hw⟩ := hq (d,m)
  exact ⟨k, hv, fun n v ht hV x hx => hw (⟨n,x⟩ : J) hx v ht hV⟩

open RG.Supply
variable {M : Metals G} {D : Rolls M.p} {A : Alloy M D} {B : Bolt A}

/-- Once a (possibly already deliberately chosen) common f, history, S and
V have reached this point, choose the joint refinement. Actual birth of
objects from Mesh/Grill etc retained in theorem types: NOT assumption-free.

`W : MaxwellData C` and `I : IR S` and their physical equations/tests via
`Climb` required on these specific common spaces and derivatives, after
arriving at the seed & grill -- never assigned independently. (Their two
Climb conditions have no further f-dependence; producers needing further
refinement there may use `keep_*`, `Refines` and `plotted` too.)
-/
theorem synchronized (simple : G.Simple) (hB : Assembly B C) (h : Arrives C f S₀ P)
    (hc : Cleaner S₀ P S V f)
    (hr : AtRank C f S) (ht : AtGrid C f S)
    (climb : ∀ g : Order, ∀ s : Seed C (f.refine g) S, Grill C (f.refine g) →
      ∃ (W : MaxwellData C) (I : IR (C:=C) S), Climb.Pre s.kernel V I.J I.p I.Y ∧
        Climb.ActLaw V W.T I.J s.kernel.spin W.hT.spin) :
    ∃ g : Order, Arrives C (f.refine g) S₀ P ∧ Cleaner S₀ P S V (f.refine g) ∧
      ∃ (W : MaxwellData C) (I : IR (C:=C) S), UV C (f.refine g) S V W I := by
  have c := hB.port simple f
  obtain ⟨L, hL⟩ := Bid.healthy hB.stamp c Work.D05.answer Work.B10.answer Work.D06.answer hc
  obtain ⟨g, hg⟩ := rank_count hr
  have hw := (keep_cleaner hc g).mesh
  have s : Seed C (f.refine g) S :=
    ⟨hB.stamp, hw.integral, ⟨P, hw.mesh, hw.volume⟩, L, Cells.recur c.cells g, hg⟩
  obtain ⟨q, hq⟩ := grid_count ht g s
  have H : Seed C (f.refine (g.refine q)) S := keep_seed s q
  obtain ⟨W, I, hp, he⟩ := climb (g.refine q) H hq
  exact ⟨g.refine q, keep_arrives h _, keep_cleaner hc _, W, I, ⟨H, hL, hp, he, hq⟩⟩
end YM.Next.BOUNDARY
