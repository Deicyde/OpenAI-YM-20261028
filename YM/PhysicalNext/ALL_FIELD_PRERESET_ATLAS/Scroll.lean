import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Emitter
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.KReceipts
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Gluing
import YM.SectorNext.RECONNECTED_LOCALITY.Leads


/-!
# Pane -> its anchored bulk list and still-flagged gas

In E some constants are already moved early (r=-1), others
when actually resetting. Choose to extract **all of this log's identity
values** here (allow other same-family local indicator rearrangements in the
subsequent pass). Test and compensate on ALL V. Use the exact numbered cluster
calculus, including repeated addresses. No positivity of the covered first gas or
the leftover d gas used. In particular one doesn't keep a scalar from one V
formula and re-use it with a different chain/book at another V.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas.Scroll
open RG Lattice Wilson Filter Function
open Push.AbsoluteSums Push.LogIdentity Ursell
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {ι κ : Type} [Countable ι] [Countable κ]
    (p : BudgetPoint) (M : Pane G n ι κ) (F : Palette G n ι κ)

def outer : Depot G n := ⟨κ,M.forces⟩
def errata : Slip n := ⟨Clusters ι,Restore.Z M.X,Restore.Znonempty M.X M.full⟩

/-- The log's **numbered**/factorial coefficient taken to the scalar.
U is identically the identity for this call. -/
def star : Clusters ι → ℝ := Restore.raw M.X fun i => F.u i 1

def upcoming : Plate n := ⟨Emit.Anchors M.X,Emit.host M.X⟩
def up : (upcoming M).Ink G := Emit.ability M.X (fun V i => F.u i V) (star M F)

/-- Missing occurrences and scalar constant masking. Do NOT find one flag
at which to attach and charge there; need uses on entire supports. This is
not `Slip.Lands`: the missing cluster can speak on an entirely healthy cluster
support, to be subtracted at incidence to d. `Restore` retains real incidence
in the exponential expansion. -/
def recant : (errata M).Ink G := fun i V => Restore.takeBack M.X (flags p.threshold V)
    (fun i => F.u i V) (star M F) i

def lowland := (outer M).combined (errata M) p

def still : (lowland p M).Ink := (outer M).filled (errata M) p F.d (recant p M F)

/-- Upper envelopes at this stage -- don't need any K Hit renewal/cap on the merged
alphabet for the all-field identity part at fixed period. -/
def fuel (b : BidLog ι κ) (i : (upcoming M).letter) :=
    Emit.share M.X (fun j => 2*Price.logPrice M.X b.soft j) i

def chassis (b : BidLog ι κ) : (lowland p M).letter → ℝ :=
    Price.tag M.X M.Y b.soft b.hard

variable {p M F} {b : BidLog ι κ} (h : b.Negative p M F)
include h

omit [Countable κ] [Countable ι] in
lemma priceStar (i) : ‖star M F i‖ ≤ Price.logPrice M.X b.soft i :=
    Price.log_bound M.X i fun _ => h.soft _ _ (SectorNext.Reconnect.Snip.all_white ..)


omit [Countable κ] in
lemma log_cap (i) (V : Config G n)
    (hv : Healthy p.threshold ((upcoming M).range i) V) : ‖up M F i V‖ ≤ fuel M b i := by
  unfold up fuel Emit.ability Restore.regular Emit.share
  rw [norm_div,norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he : ‖Restore.raw M.X (fun i => F.u i V) i.fst‖ ≤ Price.logPrice M.X b.soft i.fst :=
    Price.log_bound M.X i.1 (fun j => h.soft _ V
      (Finset.disjoint_of_subset_left (Restore.Zcontains M.X i.fst j) hv))
  exact (norm_add_le ..).trans (by rw [norm_neg]; linarith [priceStar h i.1])

omit [Countable κ] [Countable ι] in
lemma along (V : Config G n) (Y : Support n) :
    let u := Restore.good M.X (flags p.threshold V) fun i => F.u i V
    let u' := Gas.cut M.X Y u
    let g := Gas.total (blocked M.X) u'
    let z := Gas.logSum (blocked M.X) u'
    Summable (fun i => ‖Gas.value (blocked M.X) u' i‖) ∧
      Summable (fun i => ‖Gas.term (blocked M.X) u' i‖) ∧ 0 < g ∧ Real.log g = z := by
  intro u u' g z
  have ht i : ‖u' i‖ ≤ b.soft i := by
    unfold u' Gas.cut; split
    · exact Restore.good_norm M.X _ _ i h.offers.ready.2.2.2.2.1 (h.soft i V)
    rw [norm_zero]; exact h.offers.ready.2.2.2.2.1 _
  have he := Gas.price_log (blocked M.X) u'
    ⟨fun i => Or.inl rfl,fun i j => blocked_back M.X⟩ M.X p.B (literal_test M.X M.full) h.offers.grade
    (Price.permit _ _ h.offers.ready (fun i => ⟨norm_nonneg _,ht i⟩))
  exact ⟨he.1.2.1,he.2.1.2.1,he.2.2.2⟩

omit [Countable κ] [Countable ι] in
theorem unforced (V : Config G n) :
    let u := Restore.good M.X (flags p.threshold V) fun i => F.u i V
    let g := Gas.total (blocked M.X) u
    let z := Gas.logSum (blocked M.X) u
    Summable (fun i => ‖Gas.value (blocked M.X) u i‖) ∧
      Summable (fun i => ‖Gas.term (blocked M.X) u i‖) ∧ 0 < g ∧ Real.log g = z := by
  have hc (f : ι → ℝ) : Gas.cut M.X ∅ f = f := funext fun _ => if_pos (Finset.disjoint_empty_left _)
  simpa only [hc] using! along h V ∅

/-- All three lines absolute: moving actual signed constants never stands for
using log at an unverified total. -/
theorem lifted (V : Config G n) :
    let log := (upcoming M).maskedLog p (up M F) V
    let out := (lowland p M).sell p (still p M F) V
    let m := star M F
    Summable (fun i => ‖m i‖) ∧ Summable (fun i => ‖log i‖) ∧ Summable (fun i => ‖out i‖) ∧
      (∑' i,M.initial p F V i) = Real.exp ((∑' i,m i) - ∑' i,log i) * ∑' i,out i := by
  let q := Price.output M.X p.B M.Y M.I h.offers.hard h.offers.grade h.offers.ready
          h.offers.hit M.full M.realZone M.inside (flags p.threshold V)
            (fun i=>F.u i V) (fun i=>F.d i V) (star M F) (fun i=>h.soft i V)
              (fun i=>h.hard i V) (priceStar h)
  obtain ⟨-,hm,-,hl,hp,he⟩ := q
  intro log out m
  let g : Clusters ι → ℝ := Emit.maskedIn M.X p (fun V i => F.u i V) m V
  have ht : log = Emit.share M.X g := by
    funext i; unfold log Plate.maskedLog
    by_cases hi : Healthy p.threshold ((upcoming M).range i) V
    · rw [masked_eq _ _ _ _ hi, Emit.share]
      change _=Restore.good (Restore.Z M.X) _ _ i.fst/_
      unfold Restore.good; rw [if_pos (show Disjoint (Restore.Z M.X i.fst) (flags p.threshold V) from hi)]; rfl
    rw [masked_ne _ _ _ _ hi,Emit.share]; change _=Restore.good (Restore.Z M.X) _ _ i.fst/_
    unfold Restore.good; rw [if_neg (show ¬Disjoint (Restore.Z M.X i.fst) (flags p.threshold V) from hi),zero_div]
  obtain ⟨hz,hz'⟩:= Emit.pays_every M.X M.full g hl
  rw [ht, (show (∑' i : (upcoming M).letter,Emit.share M.X g i) = ∑' z,g z from hz')]; exact ⟨hm,hz,hp,he⟩

omit h in
lemma summation (hs : b.Offers p M) :
    Summable (fuel M b) ∧ Summable (chassis p M b) ∧ Summable (Price.logPrice M.X b.soft) := by
  have hb i : 0 ≤ b.soft i := hs.ready.2.2.2.2.1 _
  have hi := Price.logWeighed M.X p.B M.full hs.grade hs.ready
  have hf : Summable (Price.logPrice M.X b.soft) :=
    (Price.priced_total _ _ (Price.logPrice_ne _ hb) hs.grade hi (Restore.Znonempty _ M.full)).2.1
  exact ⟨(Emit.pays_every M.X M.full _ (hf.mul_left 2).norm).1.of_norm,
    Depot.affordable (outer M) (errata M) p (b.absolute hs).2 hf,hf⟩

section structurals
omit h
variable (hx : OriginalLight p M F)
include hx
open MeasureTheory SectorNext.Reconnect

-- Require extension on every relevant support, including threshold equality.
omit [Countable κ] in
lemma recant_names : (errata M).Vouched p (recant p M F) := by
  have hF i : LocalOn (M.X i) (F.u i) := (hx.unmasked i).sites
  let u (V : Config G n) i := F.u i V
  let X := errata M
  refine ⟨fun i => ?_,fun i k V => ?_,fun i => ?_⟩
  · intro U V he hq
    have hi : Healthy p.threshold (Restore.Z M.X i) U ↔ Healthy p.threshold (Restore.Z M.X i) V := by
      change Healthy _ ((errata M).reach i) _ ↔ Healthy _ ((errata M).reach i) _
      simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,hq]
    have ht : Restore.raw M.X (u U) i = Restore.raw M.X (u V) i := Emit.raw_local M.X u hF i U V he
    unfold recant Restore.takeBack
    simp only [show Disjoint (Restore.Z M.X i) (flags p.threshold U) = Disjoint _ (flags p.threshold V) from propext hi]
    congr!
  · have hg : Restore.raw M.X (u (Lattice.gauge k V)) i = Restore.raw M.X (u V) i :=
      Emit.raw_sym M.X u (fun i => (hx.unmasked i).symmetry) i k V
    unfold recant Restore.takeBack; rw [gauge_flags]
    split
    next _ => exact congr_arg Neg.neg hg
    rfl
  let w : SheetFunction G n := recant p M F i
  change Measurable w
  exact Measurable.ite (healthy_closed p.threshold _).measurableSet
    (Emit.raw_meas M.X u (fun i => (hx.unmasked i).borel) i).neg measurable_const

lemma verified : (lowland p M).Tenants p (still p M F) :=
  Depot.sheltered (outer M) (errata M) p
    ⟨hx.hardGauge, hx.testGauge,hx.hardReads,hx.testReads,hx.hardMeas,hx.testMeas,hx.proper⟩ (recant_names hx)

omit [Countable κ] [Countable ι] hx in
private lemma prod_regular {p : BudgetPoint} {s : Support n} {f g : SheetFunction G n}
    (h : p.Regular s f) (hg : p.Regular s g) : p.Regular s (fun V => f V * g V) := by
  let F := fun V => f V * g V
  have he V (hv : Healthy p.threshold s V) :
      ContDiffAt ℝ (p.order : WithTop ℕ∞) (F ∘ increment V) 0 := (h.smooth V hv).mul (hg.smooth V hv)
  refine ⟨fun U V he => congr_arg₂ (·*·) (h.sites U V he) (hg.sites U V he), h.borel.mul hg.borel,
    fun k V => congr_arg₂ (·*·) (h.symmetry k V) (hg.symmetry k V), he,?_⟩
  exact fun V hV k _ hl => Next.Foundations.left_has _ hl (he V hV)

omit [Countable κ] in
lemma wellLit (i) : p.Regular ((upcoming M).range i) (up M F i) := by
  let c := i.1
  let X : Support n := (upcoming M).range i
  have hl (s : Finset (Option (Fin c.1))) : p.Regular X (fun V => ∏ j∈s, F.u (c.2 j) V) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Snip.still 1
    | insert j s he ih =>
      simp_rw [Finset.prod_insert he]
      exact prod_regular (Snip.swell (hx.unmasked _) (Restore.Zcontains _ _ j)) ih
  let v := star M F c
  let a := (coefficient (blocked M.X) c.snd) / (c.fst+1).factorial
  let y (V : Config G n) : ℝ := (∏ j, F.u (c.2 j) V)
  have he : p.Regular X (fun V => v - a*y V) := Snip.subtract (Snip.still v) (Snip.scaled _ (hl _))
  let d := (((M.X (c.2 none)).card:ℝ))
  rw [show up M F i = (fun V => d⁻¹ * (v - a*y V)) from ?_]; exact Snip.scaled _ he
  funext i
  unfold up Emit.ability Emit.share Restore.regular Restore.raw Gas.term d v y a c; ring
end structurals
end YM.PhysicalNext.PreAtlas.Scroll
