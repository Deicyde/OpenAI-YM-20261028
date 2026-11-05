import YM.Next.RANK.EntryWord

/-!
# Colored sparse assembly

Every output forced or Regular here, including flag-after residues and
products among missing unmarked and mixed marked pieces. Light format with
palette for two merge types. Use Activ geometry as X exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory
open scoped BigOperators Classical

variable {V W ι : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
variable {G : Gauge} {n : Side} {ζ : V→ Site n} {t : ℝ}

/- Two constructors help make the eligibility rule uniform in marker vocab.
 Catch none when attaching an appended log member; require ANY previous token,
 even pre-flag. Attach blind can request only prior forced tokens. -/
structure Inner (G : Gauge) (ζ : V→ Site n) where
  extent : Support n
  active : extent.Nonempty
  fires : modes V
  remembers i : i∈fires.val → ζ i∈extent
  value : Config G n → ℂ
  meas : Measurable value
  loc : LocalOn extent value
  inv : GaugeInvariant value

lemma size_in (s : SourceAt G ζ) : s.extent.Nonempty:= by obtain ⟨i,hi⟩:=s.chosen; exact ⟨_,s.remembers _ hi⟩
def toInner (s : SourceAt G ζ) : Inner G ζ:= ⟨s.extent,size_in s,s.fires,s.remembers,s.value,s.meas,s.loc,s.inv⟩

-- no removes
inductive Plug (G : Gauge) (ζ : V→Site n) (t : ℝ)
| regular (K : SourceAt G ζ)
| raid (K : Lifted G ζ t)
namespace Plug
def extent : Plug G ζ t → Support n
| .regular s=> s.extent
| .raid s=> s.extent
def inventory : Plug G ζ t → Support n
| .regular _=> ∅
| .raid s=> s.inventory
def fires : Plug G ζ t → modes V
| .regular s=>s.fires
| .raid s=>s.fires
def val : Plug G ζ t → Config G n → ℂ
| .regular s=> masked t s.extent s.value
| .raid s=> s.value
def tolls (B : Plug G ζ t) (U : Config G n) : veil V:= Poly.send B.fires (B.val U)


lemma mem_extent (p : Plug G ζ t) : p.inventory ⊆ p.extent := by rcases p with s|s;exact empty_subset _;exact s.records

def landed (p : Plug G ζ t) := p.inventory.Nonempty
lemma innocent {v : Plug G ζ t} (h : ¬v.landed) : ∃ s,v=.regular s:= by rcases v with s|s; exact ⟨s,rfl⟩; exact False.elim (h s.needed)
lemma flushed {v : Plug G ζ t} (h : v.landed) : ∃ s,v=.raid s:= by rcases v with s|s;exact False.elim (not_nonempty_empty h); exact ⟨s,rfl⟩
end Plug

structure CoverReads (G : Gauge) (ζ : V → Site n) (t : ℝ) where
  extent : Support n
  active : extent.Nonempty
  fires : modes V
  remembers i : i∈fires.val → ζ i∈extent
  value : Config G n → ℂ
  meas : Measurable value
  only : UsesFinal t extent value
  inv : GaugeInvariant value
lemma inner_visits (t) (q : Inner G ζ) : UsesFinal t q.extent (masked t q.extent q.value):= by
  intro U V a b; by_cases h:Healthy t q.extent U
  · rw [masked_eq _ _ _ _ h,masked_eq];exact q.loc _ _ a; apply disjoint_iff_inter_eq_empty.mpr; rw [← b];exact disjoint_iff_inter_eq_empty.mp h
  rw [masked_ne _ _ _ _ h,masked_ne]; intro hh; apply h; exact disjoint_iff_inter_eq_empty.mpr (b.trans (disjoint_iff_inter_eq_empty.mp hh))
lemma inner_inv (t) (q : Inner G ζ) : GaugeInvariant (masked t q.extent q.value) := by
  intro k U; have he : Healthy t q.extent (gauge k U) ↔ Healthy t q.extent U:= by rw [Healthy,Healthy,gauge_flags]
  by_cases h : Healthy t q.extent U
  · rw [masked_eq _ _ _ _ (he.mpr h),masked_eq _ _ _ _ h]; exact q.inv ..
  rw [masked_ne _ _ _ _ (fun H=>h (he.mp H)),masked_ne _ _ _ _ h]
lemma innerMeas (t) (q : Inner G ζ):Measurable (masked t q.extent q.value):= masked_measurable _ _ _ q.meas

def Inner.glow (t) (q : Inner G ζ): CoverReads G ζ t:= ⟨q.extent,q.active,q.fires,q.remembers, _,innerMeas _ q,inner_visits _ q,inner_inv _ q⟩
def CoverReads.covets (b : CoverReads G ζ t) (U : Config G n):veil V:= Poly.send b.fires (b.value U)

def CoverReads.ofPlug (s : Plug G ζ t) : CoverReads G ζ t := match s with
| .regular s=> (toInner s).glow t
| .raid s=> ⟨s.extent,s.needed.mono s.records,s.fires,s.remembers,s.value,s.meas,s.only,s.inv⟩

abbrev Lining (G : Gauge) (ζ : V → Site n) (t : ℝ) := Inner G ζ ⊕ CoverReads G ζ t
def raised (s : Lining G ζ t) : CoverReads G ζ t:= Sum.elim (Inner.glow t) id s
def solute (s : Lining G ζ t) := Sum.elim (fun _=>False) (fun _=>True) s
variable (p : Plug G ζ t)
lemma p_coverVal (U) : (CoverReads.ofPlug p).covets U=p.tolls U:= by cases p <;>rfl
lemma p_coverFest : (CoverReads.ofPlug p).extent=p.extent:=by cases p<;>rfl
lemma p_coverFire : (CoverReads.ofPlug p).fires=p.fires:=by cases p<;>rfl

end YM.Next.Rank.Flux
