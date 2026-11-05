import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Casings
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Election

/-! Compulsory booklet on each sphere-joined seed packet. Finite, even
though normalized determinant also includes countable chains outside.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Shipment
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} [DecidableEq ι] {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
variable (Z : Art ι D) (h : Route.Badge.App D)
local notation "B"=>radiusB D.betaHat
local notation "t₀"=>D.betaHat

namespace Booklet
local instance fu : Fintype (Voice.Check.Test c f) := Fintype.ofFinite _

/-- No phantom gates at inactive positions. -/
def checks (p : Fleet.Packet c f) (F : Forest S.ratio) (A : Stores S) := Finset.univ.filter (fun i : Voice.Check.Test c f=> live t₀ F A ∅ (.inl i) ∧ levied S (address S i) (Parcel.fee i*B) p)

def history (p : Fleet.Packet c f) (F : Forest S.ratio) (A : Stores S) := (host S).filter (fun i=>present t₀ A F i ∧ levied S (ask D i) (askRate i*B) p)

def vitalPage (u : Fleet.Packet c f) : Formula G S ℝ := fun F A b k V p=>
  (∏ i∈checks D u F A, films D i F A b k V p) * Real.exp (∑ i ∈ history D u F A,sew D i F A b k V p)

variable {X W : Support c} {a a' : Finset (Bill S ι)}
  {F F' : Forest S.ratio} {A A' : Stores S} {V V' : Config G c} {k k' : S.Choices}
  (u : Fleet.Packet c f) (hi : coat D Z (pack u)⊆X) (hv : wind D Z (pack u)⊆ W)

include h
lemma same_ledger (hr : Physical.Reads X A A' F F' V V' k k') (hi : coat D Z (pack u)⊆X) :
    checks D u F A=checks D u F' A' ∧ history D u F A=history D u F' A' := by
  constructor <;> ext j
  · simp only [checks, Finset.mem_filter,Finset.mem_univ,true_and]
    refine and_congr_left (fun ht=>?_)
    apply screen_at D hr j ∅ ∅ ((packet_test D Z h.aperture.scale ht).1.trans hi) h.aperture.scale
  simp only [history,Finset.mem_filter]
  refine and_congr_right (fun hg=>and_congr_left (fun hh=>?_))
  exact present_at D hr j (Finset.Subset.trans (packet_log D Z h.aperture.scale hh).1 hi) h.aperture.scale

include hi hv
theorem comp {s s' : Finset ℕ} {p p' : Refs G f} (r : Survey D X W F F' A A' s s' k k' V V' p p') :
    vitalPage D u F A s k V p = vitalPage D u F' A' s' k' V' p' := by
  obtain ⟨ht,hk⟩:=same_ledger D Z h u r.fields hi
  unfold vitalPage; rw [ht,hk]
  refine congr_arg₂ HMul.hMul (Finset.prod_congr rfl fun j hj => ?_) (congr_arg Real.exp (Finset.sum_congr rfl fun j hj=>?_))
  · obtain ⟨h1,h2⟩ := packet_test D Z h.aperture.scale ((Finset.mem_filter.mp hj).2.2)
    exact (film D h j).outreach (h1.trans hi) (h2.trans hv) r
  obtain ⟨h1,h2⟩:=packet_log D Z h.aperture.scale ((Finset.mem_filter.mp hj).2.2)
  exact (local_series D h j).outreach (h1.trans hi) (h2.trans hv) r

omit hi hv in
lemma enrolled (F : Forest S.ratio) (A : Stores S) (s : Finset ℕ) (k : S.Choices) : Measurable (uncurry (vitalPage D u F A s k)) :=
  (Finset.measurable_fun_prod _ (fun j _ => (film D h j).noted _ _ _ _)).mul ((Finset.measurable_fun_sum _
    (fun i _=> (local_series D h i).noted _ _ _ _)).exp)

lemma sheets {O : Finset (Fleet.Packet c f)} {u v}
    (hi : Apart (Fleet.spans S (hump B)) O) (hu : u∈O) (hv : v∈O) (hr : u≠v)
    (F : Forest S.ratio) (A : Stores S) :
    Disjoint (checks D u F A) (checks D v F A) ∧ Disjoint (history D u F A) (history D v F A) := by
  have ht:=h.aperture.scale
  refine ⟨Finset.disjoint_left.mpr (fun i h1 h2=>hr (Parcel.no_repeat ht (fare i) ?_ hi hu hv ((Finset.mem_filter.mp h1).2.2) ((Finset.mem_filter.mp h2).2.2))),
    Finset.disjoint_left.mpr (fun i h1 h2=>hr (Parcel.no_repeat ht (answer i) ?_ hi hu hv ((Finset.mem_filter.mp h1).2.2) ((Finset.mem_filter.mp h2).2.2)))⟩
  · exact fun x hx y hy => le_trans (Parcel.test_range i x y (address_le i hx) (address_le i hy)) (by omega)
  exact fun x hx y hy=> (Parcel.asked_range D i x y hx hy).trans (by omega)

-- Strip qualifies every demanded Test/Log for use in the A step,
-- covering those physical names ALL and only once. No K factors in
-- packet book (eligibility intersects K owner).
omit h hi hv in
lemma bundled (F : Forest S.ratio) (A : Stores S) (k k₀ : S.Choices) (b : Finset ℕ) :
    let s:=chosen D F k₀ A k
    let P:=Fleet.packs S (hump B) (Fleet.manifest A)
    P.biUnion (fun p=>history D p F A)=(tapped D s).image (written D s) ∧
      (P.biUnion (fun p=> checks D p F A)).disjSum b=(Parcel.kept D s b).image (historical D s) := by
  intro s P
  have he i : i∈P.biUnion (fun p=>history D p F A) ↔ present t₀ A F i ∧ wants D A i := by
    simp only [Finset.mem_biUnion,history,Finset.mem_filter]
    rw [wants,packets_levied A _ (hump B)]
    constructor
    · rintro ⟨j,h₁,h₂,h₃,h₄⟩; exact ⟨h₃,j,h₁,h₄⟩
    rintro ⟨h₀,j,h₁,h₂⟩; exact ⟨j,h₁,reception D i (by obtain ⟨l,hl,-⟩:=Finset.not_disjoint_iff.mp h₂; exact ⟨l,hl⟩), h₀,h₂⟩
  constructor <;> ext i
  · rw [he,Finset.mem_image,← show i∈Set.range (written D s) ↔ present t₀ A F i from prescribed D s i]
    simp_rw [heated]
    constructor
    · rintro ⟨⟨j,rfl⟩,h₀⟩; exact ⟨j,h₀,rfl⟩
    rintro ⟨j,hj,rfl⟩; exact ⟨Set.mem_range_self _,hj⟩
  rw [Finset.mem_image]; rcases i with i|i
  · simp only [Finset.inl_mem_disjSum,Finset.mem_biUnion,checks,Finset.mem_filter, Finset.mem_univ,true_and]
    constructor
    · rintro ⟨p,hp,h₀,hl⟩
      have ht : live t₀ F A b (Sum.inl i) := by cases i <;> first | exact h₀ | trivial
      obtain ⟨j,hj⟩:=(show Sum.inl i∈Set.range (historical D s (b:=b)) from (controlled D s b (.inl i)).mpr ht)
      refine ⟨j,(Parcel.stays D j).mpr ?_,hj⟩
      rw [hj]; exact (packets_levied A _ _ _).mpr ⟨p,hp,hl⟩
    rintro ⟨j,hj,he⟩; rw [Parcel.stays,he] at hj
    obtain ⟨p,hp,hv⟩:=(packets_levied A (address S i) (hump B) (Parcel.fee i*B)).mp (show wanted S t₀ A i from hj)
    refine ⟨p,hp,?_,hv⟩
    have ht := (controlled D s b (.inl i)).mp ⟨j,he⟩
    cases i <;> first | exact ht | trivial
  rw [Finset.inr_mem_disjSum]; constructor
  · intro hh; use .inr (.inl ⟨i,hh⟩)
    exact ⟨(Parcel.stays D _).mpr trivial,rfl⟩
  rintro ⟨j,hj,he⟩
  exact (controlled D s b (.inr i)).mp ⟨j,he⟩
end Booklet
end YM.PhysicalNext.Dictionary.Shipment
