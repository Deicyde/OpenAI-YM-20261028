import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Gates
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Legends
import YM.SectorNext.RECONNECTED_LOCALITY.Fleet

/-!
Use the same 200 for residuals and
300 for default fine/noise/q tests, enlarge broad and frozen list and
whole support (chart protection of all hard stencils, doesn't ask annular energy
on all those rows). We also keep the actual likelihoods instead of proving
that they may be written identically one above H₁: they stay compulsory
through 300B and expand beyond (with protections before expansion). No claims of their quantitative bill here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Parcel
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Check SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
    {F : Forest S.ratio} {A : Stores S} {k : S.Choices}

def hump (B : ℕ) := 700 * B



def borders (S : StepData c f) (e : Bond f) := post S (Test.screen e)

lemma crossing (e : Bond f) (i : Site c) : i ∈ borders S e ↔ i∈Next.SectorChange.points S e := by
  simp [borders,post,pinPos,Next.SectorChange.points]; try tauto

-- `charge` scale separates address qualification from all possible
-- query footprints (origin-set assigned e.g. even when a q default is
-- numerically suppressed).
def address (S : StepData c f) : Voice.Check.Test c f → Support c
  | .void i=>{S.ratio.parent i}
  | i => post S i

def fee : Voice.Check.Test c f → ℕ
  | .screen _=>400
  | _=>300

lemma address_post (i : Voice.Check.Test c f) : location S i ∈ address S i := by
  cases i <;> first | exact Finset.mem_singleton_self _ | exact at_post (S:=S) _

lemma address_le (i : Voice.Check.Test c f) : address S i ⊆ post S i := by
  cases i <;> first | exact Finset.Subset.refl _ | exact Finset.singleton_subset_iff.mpr (at_post (S:=S) (Test.void _))

lemma test_range (i : Voice.Check.Test c f) (x y : Site c) (hx : x ∈ post S i) (hy : y ∈ post S i) : separation x y ≤ 18 := by
  have he : ∀ x∈post S i, separation (location S i) x ≤ 9 := by
    intro j hj
    cases i with
    | void i=>
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hj
      obtain ⟨w,hh,hl⟩:= halo_spec.mp (Geo.inspected_radius {i} hz)
      rw [Finset.mem_singleton.mp hh] at hl
      have ht := Work.E04.parent_separation S.ratio i z
      change separation (S.ratio.parent _) _ ≤ _; omega
    | fine i=>exact (Physical.start_diam i (at_post (S:=S) (Test.fine i)) hj).trans (by omega)
    | noise i=>exact (Physical.pin_diam i (at_post (S:=S) (Test.noise i)) hj).trans (by omega)
    | predictor i=>exact (Physical.pin_diam i (at_post (S:=S) (Test.predictor i)) hj).trans (by omega)
    | frame i=>rw [show j=i from Finset.mem_singleton.mp hj]; simp [location]
    | screen i=>exact (meetings _ ((crossing ..).mp hj)).trans (by omega)
  exact (separation_triangle _ (location S i) _).trans (Nat.add_le_add ((separation_comm ..).trans_le (he _ hx)) (he _ hy))

/-- finite override for potential paired base-log compulsory rows.
Unused indices have ∅ location. -/
def ask (D : AnalyticBridge.LocalGaussian.Desk G S) : ListID S → Support c
  | .row i => {i.1.act (hinge S i.2)}
  | .glaze i | .deficit i => borders S i
  | .folio n => decodePlace (fun z : Dots f=>z.elim (borders S) (fun _=>∅)) n
  | .thin i => {spot S i}
  | _=>∅

def askRate : ListID S → ℕ
  | .row _ | .folio _ | .thin _=>200
  | _=>400

-- twinned location query still close with oriented endpoints.
lemma asked_range (i : ListID S) (x y : Site c) (hx : x∈ask D i) (hy : y∈ask D i) : separation x y ≤ 2 := by
  have ht (i : Bond f) (h : x∈borders S i) (hh : y∈borders S i) := (separation_triangle x (portOf S i) y).trans
    (Nat.add_le_add ((separation_comm ..).trans_le (meetings _ ((crossing ..).mp h))) (meetings _ ((crossing ..).mp hh)))
  cases i with
  | folio n=>
    by_cases hr : n ∈ Set.range (barcode (Dots f))
    · obtain ⟨e|e,rfl⟩:=hr <;> simp only [ask,placed] at hx hy <;> first | exact ht _ hx hy | exact False.elim (Finset.notMem_empty _ hx)
    simp only [ask,decodePlace] at hx
    rw [Function.extend_apply' _ _ _ hr] at hx; exact False.elim (Finset.notMem_empty _ hx)
  | _ => first | exact ht _ hx hy | exfalso; exact Finset.notMem_empty x hx |
              rw [show x=y from (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm]; simp

-- computed on full typed A and F (F later for active membership). This
-- is *one* demand no matter how many seeds meeting this location.
def recorded (S : StepData c f) (P : Support c) (r : ℕ) (A : Stores S) : Prop := ¬Disjoint P (A.dome r)

lemma records (S : StepData c f) (P : Support c) (r : ℕ) (A : Stores S) : recorded S P r A ↔ ∃ x∈P,∃ y∈A.place,separation y x ≤ r := by
  simp [recorded,Stores.dome,Finset.not_disjoint_iff,halo_spec]

def levied (S : StepData c f) (P : Support c) (r : ℕ) (u : Fleet.Packet c f) : Prop := ¬Disjoint P (region (Fleet.spans S r) u)

lemma manifest_spot (x : Site c) (A : Stores S) : x∈A.place ↔ ∃ a∈Fleet.manifest A,x∈Fleet.whereAt S a := by
  simp only [Stores.place, Finset.mem_union,Finset.mem_biUnion]
  constructor
  · rintro ((h|h)|h)
    · obtain ⟨i,hi,hj⟩:=h; exact ⟨.inl i,(by simpa [Fleet.manifest]),hj⟩
    · obtain ⟨i,hi,hj⟩:=h; exact ⟨.inr (.inl i),(by simpa [Fleet.manifest]),hj⟩
    exact ⟨.inr (.inr x),(by simpa [Fleet.manifest]),Finset.mem_singleton_self _⟩
  rintro ⟨i|i|i,hi,hz⟩ <;> simp only [Fleet.manifest,Finset.inl_mem_disjSum,Finset.inr_mem_disjSum] at hi
  · exact Or.inl (Or.inl ⟨_,hi,hz⟩)
  · exact Or.inl (Or.inr ⟨_,hi,hz⟩)
  exact Or.inr ((Finset.mem_singleton.mp hz).symm ▸ hi)

lemma scanned (P : Support c) (r : ℕ) (u : Fleet.Packet c f) : levied S P r u ↔ recorded S P r (Fleet.scan u) := by
  unfold levied; rw [Finset.not_disjoint_iff,records]
  have he (i : Site c) : i∈region (Fleet.spans S r) u ↔ ∃ y∈(Fleet.scan (S:=S) u).place,separation y i ≤ r := by
    simp only [region,Fleet.spans,Finset.mem_biUnion,halo_spec,manifest_spot,Fleet.record]
    grind
  simp_rw [he]

lemma packets_levied (A : Stores S) (P : Support c) (g r : ℕ) : recorded S P r A ↔ ∃ p∈Fleet.packs S g (Fleet.manifest A),levied S P r p := by
  let v:=Fleet.packs S g (Fleet.manifest A)
  rw [← Fleet.scanned A,← scanned, Fleet.scanned]
  have he := after_union (Fleet.spans S r) v
  change region _ ((Fleet.packs ..).biUnion id)=_ at he
  rw [Fleet.seeds] at he
  simp only [levied,he,Finset.not_disjoint_iff,Finset.mem_biUnion]; grind

lemma answer (i : ListID S) : askRate i ≤ 400 := by cases i <;> simp [askRate]
lemma fare (i : Voice.Check.Test c f) : fee i ≤ 400 := by cases i <;> simp [fee]

/-- Space into the compulsory packet's own join halo. B-agreement
need not be retested when merging compulsory terms. We choose 700B
join charge (pay in cover exponents accordingly). -/
lemma preside {P : Support c} {r b : ℕ} {u : Fleet.Packet c f} (hr : r ≤ 400)
    (hb : 120≤b) (hz : ∀ x∈P,∀ y∈P, separation x y ≤ 200*b) (ht : levied S P (r*b) u) :
    halo (100*b) P ⊆ region (Fleet.spans S (hump b)) u := by
  obtain ⟨j,hj,hq⟩:=Finset.not_disjoint_iff.mp ht
  obtain ⟨a,ha,hv⟩:=Finset.mem_biUnion.mp hq
  obtain ⟨s,hs,hj'⟩:=halo_spec.mp hv
  intro i hi
  obtain ⟨l,hl,hi⟩:=halo_spec.mp hi
  refine Finset.mem_biUnion.mpr ⟨a,ha,halo_spec.mpr ⟨s,hs, (separation_triangle s j i).trans ?_⟩⟩
  have ht := (separation_triangle j l i).trans ((Nat.add_le_add (hz j hj l hl) hi).trans (by change _≤200*b+100*b; omega))
  unfold hump; have hy := Nat.mul_le_mul_right b hr; omega

lemma no_repeat {b r : ℕ} (hb : 120 ≤ b) (hr : r≤400) {P : Support c} (hz : ∀ x∈P,∀ y∈P,separation x y≤200*b)
    {O : Finset (Fleet.Packet c f)} (hO : Apart (Fleet.spans S (hump b)) O)
    {u v} (hu : u∈O) (hv : v∈O) (hi : levied S P (r*b) u) (hj : levied S P (r*b) v) : u=v := by
  obtain ⟨x,hx,-⟩:= Finset.not_disjoint_iff.mp hi
  have he (u : Fleet.Packet c f) (h : levied S P (r*b) u) := preside hr hb hz h (halo_subset _ _ hx)
  by_contra hd
  exact Finset.disjoint_left.mp (hO hu hv hd) (he _ hi) (he _ hj)
end YM.PhysicalNext.Dictionary.Parcel
