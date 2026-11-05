import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Shipments

/-! Every compulsory decision and tested dependency fits in the
packet. General halo convention at this price is deliberately
conservative. Include both endpoints even on local diag log prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary.Shipment
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix Bloch
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.LocalGaussian Spot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Wires Geo Notify Voice Voice.Check Parcel SectorNext.Reconnect SectorNext.Reconnect.Words
variable {G : Gauge} {ι : Type} {c f : Side} {S : StepData c f} (D : AnalyticBridge.LocalGaussian.Desk G S)
variable (Z : Art ι D)
local notation "B"=>radiusB D.betaHat

lemma marginTest {p : Fleet.Packet c f} {i : Voice.Check.Test c f} (hs : 120 ≤ B) (u : Site c) (ht : u∈post S i)
    (hv : levied S (address S i) (fee i*B) p) :
    ∃ j∈p,∃ o∈Fleet.whereAt S j, separation o u ≤ fee i*B+B := by
  obtain ⟨x,hx,hv⟩:=Finset.not_disjoint_iff.mp hv
  obtain ⟨j,hj,hq⟩:=Finset.mem_biUnion.mp hv
  obtain ⟨o,ho,hr⟩:=halo_spec.mp hq
  exact ⟨j,hj,o,ho,(separation_triangle o x u).trans (by have := test_range i x u (address_le i hx) ht; omega)⟩

lemma marginLog {p : Fleet.Packet c f} {i : ListID S} (hs : 120 ≤ B) (u : Site c) (ht : u∈Voice.native D i)
    (hv : levied S (Parcel.ask D i) (askRate i*B) p) :
    ∃ j∈p,∃ o∈Fleet.whereAt S j, separation o u ≤ askRate i*B+21*B := by
  obtain ⟨x,hx,hv⟩ := Finset.not_disjoint_iff.mp hv
  obtain ⟨j,hj,hq⟩:= Finset.mem_biUnion.mp hv; obtain ⟨o,ho,hr⟩ := halo_spec.mp hq
  refine ⟨j,hj,o,ho,(separation_triangle o x u).trans (Nat.add_le_add hr ?_)⟩
  have hh {e : Bond f} (h : x∈borders S e) : separation x (portOf S e)≤1 := (separation_comm ..).trans_le
    (meetings e ((crossing ..).mp h))
  cases i with
  | folio n=>
    by_cases he : n∈Set.range (barcode (Dots f))
    · obtain ⟨i|i,rfl⟩:=he <;> simp only [Voice.native,ask,placed,Sum.elim_inl,Sum.elim_inr] at ht hx
      · have hz:=hh hx
        have he : separation (portOf S i) u≤20*B := (AnalyticBridge.RelativeLogdet.lens_spec ..).mp ht
        apply (separation_triangle x (portOf S i) u).trans; omega
      exact False.elim (Finset.notMem_empty _ hx)
    simp only [ask,decodePlace,Function.extend_apply' _ _ _ he] at hx; exact False.elim (Finset.notMem_empty _ hx)
  | glaze i=> rw [show u=portOf S i from Finset.mem_singleton.mp ht]; exact (hh hx).trans (by omega)
  | deficit i=> rw [show u=portOf S i from Finset.mem_singleton.mp ht]; exact (hh hx).trans (by omega)
  | _=> first | rw [show x=u from (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp ht).symm]; simp | simp [ask] at hx

private lemma harvest {p : Fleet.Packet c f} {X : Support c} {r a q : ℕ} (ht : a+q≤r)
    (h : ∀ u∈X,∃ j∈p,∃ o∈Fleet.whereAt S j,separation o u≤a*B) :
    halo (q*B) X⊆region (Fleet.spans S (r*B)) p := by
  intro i hi; obtain ⟨y,hy,hl⟩:=halo_spec.mp hi
  obtain ⟨j,hj,o,ho,hx⟩:=h y hy
  exact Finset.mem_biUnion.mpr ⟨j,hj,halo_spec.mpr ⟨o,ho,(separation_triangle o y i).trans
    ((Nat.add_le_add hx hl).trans (by rw [← Nat.add_mul]; gcongr))⟩⟩

lemma harvest_test {p : Fleet.Packet c f} {i : Voice.Check.Test c f} {r a : ℕ} (hs : 120≤B)
    (hv : levied S (address S i) (fee i*B) p) (h : fee i+1+a ≤ r) :
    halo (a*B) (post S i) ⊆ region (Fleet.spans S (r*B)) p :=
  harvest D h (fun u hu=> by simpa only [Nat.add_mul,Nat.one_mul] using marginTest D hs u hu hv)

lemma harvest_log {p : Fleet.Packet c f} {i : ListID S} {r a : ℕ} (hs : 120≤B)
    (hv : levied S (ask D i) (askRate i*B) p) (h : askRate i+21+a ≤ r) :
    halo (a*B) (Voice.native D i) ⊆ region (Fleet.spans S (r*B)) p :=
  harvest D h (fun u hu=> by simpa only [Nat.add_mul] using marginLog D hs u hu hv)

lemma packet_test {p : Fleet.Packet c f} {i : Voice.Check.Test c f} (hs : 120≤B)
    (hv : levied S (address S i) (fee i*B) p) :
    ambient D (post S i) ⊆ coat D Z (pack p) ∧ floor D (post S i)⊆wind D Z (pack p) :=
  ⟨Finset.Subset.trans (harvest_test (r:=700) D hs hv (show fee i+1+40≤700 by have := fare i; omega)) (certain _),
    harvest_test D hs hv (show fee i+1+15≤500 by have := fare i; omega)⟩

lemma packet_log {p : Fleet.Packet c f} {i : ListID S} (hs : 120≤B)
    (hv : levied S (ask D i) (askRate i*B) p) :
    ambient D (Voice.native D i)⊆coat D Z (pack p) ∧ floor D (Voice.native D i)⊆wind D Z (pack p) :=
  ⟨Finset.Subset.trans (harvest_log (r:=700) D hs hv (show askRate i+21+40≤700 by have := answer i; omega)) (certain _),
    harvest_log D hs hv (show askRate i+21+15≤500 by have := answer i; omega)⟩

-- Compulsory held-coordinate/predicate feasibility checks. Even the
-- whole "floor" supply of a compulsory rough U vertex gets held. β,
-- seed expenditure and trigger receipts still requested at consumption.
lemma packet_space {p : Fleet.Packet c f} {i : Voice.Check.Test c f} (hs : 120≤B)
    (hh : bare i=true) (hv : levied S (address S i) (fee i*B) p) :
    zone D (post S i) ⊆ handling D Z (pack p) := by
  have hp : fee i≤300 := by cases i <;> simp [Parcel.fee,Parcel.bare] at *
  intro j hj; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  exact harvest_test D hs hv (show fee i+1+15≤400 by omega) ((Finset.mem_filter.mp hj).2.1)

lemma packet_row_space {p : Fleet.Packet c f} (i : RowPosts c f) (hs : 120≤B) (hv : levied S (ask D (.row i)) (200*B) p) :
    zone D {i.1.act (hinge S i.2)} ⊆ handling D Z (pack p) := by
  intro j hj; refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  exact harvest_log D hs hv (show 200+21+15≤400 by omega) ((Finset.mem_filter.mp hj).2.1)

lemma screen_issued {p : Fleet.Packet c f} (i : Bond f) (hp : i∈ handling D Z (pack p)) :
    levied S (address S (.screen i)) (400*B) p := Finset.not_disjoint_iff.mpr ⟨_,address_post (Test.screen i), (Finset.mem_filter.mp hp).2⟩

section seeds
lemma gate_size (P : Fleet.Packet c f) : (Fleet.scan (S:=S) P).place ⊆ region (Fleet.spans S (hump B)) P := by
  intro u hu; obtain ⟨a,ha,hj⟩:= (manifest_spot u (Fleet.scan P)).mp hu
  rw [Fleet.record] at ha; exact Finset.mem_biUnion.mpr ⟨_,ha,halo_subset _ _ hj⟩

lemma stocked {r : ℕ} (P : Fleet.Packet c f) : (Fleet.scan (S:=S) P).dome r=region (Fleet.spans S r) P := by
  ext i; unfold Pressure.Stores.dome; rw [halo_spec,Finset.mem_biUnion]
  simp only [Fleet.spans,halo_spec,manifest_spot,Fleet.record]; grind
end seeds
end YM.PhysicalNext.Dictionary.Shipment
