import YM.Further.THRESHOLD_SOURCE_RESTART.Fire
/-!
# What is actually retained in a new K history

Construct `printer`: the new K dictionary and k-scale vacuum
representation, from Menu. Records/components on the expanded alphabet
Key, old K and optional letters, with conditions including OLD support
disjointness and coverage of old flags. The step includes the new eligibility
check; unmarked K multiplies our step weight by Old K values, so no new
factor of exp(N * scalar) here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Sluice.Menu
open Function Set Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Work.H03 WilsonStartup
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {α : Type} {n : Side} {H : Rep G n} {q : BudgetPoint} (L : Menu H q α)

-- Extra for an actual field. Enforce complete old coverage on *these*
-- vertices; across components comes from coverage of new inventory.
def Ready (i : L.Record) (U : Config G n) := L.paint i.val ⊆ listAll q U ∧
    (∀ j∈ listAll q U, ¬Disjoint j.skin (L.inv i.val) → j∈L.paint i.val) ∧
    (∀ j∈ i.val.toLeft,permits H j U) ∧
      L.inv i.val ∩ flags H.p.threshold U ⊆ i.val.toLeft.biUnion (claims H)

-- keep identical predicate also in address when payload zero
def sole (i : L.Record) : ForcedAddress G n := ⟨L.limit i.val,L.inv i.val,L.has_inv _,L.has_supp _,L.Ready i⟩
variable {δ c : ℝ}
lemma read_here (h : H.activities.Valid H.p δ c) (i : L.Record) : UsesFinal q.threshold (L.limit i.val) (L.Ready i) := by
  intro U V he _
  have hv j (hj : j∈L.paint i.val) : j ∈ listAll q U ↔ j∈listAll q V :=
    enroll_reads q j (agrees_mono he (fun x hx => L.holds i.val _ hj (watches _ _ (Halos.enters hx))))
  have hE j (hj : ¬ Disjoint (Key.skin j) (L.inv i.val)) : j ∈ listAll q U ↔ j∈listAll q V := by
    obtain ⟨x,hm,hn⟩ := Finset.not_disjoint_iff.mp hj
    obtain ⟨b,hb,H⟩ := Finset.mem_biUnion.mp hn
    have hx : ¬ Disjoint b.skin (Key.skin j) := Finset.not_disjoint_iff.mpr ⟨x,H,hm⟩
    exact enroll_reads q j (agrees_mono he (fun y hy => L.holds _ _ hb (mentions _ hx hy)))
  have hJ (j) (hj : j∈i.val.toLeft) : permits H j U = permits H j V := by
    refine eligible_reads _ _ (h.forced.reads_test j) U V ?_ (flags_agree _ _ _ _ (agrees_mono he (L.halo_charge _ _ hj)))
    exact agrees_mono he (fun x hx => L.halo_charge _ _ hj (Halos.enters hx))
  have ht : L.inv i.val∩flags H.p.threshold U=L.inv i.val∩flags H.p.threshold V := by
    ext x
    simp only [Finset.mem_inter, and_congr_right_iff]
    intro hx; obtain ⟨b,hb,hn⟩ := Finset.mem_biUnion.mp hx
    have hv := flags_agree H.p.threshold U V b.skin (agrees_mono he (fun x hx => L.holds _ _ hb (watches q _ hx)))
    constructor
    · intro he; exact (Finset.mem_inter.mp (show x∈b.skin∩_ from hv ▸ Finset.mem_inter.mpr ⟨hn,he⟩)).2
    intro he; exact (Finset.mem_inter.mp (show x∈b.skin∩_ from hv.symm ▸ Finset.mem_inter.mpr ⟨hn,he⟩)).2
  unfold Ready; rw [ht]
  apply propext; constructor <;> rintro ⟨H',p,t,hu⟩
  · exact ⟨fun j hj => (hv j hj).mp (H' hj),fun j hj hh => p j ((hE j hh).mpr hj) hh, fun j hj => hJ j hj ▸ t j hj,hu⟩
  exact ⟨fun j hj => (hv j hj).mpr (H' hj),fun j hj hh => p j ((hE j hh).mp hj) hh,fun j hj => (hJ j hj).symm ▸ t j hj,hu⟩

lemma gauges (h : H.activities.Valid H.p δ c) (i : L.Record) (k U) : L.Ready i (gauge k U) ↔ L.Ready i U := by
  simp only [Ready,list_gauge,gauge_flags,permits,eligible_gauge _ _ _ _ (h.forced.symtest _ _ _)]
lemma instruments (h : H.activities.Valid H.p δ c) (i : L.Record) : MeasurableSet {U| L.Ready i U} := by
  let J := L.inv i.val
  have he : MeasurableSet {U : Config G n| J∩flags H.p.threshold U ⊆ i.val.toLeft.biUnion (claims H)} := by
    suffices H' : {U : Config G n | _} = ⋃ p : {z : Support n // J∩z ⊆ i.val.toLeft.biUnion (claims H)},
        {U| flags H.p.threshold U=p.val} from H' ▸ MeasurableSet.iUnion (fun p => flags_measurable_eq ..)
    ext U; simp only [Set.mem_iUnion,Set.mem_setOf_eq]; constructor
    · exact fun h => ⟨⟨_,h⟩,rfl⟩
    rintro ⟨p,h⟩; rw [h]; exact p.property
  apply MeasurableSet.inter _ (MeasurableSet.inter _ (MeasurableSet.inter _ he))
  · suffices ht : MeasurableSet {U : Config G n| ∀ j∈ L.paint i.val, j∈listAll q U} from ht
    rw [Set.setOf_forall]; exact MeasurableSet.iInter fun j => by
      by_cases h : j∈ L.paint i.val
      · simp only [h,true_imp_iff]; exact enroll ..
      simp [h]
  · change MeasurableSet {U : Config G n | ∀ j ∈ listAll q U, ¬Disjoint j.skin (L.inv i.val) → j∈L.paint i.val}
    rw [Set.setOf_forall]; refine MeasurableSet.iInter fun j => ?_
    by_cases h : ¬Disjoint j.skin (L.inv i.val) → j∈L.paint i.val
    · convert! (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Config G n))) using 1; ext; tauto
    convert! MeasurableSet.compl (enroll q j (G:=G)) using 1; ext; tauto
  change MeasurableSet {U | ∀ j ∈ i.val.toLeft, permits H j U}
  rw [Set.setOf_forall]; refine MeasurableSet.iInter fun j => ?_
  by_cases he : j ∈ i.val.toLeft
  · simp only [he, true_imp_iff]; exact eligible_measurable _ _ (h.forced.meas_test j)
  simp [he]

def glow : Codes n α → Config G n → ℝ :=
    Sum.elim (fun _ _=>1) (Sum.elim (fun i U => Real.exp (L.flare.charge i U))
      fun i U => Real.exp (L.more.leaf i U)-1)

def solid (i : L.Record) (U : Config G n) := if (L.sole i).eligible q.threshold U then ∏ j∈i.val,L.glow j U else 0

lemma real_solid (h : H.activities.Valid H.p δ c) (i : L.Record) : Measurable (L.solid i) ∧ GaugeInvariant (L.solid i) ∧
    UsesFinal q.threshold (L.limit i.val) (L.solid i) := by
  have he j : Measurable (L.glow j) ∧ GaugeInvariant (L.glow j) ∧ UsesFinal q.threshold (L.zone j) (L.glow j) := by
    rcases j with j|j|j
    · exact ⟨measurable_const,fun _ _ => rfl,fun _ _ _ _ => rfl⟩
    · exact ⟨(L.flare.meas _).exp, fun k U => congr_arg Real.exp (L.flare.stays j k U),fun U V h e => congr_arg Real.exp (L.flare.leg j U V h e)⟩
    exact ⟨((L.more.meas _).exp).sub measurable_const,fun k U => congr_arg (fun x => Real.exp x - 1) (L.more.stays j k U),
      fun U V h e => congr_arg (fun x => Real.exp x - 1) (L.more.leg j U V h e)⟩
  refine ⟨Measurable.ite (eligible_measurable _ _ (L.instruments h i)) (Finset.measurable_prod _ fun j _ => (he j).1) measurable_const,fun k U => ?_,fun U V ht hh => ?_⟩
  · unfold solid; rw [eligible_gauge q.threshold _ _ _ (L.gauges h i k U)]; split
    · exact Finset.prod_congr rfl fun j _ => (he j).2.1 _ _
    rfl
  unfold solid; rw [eligible_reads _ _ (L.read_here h i) U V ht hh]; split
  · exact Finset.prod_congr rfl fun j hj => reads_larger (Finset.subset_biUnion_of_mem L.zone hj) (he j).2.2 _ _ ht hh
  rfl

private abbrev blanks (n : Side) := ℕ × Site n
abbrev Book := L.Record ⊕ (blanks n)

def party : L.Book → Finset ℕ := Sum.elim (fun i => i.val.toLeft) (fun _ => ∅)
def busy : L.Book → Config G n → ℝ := Sum.elim L.solid (fun _ _=>0)
def tailK (j : L.Book) (U : Config G n) := L.busy j U * ∏ i ∈ L.party j,H.activities.K i U

def stamp : L.Book → ForcedAddress G n := Sum.elim L.sole
    (fun s => ⟨{s.2},{s.2},Finset.singleton_nonempty _,le_rfl,fun _ => False⟩)

variable [Countable α]

def label : ℕ ≃ L.Book := by
  letI : Infinite L.Book := Infinite.of_injective (fun i : ℕ => (Sum.inr (i,(0:Site n)) : L.Book)) (fun _ _ h => congr_arg Prod.fst (Sum.inr.inj h))
  exact (@Denumerable.eqv _ (Classical.choice (nonempty_denumerable L.Book))).symm

def printer : Rep G n := { H with p:=q,activities := { H.activities with forced:=L.stamp ∘ L.label, K:=L.tailK ∘ L.label }}
lemma kept_entry (i : L.Record) : (L.printer.activities.forced (L.label.symm (Sum.inl i)))=L.sole i := by
  unfold printer; simp [L.label.apply_symm_apply,stamp]
lemma new_power (i : Config G n) : L.printer.exponent i=(wished q H).exponent i := rfl
end YM.Further.ThresholdSourceRestart.Sluice.Menu
