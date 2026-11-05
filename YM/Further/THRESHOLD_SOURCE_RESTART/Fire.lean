import YM.Extra.WILSON_STARTUP.Channels
import YM.Further.THRESHOLD_SOURCE_RESTART.Columns
import YM.Further.THRESHOLD_SOURCE_RESTART.Halos
import YM.Further.THRESHOLD_SOURCE_RESTART.Silt

/-!
# Compulsory k-threshold records

These `Key` are at EVERY ORIENTATION incl degenerate torus periods. Cost
with the factor of card Signed. Each keeps ONE clipped direct gain per
Key, and the kept-short-row compensations will be charged only on such
keys. Every nonempty connected record has to retain at least one.
`Menu`: all the optional primitive corrections to the exponent, already
applied including every contributing address history and a real footprint.
Local rules for exact compatible gas identity after carrying the key set
in addition to older K records. Builds `Narrows` before Marker use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart.Sluice
open Function Set Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Work.H03 WilsonStartup
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {H : Rep G n} (q : BudgetPoint)

def must (i : Key n) (U : Config G n) := q.threshold < G.chord (faceValue (i.frame U) i.root)
def listAll (U : Config G n) := Finset.univ.filter (must q · U)
@[simp] lemma enlisted (i : Key n) (U : Config G n) : i ∈ listAll q U ↔ must q i U := by simp [listAll]
lemma list_gauge (k : Site n → G.El) (U : Config G n) : listAll q (gauge k U)=listAll q U := by
  ext i; simp [must,Key.frame,pulls_gauge]
lemma list_transfer (i : Key n) (U : Config G n) (s : Signed) (x : Site n) :
    Key.perm s x i ∈ listAll q U ↔ i ∈ listAll q (pull s x U) := by
  simp only [enlisted, must,Key.oriented (U:=U),show (Key.perm s x i).root=i.root from rfl]
lemma enroll (i : Key n) : MeasurableSet {U : Config G n| i ∈ listAll q U} := by
  simp only [enlisted,must]
  unfold Key.frame faceValue; apply IsOpen.measurableSet; apply isOpen_lt continuous_const; fun_prop
lemma enroll_reads (i : Key n) {U V : Config G n} (h : Agrees i.skin U V) : i ∈ listAll q U ↔ i ∈ listAll q V := by
  have he (U : Config G n) := Face.send_price U i.root i.1 i.native G.chord G.chord_inv fun k g => G.chord_conj g k
  simp only [enlisted,must,Key.frame,he]
  change _ < G.chord (faceValue U i.positive) ↔ _ < G.chord (faceValue V i.positive)
  rw [show faceValue U i.positive=faceValue V i.positive from face_local i.positive U V (i.skin_positive ▸ h)]
lemma claim_all (U : Config G n) : (listAll q U).biUnion Key.skin=flags q.threshold U := by
  ext x; constructor
  · intro hi; obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hi
    have hh := (enlisted q i U).mp hi
    have he := Face.send_price U i.root i.1 i.native G.chord G.chord_inv fun k g => G.chord_conj g k
    exact (flags_spec ..).mpr ⟨i.positive,i.skin_positive ▸ hx,hh.trans_eq he⟩
  intro hi; obtain ⟨p,hp,he⟩ := (flags_spec ..).mp hi
  let i := Key.shifted 1 p
  have hU : pull (1:Signed) 0 U = U := pull_id U
  have ht : i.root.2=p.2 := rfl
  have hu (U : Config G n) : faceValue U i.root = faceValue U ((0:Site n),p.2) := rfl
  have hx : i ∈ listAll q U := (enlisted ..).mpr <| (by
    unfold must; dsimp only [i]; rw [Key.shift_frame,hU,hu,translate_face]; simpa)
  refine Finset.mem_biUnion.mpr ⟨i,hx,?_⟩
  change x ∈ (touched ((0:Site n),p.2)).image (affine 1 (affine 1 0 p.1))
  simp only [affine, Signed.act_one,add_zero]
  rcases p with ⟨a,b⟩
  simp_rw [WilsonStartup.four_visit] at *; simp [affine,← add_assoc,add_comm _ a] at hp ⊢; grind

-- Enough reads at flags on mandatory patches; compartment exhaust will
-- check even the equal-plaquette variants on a thin lattice.
def walls (i : Key n) := halo (8*q.B) {i.native}
lemma mentions {i j : Key n} (h : ¬ Disjoint i.skin j.skin) : j.skin ⊆ walls q i := by
  obtain ⟨z,h1,h2⟩ := Finset.not_disjoint_iff.mp h
  intro x he; have hP := j.nearby he; have hI := i.nearby h1; have hJ := j.nearby h2
  have hz := separation_triangle z j.native x; have hx := separation_triangle i.native z x
  rw [separation_comm z j.native] at hz
  have := q.B_pos; exact halo_spec.mpr ⟨_,Finset.mem_singleton_self _,by omega⟩
lemma watches (i : Key n) : inspected i.skin ⊆ walls q i := by
  intro x hx; obtain ⟨v,h,hv⟩ := Halos.at_old hx
  have hp := separation_triangle i.native v x; have := i.nearby h; have := q.B_pos
  exact halo_spec.mpr ⟨_,Finset.mem_singleton_self _,by omega⟩

-- Optional portion on all fields at actual masks. If nonzero also needs key.
structure Shade (G : Gauge) (n : Side) (q : BudgetPoint) (α : Type) where
  patch : α → Support n
  active i : (patch i).Nonempty
  leaf : α → Config G n → ℝ
  meas i : Measurable (leaf i)
  stays i : GaugeInvariant (leaf i)
  leg i : UsesFinal q.threshold (patch i) (leaf i)
  needy i U : leaf i U≠0 → ¬ Healthy q.threshold (patch i) U
  move (s : Signed) (x : Site n) : Equiv.Perm α
  carries (s x i) : patch (move s x i)=(patch i).image (affine s x)
  shifts s x i U : leaf (move s x i) U = leaf i (pull s x U)

-- H.p operations on same H.path. More constructors may reuse this port
-- but note `cut` is BEFORE new K's. No summing costs implicit.
structure Flare (G : Gauge) (n : Side) (q : BudgetPoint) where
  charge : Key n → Config G n → ℝ
  meas i : Measurable (charge i)
  stays i : GaugeInvariant (charge i)
  leg i : UsesFinal q.threshold (walls q i) (charge i)
  shifts s x i U : charge (Key.perm s x i) U=charge i (pull s x U)

-- Cut here refers just to the UNmarked exponent change
-- (gas representation will change also).
def wished (H : Rep G n) := { H with p := q }
structure Menu (H : Rep G n) (q : BudgetPoint) (α : Type) where
  shrinks : q.threshold ≤ H.p.threshold
  flare : Flare G n q
  more : Shade G n q α
  absolute U : Summable (fun i => more.leaf i U)
  cut U : H.exponent U-(wished q H).exponent U=(∑ i∈listAll q U,flare.charge i U)+(∑' i,more.leaf i U)

variable {q} {α : Type} (L : Menu H q α)

abbrev Codes (n : Side) (α : Type) := ℕ ⊕ Key n ⊕ α
namespace Menu
abbrev paint (_ : Menu H q α) (p : Finset (Codes n α)) := p.toRight.toLeft
abbrev solicit (_ : Menu H q α) (p : Finset (Codes n α)) := p.toRight.toRight
def zone : Codes n α → Support n := Sum.elim (fun i => inspected (oldSites H i)) (Sum.elim (walls q) L.more.patch)
def limit (p : Finset (Codes n α)) := p.biUnion L.zone
def inv (p : Finset (Codes n α)) := (L.paint p).biUnion Key.skin

def Fuel (p : Finset (Codes n α)) := Ac.Spark L.zone p ∧ (L.paint p).Nonempty ∧
    (p.toLeft : Set ℕ).PairwiseDisjoint (oldSites H)
abbrev Record := {p // L.Fuel p}
lemma has_inv (p : L.Record) : (L.inv p.val).Nonempty := by
  obtain ⟨i,hi⟩ := p.property.2.1; exact ⟨i.native,Finset.mem_biUnion.mpr ⟨_,hi,i.native_mem⟩⟩
lemma holds (p : Finset (Codes n α)) (i) (hh : i∈L.paint p) : walls q i ⊆ L.limit p :=
  Finset.subset_biUnion_of_mem L.zone (Finset.mem_toRight.mp (Finset.mem_toLeft.mp hh))
lemma has_supp (p : Finset (Codes n α)) : L.inv p ⊆ L.limit p := by
  intro x h; obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp h
  exact L.holds _ _ hi (watches q _ (Halos.enters hx))
lemma halo_charge (p : Finset (Codes n α)) (i) (hi : i∈p.toLeft) : inspected (oldSites H i) ⊆ L.limit p :=
  Finset.subset_biUnion_of_mem L.zone (Finset.mem_toLeft.mp hi)
lemma zone_ne (i : Codes n α) : (L.zone i).Nonempty := by
  cases i with
  | inl i => exact (H.activities.forced i).inventory_ne.mono (Finset.Subset.trans (H.activities.forced i).inventory_sup Halos.enters)
  | inr i => cases i with
    | inl i => exact ⟨_,watches q i (Halos.enters i.native_mem)⟩
    | inr i => exact L.more.active i
end Menu
end YM.Further.ThresholdSourceRestart.Sluice
