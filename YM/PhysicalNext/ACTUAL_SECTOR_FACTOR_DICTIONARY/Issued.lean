import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Packets

/-! Expose the exact intrinsic (one Store) gate split to the Spot
computations. -/
set_option autoImplicit false
set_option linter.unusedVariables false
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
local notation "B" => radiusB D.betaHat

/-- Finite catalogue for compulsory override. Nothing to do with the
radius of convergence. -/
def host (S : StepData c f) : Finset (ListID S) :=
    Finset.univ.image Legend.row ∪ Finset.univ.image Legend.glaze ∪ Finset.univ.image Legend.deficit ∪
    (Finset.univ : Finset (Bond f)).image (Legend.folio ∘ barcode (Dots f) ∘ Sum.inl) ∪ Finset.univ.image Legend.thin

lemma reception (i : ListID S) (h : (ask D i).Nonempty) : i∈host S := by
  rcases i with i|i|i|n|n|i|i|⟨i,j,n⟩|i|i
  · simp [host]
  · simp [host]
  · simp [host]
  · by_cases ht : n∈Set.range (barcode (Dots f))
    · obtain ⟨i|i,rfl⟩:=ht <;> simp only [ask,placed,Sum.elim_inl,Sum.elim_inr,Finset.not_nonempty_empty] at h
      simp [host]
    simp only [ask,decodePlace,Function.extend_apply' _ _ _ ht, Finset.not_nonempty_empty] at h
  case thin => simp [host]
  all_goals simp [ask] at h

def wanted (S : StepData c f) (x : ℝ) (A : Stores S) (i : Voice.Check.Test c f) : Prop := recorded S (address S i) (fee i*radiusB x) A
def wants (D : AnalyticBridge.LocalGaussian.Desk G S) (A : Stores S) (i : ListID S) : Prop := recorded S (ask D i) (askRate i*radiusB D.betaHat) A

def kept (u : Spot D) (b : Finset ℕ) := Finset.univ.filter fun i : u.Gates b => (historical D u i).elim (wanted S D.betaHat u.A) (fun _=>True)
def tapped (u : Spot D) : Finset u.Log := ((host S).filter (wants D u.A)).preimage (written D u) (once D u).injOn

variable {u : Spot D} {b : Finset ℕ}
lemma stays (i : u.Gates b) : i∈kept D u b ↔ (historical D u i).elim (wanted S D.betaHat u.A) (fun _=>True) := by simp [kept]
lemma heated (i : u.Log) : i∈tapped D u ↔ wants D u.A (written D u i) := by
  rw [tapped, Finset.mem_preimage,Finset.mem_filter]
  exact ⟨fun h => h.2,fun h=> ⟨reception D (written D u i) (by obtain ⟨x,h,-⟩:=Finset.not_disjoint_iff.mp h; exact ⟨_,h⟩), h⟩⟩

section coverage
local notation "A₀" => A
-- exact incidence from surviving intact gates and d.Valid kept predicates, not assumed once loosened.
lemma cost_here (i : Cell f) (h : i∈A.costs) : i.1 ∈ touched i ∧ wanted S D.betaHat A (.fine i) := by
  have ht:= Work.E01.base_touched i
  let q:=S.ratio.parent i.1
  have he := at_post (S:=S) (Test.fine i)
  exact ⟨ht,Finset.not_disjoint_iff.mpr ⟨q,he,halo_subset _ _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
    ⟨i,h,he⟩)))⟩⟩
lemma aisle_here (i : Bond c) (h : i∈A.aisles) : wanted S D.betaHat A (.noise i) := by
  have he := at_post (S:=S) (Test.noise i)
  exact Finset.not_disjoint_iff.mpr ⟨i.1,he, halo_subset _ _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨i,h,he⟩)))⟩


end coverage

/-- Valid even away from Masks, for reassembly in a component. Determines
which independent addresses correspond to physical letters. Also include K
ownership via selected b. -/
def present (x : ℝ) (A : Stores S) (F : Forest S.ratio) : ListID S → Prop
  | .glaze i | .surge i => Physical.openBond A F x i
  | .deficit i => Print.winter x A F i
  | .spark i j n=>Physical.openBond A F x i ∧ Physical.openBond A F x j
  | _=>True

def live (x : ℝ) (F : Forest S.ratio) (A : Stores S) (b : Finset ℕ) : Voice.Check.Test c f ⊕ ℕ → Prop
  | .inr j=> j∈b
  | .inl (.screen i)=> Physical.openBond A F x i
  | _=>True

lemma advertised {u : Spot D} (i : u.Log) : present D.betaHat u.A u.F (written D u i) := by
  rcases i with i|i|(i|i|i)|(i|i|⟨i,j,n⟩)|i|i <;>
    first | trivial | exact ⟨i,rfl⟩ | exact (Print.sees_frost D.betaHat ..).mpr i.property | exact ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩
lemma visited (i : u.Gates b) : live D.betaHat u.F u.A b (historical D u i) := by
  rcases i with (i|i|i|i|i)|i|i <;> first | trivial | exact i.property | exact ⟨i,rfl⟩

-- optional/protected stamps on the real non-tree coordinates
lemma prescribed (u : Spot D) (i : ListID S) :
    i ∈ Set.range (written D u) ↔ present D.betaHat u.A u.F i := by
  constructor
  · rintro ⟨j,rfl⟩; exact advertised D j
  rintro h; cases i with
  | row i=>exact ⟨.inl i,rfl⟩
  | glaze i=>obtain ⟨a,rfl⟩:=h; exact ⟨.inr (.inl a),rfl⟩
  | deficit i=>
    let e : u.F.Free:=⟨i,h.1⟩; let b : u.FrozenKey:=⟨e,h.2⟩
    exact ⟨.inr (.inr (.inl (.inl b))),rfl⟩
  | folio i=>exact ⟨.inr (.inr (.inl (.inr (.inl i)))),rfl⟩
  | starboard i=>exact ⟨.inr (.inr (.inl (.inr (.inr i)))),rfl⟩
  | thin i=>exact ⟨.inr (.inr (.inr (.inl (.inl i)))),rfl⟩
  | surge i=>obtain ⟨a,rfl⟩:=h; exact ⟨.inr (.inr (.inr (.inl (.inr (.inl a))))),rfl⟩
  | spark i j n=>obtain ⟨⟨a,ha⟩,b,hb⟩:=h; exact ⟨.inr (.inr (.inr (.inl (.inr (.inr (a,b,n)))))), by simp [written,ha,hb]⟩
  | opened i=>exact ⟨.inr (.inr (.inr (.inr (.inl i)))),rfl⟩
  | letter i=>exact ⟨.inr (.inr (.inr (.inr (.inr i)))),rfl⟩

lemma controlled (u : Spot D) (b : Finset ℕ) (i : Voice.Check.Test c f ⊕ ℕ) :
    i∈Set.range (historical D u (b:=b)) ↔ live D.betaHat u.F u.A b i := by
  constructor
  · rintro ⟨j,rfl⟩; exact visited D j
  intro h; rcases i with i|i
  · cases i with
    | fine i=>exact ⟨.inl (.inl i),rfl⟩
    | noise i=>exact ⟨.inl (.inr (.inl i)),rfl⟩
    | void i=>exact ⟨.inr (.inr i),rfl⟩
    | frame i=>exact ⟨.inl (.inr (.inr (.inl i))),rfl⟩
    | predictor i=>exact ⟨.inl (.inr (.inr (.inr (.inl i)))),rfl⟩
    | screen i=>obtain ⟨e,rfl⟩:=h; exact ⟨.inl (.inr (.inr (.inr (.inr e)))),rfl⟩
  exact ⟨.inr (.inl ⟨i,h⟩),rfl⟩
end YM.PhysicalNext.Dictionary.Parcel
