import YM.Slice.Strips

/-!
# Sampling all layers including seams

Prove the Haar-product disintegration indexed by the *same* Cut
site/link convention. This is an actual measure-preserving representation.
Once the strict probes and Wilson integrand are pulled there, use Fubini.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set Filter MeasureTheory
open MeasureTheory.Measure Lattice Wilson Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {n : Side} {G : Gauge} (C : Cut n)

abbrev Inner (C : Cut n) := {v : Per n // Plus C v}
abbrev Steps (C : Cut n) := {v : Per n // bridge C v}

-- noncomputable Fintype for Pi
instance : Fintype (Inner C) := by
  classical
  unfold Inner
  infer_instance
instance : Fintype (Steps C) := by
  classical
  unfold Steps
  infer_instance
instance : Fintype ↥(gate C) := Fintype.ofFinite _
instance : Fintype ↥(pier C) := Fintype.ofFinite _

abbrev Open (C : Cut n) (G : Gauge) := (Inner C → Leaf G C.pos n) × (Steps C → Thread G C.pos n)
abbrev PlusVol C G := Open (n := n) C G
abbrev Doors (C : Cut n) (G : Gauge) := (↥(gate C) → Thread G (Cut.pos C) n)
abbrev Posts (C : Cut n) (G : Gauge) := (↥(pier C) → Leaf G (Cut.pos C) n)
abbrev Rest (C : Cut n) (G : Gauge) := Posts C G × Doors C G
abbrev Dwelling (C : Cut n) (G : Gauge) := Rest C G × (Open C G × Open C G)

instance : BorelSpace (Open C G) := by unfold Open Leaf Thread; infer_instance
instance : BorelSpace (Rest C G) := by unfold Rest Posts Doors Leaf Thread; infer_instance
instance : SecondCountableTopology (Open C G) := by unfold Open Leaf Thread; infer_instance
instance : SecondCountableTopology (Rest C G) := by unfold Rest Posts Doors Leaf Thread; infer_instance

instance : SecondCountableTopology (Open C G × Open C G) := TopologicalSpace.instSecondCountableTopologyProd (α := Open C G) (β := Open C G)
instance : BorelSpace (Open C G × Open C G) := Prod.borelSpace (α := Open C G) (β := Open C G)
instance : SecondCountableTopology (Dwelling C G) := TopologicalSpace.instSecondCountableTopologyProd (α := Rest C G) (β := Open C G × Open C G)
instance : BorelSpace (Dwelling C G) := Prod.borelSpace (α := Rest C G) (β := Open C G × Open C G)

noncomputable section
open scoped Classical

def reaches (v : Per n) (p : Dwelling C G) : Leaf G C.pos n :=
  if h : Plus C v then p.2.1.1 ⟨v,h⟩
  else if w : Plus C (level C v) then p.2.2.1 ⟨level C v,w⟩
  else p.1.1 ⟨v,h,w⟩

def attach (v : Per n) (p : Dwelling C G) : Thread G C.pos n :=
  if h : bridge C v then p.2.1.2 ⟨v,h⟩
  else if w : bridge C (imageChord C v) then p.2.2.2 ⟨imageChord C v,w⟩
  else p.1.2 ⟨v,h,w⟩

def wire (p : Dwelling C G) (t : Per n) : Layer G C.pos n := (reaches C t p,attach C t p)

@[simp] theorem hit (v : Inner C) (p : Dwelling C G) : (wire C p v).1 = p.2.1.1 v := by simp [wire,reaches,v.property]
@[simp] theorem hitOpp (v : Inner C) (p : Dwelling C G) : (wire C p (level C v)).1 = p.2.2.1 v := by
  unfold wire reaches
  simp only [opposite_leaf v.property,↓reduceDIte]
  rw [dif_pos (by rw [level_twice]; exact v.property)]; simp

@[simp] theorem seam (v : ↥(pier C)) (p : Dwelling C G) : (wire C p v).1 = p.1.1 v := by
  simp only [wire, reaches,v.property.1,v.property.2,↓reduceDIte]
@[simp] theorem pointed (v : Steps C) (p : Dwelling C G) : (wire C p v).2 = p.2.1.2 v := by simp [wire,attach,v.property]
@[simp] theorem pointed_back (v : Steps C) (p : Dwelling C G) : (wire C p (imageChord C v)).2 = p.2.2.2 v := by
  unfold wire attach
  simp only [opposite_time v.property,↓reduceDIte]; rw [dif_pos (by rw [chord_turn]; exact v.property)]
  simp

@[simp] theorem checkpoint (v : ↥(gate C)) (p : Dwelling C G) : (wire C p v).2 = p.1.2 v := by
  simp only [wire,attach,v.property.1,v.property.2,↓reduceDIte]

@[fun_prop] lemma wire_cont : Continuous (wire (G := G) C) := by
  apply continuous_pi; intro i
  unfold wire reaches attach
  split_ifs <;> fun_prop

def iso : Dwelling C G ≃* Circle G C.pos n where
  toFun := wire C
  invFun p := ((fun i => (p i).1,fun i => (p i).2),(fun i => (p i).1,fun i => (p i).2),
    (fun i => (p (level C i)).1, fun i => (p (imageChord C i)).2))
  left_inv p := by
    apply Prod.ext
    · exact Prod.ext (funext fun i => seam ..) (funext fun i => checkpoint ..)
    apply Prod.ext
    · exact Prod.ext (funext fun i => hit ..) (funext fun i => pointed ..)
    exact Prod.ext (funext fun i => hitOpp ..) (funext fun i => pointed_back ..)
  right_inv s := by
    funext i
    apply Prod.ext <;> dsimp only [wire]
    · unfold reaches; split_ifs <;> simp
    unfold attach; split_ifs <;> simp
  map_mul' x y := by
    ext1 i
    change (reaches C i (x*y), attach C i (x*y)) = (reaches C i x * reaches C i y, attach C i x*attach C i y)
    unfold reaches attach; split_ifs <;> rfl -- abbreviations issue
end

variable (G)
def postM := Measure.pi fun _ : ↥(pier C) => trans n G C.pos
def doorM := Measure.pi fun _ : ↥(gate C) => threads n G C.pos
def restM := (postM G C).prod (doorM G C)
def fieldM := (Measure.pi fun _ : Inner C => trans n G C.pos).prod (Measure.pi fun _ : Steps C => threads n G C.pos)
def dwellM := (restM G C).prod ((fieldM G C).prod (fieldM G C))

instance : IsProbabilityMeasure (postM G C) := by unfold postM; infer_instance
instance : IsProbabilityMeasure (doorM G C) := by unfold doorM; infer_instance
instance : IsProbabilityMeasure (restM G C) := by unfold restM; infer_instance
instance : IsProbabilityMeasure (fieldM G C) := by unfold fieldM; infer_instance
instance : IsProbabilityMeasure (dwellM G C) := by unfold dwellM; infer_instance

instance : IsHaarMeasure (postM G C) := by unfold postM; constructor
instance : IsHaarMeasure (doorM G C) := by unfold doorM; constructor
instance : MeasurableMul (Posts C G) := by unfold Posts Leaf; infer_instance
instance : MeasurableMul (Doors C G) := by unfold Doors Thread; infer_instance
instance : IsHaarMeasure (restM G C) := Measure.prod.instIsHaarMeasure (G := Posts C G) (H := Doors C G) (postM G C) (doorM G C)
instance : IsHaarMeasure (fieldM G C) := by
  let α := Measure.pi fun _ : Inner C => trans n G C.pos
  let ζ := Measure.pi fun _ : Steps C => threads n G C.pos
  haveI : IsHaarMeasure α := by unfold α; constructor
  haveI : IsHaarMeasure ζ := by unfold ζ; constructor
  haveI : MeasurableMul (Inner C → Leaf G C.pos n) := by unfold Leaf; infer_instance
  haveI : MeasurableMul (Steps C → Thread G C.pos n) := by unfold Thread; infer_instance
  exact Measure.prod.instIsHaarMeasure (G := Inner C → Leaf G C.pos n) (H := Steps C → Thread G C.pos n) α ζ
instance : MeasurableMul (Open C G) := by unfold Open Leaf Thread; infer_instance
instance : MeasurableMul (Rest C G) := by unfold Rest Posts Doors Leaf Thread; infer_instance
instance : MeasurableMul (Open C G × Open C G) := ContinuousMul.measurableMul (γ := Open C G × Open C G)
instance : IsHaarMeasure (dwellM G C) := by
  let ζ := (fieldM G C).prod (fieldM G C)
  haveI : IsHaarMeasure ζ := Measure.prod.instIsHaarMeasure (G := Open C G) (H := Open C G) _ _
  exact Measure.prod.instIsHaarMeasure (G := Rest C G) (H := Open C G × Open C G) (restM G C) ζ

variable {G}

lemma wiredVolume : MeasurePreserving (wire C) (dwellM G C) (spread n G C.pos) :=
  MonoidHom.measurePreserving (f := (iso (G := G) C).toMonoidHom) (wire_cont C) (iso C).surjective (by simp)

def replace (x : Open C G) : Open C G := (x.1,x.2⁻¹)

lemma twisted : MeasurePreserving (replace C) (fieldM G C) (fieldM G C) := by
  unfold fieldM
  have hg : MeasurePreserving (fun v : Thread G C.pos n => v⁻¹) (threads n G C.pos) (threads n G C.pos) :=
    measurePreserving_pi _ _ (f := fun _ => Inv.inv) (fun _ => G.preserve_inv)
  have hi : MeasurePreserving (fun f : Steps C → Thread G C.pos n => f⁻¹) (Measure.pi fun _ => threads n G C.pos) _ :=
    measurePreserving_pi _ _ (f := fun _ => Inv.inv) (fun _ => hg)
  exact (MeasurePreserving.id _).prod hi

/-- The second half uses inverse thread convention. -/
def follow (p : Dwelling C G) := wire C (p.1,p.2.1,replace C p.2.2)
lemma follow_space : MeasurePreserving (follow C) (dwellM G C) (spread n G C.pos) :=
  (wiredVolume C).comp ((MeasurePreserving.id _).prod ((MeasurePreserving.id _).prod (twisted C)))

@[fun_prop] lemma continuous_follow : Continuous (follow (G := G) C) := by
  unfold follow replace; fun_prop

lemma board : MeasurePreserving (chain C.pos ∘ follow C) (dwellM G C) (prior G n) := (chain_volume _).comp (follow_space C)
end YM.Slice
