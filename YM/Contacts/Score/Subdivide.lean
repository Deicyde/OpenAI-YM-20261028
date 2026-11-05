import YM.Contacts.Score.Scripts
/-!
# Binomial regrouping with finite subpartitions in the different frames

Permute only the subpartitions on disjoint groups. Works on score products where the optical terms
carry their prescribed order inside. Sum over **all** refinements, not any particular maximal tree.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule Ordered
open scoped Topology BigOperators Classical ContDiff TensorProduct InnerProductSpace
variable {k : ℕ} {E F : Type*} {g : Group k}[Ring F]
def options (P : Pieces g)(C : choices P) (i : Group k) : Pieces i := if h:i∈P.parts then C ⟨i,h⟩ else ⊤
@[simp] lemma selected (P : Pieces g) (C : choices P) (i : P.parts) : options P C i.val=C i:= dif_pos i.property
lemma contents (P : Pieces g)(C : choices P): (stitch P C).parts=P.parts.biUnion (fun a=> (options P C a).parts):= by
  ext x; rw [stitches,Finset.mem_biUnion]; exact ⟨fun ⟨a,ha⟩=> ⟨_,a.property,by rw [selected]; exact ha⟩, fun ⟨a, ha, h⟩=> ⟨⟨a,ha⟩,(dif_pos ha : options P C a=_ ) ▸ h⟩⟩

def permitted (p : Group k→ F) := ∀ a b : Group k, Disjoint a b → Commute (p a) (p b) -- empty commutes too or tweak
lemma permitted.stands {p : Group k→ F} (h : permitted p) (P : Pieces g) : (P.parts:Set (Group k)).Pairwise fun i j=>Commute (p i) (p j) := fun _ hi _ hj he=> h _ _ (P.disjoint hi hj he)
def parcel (p : Group k → F) (P : Pieces g) := Ordered.product P.parts p
lemma sewn (P : Pieces g)(C : choices P)(p : Group k→ F)(h : permitted p) : parcel p (stitch P C)=assembly F P.parts (fun i:P.parts=> parcel p (C i)):= by
  have hp := h.stands (stitch P C); have hh : (P.parts:Set (Group k)).Pairwise fun i j=> Disjoint (options P C i).parts (options P C j).parts := by
    intro i hi j hj he; refine Finset.disjoint_left.mpr (fun a ha hb=>?_)
    have hA:= (options P C i).subset ha; have hB:=(options P C j).subset hb
    obtain ⟨x,hx⟩:= (options P C i).nonempty_of_mem_parts ha; exact Finset.disjoint_left.mp (P.disjoint hi hj he) (hA hx) (hB hx)
  rw [contents] at hp; rw [parcel,contents, Ordered.gather_product _ _ hh hp]; unfold Ordered.product
  apply congr_arg (assembly ..); funext i; change parcel p _ = _; rw [selected P C i]

/-- Sum over proper sub-strata of one block using its punctured partition expansions. -/
def totalForm (p : Group k → F) (g : Group k) := ∑ P:Pieces g, parcel p P
def receding (p : Group k → F)(g : Group k) := ∑ P∈(Finset.univ.erase (⊤:Pieces g)), parcel p P
lemma partition_cases {p : Group k→ F} (h : g.Nonempty) : totalForm p g = receding p g + p g := by unfold totalForm; rw [← Finset.sum_erase_add (a:=⊤) _ _ (Finset.mem_univ _)]; change receding _ _ + parcel p (⊤:Pieces g)=_; rw [parcel,one_set _ rfl h,product_one]
lemma over_refinements (p : Group k → F) (Q : Pieces g) (h : permitted p) :
    ∑ P : ↑(Set.Iic Q), parcel p P.val = parcel (totalForm p) Q := by
  let e : choices Q≃ ↑(Set.Iic Q):= Equiv.ofBijective _ (stitch_bijection Q)
  rw [← Equiv.sum_comp e (fun P=>parcel p P.val)]; unfold parcel Ordered.product totalForm; -- use map_sum with subtype. change names
  rw [(assembly F Q.parts).map_sum (α:=fun i=>Pieces i.val) (g:=fun i y=> parcel p y)]
  exact Finset.sum_congr rfl fun x _=> sewn Q x p h
lemma full_expands (p : Group k → F) (Q : Pieces g) (h : permitted p) :
   ∑ P∈ (Finset.univ.filter fun v=>v≤ Q),parcel p P=parcel (totalForm p) Q:= by
     rw [← over_refinements p Q h]; exact (Finset.sum_subtype _ (fun _=>by simp) (parcel p)) -- check name
end YM.Contacts.Normal
