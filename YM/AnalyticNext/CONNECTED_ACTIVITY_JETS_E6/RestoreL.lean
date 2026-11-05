import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.ColumnL
import YM.Push.ABSOLUTE_SUMS.Copies

/-!
# Second enumeration with many copies
Signs at previous F. Exact factor once per repeated position.
Coverage on resurrected D's. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open  Ursell Trees Multiple 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C δ e : ℝ} {R : Rep G f} {Z Z' : Support c} {L : Side} {V : Config G c}
variable {k k' : Finset ℕ} {w v : Air f G}
variable {j b l d : ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

namespace Letter
variable {ι κ : Type}

-- Composition fixed s/t
def hint (p : Finset ι × Reps κ) : Reps (ι⊕κ) := ⟨p.1.disjSum p.2.1, fun i=> match e:i.val with
    | .inl _ => 0
    | .inr j => p.2.2 ⟨j,inr_mem_disjSum.mp (e ▸ i.2)⟩⟩
def hidden (p : Reps (ι⊕κ)) : Finset ι × Reps κ :=
    (p.1.toLeft,⟨p.1.toRight,fun j=> p.2 ⟨.inr j.val,mem_toRight.mp j.2⟩⟩)

def staysOne (p : Reps (ι⊕κ)) : Prop := ∀ a, ∀ h : Sum.inl a∈p.1, p.2 ⟨Sum.inl a,h⟩=0

lemma hinter (p : Finset ι × Reps κ) : staysOne (hint p) := fun _ _=> rfl
-- rfl relies classical!
lemma tracks (p : Finset ι × Reps κ) : hidden (hint p)=p := by
  rcases p with ⟨i,s,z⟩
  let p:= hint (i,⟨s,z⟩)
  have hk : (hidden p).2.1=s := toRight_disjSum ..
  refine Prod.ext (toLeft_disjSum ..) ?_
  refine Sigma.ext hk ?_
  generalize hf : (hidden p).2 = a
  have hp : ∀ v, ∀ h : v∈s,a.snd ⟨v, by rw [← hf,hk]; assumption⟩=z ⟨v,h⟩ := by
    intro v hv; subst a; rfl
  obtain ⟨y,g⟩ := a
  replace hk : y=s := (congr_arg Sigma.fst hf.symm).trans hk
  subst y; exact heq_of_eq (funext fun ⟨v,hv⟩ => hp v hv)
lemma unruly (p : Reps (ι⊕κ)) (h : staysOne p) : hint (hidden p)=p := by
  have he : (hint (hidden p)).fst=p.fst := by change Finset.disjSum _ _=_; ext i; cases i <;> simp [hidden]
  refine Sigma.ext he ?_
  have hg (x) (hx : x∈p.1) : (hint (hidden p)).snd ⟨x,he.symm ▸ hx⟩=p.2 ⟨x,hx⟩ := by
    rcases x with x|x
    · exact (h x _).symm
    rfl
  generalize hv : (hint (hidden p))=a at *
  obtain ⟨p,f⟩ := p; obtain ⟨q,g⟩ := a; change q=p at he; subst q
  exact heq_of_eq (funext fun i=> hg i.val i.2)

lemma hint_price (p : Finset ι × Reps κ) (x : ι→ℝ) (y : κ→ℝ) : manyW (Sum.elim x y) (hint p)=(∏ i∈p.1, x i)*manyW y p.2 := by
  let g : ((↥p.1) ⊕ (↥p.2.1)) → ↥(hint p).1 := Sum.elim (fun i => ⟨Sum.inl i.val,inl_mem_disjSum.mpr i.2⟩) (fun i => ⟨Sum.inr i.val,inr_mem_disjSum.mpr i.2⟩)
  have hi : Injective g := by
    rintro (i|i) (j|j) h <;> have he := congr_arg Subtype.val h <;> simp only [g,Sum.elim,Sum.inl.injEq,Sum.inr.injEq] at he
    · exact congr_arg _ (Subtype.ext he)
    · cases he
    · cases he
    exact congr_arg _ (Subtype.ext he)
  have ht : Surjective g := by
    rintro ⟨(i|i),h⟩
    · exact ⟨.inl ⟨i,inl_mem_disjSum.mp h⟩,rfl⟩
    exact ⟨.inr ⟨i,inr_mem_disjSum.mp h⟩,rfl⟩
  let E := Equiv.ofBijective g ⟨hi,ht⟩
  rw [manyW, ← E.prod_comp, Fintype.prod_sum_type]
  congr 1
  · rw [← Finset.prod_coe_sort p.1 x]; refine prod_congr rfl fun i _=> ?_
    change x i.val ^ (0+1) / ((0+1).factorial:ℕ)=_
    simp
end Letter
end YM.ConnectedActivityE6
