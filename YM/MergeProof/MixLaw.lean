import YM.MergeProof.Emit
import YM.MergeProof.Motion

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Photo
open Function Lattice RG Wilson Finset MeasureTheory Marker GridRenewal.Rain Filter PhysicalNext.Repeat Mallow Ovens Motion Switch
open scoped Topology BigOperators Classical InnerProductSpace
variable {ι V : Type}[Fintype ι][DecidableEq V] {B : Census V}
variable {G : Gauge} {n: Side}{P : BudgetPoint}
variable (r:ι→ Poly B)(hr:∀ i,r i*r i=0) (A: Activities G n) (K:ℝ → Finset ι → Code G n)

def fronts (f:ℕ→Poly B) (U:Config G n) (P : BudgetPoint)(p: Finset ℕ):Poly B:= if A.admissible P U p then ∏ i∈p,f i else 0
variable {w:ℝ}(hp:Pays A P K w P.supportExponent) (U:Config G n)

def tomes (p:Finset ℕ) (U:Config G n) (t:ℝ)(q:Finset ι):= (black A (K t q)).gasOccurrence P p U
lemma tomes_budget (hp:Pays A P K w P.supportExponent) : ∃ b:Finset ℕ→ℝ,Summable b∧∀ v,Paid (fun U t q=> tomes (P:=P) A K v U t q) (b v):=by
   obtain ⟨b,h,hB⟩:=hp.bought
   have he:=Push.AbsoluteSums.Product.everyone_ne _ _ (fun i=>(h i).rocket) (fun i _=> (A.forced i).inventory_ne.mono (A.forced i).inventory_sup) hB
   have hb: Summable b:= he.2.1.of_nonneg_of_le (fun i=>(h i).rocket) (fun i=> le_mul_of_one_le_right (h i|>.rocket) (Real.one_le_exp (mul_nonneg P.exponent_pos.le (by positivity))))
   refine ⟨_,summable_finsetProd_of_summable_nonneg (fun i=>(h i).rocket) hb,fun v=>?_⟩
   apply ((Paid.prod v _ _ (fun i (_:i∈ v)=>h i)).gate (X:={U| A.admissible P U v})).congr
   intro U t ht; ext p
   by_cases hx : A.admissible P U v
   · rw [Set.indicator_of_mem (show U∈_ from hx)]; simp only [Finset.prod_apply]; exact (if_pos hx).symm
   rw [Set.indicator_of_notMem]; exact (if_neg hx).symm; exact hx

include hp hr
lemma holds : HasSum (fronts A (fun i=>sound r (fun t u=>K t u i U)) U P) (sound r (fun t u=> (black A (K t u)).gas P U)):=by
   obtain ⟨b,h,hP⟩:=tomes_budget A K hp
   apply (soundSum r (fun i=>tomes (P:=P) A K i U) (F:=fun t u=> (black A (K t u)).gas P U) (a:=b) (fun i=> Paid.toPoint (tomes (P:=P) A K i) (hP i) U) h (fun _ _ _=> rfl)).congr_fun
   intro i; symm; unfold fronts; split
   next he=>
     let A' (j:ℕ):Ways ι:= fun t u=> K t u j U; have hu(t u): tomes (P:=P) A K i U t u= ∏ j∈i,A' j t u:= if_pos he
     rw [show tomes (P:=P) A K i U= ∏ j∈i,A' j from (by ext; rw [hu]; simp)]
     obtain ⟨c,h,-⟩:=hp.bought; exact Switch.product _ hr i A' c (fun j _=>Paid.toPoint _ (h j) U)
   next he=> rw [show tomes (P:=P) A K i U= (fun _ _=>0) from (by ext; exact if_neg he), const_sounds]; simp
end YM.Merge.Photo
