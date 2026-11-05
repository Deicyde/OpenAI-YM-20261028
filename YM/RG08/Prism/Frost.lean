import YM.RG08.Prism.Egg
import YM.RG08.Isles.Fruit

/-!
# Supply the finite block recipe in common-cell alphabets from actual Flat lines. Γ and μ
 ready for repeated uses; projections do not change price.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Prism
open Filter Function Matrix Lattice Exterior Stationary RG Laurent Fold Glyph Room Camera Steam MvPolynomial Finset Bloch Mount Drum Forms
open Rows Pert.Bulk Packets Isles
open Precision RG Wilson Tack Tree
open scoped Classical Matrix ContDiff Topology BigOperators InnerProductSpace PowerSeries ENNReal
variable {I J U R:Type}{σ p:ℝ}
def winter (g:Kernel I J):Kernel (I⊕ U) (J⊕ R):=fun i j=> Sum.elim (fun a=> Sum.elim (fun b=>g (i.1,a) (j.1,b)) (fun _=>0) j.2) (fun _=>0) i.2
def chill (g:Kernel I J):Kernel (I⊕U) J:=fun i j=> Sum.elim (fun a=>g (i.1,a) j) (fun _=>0) i.2
def rightSumKernel (g:Kernel I J):Kernel (U⊕I) J:=fun i j=> Sum.elim (fun _=>0) (fun a=>g (i.1,a) j) i.2

def winterSeat {P:Side}(M:Matrix (Co P I) (Co P J) ℝ):Matrix (Co P (I⊕ U)) (Co P (J⊕ R)) ℝ:=fun i j=>i.2.elim (fun a=> j.2.elim (fun b=>M (i.1,a) (j.1,b)) (fun _=>0)) (fun _=>0)
def chillSeat {P:Side}(M:Matrix (Co P I) (Co P J) ℝ):Matrix (Co P (I⊕ U)) (Co P J) ℝ:=fun i j=>i.2.elim (fun a=>M (i.1,a) j) (fun _=>0)
def shineSeat {P:Side}(M:Matrix (Co P I) (Co P J) ℝ):Matrix (Co P (U⊕I)) (Co P J) ℝ:=fun i j=>i.2.elim (fun _=>0) (fun a=>M (i.1,a) j)

lemma priced_winter {g:Kernel I J}(h:Rows.Priced σ p g): Priced σ p (winter (U:=U) (R:=R) g):=by
 refine ⟨h.pos,?_,?_,?_⟩
 · rintro ⟨a,i|b⟩ ⟨q,e|t⟩ z;exact h.city (a,i) (q,e) z;all_goals rfl
 · rintro ⟨a,i|v⟩ (j|t);exact h.row (a,i) j;all_goals simp [winter,bill]
 rintro (a|b) ⟨t,q|v⟩;exact h.col a (t,q);all_goals simp [winter,bill]
lemma winter_tag {g:Kernel I J}{K:∀ P:Side, Matrix (Co P I) (Co P J) ℝ}(h:Tagged σ p g K): Tagged σ p (winter g (U:=U) (R:=R)) (fun i=> winterSeat (K i)):=by
 refine ⟨priced_winter h.toPriced,?_⟩; rintro n ⟨q,i|a⟩ ⟨o,b|r⟩;exact h.seen n (q,i) (o,b);all_goals simp [winter,winterSeat,display]
lemma priced_chill {g:Kernel I J}(h:Rows.Priced σ p g): Priced σ p (chill (U:=U) g):=by
 refine ⟨h.pos,?_,?_,?_⟩
 · rintro ⟨a,i|b⟩ q z;exact h.city (a,i) q z;rfl
 · rintro ⟨a,i|v⟩ j;exact h.row (a,i) j;simp [chill,bill]
 rintro (i|a) q;exact h.col i q;simp [chill,bill]
lemma chill_tag {g:Kernel I J}{K:∀ P:Side, Matrix (Co P I) (Co P J) ℝ}(h:Tagged σ p g K): Tagged σ p (chill g (U:=U)) (fun i=> chillSeat (K i)):=by
 refine ⟨priced_chill h.toPriced,?_⟩; rintro n ⟨q,i|a⟩ o;exact h.seen n (q,i) o;simp [chill,chillSeat,display]
lemma shine_tag {g:Kernel I J}{K:∀ P:Side, Matrix (Co P I) (Co P J) ℝ}(h:Tagged σ p g K): Tagged σ p (rightSumKernel g (U:=U)) (fun i=> shineSeat (K i)):=by
 refine ⟨⟨h.pos,?_,?_,?_⟩,?_⟩
 · rintro ⟨t,u|i⟩ q z;rfl;exact h.city (t,i) q z
 · rintro ⟨a,v|i⟩ j;simp [rightSumKernel,bill];exact h.row (a,i) j
 · rintro (a|i) q;simp [rightSumKernel,bill];exact h.col i q
 rintro n ⟨q,a|i⟩ o;simp [rightSumKernel,shineSeat,display];exact h.seen n (q,i) o

variable {G:Gauge}(P:Patch)(K:KernelChoices)(A B:Bed)(n:Side)
local notation "S₀"=>RG08.Line.habitat P K n
lemma ready_line {σ p:ℝ}(h: Cell.Warm G K P A σ p):
 (grace G S₀ (Line.green S₀) A B).g=Line.NativeLine S₀ G A:=by
 obtain ⟨hr,ht,hh⟩:= h.invert n; apply (Prism.gross G S₀ (Line.green S₀) A B (Γ:=Line.NativeLine S₀ G A) (Given.mk hr ht hh)).1
-- notation not Pole base

def winterGreen (n:Side):=winterSeat (U:=Loc G 1) (R:=Loc G 1) (Line.cellLine P K G A n)
def springGreen (n:Side):= chillSeat (U:=Loc G 1) (Cell.predictorFinite P K G A n) + shineSeat (U:=Co P.L (Loc G 1)) (1:Matrix (Lines G n 1) (Lines G n 1) ℝ)

lemma ready_phases {σ p:ℝ}(h: Cell.Warm G K P A σ p) : press (grace G S₀ (Line.green S₀) A B) (fir S₀) = winterGreen P K A n:=by
 ext a b :1; obtain ⟨x,rfl⟩:= (fir (G:=G) S₀).surjective a;obtain ⟨y,rfl⟩:= (fir (G:=G) S₀).surjective b
 simp only [press,Matrix.submatrix_apply,Equiv.symm_apply_apply,Prism.ember]
 cases x <;> cases y
 next i j=>
    rw [Matrix.fromBlocks_apply₁₁,ready_line _ _ _ B n h, fir_1,fir_1]
    unfold winterGreen winterSeat lowSlot; rw [Line.native_paid];unfold repackM; -- unitSplit=splitCo
    change _= (Line.NativeLine S₀ G A) ((unitSplit G S₀ 1).symm ((unitSplit G S₀ 1) i)) ((unitSplit G S₀ 1).symm ((unitSplit G S₀ 1) j));simp
 all_goals rfl
lemma ready_mean {σ p:ℝ}(h:Cell.Warm G K P A σ p) : script (grace G S₀ (Line.green S₀) A B) (fir S₀)=springGreen P K A n:=by
 ext a b :1; obtain ⟨u,rfl⟩:= (fir (G:=G) S₀).surjective a
 unfold script;rw [Equiv.symm_apply_apply];cases u with
 | inl k=>
   unfold Drum.mean
   rw [ready_line _ _ _ B n h, Matrix.mul_smul]
   rw [springGreen,← Cell.root_read P K G A n]; rw [Matrix.add_apply]; unfold chillSeat shineSeat
   change Cell.RootField K G S₀ A k b = repackM (unitSplit G S₀ 1) (Equiv.refl _) (Cell.RootField K G S₀ A) ((unitSplit G S₀ 1) k) b+0
   simp [repackM]
 | inr k=>
   rw [fir_2,springGreen,Matrix.add_apply]; unfold chillSeat shineSeat highSlot; simp only [Sum.elim_inr, zero_add, Matrix.one_apply, Prod.eta]; by_cases hk : k = b <;> simp [hk]

-- identity line
variable {I:Type}[Fintype I]
def obvious:Kernel I I:=fun i j=> if i=j then 1 else 0
omit [Fintype I] in
lemma obvious_bill [DecidableEq I](σ:ℝ): Tagged σ 1 (obvious (I:=I)) (fun c=> (1:Matrix (Co c I) (Co c I) ℝ)):=by
 refine ⟨⟨zero_le_one,?_,?_,?_⟩,?_⟩
 · rintro ⟨x,i⟩ ⟨y,j⟩ u;simp [obvious,Packets.pass,Prod.ext_iff]
 · rintro ⟨x,i⟩ j
   simp [obvious,Prod.ext_iff,bill,apply_ite abs,ite_mul,apply_ite ENNReal.ofReal]
   by_cases he:i=j <;> simp [he,sep_self]
 · rintro j ⟨x,i⟩
   simp [obvious,Prod.ext_iff,bill,apply_ite abs,ite_mul,apply_ite ENNReal.ofReal];by_cases he:j=i <;> simp [he,sep_self]
 rintro c ⟨x,i⟩ ⟨y,j⟩;rw [Matrix.one_apply]; unfold display obvious; dsimp only
 rw [tsum_eq_single x (fun z hz => by
   by_cases hw : wrap c z = y <;> simp [hw, Prod.ext_iff, Ne.symm hz])]
 by_cases hi:i=j <;> by_cases hx: (wrap c) x=y <;> simp [Prod.ext_iff,hi,hx]

-- rewards all exact
def ice :Kernel (Tack.Head P G) (Tack.Head P G):= winter (Line.warm P K G A)
def rains :Kernel (Tack.Head P G) (Loc G 1):= chill (Cell.predictor P K G A)+ rightSumKernel obvious
lemma ready_roads {σ p:ℝ}(h:Cell.Warm G K P A σ p)(ha:0<σ)(hs:σ ≤ 1): Tagged σ p (ice (G:=G) P K A) (winterGreen (G:=G) P K A) ∧ Tagged σ (p*Cell.key G P K+1) (rains (G:=G) P K A) (springGreen (G:=G) P K A):= ⟨winter_tag h.bill,(chill_tag (Cell.predictor_price P K G A h ha.le hs)).add (shine_tag (obvious_bill _)) ha.le⟩
end YM.RG08.Prism
