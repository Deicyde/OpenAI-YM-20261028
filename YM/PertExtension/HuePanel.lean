import YM.PertExtension.TopCalibration
import YM.Next.RANK.Inks

/-! Color covariant polynomial data helpers with actual adjoint rotations. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.Hue
open Function Filter Set Finset MeasureTheory MvPolynomial Lattice Heat.Top Next.Rank
open Next
open scoped Matrix.Norms.Frobenius Topology Classical BigOperators Real ContDiff
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{α β V :Type*}
abbrev Panel (α : Type*)(G : Gauge):=α×G.ColorIndex
abbrev Poly (α) (G:Gauge):= MvPolynomial (Panel α G) ℂ
abbrev Mask (α) (G:Gauge):=α→G.Color
def tint (u:G.El)(q:Mask α G): Mask α G:= fun x=>G.adjoint u (q x)
def display (q:Mask α G):Poly α G →ₐ[ℂ] ℂ:=aeval fun i=> (↑((q i.1) i.2:ℝ):ℂ)
def Fixed (P : Poly α G) := ∀ u x, display (tint u x) P= display x P
def Clear (P : Poly α G) := ∀ x, star (display x P)= display x P

def rag (u:G.El)(i:Panel α G):Panel α G→₀ℂ:=∑ j:G.ColorIndex,Finsupp.single (i.1,j) ((G.adjoint u (EuclideanSpace.basisFun _ ℝ j) i.2:ℝ):ℂ)
abbrev inked (u:G.El) := Normal.exchange (@rag G α u)
lemma hue (x : Mask α G)(u:G.El)(p:Poly α G) : display (tint u x) p = display x (inked u p):= by
  apply DFunLike.congr_fun (g:=(display x).comp (inked u));ext1 i
  simp only [display,aeval_X,AlgHom.comp_apply,Normal.exchange_x, Normal.glyph, rag,_root_.map_sum,Finsupp.linearCombination_single,_root_.map_smul]
  let B:= (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
  have he : x i.1=∑ j,B.repr (x i.1) j • B j := (B.sum_repr _).symm
  have hv j : B.repr (x i.1) j=x i.1 j := by dsimp only [B];simp
  unfold tint
  conv_lhs => rw [he,_root_.map_sum]
  simp_rw [map_smul]
  rw [show ∀ g : G.ColorIndex → G.Color,(∑ i,g i).ofLp i.2=∑ j,(g j).ofLp i.2 from fun g => map_sum (EuclideanSpace.proj i.2 : G.Color →L[ℝ] ℝ) g _,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _=> ?_; rw [hv]; change ((↑( (x i.1 j:ℝ)*((G.adjoint u) (B j)) i.2 ):ℂ))= _; rw [Complex.ofReal_mul]; exact mul_comm ..

lemma touchable {p q:Poly α G}(h: ∀ x, display x p=display x q):p=q:=by
  apply Spindle.audible; intro s; let A : Mask α G := fun i=> WithLp.toLp 2 (fun j=>s (i,j))
  exact h A
lemma Fixed.actual {p:Poly α G}(h : Fixed p)(u:G.El):inked u p=p:=by
  apply touchable; intro x;rw [← hue,h u]
lemma Clear.actual {p:Poly α G}(h : Clear p): Spindle.retro _ p=p:=by
  apply touchable; intro x
  have h' := Spindle.escorted (fun i:Panel α G=> x i.1 i.2) p
  exact h'.trans (h x)
lemma promote_clear {p:Poly α G} (h:Spindle.retro _ p=p):Clear p:= by
  intro x
  exact (Spindle.escorted (fun i:Panel α G=> x i.1 i.2) p).symm.trans (congr_arg _ h)

def Lone {A:Type*}(P:MvPolynomial A ℂ)(k:ℕ):Prop:= IsWeightedHomogeneous (fun _=> (1:ℕ)) P k

lemma cut_natural {A:Type*}(T:MvPolynomial V ℂ→ₐ[ℂ] MvPolynomial A ℂ)(ht : ∀ (i:V), Lone (T (X i)) 1)(n:ℕ)(P:MvPolynomial V ℂ): T (cut n P)=cut n (T P):=by
   induction P using MvPolynomial.induction_on' with
   | monomial f r=>
     have hp : Lone (T ((monomial f) r)) (Heat.Top.degree f) := by
       rw [monomial_eq,map_mul, show T (C r) = C r from T.commutes _]
       unfold Finsupp.prod
       simp only [map_prod,map_pow]
       refine IsWeightedHomogeneous.C_mul ?_ _
       rw [degree_eq];unfold Finsupp.sum
       apply IsWeightedHomogeneous.prod;intro i hi
       simpa using! IsWeightedHomogeneous.pow (ht i) (f i)
     rw [cut_mono];by_cases h:Heat.Top.degree f = n
     · rw [← h,if_pos rfl]; exact (hp.weightedHomogeneousComponent_same).symm
     rw [if_neg h,map_zero];exact (hp.weightedHomogeneousComponent_ne n (Ne.symm h)).symm
   | add p q hi hj => rw [map_add,map_add,map_add,map_add,hi,hj]

lemma incision (u:G.El)(n : ℕ)(p:Poly α G) : inked u (cut n p)=cut n (inked u p):=by
  apply cut_natural; intro i
  rw [Normal.exchange_x]; unfold rag; rw [map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ ?_
  intro j hj
  simp only [Normal.glyph,Finsupp.linearCombination_single,← C_mul']
  exact (isWeightedHomogeneous_X ..).C_mul _
lemma Fixed.slice {p:Poly α G}(h:Fixed p) (k:ℕ): Fixed (cut k p):=by intro u x; rw [hue,incision,h.actual]
lemma Clear.slice {p:Poly α G}(h:Clear p) (k:ℕ): Clear (cut k p):=promote_clear (calc
  _ = cut k (Spindle.retro _ p):=by ext j; simp only [Spindle.retro,coeff_map,cut_coeff];aesop
  _ = _ := by rw [h.actual])

lemma lift_panel (f:α→β)(P:Poly α G) (x:Mask β G):
     display x (rename (fun i=>(f i.1,i.2)) P)=display (x∘f) P:=by unfold display; rw [aeval_rename];rfl
lemma Fixed.relabel (f:α→β){P:Poly α G}(h:Fixed P): Fixed (rename (fun i=>(f i.1,i.2)) P : Poly β G):=by
   intro i x; rw [lift_panel,lift_panel];exact h i (x ∘ f)
lemma Clear.relabel (f:α→β){P:Poly α G}(h:Clear P):Clear (rename (fun i=>(f i.1,i.2)) P : Poly β G):=by
   intro x;rw [lift_panel,h]

end YM.PertExtension.Hue
