import YM.FullVolume.Nectar.Supreme
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Tint GridApprox.Nil
variable {X I E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{v a b:ℝ}{F:sun→ X→E}
abbrev frosty (R:Set X)(u:Tint E X)(x:X):= R.indicator (fun i=> Tint.see E i u) x
lemma artF (R:Set X)(u:Tint E X)(x:X): ‖frosty R u x‖≤‖u‖:=by
    unfold frosty; by_cases hx:x∈R; rw [indicator_of_mem hx]; exact lp.norm_apply_le_norm (by simp) (Tint.cast u) x
    rw [indicator_of_notMem hx,norm_zero]; exact norm_nonneg _
def tints (R:Set X)(u:Tint E X):Tint E X:=wear ⟨frosty R u,memℓp_infty ⟨‖u‖,Set.forall_mem_range.mpr (artF R u)⟩⟩
lemma older (x:ℂ) {v: ℂ}: x*v=x*v:=rfl
lemma Feel.cropped (R:Set X)(h:Feel F a):Feel (fun t=> R.indicator (F t)) a:=by
    obtain ⟨u,hp,h⟩:=h.costs
    let A(t:Tint E X):= tints R t; refine ⟨fun i=> A (u i),fun i j=> congr_arg (fun f:X→E=> R.indicator f j) (funext (hp i)),?_⟩
    have hv: ∀ p q:Tint E X,A (p-q)=A p-A q:=by
        intro p q; apply Tint.liftEqual;intro i; rw [map_sub]; by_cases h:i∈R; exact (indicator_of_mem h (fun j=>Tint.see E j (p-q))).trans ((map_sub (Tint.see E i) p q).trans (congr_arg₂ Sub.sub (indicator_of_mem h _).symm (indicator_of_mem h _).symm))
        rw [show Tint.see E i (A (p-q))=0 from indicator_of_notMem h (fun j=>Tint.see E j (p-q)),show Tint.see E i (A p)=0 from indicator_of_notMem h (fun j=>Tint.see E j p), show Tint.see E i (A q)=0 from indicator_of_notMem h (fun j=>Tint.see E j q), sub_self]
    have hx(p:Tint E X): ‖A p‖≤1*‖p‖:=by rw [one_mul]; apply le_trans (lp.norm_le_of_forall_le (f:=(Tint.cast (A p))) (norm_nonneg p) (fun i=> artF R p i)); exact le_rfl
    rw [show a=1*a from (one_mul _).symm]; exact PaidBeam.transit A hv zero_le_one hx u h
lemma Feel.stacks (v:Finset I)(f:I→sun→X→E)(b:I→ℝ)(h:∀ i∈v,Feel (f i) (b i)):Feel (fun t p=>∑ i∈v,f i t p) (∑ i∈v,b i):=by
    induction v using Finset.induction with
    | empty=> simp only [sum_empty]; exact Feel.staticC (fun _=>0) le_rfl (fun _=>by simp)
    | insert i u hi ih=>simp_rw [sum_insert hi];exact Feel.united (h i (mem_insert_self ..)) (ih fun i hi=> h i (mem_insert_of_mem hi))
local notation "T₀"=> Tint ℂ X
private def time (X:Type): Tint ℂ X→L[ℝ] Tint ℂ X→L[ℝ] Tint ℂ X:=
   show (lp (fun _:X=>ℂ) ∞) →L[ℝ] (lp (fun _:X=>ℂ) ∞) →L[ℝ] (lp (fun _:X=>ℂ) ∞) from ContinuousLinearMap.mul ℝ _
lemma Feel.times {F G:sun→ X→ℂ}(hf:Feel F a)(hg:Feel G b): Feel (fun i=>F i*G i) (a*b):=by
   obtain ⟨f,h,hP⟩:=hf.costs; obtain ⟨g,hx,hQ⟩:=hg.costs;let A:=time X; refine ⟨(fun x=> A (f x) (g x)),fun i j=>?_,?_⟩
   · exact (show _=_ from congr_arg₂ HMul.hMul (h i j) (hx i j))
   obtain ⟨P,hp,h1⟩:=hP.arrives; obtain ⟨Q,hq,h2⟩:=hQ.arrives; have hz:‖A‖≤1:=by exact ContinuousLinearMap.opNorm_mul_le ℝ (lp (fun _:X=>ℂ) ∞)
   refine ⟨brave A P Q, (braveN ..).trans ((mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hz).trans (mul_le_mul hp hq (norm_nonneg _) hf.positives)),fun i=>?_⟩
   rw [Beam.harp,h1,h2]
section stack
variable {V : Type}[DecidableEq V][Fintype V] {B:Census V}
variable {w:V→ℝ} {F G:sun→X→Poly B}(hw:∀ i,0<w i)
def LeafPaid (w:V→ℝ) (F:sun→X→Poly B)(a:ℝ):Prop:=∃ v:Sheet B, 0 ≤ v∧ wordsPrice w v≤ a∧ ∀ j, Feel (fun i x=>(F i x).part j) (v j)
namespace LeafPaid
lemma silence : LeafPaid w (0:sun→ X→Poly B) 0:=by
    refine ⟨0,le_rfl,?_,fun _=>?_⟩; simp [wordsPrice]
    exact Feel.staticC (fun _=>0) le_rfl (fun _=>norm_zero.le)
lemma solo (u:ℂ): LeafPaid w (fun _ _ : _=> Poly.bead B u : sun→X→Poly B) ‖u‖ := by
    let v(i:B.Mode):=if i=B.quiet then ‖u‖ else 0; refine ⟨v,fun i=> ?_,?_,fun j=>?_⟩
    · unfold v;split;exact norm_nonneg _; rfl
    · simp [wordsPrice,v, mul_ite]
    simp_rw [Poly.bead]; change Feel (fun i:sun=>fun x:X=> (Poly.send B.quiet u).part j) (v j); simp_rw [Poly.part_send]; unfold v; split_ifs
    · exact Feel.staticC (fun _=>u) (norm_nonneg _) (fun _=>le_rfl)
    exact Feel.staticC (fun _=>0) le_rfl (fun _=>norm_zero.le)
include hw
lemma mixP (h:LeafPaid w F a)(hp:LeafPaid w G b): LeafPaid w (fun i U=> F i U* G i U) (a*b):=by
   obtain ⟨v,hv,hA,hV⟩:=h; obtain ⟨t,ht,hB,hT⟩:=hp
   refine ⟨combine v t, merged_nn v t hv ht,(merged_price v t hv ht w hw).trans (mul_le_mul hA hB (sum_nonneg fun i _=>mul_nonneg (Poly.worth hw _|>.le) (ht i)) ((sum_nonneg fun i _=>mul_nonneg (Poly.worth hw _|>.le) (hv i)).trans hA)),fun i=>?_⟩
   simp_rw [Poly.part_mul]; unfold GridApprox.Nil.combine; apply Feel.stacks; intro j _; apply Feel.stacks; intro k _; split_ifs; exact Feel.times (hV j) (hT k)
   exact Feel.staticC (fun _=>0) le_rfl (fun _=>norm_zero.le)
lemma bags (s:Finset I)(F:I→sun→X→Poly B)(p:I→ℝ)(hx:∀ i∈ s, LeafPaid w (F i) (p i)): LeafPaid w (fun t x=> ∏ i∈s,F i t x) (∏ i∈s,p i):=by
    induction s using Finset.induction with
    | empty=>simp only [Finset.prod_empty];simpa using solo (X:=X) (B:=B) (w:=w) (1:ℂ)
    | insert i s hi ih=> simp_rw [prod_insert hi]; exact mixP hw (hx _ (mem_insert_self ..)) (ih fun i hi=> hx i (mem_insert_of_mem hi))
end LeafPaid
end stack
end YM.FullVolume.Nectar
