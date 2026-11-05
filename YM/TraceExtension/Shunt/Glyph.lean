import YM.TraceExtension.Shunt.Ramps
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Shunt
open RG Wilson Lattice Source Labels Finset Push.Local Next.Foundations MergeProof Planned.GuardedAtom Guard Extra.Histories Filter Function Relay
open MeasureTheory
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side} {T:SectionData F}{H:Hol G}{R:Rep G n}{v w p c k u a:ℝ}
variable {P Q:Support n} {Z X: Coefficient F n}{f g:Film G n}
lemma Proxy.plus (h:Proxy T H R P Z f v k w)(hp: Proxy T H R P X g v u a): Proxy T H R P (beside Z X) (f+g) v (k+u) (w+a):=by
    obtain ⟨b,hb,hF⟩:=h.charge; obtain ⟨c,hc,hX⟩:=hp.charge; let T':=beside Z X; have he : T'.exponentialEntry 0 T R= Z.exponentialEntry 0 T R+ X.exponentialEntry 0 T R:= duo_exp T hF hX; obtain ⟨hZ,hR⟩:= presentation h.format hF hp.format hX
    refine ⟨hZ,⟨_,?_,hR⟩,?_,fun U hu=> ?_,fun U=>?_,?_,?_,?_⟩
    · rw [reckon]; linarith only [Extra.Histories.Size.add F Z.x X.x,hb,hc]
    · rw [sideK,h.naked,hp.naked,add_zero]
    · rw [he,Pi.add_apply,h.pose _ hu,hp.pose _ hu];rfl
    · rw [he,Pi.add_apply]; exact (norm_add_le ..).trans (add_le_add (h.all _) (hp.all _))
    · rw [he]; exact fun U V hu hv=>congr_arg₂ (· + ·) (h.locale _ _ hu hv) (hp.locale _ _ hu hv)
    · rw [he]; intro g U; exact congr_arg₂ (· + ·) (h.symm ..) (hp.symm ..)
    rw [he]; exact h.pay.add hp.pay
lemma Proxy.wide (h:Proxy T H R P Z f v k w)(he:k≤u)(hx:w ≤ a)(hP:P ⊆ Q): Proxy T H R Q Z f v u a:=⟨h.format,h.charge.imp (fun _ hx=>⟨hx.1.trans he,hx.2⟩),h.naked,fun U hu=> h.pose U (Disjoint.mono_left hP hu),fun U=>(h.all U).trans hx,Work.H03.reads_larger hP h.locale,h.symm,h.pay⟩
lemma blue_price(h:Readable H T R.p n p)(hp:T.footprint (0:Site n)⊆ P)(hF:R.p.Regular P f)(hz:R.p.supBounds (0:Site n) P f w)(hv: 0 < v) :
   let A:=R.p.mass P w*(readPrice H F+atomPrice H F p); let B:=R.p.mass P w*((1+p)*readPrice H F+atomPrice H F p)
   Proxy T H R P (secondary T H R P f) f v A B:=by
    have h':= ramps T H R P f h hp hF hz hv; have ht:= R.p.loMass P w hz.1; have hy:1≤atomPrice H F p:=atomPrice_ge_one _ _ h.nonneg; have hP:1≤readPrice H F:=readPrice_pos H F; intro A B
    refine h'.wide ?_ ?_ (fun _ he=>he)
    · have hu:=mul_le_mul_of_nonneg_right ht (zero_le_one.trans hP); unfold A BudgetPoint.mass at *; linarith only [hu]
    unfold B; apply le_trans (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by positivity:0≤readPrice H F)) (by positivity[h.nonneg]: 0 ≤ 1+p)) (mul_le_mul_of_nonneg_left ht (zero_le_one.trans hy))) (le_of_eq ?_);ring
variable {L:Type} [DecidableEq L]
lemma Proxy.summed (W:Finset L)(X:L→ Coefficient F n)(ψ:L→Film G n)(vL wL:L→ℝ)(h:Proxy T H R P Z f v k w) (hp: ∀ i∈W,Proxy T H R P (X i) (ψ i) v (vL i) (wL i)):
   ∃ S:Coefficient F n,Proxy T H R P S ((∑ i∈W,ψ i)+f) v ((∑ i∈W,vL i)+k) ((∑ i∈W,wL i)+w)∧ S.x=(∑ i∈W,(X i).x)+Z.x:=by
   induction W using Finset.induction with
   | empty=>simp only[sum_empty,zero_add];exact ⟨_,h,rfl⟩
   | insert i W hi ih=>
      obtain ⟨A,ha,hA⟩:= ih (fun j hj=> hp j (mem_insert_of_mem hj)); rw [sum_insert hi,sum_insert hi,sum_insert hi,sum_insert hi,add_assoc, add_assoc,add_assoc,add_assoc]; exact ⟨_,(hp i (mem_insert_self ..)).plus ha,(reckon _ A).trans (by rw[hA])⟩
end YM.Trace.Shunt
