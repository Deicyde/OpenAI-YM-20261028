import YM.TraceExtension.Pills.Lag
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{R M k:ℕ} {I:Type} {x:Site n} {X Y:Link G n}
variable (L:Finset I) (P:I→Wo G) (h:hush L P) (b:Cards G)
section lette
variable (hp: Stifle X R) (hv:RelativeP Y (R+1+M)) (i j:Fin 2) (he:i ≠ j) (hl:∀ i∈L,(P i).length ≤ M)
private lemma stood (p:Wo G): ∑ x:Site n,crease p x i b X * crease p x j b Y=∑ y:Site n, eyeB X y (p.leg i).plaq (b i) * eyeB Y (wrap n ((p.leg j).offset-(p.leg i).offset)+y) (p.leg j).plaq (b j):=by
    let v:=wrap n (p.leg i).offset
    rw [← Equiv.sum_comp (Equiv.addLeft v) (fun y:Site n=> eyeB X .. * eyeB Y ..)]
    refine Finset.sum_congr rfl (fun y _=>?_); unfold crease; change _=eyeB X (v+y) _ _* _; congr 2
    rw [show Equiv.addLeft v y=v+y from rfl]; unfold v; rw [map_sub]; abel
include h hp hv he hl
private lemma agree(a:Fin 2→PlaqAxes)(x:Site n): (∑ k∈L,charge (P k) a b* (eyeB X x (a i) (b i) * eyeB Y (wrap n (((P k).leg j).offset-((P k).leg i).offset)+x) (a j) (b j)))=0:=by
    by_cases hX: eyeB X x (a i) (b i)=0; · simp[hX]
    let v(k):=((P k).leg j).offset-((P k).leg i).offset
    obtain ⟨F,C,hY⟩:= hv.valid (a j) (b j); have H(k)(hk:k∈ L): eyeB Y (wrap n (v k)+x) (a j) (b j)=C+F (lift x)+F (v k):=by
        rw [show wrap n (v k)+x=wrap n (lift x+v k) by rw [map_add,wrap_lift,add_comm]]; rw[hY _ (localeT (R:=M) (v k) ((pollinate (P k) i j he).trans (hl k hk)) (eye_small hp _ _ hX)),map_add,add_assoc]
    let D:=eyeB X x (a i) (b i); let Q:=C+F (lift x)
    apply Eq.trans (b:= D*((∑ k∈L,charge (P k) a b)*Q+∑ k∈L,charge (P k) a b*F (v k)))
    · rw [Finset.sum_mul,← Finset.sum_add_distrib,Finset.mul_sum]; refine sum_congr rfl fun k hk=> ?_ ; rw[H k hk]; unfold D Q v; ring
    rw[(h a b).1,hush_sum L P h F a b i j he]; ring
lemma pong : (∑ k∈L,(P k).coeff b * ∑ x:Site n, crease (P k) x i b X * crease (P k) x j b Y)=0:=by
    simp_rw [stood b i j,mul_sum]; rw[sum_comm]; apply sum_eq_zero fun x _=>?_ ; have hx(k):
       let Q:=P k; let v:=wrap n ((Q.leg j).offset-(Q.leg i).offset)+x; Q.coeff b * (eyeB X x (Q.leg i).plaq (b i) * eyeB Y v (Q.leg j).plaq (b j))= ∑ a:Fin 2→ PlaqAxes,charge Q a b * (eyeB X x (a i) (b i)* eyeB Y v (a j) (b j)):=by
       intro Q v; rw[sum_eq_single (fun a=> (Q.leg a).plaq),charge,if_pos rfl]; intro a _ hz; rw[charge,if_neg hz.symm,zero_mul]; simp
    simp_rw[hx]; rw [sum_comm]; apply sum_eq_zero fun p _=> agree L P h b hp hv i j he hl p x
end lette
private lemma scale_per(s: Signed)(p:Wo G)(x:Site n): ContDiffAt ℝ ω (fun z:Link G n=> p.unmasked (pull s 0 (input G n z)) x) 0:=by
    simp_rw [flip_links]; let T:=orderTurn (G:=G) (m:=n) s; exact ContDiffAt.comp (g:=fun y=> p.unmasked (input G n y) x) (f:=T) _ ((map_zero T).symm ▸ shelfB p x) T.contDiff.contDiffAt
include h
lemma combM (S T:Link G n) (hp:Stifle S R)(he:∀ s:Signed, RelativeP (orderTurn s T) (R+1+1+M)) (hR:∀ i∈L,(P i).length≤M): sheen (paper L P) S T=0:=by
    let A(k:I)(s:Signed)(x:Site n):Link G n→ℝ:=fun y=> (P k).unmasked (pull s 0 (input G n y)) x
    let X(k:I)(y:Link G n):=∑ s:Signed,∑ x: Site n,A k s x y
    have hs(k:I)(s:Signed):ContDiffAt ℝ ω (fun y=>∑ x,A k s x y) 0:= ContDiffAt.sum (fun x _=> scale_per ..)
    have hx(k): ContDiffAt ℝ ω (X k) 0:= ContDiffAt.sum fun i _=> hs k i
    let Q(v: Signed)(S:Link G n):=orderTurn v S
    have hu(k:I)(s:Signed)(x:Site n): iteratedFDeriv ℝ 2 (A k s x) 0 ![S,T]=(∑ i,laceF (P k) x i (Q s S) (Q s T))+(∑ i,laceF (P k) x i (Q s T) (Q s S)):= blender ..
    unfold sheen; rw [show paper L P ∘ input G n= VerifiedReset.factor • fun x=>∑ i∈L,X i x from rfl, iteratedFDeriv_const_smul_apply, _root_.smul_apply]; swap
    · exact ContDiffAt.sum fun i _=> (hx i).of_le le_top
    rw [iteratedFDeriv_fun_sum_apply (fun i hi=> (hx i).of_le le_top), _root_.sum_apply]
    suffices ht:(∑ k∈L,iteratedFDeriv ℝ 2 (X k) 0 ![S,T])=0 by rw[ht,smul_zero]
    have ht(k:I): iteratedFDeriv ℝ 2 (X k) 0 ![S,T]=∑ s,∑ x:Site n, ((∑ i,laceF (P k) x i (Q s S) (Q s T))+(∑ i,laceF (P k) x i (Q s T) (Q s S))):=by
       unfold X; rw[iteratedFDeriv_fun_sum_apply (fun i _=> (hs k i).of_le le_top),_root_.sum_apply]; apply Finset.sum_congr rfl fun s _=> ?_
       rw [iteratedFDeriv_fun_sum_apply (f:= fun x=> A k s x) (fun i _=> (show ContDiffAt ℝ ω _ _ from scale_per s (P k) i).of_le le_top), _root_.sum_apply]; exact sum_congr rfl fun i _=> hu k s i
    simp_rw [ht]; rw [sum_comm]; apply sum_eq_zero fun s _=>?_
    simp only[Finset.sum_add_distrib]; refine Eq.trans (congr_arg₂ (· + ·) ?_ ?_) (add_zero (0:ℝ))
    · simp_rw [sum_comm (s:= (univ:Finset (Site n))) (t:=(univ:Finset (Cards G)))]; rw[sum_comm]; refine sum_eq_zero fun b _=> ?_; simp_rw[laceF,← Finset.mul_sum]; exact pong L P h b (stark hp s) (he s) 0 1 (by decide) hR
    simp_rw [sum_comm (s:=(univ:Finset (Site n))) (t:=(univ:Finset (Cards G)))]; rw[sum_comm]; refine sum_eq_zero fun b _=>?_ ; simp_rw [laceF, mul_comm (crease _ _ 0 _ (Q s T)),← Finset.mul_sum]; exact pong L P h b (stark hp s) (he s) 1 0 (by decide) hR
end YM.Trace.Pills
