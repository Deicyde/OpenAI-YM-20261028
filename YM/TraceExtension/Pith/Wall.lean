import YM.TraceExtension.Pith.Party
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pith
open Function Filter Set Extraction Ward Climb Spec Over Pilot Table Analysis Maxwell StressFlux Work Work.A05 Work.A15 MeasureTheory Next.UVStress Spin
open scoped Topology BigOperators InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{p:Extraction.Order}{S:Table C.book}{H:(Bel C.book).Hierarchy}{n:ℕ}
local notation "F₀" => Bel C.book
local instance (n:ℕ): ContinuousSMul ℝ (Points n):=IsBoundedSMul.continuousSMul

def erase{i:ℕ}(v:(Bel C.book).Field i): Axis→Axis→(Bel C.book).Field i:=fun a b=> if a=b then v else 0
abbrev post(P:change S 4)(w:(Bel C.book).Stress): S.Stress:= fun a b=> P (w a b)
structure Measures (F:Final C p S)(s:ℝ)(P:change S 4)(a d e:ℝ): Prop where
   reads : ∀ i j,P.symm (s^4 • F.sector.energy i j)=a • standard4 C i j +d • erase (C:=C) (stepField C) i j +e • erase (C:=C) ((F₀).unit 4) i j

section S
variable (F:Final C p S){P:change S 4}{a d e s:ℝ}(hp: Measures F s P a d e)(x:Points (n+1))(hx:x∈conf _)(hr:0<s)
include hp
lemma Measures.codes : (s^4:ℝ) • F.sector.energy= a • post (C:=C) P (standard4 C)+d • post (C:=C) P (erase (C:=C) (stepField C))+e • post (C:=C) P (erase (C:=C) ((F₀).unit 4)):=by
   funext i j; have hx:= hp.reads i j; apply P.symm.injective; rw[show ((s^4:ℝ) • F.sector.energy) i j= s^(4:ℕ) • (F.sector.energy i j) from rfl,hx]; simp only[Pi.smul_apply,Pi.add_apply, post,map_add]
   have hv(c:ℝ) v:P.symm (c • P v)=c • v:=by rw[show P.symm (c • P v)=c • P.symm (P v) from (P.symm.toLinearMap.restrictScalars ℝ).map_smul ..,P.symm_apply_apply]
   rw[hv,hv,hv]

omit hp in
def divRead (x : Points (n+1))(v: Fin n→ (Bel C.book).Field 4)(w:(Bel C.book).Stress)(b:Axis)(s:ℝ)(P:change S 4):=∑ a:Axis, pron a (post (C:=C) P w a b) (P∘ v) x s

include hx hr
omit hp in
lemma div_read (v:Fin n→(Bel C.book).Field 4)(w:(Bel C.book).Stress)(b:Axis): divRead x v w b s P=(s:ℂ)* Work.A05.frontRead (s • x) (fun i=>⟨4,P (v i)⟩) (4+1) (∑ i:Axis,F.sector.derivatives.deriv 4 i (post (C:=C) P w i b)):=by
   unfold divRead; rw [map_sum,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> strains F.sector.derivatives F.room.kernel F.phase.transport.derivatives x hx i _ _ hr
include F
omit hp in
lemma div_cross (v:Fin n→ (Bel C.book).Field 4)(B:(Bel C.book).Field 4)(b:Axis): divRead x v (erase (C:=C) B) b s P= pron b (P B) (P ∘ v) x s:=by
   unfold divRead; rw [Finset.sum_eq_single b]
   · simp[post,erase]
   · intro i _ he; simp only[post,erase,if_neg he,map_zero]; rw [strains F.sector.derivatives F.room.kernel F.phase.transport.derivatives x hx i 0 (P ∘ v) hr,map_zero,map_zero,mul_zero]
   simp

set_option maxHeartbeats 800000 in
lemma conserv (hv:P ((F₀).unit 4)=S.unit 4)(v:Fin n→(Bel C.book).Field 4)(b:Axis):
    a • divRead x v (standard4 C) b s P + d • divRead x v (erase (C:=C) (stepField C)) b s P=0:=by
   let f:=F.sector.derivatives.deriv 4; let g(w:S.Stress):=∑ i:Axis,f i (w i b)
   have hS(c:ℝ)(w:S.Stress):g (c • w)= c • g w:=by unfold g; rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _=> ((f i).restrictScalars ℝ).map_smul ..)
   have hA(y z:S.Stress):g (y+z)=g y+g z:=by unfold g; simp only [Pi.add_apply,map_add, Finset.sum_add_distrib]
   have hp:= congr_arg g (hp.codes F); rw [hS,hA,hA,hS,hS,hS] at hp
   let H:=F.room.kernel; let V:= F.sector; have he:= F.phase.transport
   rw [show g V.energy=0 from he.conserved.divergence b, smul_zero,show g (post (C:=C) P (erase (C:=C) ((F₀).unit 4)))=0 from ?_, smul_zero, add_zero] at hp
   · rw [div_read F x hx hr, div_read F x hx hr]; let u:=g (post (C:=C) P (standard4 C)); let q:=g (post (C:=C) P (erase (C:=C) (stepField C))); let L:= Work.A05.frontRead (s • x) (fun i:Fin n=> (⟨4,P (v i)⟩:S.Tag)) (4+1);
     change a • ((s:ℂ)*L u)+d • ((s:ℂ)*L q)=0
     rw [← mul_smul_comm, ← mul_smul_comm,← mul_add, ← show L (a • u)=a • L u from (L.restrictScalars ℝ).map_smul ..,← show L (d • q)=d • L q from (L.restrictScalars ℝ).map_smul ..,← map_add, hp.symm,map_zero,mul_zero]
   unfold g; refine Finset.sum_eq_zero fun i _=> ?_; by_cases ht:i=b
   · simp only[post,erase,if_pos ht,hv]; exact V.derivatives.unit_drop H.laws he.derivatives H.smooth _ _
   simp only[post,erase,if_neg ht,map_zero]

omit hp hx F hr in
def flair(x : Points (n+1))(χ:E4→ℝ) (w:(Bel C.book).Stress) (b:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4)(s:ℝ)(P:change S 4):=∑ a, say x χ a w b Y v s P
variable {χ:E4→ℝ}(hw:Window x χ)
include hw
omit hp F hx in
lemma scale_flair (w:(Bel C.book).Stress)(b:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4):
    shellGrad S (post (C:=C) P w) (stretch s χ) b (s • x) (fun i=> ⟨4,P (v i)⟩) (P Y)=(s:ℂ)^3 * flair x χ w b Y v s P:=by
   unfold flair shellGrad; rw [Finset.mul_sum,← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=> ?_
   unfold say; rw [mul_neg]; congr! 1
   let q:= Fin.cons (α:=fun _:Fin (n+2)=>S.Tag) (⟨4,post (C:=C) P w i b⟩: S.Tag) (Fin.cons ⟨4,P Y⟩ (fun i=>⟨4,P (v i)⟩)); let f(y:E4):= (1:ℝ)
   have ht:= integrate_sheet_scale hr x q hw.1 i f; rw[← ht]; simp only [sheet,Work.A05.weight,stretch,q,post,f,one_smul,mul_one,disc]

set_option maxHeartbeats 800000 in
lemma translates (hv:P ((F₀).unit 4)=S.unit 4)(b:Axis)(Y:(Bel C.book).Field 4)(v:Fin n→(Bel C.book).Field 4):
    a • flair x χ (standard4 C) b Y v s P +d • flair x χ (erase (C:=C) (stepField C)) b Y v s P= pron b (P Y) (P ∘ v) x s:=by
   let E:= F.sector; let T:= F.phase.transport; let q(i:Fin n): S.Tag:= ⟨4,P (v i)⟩; let B:= post (C:=C) P (erase (C:=C) ((F₀).unit 4))
   have hh(x y:Axis):(if x=y then (1:ℂ) else 0)=(if y=x then 1 else 0):=by simp [eq_comm]
   have hp': B=UVNext.FreeStress.fossil (S:=S) (fun i j=>if i=j then 1 else 0):=by funext i j; unfold B post erase UVNext.FreeStress.fossil; by_cases hj:i=j<;> simp [hj,hv]
   have h:=window_stretch hr hw; have hS:= smul_conf hr hx
   let L:= translationFlux hS h F.room.kernel.smooth q (P Y) b
   have hV:= Work.A05.frontRead_at (s • x) q (4+1)
   have hz:L B=0:=by unfold L; rw [translationFlux_apply,hp',(UVNext.FreeStress.unit_shell F.room.kernel (fun i j=> if i=j then 1 else 0) hh).translation hS q h, show ((0: Parts S) 4 b (P Y))=0 from rfl]; exact ((hV 0).symm).trans (map_zero _)
   have ht:=congr_arg (L.restrictScalars ℝ) (hp.codes F); let u:=L (post (C:=C) P (standard4 C)); let j:=L (post (C:=C) P (erase (C:=C) (stepField C)))
   rw[map_smul,map_add,map_add,map_smul,map_smul,map_smul] at ht; change (s^4:ℝ) • L _=a • u+d • j+e • L B at ht; rw[hz,smul_zero,add_zero] at ht
   unfold u j L at ht; simp_rw [translationFlux_apply] at ht; rw[T.charges.translation hS q h b 4 (P Y),← show _= S.useAt S _ _ from hV _, show shellGrad _ _ _ _ _ q _=_ from scale_flair (P:=P) x hr hw (standard4 C) b Y v] at ht
   rw [show shellGrad _ _ _ _ _ q _=_ from scale_flair (P:=P) x hr hw (erase (C:=C) (stepField C)) b Y v] at ht
   rw [strains E.derivatives F.room.kernel T.derivatives x hx b (P Y) (P ∘ v) hr]; let y:= Work.A05.frontRead (s • x) q (4+1) (E.derivatives.deriv 4 b (P Y)); change _= (s:ℂ)*y
   refine mul_left_cancel₀ (show (s:ℂ)^3 ≠ 0 from pow_ne_zero _ (by exact_mod_cast hr.ne')) ?_
   rw [mul_add, mul_smul_comm, mul_smul_comm]; refine ht.symm.trans ?_
   change (s^4:ℝ) • y=(s:ℂ)^3*((s:ℂ)*y); rw[pow_succ,Complex.real_smul]; push_cast; ring
end S
end YM.Trace.Pith
