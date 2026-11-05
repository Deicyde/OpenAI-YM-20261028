import YM.RG08.Fold.Flares

/-! # Real-ledger rail application, from total Hessian law -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fold
open Glyph Steam Room Carrel Camera Matrix MvPolynomial Function Finset Filter Cloud Haze
open scoped BigOperators ContDiff Topology Classical Matrix PowerSeries
variable {I O B A C:Type}[Fintype I][Fintype O][Fintype B][Fintype A][Fintype C]
variable {A₀:Camera.Strip (Camera.Raw I B) (Camera.Raw I O)} -- unfolding packs
variable {P Q:Matrix I I ℝ} {N:Matrix O O ℝ}{K:Matrix B B ℝ}

lemma leadzero (q:Rail I O B)(H:acclim q.h P Q N K): tiny (belt q.b (platen K I)-platen N I):=by
 have ht(i:B):tap 0 (q.b (Sum.inr i))=median (tip q.h) (.inr i):=intro_tip q.h _
 have hv:=tipread q.ambient
 change tap 0 _=0
 unfold tap;rw [map_sub,sub_eq_zero];change tap 0 (belt q.b (liftInn _))=tap 0 (liftInn _)
 rw [rim]; unfold tap
 simp only [PowerSeries.coeff_C,↓reduceIte]
 apply MvPolynomial.funext; intro x
 simp only [sink,shelter,map_sum,_root_.map_smul,map_mul,MvPolynomial.aeval_X]; simp_rw [MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,map_sum]
 have he(i): MvPolynomial.eval x ((PowerSeries.coeff 0 (R:=Inn (Raw I O))) (q.b (.inr i)))=(horn q.h *ᵥ (x ∘ Sum.inr)) i:=by rw [show PowerSeries.coeff 0 (q.b (.inr i))=_ from ht i]; simp only [median,map_sum,MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,eval_X];exact congrFun (tipread q.ambient x).2 i -- private
 simp_rw [eval_mul,he,eval_X]
 have hh : exof q.h=0:=by ext i j;exact q.centered i j
 have hl:= H 0 (x ∘ Sum.inr)
 simp only [hh,mulVec_zero,zero_mulVec,zero_add] at hl
 simp only [eval_C]
 have ht {J:Type}[Fintype J](P:Matrix J J ℝ)(x:J→ℝ): winery P x=(-1/2:ℝ)*∑ i:J,∑ j:J,P i j*(x i*x j):=by
    unfold winery winB mulVec dotProduct;simp_rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;ring
 have hf {I:Type}[Fintype I](P:Matrix I I ℝ):winery P 0=0:=by simp [winery,winB]
 rw [hf,hf,zero_add,zero_add,ht K,ht N] at hl
 change (-1/2:ℝ)*_=_
 exact hl.symm

structure Peak (I O A:Type)[Fintype I][Fintype O][Fintype A] extends Ledger (Raw I O) A where
 inside : Matrix I I ℝ
 outside: Matrix O O ℝ
 mirror: insideᵀ=inside
 inverse : IsUnit inside.det
 symm (i j:I): inside⁻¹ i j=inside⁻¹ j i
 present: theater=morn inside⁻¹ symm O
 warm: K=heater inside O
 cold: κ=platen outside I
 orientation : Ledger.Sincere toLedger

namespace Peak
variable (S:Peak I O A)(T:Peak I B C)

-- geometry-side fee equation assumes real ratio at physical |det|, derives divided
-- determinant and constant scale (normalized, usually exact). Measured where inside
-- canonical charts.

def rated (p:Camera.Strip (Raw I B) (Raw I O)) (z:Cellar (Raw I O)):ℝ:= (Matrix.of fun (i j:I)=> wedge (.inl j) (p (.inl i)) z).det
omit [Fintype O] [Fintype B] in
lemma rate_birth (p:Camera.Strip (Raw I B) (Raw I O)):rated p 0=(peek p).det:=rfl
lemma rail_treasury (r:Rail I O B)(p:Still (Raw I O))(g:Still (Raw I B))(hp:p 0=1)(hg:g 0=1)
    (ht:p =ᶠ[𝓝 0] fun x=> g (Camera.roll r.h x)*|rated r.h x|):
     p=ᶠ[𝓝 0](g ∘ Camera.roll r.h)*r.jac:=by
 have he := ht.self_of_nhds
 simp only [hp,r.flat,hg,one_mul,rate_birth,peekID] at he
 have hc:ContDiffAt ℝ ω (rated r.h) 0:=by
    unfold rated; simp_rw [Matrix.det_apply',Matrix.of_apply];exact ContDiffAt.sum fun i _=> ContDiffAt.mul contDiffAt_const (contDiffAt_prod fun j _=> Pace.wedge _ (r.smooth _))
 have hn := hc.continuousAt
 filter_upwards [ht, hn.eventually (Metric.ball_mem_nhds (rated r.h 0) (by norm_num : (0:ℝ)< 1))] with y hy hBall
 change p y=g (Camera.roll r.h y)*r.jac y
 unfold Rail.jac;rw [hy,det_mul, ← show rated r.h y= _ from rfl,det_nonsing_inv];congr 1
 rw [Real.dist_eq,rate_birth,peekID] at hBall
 change _=Ring.inverse _ * rated r.h y
 rw [Ring.inverse_eq_inv]
 generalize r.L.det =x, rated r.h y=z at *
 rcases le_total 0 x with H|H 
 · rw [abs_of_nonneg H] at he
   have hx:x=1:=by linarith
   rw [hx,inv_one,one_mul,abs_of_nonneg];rw [hx,abs_lt] at hBall;linarith
 rw [abs_of_nonpos H] at he
 have hx:x=(-1):=by linarith
 rw [hx,inv_neg,inv_one,neg_one_mul,abs_of_nonpos];rw [hx,abs_lt] at hBall;linarith

protected lemma complete (S:Peak I O A)(T:Peak I B C)(q: Rail I O B)
    (h:acclim q.h S.inside T.inside S.outside T.outside):Rail.Base S.toLedger T.toLedger q:=by
 constructor
 · exact T.orientation
 · exact S.orientation
 · exact ⟨S.inside⁻¹,S.symm,S.present⟩
 · exact ⟨T.inside⁻¹,T.symm,T.present⟩
 · rw [T.present,S.present];apply q.patrol
   have he := lean_cov h T.mirror S.mirror S.inverse T.inverse (by rw [peekID]; exact q.unitL); rw [peekID] at he;exact he
 · rw [S.warm,T.warm];exact firstRail q h
 rw [S.cold,T.cold]; exact leadzero q h

protected theorem ate (S:Peak I O A)(T:Peak I B C)(q:Camera.Strip (Raw I B) (Raw I O))(hq:∀ i,Pace (q i))(h0:Camera.roll q 0=0)(ht : silent q)
   (p:Still (Raw I O))(v:Still (Raw I B))(hp:Pace p)(hv:Pace v)(hp0:p 0=1)(hv0:v 0=1)
   (c:Port (Raw I O)) (d:Port (Raw I B))(hc: S.toLedger.printed=c+flask (Real.log ∘ p)-liftInn S.K-S.κ)(hd:T.toLedger.printed=d+flask (Real.log ∘ v)-liftInn T.K-T.κ) -- field accessor errors
   (H:c=belt (rescaleFields q) d)
   (hg:p=ᶠ[𝓝 0] fun x=>v (Camera.roll q x)* |rated q x|):
    ∃ b: Raw I B→Port (Raw I O), (∀ i:B,b (Sum.inr i)=rescaleFields q (.inr i)) ∧ belt b (T.κ+T.toLedger.connected) = S.κ+S.toLedger.connected:=by
 have hU:IsUnit (peek q):= by
    apply (isUnit_iff_isUnit_det _).mpr
    rw [isUnit_iff_ne_zero]; intro hv;have he:=hg.self_of_nhds; simp only [hp0,h0,hv0,one_mul,rate_birth,hv,abs_zero,one_ne_zero] at he
 have he {E I Y:Type}[Fintype E][Fintype I][Fintype Y](S: Peak I E Y){c:Port (Raw I E)}{p:Still (Raw I E)}(h:S.toLedger.printed=c+flask (Real.log ∘ p)-liftInn S.K-S.κ)(hp:p 0=1):
    tap 0 c =heater S.inside E+sink S.outside I:=by
    have hh:=S.toLedger.cold S.orientation
    change PowerSeries.coeff 0 (S.toLedger.printed)=0 at hh
    rw [h,map_sub,map_sub,map_add] at hh
    rw [S.warm,S.cold] at hh;simp [flask,Camera.print,hp,platen] at hh
    rw [tap,PowerSeries.coeff_zero_eq_constantCoeff]; exact eq_add_of_sub_eq' (sub_eq_zero.mp hh) -- eq_add_of_sub_eq? gives c = sink+heat
 have hr:=acclimatize ht c c d (he S hc hp0) (he T hd hv0) H
 obtain ⟨r,Hr⟩:=railize hr hU T.mirror T.inverse ht hq h0
 subst Hr
 refine ⟨r.b,fun i=>rfl,?_⟩
 apply Rail.arrived r (H:=S.toLedger) (S:=T.toLedger) {S.complete T r hr with
    a:=p,b:=v,smoothL:=hp,smoothR:=hv,fixedL:=hp0,fixedR:=hv0,haar:=rail_treasury r p v hp0 hv0 hg,
    c:=c,d:=d,born:=hc,again:=hd,forward:=H}
end Peak
end YM.RG08.Fold
