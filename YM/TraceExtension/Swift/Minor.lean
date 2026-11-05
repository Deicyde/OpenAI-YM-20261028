import YM.TraceExtension.Swift.Ledge
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Analysis
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo Zn
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {m k i:ℕ}{s C:ℝ}{F:X×ℝ→Y} {x:X}
open Outer.Nodes (loc)
def dulect (m:ℕ)(s:ℝ)(F:X×ℝ→Y)(x:X) := duel m s (fun t=> F (x,t))-s • D (0,1) F (x,0)
lemma pretty (h:ContDiff ℝ ω F): ContDiff ℝ ω (dulect m s F) :=by
    unfold dulect duel; refine (ContDiff.sum (fun i _=> contDiff_const.smul ((h.comp (f:=fun x=>(x,_)) (contDiff_id.prodMk contDiff_const)).sub (h.comp (f:=fun x=>(x,_)) (contDiff_id.prodMk contDiff_const))))).sub (contDiff_const.smul ((contDiff_iff_contDiffAt.mpr fun x=> dSmooth (f:=F) (u:=((0,1):X ×ℝ)) (x:=x) (h.contDiffAt) (by simp)).comp (f:=fun x=>(x,_)) (contDiff_id.prodMk contDiff_const)))
lemma viD (h:DifferentiableAt ℝ F (x,s))(v:X): D v (fun y=> F (y,s)) x=D (v,0) F (x,s):=by
   let L:=ContinuousLinearMap.inl ℝ X ℝ; let U(y:X):X×ℝ :=(y,s); have he:HasFDerivAt U L x:= (hasFDerivAt_id x).prodMk (hasFDerivAt_const s _)
   unfold D; rw [show (fun y=> F (y,s))= F ∘ U from rfl,(h.hasFDerivAt.comp x he).fderiv];rfl
lemma dis (h:DifferentiableAt ℝ F (x,s)) : D (0,1) F (x,s)=deriv (fun t=> F (x,t)) s:= by
   let L: ℝ→L[ℝ] X×ℝ:= ContinuousLinearMap.inr ..; let g(t:ℝ):= (x,t); have ht:HasFDerivAt g L s:= (hasFDerivAt_const ..).prodMk (hasFDerivAt_id _); exact ((h.hasFDerivAt.comp s ht).hasDerivAt.deriv).symm
lemma duel_step (m:ℕ)(s:ℝ)(h:ContDiff ℝ ω F)(v:X): D v (dulect m s F)= dulect m s (D (v,0) F):=by
   have ht(x:X)(t:ℝ): DifferentiableAt ℝ (fun x=>F (x,t)) x:=((h.comp (f:=fun x=> (x,t)) (contDiff_id.prodMk contDiff_const)).contDiffAt.differentiableAt (by simp))
   let Z:=D ((0,1):X ×ℝ) F; let P:=D (v,(0:ℝ)) F; have hp:ContDiff ℝ ω P:=contDiff_iff_contDiffAt.mpr fun x=> dSmooth h.contDiffAt _ (by simp); have hZ:ContDiff ℝ ω Z:=contDiff_iff_contDiffAt.mpr fun x=> dSmooth h.contDiffAt _ (by simp)
   let f(x:X):=∑ i∈range m,wage m i • (F (x,loc i*s)-F (x,0)); have hf: ContDiff ℝ ω f:= ContDiff.sum (fun i _=> contDiff_const.smul ((h.comp (contDiff_id.prodMk contDiff_const)).sub (h.comp (contDiff_id.prodMk contDiff_const))))
   let U(x:X):= Z (x,(0:ℝ)); have hu:ContDiff ℝ ω U:=hZ.comp (contDiff_id.prodMk contDiff_const)
   ext1 x; change fderiv ℝ (fun x=> f x - s • U x) x v = _
   rw [fderiv_fun_sub (hf.contDiffAt.differentiableAt (by simp)) (show DifferentiableAt ℝ (fun z=>s • U z) x from ((hu.contDiffAt.const_smul (c:=s)).differentiableAt (by simp))), fderiv_fun_const_smul (c:=s) (hu.contDiffAt.differentiableAt (by simp))]; change D v f x - s • D v U x = duel m s _- _
   have hh : D v U x=D ((0,1):X×ℝ) P (x,0):= (viD (F:=Z) (hZ.contDiffAt.differentiableAt (by simp)) v).trans (commuteD (h.contDiffAt.of_le le_top) ..)
   rw [hh]; apply congr_arg₂ _ _ rfl
   unfold f D duel
   rw [fderiv_fun_sum]; rw [_root_.sum_apply]; refine Finset.sum_congr rfl fun i _=> ?_
   · rw [fderiv_fun_const_smul, fderiv_fun_sub (ht ..) (ht ..)]; swap; · exact (ht ..).sub (ht ..)
     exact congr_arg (wage m i • ·) (congr_arg₂ (· - ·) (viD (h.contDiffAt.differentiableAt (by simp)) v (F:=F) (x:=x) (s:=loc i*s)) (viD (h.contDiffAt.differentiableAt (by simp)) v (F:=F) (x:=x) (s:=0)))
   intro i _; exact ((ht x _).sub (ht x _)).const_smul _
lemma carapace {f:X→Y}(h:Allows (k+1) f x C)(u:X):Allows k (D u f) x (‖u‖*C):=by
   let T:=(ContinuousLinearMap.apply ℝ Y u)
   have ht: ‖T‖ ≤ ‖u‖:= T.opNorm_le_bound (norm_nonneg _) (fun p=> (p.le_opNorm _ |>.trans (mul_comm ..).le))
   have hx:Allows k (fderiv ℝ f) x C:=⟨h.analytic.fderiv_right (by simp),fun m hp=>by rw[norm_iteratedFDeriv_fderiv]; exact h.norm_le _ (Nat.succ_le_succ hp)⟩
   exact hx.linear T ht
lemma compass (h:ContDiff ℝ ω F)(hm:0 < m)(he:0<s)(hf:∀ t:ℝ,0≤ t → t ≤ kettle m*s→Allows (k+m+1) F (x,t) C) : ‖iteratedFDeriv ℝ k (dulect m s F) x‖ ≤ tome m*C*s^(m+1):=by
   induction k generalizing F C with
   | zero=>
       rw [norm_iteratedFDeriv_zero,dulect, dis]; swap; · exact h.contDiffAt.differentiableAt (by simp)
       refine toll _ hm s he (fun t=>F (x,t)) fun t hv hu=>?_; let L:=ContinuousLinearMap.inr ℝ X ℝ; let v(t:ℝ):=F (x,t); let Z(p:X×ℝ):=F ((x,0)+p); have hz: v= Z ∘ L:= funext fun t=> by simp [v,Z,L]
       have ht: Allows (m+1) Z (L t) C:=by
           have h':(x,0)+L t=(x,t):=by simp[L];
           refine ⟨(h.comp (f:=fun p=> ((x,0):X ×ℝ)+p) (contDiff_const.add contDiff_id)).contDiffAt,fun i hi=>?_⟩; unfold Z; rw[iteratedFDeriv_comp_add_left,h']; exact (hf _ hv hu).norm_le _ (by omega)
       change Allows (m+1) v t C; exact hz.symm ▸ pre_short L ht (L.opNorm_le_bound zero_le_one (fun x=> by simp [L]))
   | succ k ih =>
      have hc:= (hf 0 le_rfl (by positivity [Outer.Nodes.loc_pos m])).nonneg
      have hd(v:X):ContDiff ℝ ω (D ((v,0):X×ℝ) F):= contDiff_iff_contDiffAt.mpr fun x=> dSmooth (h.contDiffAt (x:=x)) _ (by simp)
      have hp(v:X)(x':ℝ)(ha:0 ≤ x')(ht:x'≤ kettle m*s): Allows (k+m+1) (D ((v,0):X×ℝ) F) (x,x') (‖v‖ * C):=by simpa using carapace (k:=k+m+1) (show Allows (k+m+1+1) F (x,x') C from (by rw[show k+m+1+1=k+1+m+1 by omega]; exact hf x' ha ht)) ((v,0):X ×ℝ)
      refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (mul_nonneg (tome0 _) hc) (by positivity)) (fun v=>?_); rw [← Fin.cons_self_tail v, Analysis.cons_inner (((pretty h (m:=m) (s:=s)).of_le le_top).contDiffAt),duel_step m s h]; apply ((ContinuousMultilinearMap.le_opNorm ..).trans (le_trans (mul_le_mul_of_nonneg_right (ih (hd (v 0)) (hp (v 0))) (by positivity)) (le_of_eq ?_))); rw[Fin.prod_univ_succ];simp only [Fin.cons_self_tail,Fin.tail]; ring
lemma attend (h: ContDiff ℝ ω F)(hm:0 < m)(he:0 < s)(hf:∀ t:ℝ,0 ≤ t → t ≤ kettle m*s→Allows (k+m+1) F (x,t) C) : Allows k (dulect m s F) x (tome m*C*s^(m+1)):= ⟨(pretty h).contDiffAt, fun i hi=> compass (k:=i) h hm he fun t h h'=> (hf t h h').order (by omega)⟩
end YM.Trace.Swift
