import YM.RG12.Spins.Fierce
import YM.Next.STATIONARY.Joint.OnShell
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Set Lattice Wilson RG Source Source.Drops Labels Next.Foundations Planned.AtomRegular Foliage WardBin.Lies Multi.Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {F :Type} [NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}{d:ℕ}{n:Side}{B:BudgetPoint}{t:ℝ}
lemma bareHat {f:Config G n→F}(h0:G.Simple)(h:GaugeInvariant f)(hf:Germ 4 f 1): fderiv ℝ (f∘ increment (1:Config G n)) 0 =0:=by
   apply ContinuousLinearMap.ext; intro v
   refine Stationary.slot_fixed h0 _ (fun u p=> ?_) v
   let A:=AnalyticBridge.VerifiedReset.colorMove (n:=n) u
   refine Stationary.chain_fixed (F:=f∘increment 1) A ?_ (hf.differentiableAt (by norm_num)) p
   exact Eventually.of_forall (fun v=> by simp only [Function.comp_apply,A]; rw [AnalyticBridge.VerifiedReset.exp_move,h]) -- simp ← loops?
lemma coupled4 (H:Hol G)(o:Site n)(y:Jet G)(P Q:Config G n→F)(hf:Germ 4 P 1)(hg:Germ 4 Q 1)
   (hp:fderiv ℝ (P ∘ increment 1) 0=fderiv ℝ (Q ∘ increment (1:Config G n)) 0):
   let T:= testLog H d o y; let V:=iteratedDeriv 2 T 0; let σ:=Fintype.card (OrderedFinpartition 4)
   ‖iteratedDeriv 4 (P ∘ H.testLinks d o y) 0-iteratedDeriv 4 (Q ∘ H.testLinks d o y) 0‖ ≤ (σ:ℝ)*‖leftDerivs P [V,V] 1-leftDerivs Q [V,V] 1‖:=by
    intro T V σ
    let X(P :Config G n→F) := P ∘ increment 1; let f:= X P; let g:= X Q
    have hQ : ContDiffAt ℝ 4 f 0:=hf; have hP:ContDiffAt ℝ 4 g 0:=hg
    have hH:T 0=0:= testLog_zero ..; have hh:ContDiffAt ℝ 4 T 0:= (testLog_diff ..).of_le le_top
    have hx : ContDiffAt ℝ 4 (f ∘ T) 0:= (hH.symm ▸ hQ).comp _ hh; have hY : ContDiffAt ℝ 4 (g ∘ T) 0:= (hH.symm ▸ hP).comp _ hh
    have H':=increment_testLog H d o y
    have hy(z):iteratedDeriv 4 (z ∘ H.testLinks d o y) 0= iteratedFDeriv ℝ 4 (X z ∘ T) 0 (fun _=>1):=congrArg (fun h:ℝ [×4]→L[ℝ] F=> h fun _=>1) ((H'.fun_comp z |>.iteratedFDeriv (𝕜:=ℝ) _).eq_of_nhds)
    have hyD(z)(h: ContDiffAt ℝ 4 (X z) 0) : leftDerivs z [V,V] (1:Config G n) = iteratedFDeriv ℝ 2 (X z) 0 (fun _=>V):=by
       have hF:=Next.Foundations.leftDerivs_diag (1:Config G n) V z 2 0
       rw [zero_smul,Work.G07.at_zero_increment] at hF; change leftDerivs z _ (1:Config G n)= iteratedDeriv 2 _ 0 at hF; apply hF.trans
       let L:= (ContinuousLinearMap.id ℝ ℝ).smulRight V
       have ht (Y K:Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y][NormedAddCommGroup K][NormedSpace ℝ K](f:Y→K)(L:ℝ→L[ℝ] Y)(h:ContDiffAt ℝ 4 f 0) : iteratedDeriv 2 (f ∘ L) 0= iteratedFDeriv ℝ 2 f 0 (fun _=> L 1):=by
         have hv:=h.eventually (by norm_num)
         have hp': fderiv ℝ (f ∘ L) =ᶠ[𝓝 0] (fun y=>(fderiv ℝ f (L y)).comp L):= ((show Tendsto (L:ℝ→Y) (𝓝 0) (𝓝 0) by simpa using L.continuous.tendsto 0).eventually hv).mono fun y H=> by rw [fderiv_comp y (H.differentiableAt (by norm_num)) L.differentiableAt,L.fderiv]
         let V:= fderiv ℝ f ∘ L
         have ha: DifferentiableAt ℝ (fderiv ℝ f) 0:=(h.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
         have he:DifferentiableAt ℝ (fderiv ℝ f) (L 0):=by simpa
         have h':DifferentiableAt ℝ V 0:= he.comp 0 L.differentiableAt
         unfold iteratedDeriv; simp only [iteratedFDeriv_two_apply]; rw [hp'.fderiv_eq]; change fderiv ℝ (fun y=> (V y).comp L) 0 1 1= _; rw [fderiv_clm_comp (c:=V) (d:=(fun _:ℝ=>L)) h' (differentiableAt_const L),show fderiv ℝ V 0=(fderiv ℝ (fderiv ℝ f) (L 0)).comp L from (fderiv_comp 0 he L.differentiableAt).trans (by rw [L.fderiv]),show fderiv ℝ (fun _:ℝ=>L) 0=0 from (hasFDerivAt_const L (0:ℝ)).fderiv,map_zero]; change V 0 _ + _=_; simp
       exact (ht (Directions G n) _ (X z) L h).trans (by change iteratedFDeriv ℝ 2 (X z) 0 (fun _=> (1:ℝ) • V) = _; rw [one_smul])
    have hd: fderiv ℝ (f-g) 0=0:=by rw [fderiv_sub (hQ.differentiableAt (by norm_num)) (hP.differentiableAt (by norm_num)),show fderiv ℝ f 0=fderiv ℝ g 0 from hp,sub_self]
    have he:=formed T (f-g) hh (hQ.sub hP) hH (arc_still ..) hd
    rw [hy,hy,hyD _ hQ,hyD _ hP]; change ‖iteratedFDeriv ℝ 4 (f∘T) _ _ - iteratedFDeriv ℝ 4 (g∘T) _ _‖ ≤ _
    unfold iteratedDeriv at he; rw [show (f-g)∘T=f∘T-g∘T from rfl,iteratedFDeriv_sub_apply hx hY,_root_.sub_apply,iteratedFDeriv_sub_apply (hQ.of_le (m:=(↑(2:ℕ):ℕ∞ω)) (by norm_num)) (hP.of_le (by norm_num))] at he; exact he
-- actual positive weight four observer price.Field cap.IScalar d0 treated by Ward.
theorem energyProbe (H:Hol G)(d:ℕ)(y:Jet G): ∃ A:ℝ,0 ≤ A∧∀ (n:Side)(o:Site n)(X:Support n)(v:Fin (d+1)),v.val=4 →∀ (B:BudgetPoint)(P Q:Config G n→ℂ)(c:ℝ),
   Germ 4 P 1 →Germ 4 Q 1 → fderiv ℝ (P ∘ increment 1) 0=fderiv ℝ (Q ∘ increment (1:Config G n)) 0→
   (∀ v:Directions G n,B.dirBound o v→‖leftDerivs P [v,v] 1 - leftDerivs Q [v,v] 1‖ ≤ c)→0≤c→ ‖Push.Local.sample H o X B.threshold P (y,v)- Push.Local.sample H o X B.threshold Q (y,v)‖≤ A*c :=by
     obtain ⟨M,hM,hT⟩:=testLog_bound H d 2 y
     refine ⟨Fintype.card (OrderedFinpartition 4)*(M^2),by positivity,fun n o X v hv B P Q c hP hQ hD hV hc=>?_⟩
     unfold Push.Local.sample; split
     · change ‖iteratedDeriv v.val _ _-iteratedDeriv v.val _ _‖ ≤ _; rw [hv]; have he:= coupled4 (d:=d) H o (B.threshold • y) P Q hP hQ hD
       let T:= iteratedDeriv 2 (testLog H d o (B.threshold • y)) 0
       have hp :B.dirBound o (M⁻¹ • T):=by
          intro i; change ‖M⁻¹ • T i‖ ≤ B.threshold*(1+(separation i.1 o:ℝ))^B.power
          rw [norm_smul_of_nonneg (inv_pos.mpr hM).le]
          refine (mul_le_mul_of_nonneg_left (hT n o i B.threshold B.threshold_pos.le B.threshold_le) (inv_pos.mpr hM).le).trans ?_
          rw [← mul_assoc,←mul_assoc,inv_mul_cancel₀ hM.ne',one_mul,pow_one]; exact mul_le_mul_of_nonneg_left (le_self_pow₀ (by simp) (by have h:=B.power_ge; omega)) B.threshold_pos.le
       rw [mul_assoc]; apply he.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)); change ‖leftDerivs P [T,T] 1-leftDerivs Q _ _‖ ≤ _
       have hh (F:Config G n→ℂ): leftDerivs F [T,T] 1=M^2 • leftDerivs F [M⁻¹ • T,M⁻¹ • T] 1:=by
          simpa only [List.map_cons,List.map_nil,List.length_cons,List.length_nil,smul_smul,mul_inv_cancel₀ hM.ne',one_smul] using Push.RelayDifference.left_dilate F [M⁻¹ • T,M⁻¹ • T] M (1:Config G n)
       rw [hh P,hh Q,← smul_sub,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]; gcongr; exact hV _ hp
     simp only [hv,Nat.reduceEqDiff,↓reduceIte,sub_self,norm_zero]; positivity
end YM.RG12.Spins
