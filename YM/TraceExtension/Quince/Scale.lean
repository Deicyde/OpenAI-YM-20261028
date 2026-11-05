import YM.TraceExtension.Quince.Precinct
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Precision Labels Source Source.Drops
open Push.Local (Probe)
open Push Planned.PrimaryIntegral295 PPX Flutes Place Bazaars Exterior Streets Postcards WardBin.Lies Cabins Bid
open Next Next.Foundations JointLoad JointLoad.Heir Bloch Carrier Next.Free Laurent Cub Finset
open MultiNext.SignedSource
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge} {n c f:Side}
variable {k p d r j u:ℕ}{B:BudgetPoint}{S:StepData c f}{T:Tube G S}
section income
variable {L:Side}{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{q:Cover→ℝ} {A₁ B₁: Cover→E}{x:Cover}{s D d₁ d₂:ℝ}{n r:ℕ}(hs:0<s)(hq:Width s D q)(hf:∀ i,‖A₁ i‖ ≤ d₁*liftCost n i)(hF:∀ i,‖B₁ i‖ ≤ d₂*liftCost n i)(hp:∀ i:Cover,size i < r→ A₁ (x+i)=B₁ (x+i))(h1:0≤d₁)(h2:0≤d₂)
-- summable priced differences
include hs hq h1 h2 hf hF hp
lemma stream_scale : ‖stream q x A₁-stream q x B₁‖ ≤ Real.exp (-(s/2)*r)*(d₁+d₂)*liftCost n x*widthCost (s/2) n*D:=by
   let F(i:Cover):= q i • A₁ (x+i)-q i • B₁ (x+i); have hh:=stream_income hs hq x n h1 hf; have hv:= stream_income hs hq x n h2 hF; rw [stream,stream,← hh.2.1.of_norm.tsum_sub hv.2.1.of_norm]
   let M:= Real.exp (-(s/2)*r)*(d₁+d₂)*liftCost n x*widthCost (s/2) n
   let b(i:Cover) := Real.exp (s*size i)*‖q i‖
   have hz:= zero_le_one.trans (widthCost_ge (half_pos hs) n); have hY:0≤ M:=by unfold M; positivity [liftCost_pos n x]
   have hx(i:Cover): ‖F i‖ ≤ M*b i:=by
        by_cases h : size i < r
        · rw [show F i=0 from by unfold F; rw [hp i h];simp,norm_zero]; unfold b; positivity
        let X:=liftCost n x
        have he: liftCost n (x+i) ≤ X*widthCost (s/2) n*(Real.exp (-(s/2)*r)*Real.exp (s*size i)):=by
            apply (liftCost_add ..).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (liftCost_pos ..)
            apply (widthBill _ (half_pos hs) n _ (by positivity : (0:ℝ) ≤ size i)).trans
            rw [← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hz; apply Real.exp_monotone; have ht:(r:ℝ) ≤ size i:= Nat.cast_le.mpr (le_of_not_gt h); nlinarith
        apply (norm_sub_le ..).trans; rw [norm_smul,norm_smul, ← mul_add]; calc
            _ ≤ ‖q i‖*((d₁+d₂)*liftCost n (x+i)) := by apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [add_mul]; exact add_le_add (hf _) (hF _)
            _ ≤ ‖q i‖*((d₁+d₂)*(X*widthCost (s/2) n*(Real.exp (-(s/2)*r)*Real.exp (s*size i)))):=by gcongr
            _ = M*b i:=by unfold b M X;ring
   have he:Summable (fun i=> M*b i):= by exact_mod_cast hq.2.1.mul_left M
   have hh:Summable (fun i=> ‖F i‖):= .of_nonneg_of_le (fun i=> norm_nonneg _) hx he
   refine (norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum hx he).trans ?_)
   rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hq.2.2 hY
end income
-- normalized differences
section regen
variable {b m k:ℕ}{u t π σ M C' N:ℝ} {Q:Probe G d}(H:Hol G){X:Support f}{Y:Support c}
-- argument base.Gen kernels normalized
variable (hV:T.R.A0.strip σ M)(hσ:0<σ)(hM:0≤M)(h:Blend π t u)
   (hi:20*(m+b+1)< c.val)(hh:∀ i∈X,halo b {S.ratio.parent i}⊆Y)(hY:∀ i∈Y,separation 0 i ≤ m)
abbrev poleQ (Q:Probe G d)(H:Hol G)(m:ℕ)(T:Tube G S)(u t:ℝ):ℝ→Directions G f:= tapes S T.R.A0 ∘ Flutes.lode Q H c u t m
abbrev ownQ (Q:Probe G d)(k m:ℕ)(T:Tube G S)(u t:ℝ): Directions G f := fun i=> (applyLine T.R.A0 (Ramble.lamina Q k t u)) (lift i.1) i.2
lemma meant_o (Q:Probe G d)(m:ℕ)(T:Tube G S)(h:0<t)(s:ℝ): Heir.route T (Heir.crop (S.ratio.parent 0) m (1:Site c→G.El) (H.testLinks d 0 (u • Q.1) s))= t • poleQ Q H m T u t s:=by
    rw[anchor0 S.ratio, show (H.testLinks _ _ _ _)=Flutes.fare Q H c u s from rfl, stole _ _ h, map_smul, walked];rfl
lemma poleQs (Q:Probe G d)(m:ℕ)(T:Tube G S)(u t:ℝ): ContDiffAt ℝ ω (poleQ Q H m T u t) 0:=by
   let φ:= Flutes.lode Q H c u t m; have ht : ContDiffAt ℝ ω φ 0:=by
       apply contDiffAt_pi.mpr; intro i; obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv c).surjective i; unfold φ; rw [nose]; split <;> first|exact Ramble.script_smooth ..| exact contDiffAt_const
   exact ContDiffAt.comp _ (tapes S T.R.A0).contDiff.contDiffAt ht
lemma poleQ_0 (Q:Probe G d)(m:ℕ)(T:Tube G S)(u t:ℝ): poleQ Q H m T u t 0=0:=by
   have hκ: Flutes.lode Q H c u t m 0=0:=by
       unfold Flutes.lode Cabins.patched; ext1 i; unfold Cabins.room; split; · simp [Flutes.fare_zero,Lattice.gauge]
       rfl
   unfold poleQ; rw[Function.comp_apply,hκ,map_zero]
-- isle cost
variable (hs: Carries (Ramble.lamina Q k t u) (d*k) C')
include hσ hV hM hi hh hY hs
set_option maxHeartbeats 450000 in
lemma clarity (i:Bond f)(he:i.1∈ X):
    ‖iteratedDeriv k (poleQ Q H m T u t) 0 i-ownQ Q k m T u t i‖ ≤ (4:ℝ) * (Real.exp (-(σ/2)*b)*(C'+C')*(1+4*(m:ℝ))^(d*k)*widthCost (σ/2) (d*k)*M):=by
    let φ:= Flutes.lode Q H c u t m; let F:=iteratedDeriv k φ 0
    have hx : ContDiffAt ℝ ω φ 0:= by
        apply contDiffAt_pi.mpr; intro i; obtain ⟨i,rfl⟩ := (Work.E03.poleEquiv c).surjective i; unfold φ; rw[nose]; split <;> first| exact Ramble.script_smooth ..| exact contDiffAt_const
    rw [show iteratedDeriv k (poleQ Q H m T u t) 0= tapes S T.R.A0 F from DFunLike.congr_fun ((tapes S T.R.A0).iteratedFDeriv_comp_left hx (show (k:WithTop ℕ∞) ≤ ω from le_top)) (fun _=>1)]
    let s:= lift i.1; let g:=S.ratio; let Tp:= T.R.A0; let x:=cellar S.patch.L s
    have hu:x=lift (S.ratio.parent i.1):=roomK hi hh hY i.1 he
    let V:= aboard G c F; let W:=Ramble.lamina Q k t u
    have ht: tapes S Tp F i=applyLine Tp V s i.2:=by
       have ht:=street g Tp (show Whole Tp from ⟨σ,M,hσ,hV⟩) F; rw [← show _=applyLine Tp V from (show aboard G f _= _ from ht)]; unfold aboard collect; unfold s; rw [wrap_lift]; rfl
    have hp(z:Cover)(a:Axis):V z a= if separation 0 (wrap c z) ≤ m then W (lift (wrap c z)) a else 0:=by
       let e:= Work.E03.poleEquiv c (wrap c z,a); let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Exterior.Body 1 c=>G.Color) e
       have hh : (L ∘ φ)=(if separation 0 (wrap c z) ≤ m then Ramble.script Q t u (lift (wrap c z)) a else 0):= nose ..
       change L (iteratedDeriv k φ 0)= _
       rw [show L (iteratedDeriv k φ 0)=iteratedDeriv k (L ∘ φ) 0 from (DFunLike.congr_fun (L.iteratedFDeriv_comp_left hx le_top) (fun _:Fin k=>1)).symm, hh]; split; · rfl
       simp
    have h0(z:Cover)(a:Axis): ‖V z a‖ ≤ C'*liftCost (d*k) z:=by
       rw [hp]; split
       · rename_i hx; apply (hs.2 (lift (wrap c z)) a).trans; apply mul_le_mul_of_nonneg_left _ hs.1; unfold liftCost; gcongr; exact sum_le_sum fun i _=> below_wrap c z i
       rw [norm_zero]; exact mul_nonneg hs.1 (liftCost_pos ..)
    have hy: size x≤4*m:=by
       rw [hu]; apply Flutes.cards; simpa only [sub_zero] using Work.E08.lift_mem_box (hY _ (hh _ he (halo_subset _ _ (Finset.mem_singleton_self _))))
    let Z:=Real.exp (-(σ/2)*b)*(C'+C')*(1+4*(m:ℝ))^(d*k)*widthCost (σ/2) (d*k)*M
    unfold ownQ; rw [ht,applyLine,applyLine,← sum_sub_distrib]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> Z) (fun a _=>?_)).trans ?_)
    · let Q':=member Tp s i.2 a
      have hh (z:Cover)(h:size z<b): V (x+z) a=W (x+z) a:=by rw [hp]; obtain ⟨hv,h⟩:=marginW hi hh hY _ he z h.le; rw[if_pos (show separation (0:Site c) (wrap c (x+z)) ≤ m from hv),show lift (wrap c (x+z))=x+z from h]
      apply (stream_scale (hf:=fun i=>h0 i a) (hF:=fun i=>hs.2 i a) hσ (hq:=(show Laurent.Width σ M Q' from hV _ _)) (hp:=hh) hs.1 hs.1).trans; unfold Z; have hx:=zero_le_one.trans (widthCost_ge (half_pos hσ) (d*k)); have h:=hs.1; change _ ≤ _; unfold liftCost; gcongr; exact_mod_cast hy
    simp [Axis,Z]
end regen
end YM.PhysicalNext.Repeat.Quince
