import YM.TraceExtension.Quince.Unison
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Wilson Finset Source Extra.Histories Labels
open Push Local Next.Foundations Cub
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{R:Rep G n}{o:Site n}{H:Hol G}{d:ℕ}{F:Frame G d}{Y:SectionData F}{x:F.Coeff}
section Pierce
variable {p:BudgetPoint}{I:Type*}{f:I → Config G n→ℂ}{u:I→ℝ}{X:I→Support n}{c a:ℝ}{b:ℕ}(ha:∀ i,p.Regular (X i) (f i))(hv:∀ i,p.supBounds o (X i) (f i) (u i))(hc:SumBudget (fun i=>p.mass (X i) (u i)) a)(ht:∀ i,o ∈ X i)(hb:∀ i,Nonwrapping (X i) o→H.PiVanish d o (f i))
variable (he:10*(b*(4*p.B+2)+2*p.B)< n.val)(h:∀ V∈dent p,Local.presented Y o p.threshold x V=∑' i,f i V)(hy:Local.Readable H Y p n c)
include hv hc ht he
lemma husk (W':I→ℂ)(hq:∀ i,‖W' i‖ ≤ u i)(hP:Summable u)(S:Set I)(h:∀ i∈ S,¬ Nonwrapping (X i) o):
    ‖∑' i: ↑S,W' i.val‖ ≤ Real.exp (-p.supportExponent*b)*a:=by
   let w:=Real.exp (-p.supportExponent*b); have hw:0≤w:= (Real.exp_pos _).le
   have hh : Summable (fun i=> ‖W' i‖):= .of_nonneg_of_le (fun _=>norm_nonneg _) hq hP
   let f(i):= p.mass (X i) (u i); let g(i):=w*f i
   have he'(i: ↑S): ‖W' i.val‖≤ g i.val:= (hq _).trans (prime_fuel he (ht i.val) (h i.val i.property) (hv i.val).1)
   apply (norm_tsum_le_tsum_norm (show Summable (fun i: S=> ‖W' i.val‖) from hh.subtype _)).trans
   have h':Summable g:=hc.2.1.mul_left w; have hz:Summable (fun i:↑S=> g i.val):=h'.subtype _
   apply ((show Summable (fun i:↑S=> ‖W' i.val‖) from hh.subtype _).tsum_le_tsum he' hz).trans; refine le_trans ((show (∑' i:↑S,g i.val) ≤ ∑' i,g i from ?_)) ?_
   · rw [← h'.tsum_subtype_add_tsum_subtype_compl S]; exact le_add_of_nonneg_right (tsum_nonneg (fun i =>mul_nonneg hw (hc.1 i.val)))
   unfold g at *
   rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hc.2.2 hw
include ha hv hc ht hb he h hy
lemma loom_s (Q : Probe G d): ‖Local.runProbe F Q x‖ ≤ Local.partPrice H Q*(Cub.gaugeMeter d * (Real.exp (-p.supportExponent*b)*a)):=by
   have hx:Summable u:= .of_nonneg_of_le (fun i=>(hv i).1) (fun i=>p.loMass _ _ (hv i).1) hc.2.1
   let W:Set I:= {i|Nonwrapping (X i) o}
   let g:=Local.presented Y o p.threshold x
   let X':= Y.footprint o
   have hg:= (Local.presented_good o hy x).1
   have hsX:Nonwrapping X' o:= nonwrapping_placement _ _ hy.fit
   have hD:weighted H F o X' p.threshold g=x:=by
       have ht : Local.project H o X' g d= F.coords.symm (F.scaled p.threshold⁻¹ x):=project_eq (placed_reads Y o hy.fit hy.sound _)
       rw [weighted,ht,F.coords.apply_symm_apply,F.scaled_inv p.threshold_pos.ne']
   let K:= Real.exp (-p.supportExponent*b)*a; let A:= Real.exp (-p.supportExponent*b); have hA:0≤A:= (Real.exp_pos _).le; have hv':0≤a:=(tsum_nonneg hc.1).trans hc.2.2
   let M:=Local.partPrice H Q; let m:= Cub.gaugeMeter d
   have hP(D:Finset W): ‖Local.sample H o X' p.threshold g Q‖ ≤ M*(m*((∑' i: ↑((↑D:Set W)ᶜ:Set W),u i.val.val)+K)):=by
       let G':=∑ i∈D,f i.val
       have hp: Chart d G' 1:=by unfold Chart G'; simp_rw[Function.comp_def, Finset.sum_apply]; exact ContDiffAt.sum fun i _=> ((ha _).smooth 1 (one_healthy (X i.val) _ p.threshold_pos.le)).of_le (Nat.cast_le.mpr hy.order)
       let R:= (∑' i: ↑((↑D:Set W)ᶜ:Set W),u i.val.val)
       have hf : logSample H o X' p.threshold (G' ∘ increment 1) Q=0:=by
           rw [score,Local.sample,if_pos hsX]; simp only[Function.comp_def,G',Finset.sum_apply];
           let F(i:W)(y:ℝ):ℂ:= f i.val (H.testLinks d o (p.threshold • Q.1) y); let k:=Q.2.val
           have h(i:W) : ContDiffAt ℝ (k:WithTop ℕ∞) (F i) 0 ∧ iteratedDeriv k (F i) 0=0:=by obtain ⟨hx,ht⟩:=hb i.val i.property (p.threshold • Q.1); have hk:k ≤ d:= Nat.le_of_lt_succ Q.2.isLt; exact ⟨hx.of_le (Nat.cast_le.mpr hk),ht _ hk⟩
           change iteratedDeriv k (fun y=> ∑ i ∈ D,F i y) 0=0; rw[iteratedDeriv_fun_sum]; apply Finset.sum_eq_zero (fun i _=> (h i).2); exact fun i _=> (h i).1
       have HC:= Cub.speedTest H X' Q ((show p.Regular X' g from hg).smooth 1 (one_healthy X' _ p.threshold_pos.le)|>.of_le (Nat.cast_le.mpr hy.order)) hp (B:=p) (c:=R+K) (o:=o) ?doPrice
       case doPrice =>
          intro l ht' he'; let x (i:I):=leftDerivs (f i) l 1; let A':= (∑ i∈D,x i.val); let B:= (∑' i:↑(Wᶜ:Set I),x i.val); let C:= (∑' i:↑((D:Set W)ᶜ:Set W),x i.val.val)
          have hu(i:I):‖x i‖ ≤ u i:= (hv i).2 1 (one_healthy _ _ p.threshold_pos.le) _ (ht'.trans hy.order) he'
          have hz: Summable (fun i=>‖x i‖):=.of_nonneg_of_le (fun _=>norm_nonneg _) hu hx
          have hx' : ‖B‖ ≤ K:= husk hv hc ht he x hu hx Wᶜ (fun i hi=> hi)
          have hh : ‖C‖ ≤ R:= (norm_tsum_le_tsum_norm ((hz.subtype _).subtype _)).trans (((hz.subtype _).subtype _).tsum_le_tsum (fun i=>hu _) ((hx.subtype _).subtype _))
          rw [line_fare ha hv hx h 1 (dent1 _) l (ht'.trans hy.order) he',left_sum D _ _ l (fun i _=> (show Local.Chart p.order (f i.val) 1 from (ha _).smooth _ (one_healthy _ _ p.threshold_pos.le))) (ht'.trans hy.order)]; change ‖(∑' i:I,x i)-A'‖ ≤ _
          rw [← hz.of_norm.tsum_subtype_add_tsum_subtype_compl W, show (∑' i:W,x i.val)=A'+C from (show A'+C=_ from (hz.of_norm.subtype (· ∈ W)).sum_add_tsum_subtype_compl D).symm]; change ‖A'+C+B-A'‖≤R+K; rw [show A'+C+B-A'= C+B by abel]; exact (norm_add_le ..).trans (add_le_add hh hx')
       have hP:=Local.compareSample hg hy.order hy.power HC; rwa [hf,sub_zero] at hP
   let Wβ:=fun i:W=>u i.val; have ht:=tendsto_tsum_compl_atTop_zero Wβ; have he:(Tendsto (fun D:Finset W=> M*(m*((∑' i:↑((D:Set W)ᶜ:Set W),u i.val.val)+K))) atTop (𝓝 (M*(m*K)))):=by
       have h := ht.add_const K; rw [zero_add] at h; have H' := h.const_mul m|>.const_mul M; exact H'
   rw[← show weighted H F o X' p.threshold g=x from hD,← Local.sample_eq F H o p.threshold hg hy.order]; exact ge_of_tendsto he (Eventually.of_forall hP)
end Pierce
end YM.PhysicalNext.Repeat.Quince
