import YM.TraceExtension.Swift.Flag
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Analysis Matrix
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo Zn StressFlux
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side}{s u C A T:ℝ}{k m:ℕ}
abbrev Rho(G:Gauge)(n:Side):= Directions G n × ℝ
def transit (o:Bond n) (v:G.Color) (p:Rho G n):= rung (increment 1 p.1) o v p.2
lemma voy (D:ℝ)(hd:1≤D)(k:ℕ)(G:Gauge):∃ A:ℝ,0≤ A∧ ∀ (n:Side)(o:Bond n)(v:G.Color),‖v‖≤1→∀ p:Rho G n,‖p‖≤D→∀ i,Allows k (fun x=>G.mat (transit o v x i)) p A:=by
    obtain ⟨S,hS,H⟩:=Turret.atp G k D (by positivity)
    let A:=2^k*S*S; refine ⟨A,by positivity,fun n o v hv p hp i=>?_⟩
    let U(x:Rho G n) := input G n (x.2 • phB o v)
    let L:Rho G n→L[ℝ] Directions G n:= (ContinuousLinearMap.snd ℝ (Directions G n) ℝ).smulRight (edgeColor (phB o v))
    have hV: ‖edgeColor (phB o v)‖≤ 1:=by unfold phB; simp; apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; by_cases h:j=o <;> simp [h,hv]
    have he:‖L‖≤1:=L.opNorm_le_bound zero_le_one (fun x=> (le_trans (le_of_eq (norm_smul (x.2) (edgeColor (phB o v)))) (by rw[one_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) hV).trans (norm_snd_le x))))
    have hh(x:Rho G n): U x=increment 1 (L x):=by funext i; rw[increment]; simp only [Pi.one_apply,mul_one]; unfold U; rw[input_color,map_smul]; rfl
    have hx : Allows k (fun x=>G.mat (U x i)) p S:=by simp_rw [hh]; exact pre_short L (f:=fun x=>G.mat (increment (1:Config G n) x i)) (H n 1 (L p) (((L.le_opNorm _).trans ((mul_le_mul_of_nonneg_right he (norm_nonneg p)).trans_eq (one_mul _))).trans hp) i) he
    let W(x:Rho G n):=increment (1:Config G n) x.1
    exact hx.times (f:=fun y=>U y i) (g:=fun y=>W y i) (allows_first_var (p:=p) (f:=fun y=>G.mat (increment (1:Config G n) y i)) (H n 1 p.1 ((norm_fst_le p).trans hp) i))
lemma spoutW (S:BudgetPoint) (o:Bond n)(v:G.Color)(x:Rho G n): Army (transit o v) x:= by
    let Q(x:Rho G n):= increment (1:Config G n) x.1
    exact (Army.powL (v:=fun x:Rho G n=> x.2 • phB o v) (by fun_prop)).mul (show Army Q x from fun i=> by
       let V:= incrementA (1:Config G n) x.1 i
       exact ContDiffAt.comp (f:=Prod.fst) (g:=fun p:Directions G n=>G.mat (increment (1:Config G n) p i)) x V contDiffAt_fst)
lemma spine(G:Gauge)(D:ℝ)(hd:1 ≤ D)(k:ℕ):∃ A:ℝ,0 ≤ A∧ ∀ (n:Side)(F:Peat G n)(o:Bond n)(v:G.Color)(r s C:ℝ) (B:Support n),‖v‖≤1→ 0 < s→ s≤1 → Splendor F B k C A → 2 ≤ k →
    ∀ x:Rho G n,‖x‖ ≤ D→ Allows k (fun y=> F (transit o v (s • y))) x (C*evenR 2 D*s^ (2:ℕ)):=by
    obtain ⟨A,hA,H⟩:=voy D hd k G; refine ⟨A,hA,fun n F o v r s C B hv hs hp h he x hx=> ?_⟩
    let f(y:Rho G n):=F (transit o v y); let U:=transit o v; have hz: U 0=1:=by simp [U,transit,rung,Work.G07.at_zero_increment]
    have hi(p:Rho G n)(hp:‖p‖ ≤D): Allows k f p C:= h.tickets _ U _ (H n o v hv _ hp)
    have hn := hi 0 (by rw[norm_zero]; linarith); have hm: Army U 0:=fun j=> (H n o v hv 0 (by rw [norm_zero]; linarith) j).analytic
    let g:=content ∘ U; have hg:g 0=0:=by simp [g,hz]
    obtain ⟨hT,hF⟩:= h.cloth; change Perfect.braid (F ∘ input G n) _ _ _ at hF
    have hu : Perfect.braid f (fun _=>0) 0 1:=by refine (braided (n:=1) (H:=(F ∘ input G n) ∘ g) ?_).trans (wove (w:=g) (hg.symm ▸ hF) (hg.symm ▸ (show Cleric _ from hT).dye) contDiffAt_const (hm.logL hz)); filter_upwards [(show Tendsto U _ (𝓝 1) from hz ▸ hm.cont.tendsto).eventually content_encodes] with x hx; exact congr_arg F hx.symm
    apply heaven (f:=f) 2 D (by linarith only[hd]) hs.le hp (fun x hx=> hi x (hx.trans (mul_le_of_le_one_right (by linarith only[hd]) hp))) hn.nonneg he _ x hx; intro i hv
    rw[hu i (by omega),iteratedFDeriv_zero_fun,Pi.zero_apply,norm_zero]; positivity[hn.nonneg]
lemma spineY (G:Gauge)(D:ℝ)(hd:1 ≤ D)(k:ℕ):∃ A K:ℝ,0≤ A∧1 ≤ K∧∀ (n:Side)(Y:Gal G n)(o:Bond n)(v:G.Color)(s C:ℝ),0≤ C→‖v‖≤1→0 < s→ s≤1→Y 1=0→ Climate Y k C A→ 1≤ k→
   ∀ x:Rho G n,‖x‖≤D→ Allows k (fun y=> clamor o Y v (transit o v (s • y))) x (K*C*s):=by
   obtain ⟨A,hA,H⟩:=voy D hd (k+1) G
   let L:= (WithLp.linearEquiv 2 ℝ (G.ColorIndex→ℝ)).symm.toContinuousLinearMap
   let P:= (‖innerSL ℝ (E:=G.Color)‖ * ‖L‖) * evenR 1 D
   have he:0≤ P:=by unfold P evenR; positivity
   refine ⟨A,1+P,hA,le_add_of_nonneg_right he,fun n Y o v s C hC hv hs hp ht hz hk x hx=>?_⟩
   let U:=transit o v; have h₁:U 0=1:=by simp [U,transit,rung,Work.G07.at_zero_increment]
   have hQ(i p)(hp:‖p‖≤D):Allows k (fun x=> Y (U x) i) p C:= (hz.laps _ _ _ (H n o v hv p hp) i).order (by omega)
   let F(y:Rho G n):= clamor o Y v (U y); let Q:=(innerSL ℝ (E:=G.Color)).flip
   let T:= ‖innerSL ℝ (E:=G.Color)‖ * (‖L‖ * C)
   have hu(x:Rho G n)(hx:‖x‖≤D): Allows k F x T:=by
       unfold F clamor; simp_rw[zeal]
       have hm: Allows k (fun y=>edgeColor (Y (U y)) o) x (‖L‖ * C):= (allows_pi (f:=fun y:Rho G n=>fun i=>edgeColor (Y (U y)) o i) hC (fun i=> hQ (o.1,Exterior.coord o.2,i) x hx)).linear L le_rfl
       have hv':‖Q v‖≤‖innerSL ℝ (E:=G.Color)‖:= (Q.le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hv).trans_eq (ContinuousLinearMap.opNorm_flip ..))
       exact hm.linear (Q v) hv'
   have h₀:=hu 0 (by rw[norm_zero];linarith); apply (heaven (f:=F) 1 D (by positivity) hs.le hp (fun y hy=>hu y (hy.trans (mul_le_of_le_one_right (by positivity) hp))) h₀.nonneg hk _ x hx).mono
   · rw [pow_one]; apply mul_le_mul_of_nonneg_right _ hs.le
     exact (le_of_eq (show T*evenR 1 D=P*C by unfold P T; ring)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hC)
   intro i hi; obtain rfl:i=0:=by omega
   rw[norm_iteratedFDeriv_zero,show F 0=0 from ?_]; · rw[norm_zero]; positivity[h₀.nonneg]
   unfold F clamor; rw[h₁,ht,zero_dotProduct]
end YM.Trace.Swift
