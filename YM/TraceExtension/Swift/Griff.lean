import YM.TraceExtension.Swift.Orca
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Set Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Analysis Matrix Metric
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits Pills Loft Xo Zn StressFlux
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {n:Side}{k m:ℕ}
-- resource-sharp FD. analytic scaled fluct over arbitrary near box all simultaneous coordinates.
def rumba(m:ℕ)(Y:Gal G n)(F: Peat G n)(h:ℝ)(e:Bond n) (x:G.Color)(U:Config G n):ℝ:= duel m h (orbC Y F U e x)-h •deriv (orbC Y F U e x) 0
def powerF(o:Bond n)(v:G.Color)(F:Peat G n)(s:ℝ)(p:Rho G n):= science o v F (increment 1 (s • p.1)) (s*p.2)
def Orpus (o:Bond n) (v:G.Color)(F:Peat G n)(Y:Gal G n)(s:ℝ)(p:Rho G n):= orbC Y F (increment 1 (s • p.1)) o v (s*p.2)
def zeff (T A s:ℝ):=2*(T*evenR 2 A*s^2)
def Spells (G:Gauge)(A D':ℝ)(k m:ℕ)(o:Bond n) (v:G.Color) (s h T:ℝ) (F: Peat G n): Prop:=
    let L:=k+m+1; ∀ x:Rho G n, ‖x.1‖≤ A→0≤ x.2→x.2≤ kettle m*(h/s) → Allows L (fun v'=>Real.exp (powerF o v F s v')) x (composeCost L D' (zeff T A s))
private lemma backF(o:Bond n) (v:G.Color) (F:Peat G n)(p:Rho G n) (s:ℝ): powerF o v F s p = F (transit o v (s • p))-F (transit o v (s • (p.1,0))):=by unfold powerF science transit;simp[rung]
private lemma grace(G:Gauge)(A:ℝ)(ha:1 ≤ A)(k m:ℕ)(hm:1≤ m) : ∃ C D:ℝ,0≤ C∧ 0≤ D∧∀ (n:Side)(P:Support n)(F: Peat G n)(s h T:ℝ)(o:Bond n)(v:G.Color), ‖v‖≤1→ 0≤ T→
    0 < s→s≤1→0<h→ kettle m*(h/s)≤ A→ (zeff T A s)*(kettle m*(h/s))≤ 1→ Splendor F P (k+m+1) T C→ Spells G A D k m o v s h T F:=by
    obtain ⟨C,hC,Hc⟩:= spine G A ha (k+m+1)
    obtain ⟨D,hD,H⟩:=exists_allows (f:=Real.exp) (s:=closedBall 0 1) (isCompact_closedBall _ _) (fun x hx=>Real.contDiff_exp.contDiffAt) (k+m+1)
    refine ⟨C,D,hC,hD,fun n P F s h T o v hv ht hs he hu hA hx hh=>?_⟩
    intro y hy hT hY
    let L:=k+m+1; let z:= T*evenR 2 A*s^2; let K:=zeff T A s; let R:= Rho G n;let p:=k+m+1;let f:=powerF o v F s
    let U(x:Rho G n):=F (transit o v (s • x)); have hZ(x:Rho G n)(hx:‖x‖≤ A): Allows L U x z:= Hc n F o v 0 s T P hv hs he hh (by omega) x hx
    let B: Rho G n→L[ℝ] Rho G n:= ContinuousLinearMap.inl ℝ (Directions G n) ℝ ∘L ContinuousLinearMap.fst ..; have hB:‖B‖≤1:= B.opNorm_le_bound zero_le_one (fun v=>by rw [one_mul]; simpa[B] using norm_fst_le v)
    have hf(x:Rho G n)(hx:‖x‖≤A): Allows L f x K:=by
        rw [show f = U - (U ∘ B) from funext (fun p=>backF o v F p s)]
        have he:= pre_short B (f:=U) (hZ _ (((B.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hB (norm_nonneg _)).trans_eq (one_mul _))).trans hx)) hB;
        have hw:= (hZ _ hx).add (he.smul (-1)); rw [abs_neg,abs_one,one_mul,← two_mul] at hw; exact hw.germ (Eventually.of_forall fun i=>by simp only [neg_one_smul,Pi.sub_apply, sub_eq_add_neg])
    have hz: ‖y‖≤ A:=max_le hy (le_trans (le_trans (Real.norm_of_nonneg hT).le hY) hA)
    let Y:= ((y.1,0):Rho G n); have hW: Y∈closedBall 0 A:= by simpa[Y] using hy
    have ht : ‖f y‖ ≤1:=by
        have ht: f Y=0:=by simp[Y,f,powerF,science,rung]
        have hv(a:Rho G n)(ha:a∈closedBall 0 A): ‖a‖≤A:=by simpa using ha
        have he:= Convex.norm_image_sub_le_of_norm_fderiv_le (s:=closedBall 0 A) (𝕜:=ℝ) (f:=f) (C:=K) (fun x h=> (hf x (hv x h)|>.analytic.differentiableAt (by simp))) (fun x h=> ?_) (convex_closedBall ..) hW (show y∈closedBall 0 A by simpa using hz)
        · rw[ht, sub_zero,show y-Y=(0,y.2) from Prod.ext (by simp[Y]) (by simp[Y])] at he; simp only[Prod.norm_def,norm_zero, max_eq_right hT,Real.norm_of_nonneg hT] at he; exact he.trans ((mul_le_mul_of_nonneg_left hY (hf _ hz|>.nonneg)).trans hx)
        rw [← norm_iteratedFDeriv_one]; exact (hf x (hv x h)).norm_le _ (by omega)
    exact (H _ (show f y∈ _ by simpa using ht)).comp (f:=f) (hf y hz)
def orbAmt (K u T A s D:ℝ)(k:ℕ):= (2^k)*(K*u*s)*composeCost k D (zeff T A s)
lemma spark_orb (J:BudgetPoint)(o:Bond n)(v:G.Color)(s:ℝ) {F:Peat G n}{Y:Gal G n}(he:Drift _ F)(h: Drift _ Y): ContDiff ℝ ω (Orpus o v F Y s):=by
    let U(x:Rho G n):= transit o v (s • x);let L:= ContinuousLinearMap.inl ℝ (Directions G n) ℝ ∘L (ContinuousLinearMap.fst ℝ (Directions G n) ℝ)
    have hx:(Orpus o v F Y s)= (fun x=> dotB (Y (U x)) (phB o v) * Real.exp (powerF o v F s x)):=by ext1 x; simp only [Orpus,orbC,clamor,powerF,fast_dot];rfl
    have ht(x:Rho G n): Army U x:=by intro i; exact ContDiffAt.comp (g:=fun y=> G.mat (transit o v y i)) (f:=fun y=>s • y) x (spoutW J _ _ _ i) (by fun_prop)
    have hU:ContDiff ℝ ω (F ∘ U):= contDiff_iff_contDiffAt.mpr fun x=> he _ U x (ht x)
    have hV:ContDiff ℝ ω (Y ∘ U):= contDiff_iff_contDiffAt.mpr fun x=> h _ U x (ht x)
    have hp : ContDiff ℝ ω (powerF o v F s):=by rw [show powerF o v F s= F ∘ U-F ∘ U ∘ L from funext (fun i=>backF o v F i s)]; exact hU.sub (hU.comp L.contDiff)
    rw[hx]; exact ((dotB.flip (phB o v)).contDiff.comp hV).mul (Real.contDiff_exp.comp hp)
lemma brill (G:Gauge)(A:ℝ)(ha:1≤A)(k m:ℕ)(hm:1 ≤ m): ∃ C Z D:ℝ, 0 ≤ C ∧1 ≤ Z ∧ 0 ≤ D∧∀ (n:Side) (P:Support n)(F:Peat G n) (Y:Gal G n) (s h T w:ℝ)
    (o:Bond n)(v:G.Color), ‖v‖≤1 → 0 ≤ T → 0 ≤ w → 0 < s→s≤1→0<h→ kettle m*(h/s)≤ A→ zeff T A s * (kettle m*(h/s)) ≤ 1→
    let d:=k+m+1; Y 1=0 → Climate Y d w C→ Splendor F P d T C →
    Spells G A D k m o v s h T F ∧ ∀ x:Rho G n,‖x.1‖≤ A→0≤ x.2→x.2 ≤ kettle m*(h/s)→Allows d (Orpus o v F Y s) x (orbAmt Z w T A s D d):=by
    obtain ⟨C,K,hC,hK,H⟩:=grace G A ha k m hm; obtain ⟨L,Y,hL,hY,H'⟩:=spineY G A ha (k+m+1)
    refine ⟨max C L,Y,K,hC.trans (le_max_left ..),hY,hK,fun n P F X s h T w o v hv ht hw hs he hP hD hT hx hp hy=> ?_⟩
    have hh:= H _ P F s h _ o v hv ht hs he hP hD hT (Zn.post (k+m+1) _ _ _ _ _ P (le_max_left ..) hy le_rfl)
    refine ⟨hh,fun x hX hQ hV=>?_⟩; have hl: ‖x‖≤ A:= max_le hX (((Real.norm_of_nonneg hQ).le.trans hV).trans hD)
    have ht:= H' n X o v s w hw hv hs he hx (Zn.follower _ _ _ _ _ _ (le_max_right ..) hp le_rfl) (by omega) x hl
    have he:= ht.bilinear (ContinuousLinearMap.mul ℝ ℝ) (hh x hX hQ hV) (ContinuousLinearMap.opNorm_mul_le ℝ ℝ); rw[mul_one] at he; exact he
lemma fringe (J:BudgetPoint){F:Peat G n}{Y:Gal G n}{o:Bond n}{v:G.Color}{s h C A:ℝ}(hm:1 ≤ m)(hs:0 < s)(hp:0<h)(hF:Drift _ F)(hY:Drift _ Y)
   (hx:∀ x:Rho G n,‖x.1‖≤ A→0≤ x.2→x.2 ≤ kettle m*(h/s)→ Allows (k+m+1) (Orpus o v F Y s) x C) (x:Directions G n)(hV: ‖x‖ ≤ A):
    Allows k (minor (rumba m Y F h o v) s) x (tome m*C*(h/s)^(m+1)):=by
    let g:= Orpus o v F Y s; let t:=h/s; have ht:= attend (F:=g) (spark_orb J _ _ _ hF hY) hm (div_pos hp hs) (fun t ht hz=> hx (x,t) hV ht hz)
    apply ht.germ (Eventually.of_forall (fun z:Directions G n=> ?_)); unfold dulect; let U:= increment (1:Config G n) (s • z); let Z:= orbC Y F U o v
    have he: D (0,1) g (z,0) = s * deriv Z 0:=by
        rw[dis ((spark_orb J o v s hF hY).contDiffAt.differentiableAt (by simp))]; -- deriv_scale linear w/o differentiability for inv.
        let M:=s • ContinuousLinearMap.id ℝ ℝ; rw [show (fun t:ℝ=>g (z,t))= Z ∘ M from rfl]
        have hu': DifferentiableAt ℝ Z (M 0):=by rw[map_zero]; exact (claret Y F U hY hF _ _).differentiableAt
        rw [deriv_comp _ hu' M.differentiableAt,map_zero,M.deriv]; simp[M,mul_comm]
    unfold minor rumba; apply congr_arg₂ (· - ·)
    · unfold duel; apply sum_congr rfl fun i _=>?_ ; unfold g Orpus; dsimp only; rw [show s*(Outer.Nodes.loc i*(h/s))= Outer.Nodes.loc i*h from by field_simp, mul_zero]
    rw[he,smul_eq_mul]; field_simp;rfl
end YM.Trace.Swift
