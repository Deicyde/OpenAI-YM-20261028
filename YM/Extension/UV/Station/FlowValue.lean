import YM.Extension.UV.Station.Flutter
import YM.Next.STATIONARY.Joint.Gauge
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open YM Lattice Wilson Filter Precision Matrix Function
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
namespace YM.Extension.UV.StationaryData
open Exterior Laurent RG Tree WilsonStartup.Change Stationary
variable {G:Gauge} {c m:Side} {p p':Clip}{S:StepData m c} (B:Forest S.ratio)
local notation "M₁" => fieldDir G m 1
local notation "M₂" => fieldDir G c 1
local notation "LogMap" => Work.F03.axisLog B (G:=G)
abbrev AT (c:Side)(p:Clip)(P:PathData G):= (mainTerm p P ∘ represent (n:=c))
lemma log_smooth : ContDiffAt ℝ ω LogMap 0:=(Work.F03.inclusion_smooth B).snd
lemma log_zero : LogMap 0=0:= congr_arg Prod.snd (Work.F03.inclusion_zero B)
lemma log_works : represent ∘ LogMap =ᶠ[𝓝 0] readFine B:= Work.F03.inclusion_works B
lemma log_dir (v): fderiv ℝ LogMap 0 v = Bid.stretch (S:=S) B v:=by
    have ht := DFunLike.congr_fun (((Work.F03.inclusion_smooth B |>.differentiableAt (by simp)).hasFDerivAt.snd.fderiv)) v
    exact ht.trans (congrArg Prod.snd (Work.F03.inclusion_deriv (S:=S) B v))

lemma ink_sub {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{F:Type}[NormedAddCommGroup F][NormedSpace ℝ F] {f g:E→F} {x:E}(hf:ContDiffAt ℝ ω f x)(hg:ContDiffAt ℝ ω g x){k v}: dirT (f-g) k x v=dirT f k x v-dirT g k x v:=DFunLike.congr_fun (iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top)) (fun _:Fin k=>v)
def coreS (p:Clip) (P P':PathData G) (c:Side):fieldDir G c 1→ℝ := (AT c p P) - (AT c p P')

abbrev junction (θ:S.Choices)(p:Clip) (P:PathData G):= onSlice B θ p P
local notation "X₂"=>AxisChart G B
lemma swing (w:X₂)(v:M₁)(hw:w=0) : True := trivial
lemma swing_main {E' X F:Type} [NormedAddCommGroup E'][NormedSpace ℝ E'][NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup F][NormedSpace ℝ F](w:E'→X)(z:X→F) (x y:E')(hx:ContDiffAt ℝ ω z (w x))(hy:ContDiffAt ℝ ω w x): dirT (z ∘ w) 1 x y = fderiv ℝ z (w x) (fderiv ℝ w x y):= by rw [dirT_one,fderiv_comp _ (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp))]; rfl
set_option maxHeartbeats 600000 in
private lemma test_rate (θ:S.Choices) (k v) (P Q P' Q':PathData G) (h:ContDiffAt ℝ ω (AT c p P) 0) (hQ:ContDiffAt ℝ ω (AT c p Q) 0)
    {f g:M₁→X₂} (hf:Critical B p P f) (hg:Critical B p Q g)
    (hb:Matches (k+2) (AT c p P) (AT c p Q) 0) (hv:Definite (junction B θ p P))
    (ht:Matches 4 (junction B θ p P ∘ WilsonStartup.Change.graph f) (AT m p' P') 0) (hu:Matches 4 (junction B θ p Q ∘ WilsonStartup.Change.graph g) (AT m p' Q') 0) (hk:k+3≤4) :
    dirT (coreS p' P' Q' m) (k+3) 0 v=dirT (coreS p P Q c) (k+3) 0 (Bid.stretch B (fderiv ℝ (YM.WilsonStartup.Change.graph f) 0 v)):=by
 have hg₀:= (station_of hf θ).at0
 have hl (s:WithTop ENat) : ContDiffAt ℝ s (LogMap ∘ YM.WilsonStartup.Change.graph f) 0 := by exact (hg₀.symm ▸ (log_smooth B).of_le le_top).comp _ ((station_of hf θ).chart.of_le le_top)
 have h₂ : (LogMap ∘ YM.WilsonStartup.Change.graph f) 0=0:=by change LogMap (YM.WilsonStartup.Change.graph f 0)=0; rw [hg₀,log_zero]
 let y:=Bid.stretch B (fderiv ℝ (YM.WilsonStartup.Change.graph f) 0 v); let x:=YM.WilsonStartup.Change.graph f
 have hy : dirT (LogMap ∘ x) 1 0 v=y:= by rw [swing_main x LogMap _ _ (by change ContDiffAt ℝ ω _ (YM.WilsonStartup.Change.graph f 0); exact hg₀.symm ▸ log_smooth B) (station_of hf θ).chart, show x 0=0 by exact hg₀,log_dir]
 have hr:=pure_pull (k:=k+3) (g:=coreS p P Q c) (w:=LogMap ∘ x) (by omega) (h.sub hQ) (hl _) h₂ (fun i hi=>by unfold coreS;rw [iteratedFDeriv_sub_apply (h.of_le le_top) (hQ.of_le le_top),hb.jets i (by omega),sub_self] ) v
 apply Eq.trans _ (hr.trans (by rw [hy]))
 have he_term : coreS p P Q c ∘ (LogMap ∘ x) =ᶠ[𝓝 0] ((junction B θ p P) ∘ x - (junction B θ p Q) ∘ x) := by
   filter_upwards [((station_of hf θ).home).eventually (log_works B)] with z hz; dsimp [onSlice,coreS,Precision.tested,x]; change represent (LogMap (x z)) = _ at hz; dsimp [x] at hz; rw [hz]; unfold junction onSlice; dsimp [onSlice,Function.uncurry, Precision.tested,readFine]; abel
 rw [show dirT (coreS p P Q c ∘ (LogMap ∘ x)) (k+3) 0 v= dirT (((junction B θ p P)∘x) - ((junction B θ p Q)∘x)) .. from DFunLike.congr_fun ((he_term.iteratedFDeriv ℝ (k+3)).self_of_nhds) (fun _=>v),ink_sub ht.left (((hg₀.symm ▸ (hg.2.2 θ).1)).comp _ (station_of hf θ).chart)]
 rw [coreS,ink_sub ht.right hu.right]
 rw [(show dirT _ _ _ _=dirT _ _ _ _ from DFunLike.congr_fun (ht.jets _ hk).symm (fun _=>v)),(show dirT _ _ _ _=dirT _ _ _ _ from DFunLike.congr_fun (hu.jets _ hk).symm (fun _=>v))]
 exact ((verdict_value (station_of hf θ) (station_of hg θ) (tested_match hb hf θ) hv).2 v).trans ((residual_pull (tested_match hb hf θ) (station_of hf θ).chart hg₀ v).symm)

section consumption
open Matrix
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
variable (P Q P' Q':PathData G) {η η':ℝ} {A: Crossover (S:=S) p p' P P' η B} {b:Crossover (S:=S) p p' Q Q' η' B}
  {u u':ℕ→M₁→X₂} (ha:Crossover.Accepts B A u)(hb:Crossover.Accepts B b u') (hM : Matches 2 (AT c p P) (AT c p Q) 0) (W:ℕ→ Matrix (Body 1 c) (Body 1 m) ℝ)
-- Two symbols E extras shadow earlier names; consumption exact at the field tensors as functions of real potentials in Wilson chart.

def directed (M:Matrix (Body 1 c) (Body 1 m) ℝ) := fun v : M₁ => arm G c 1 (uniformM M ((arm G m 1).symm v))

lemma directed_rate {v:M₁} {Y:Matrix (Body 1 c) (Body 1 m) ℝ} (s:M₁→X₂) (h:HasDerivAt (fun t:ℝ=>s (t•v)) (relative B Y v) 0) (hd:ContDiffAt ℝ ω s 0):
   directed (extracted S B Y) v=Bid.stretch B (v,dirT s 1 0 v) := by
 have hx:HasDerivAt (fun t:ℝ=>s (t•v)) ((fderiv ℝ s (0:M₁)) v) 0 := by
   simpa [Function.comp_def] using (((show DifferentiableAt ℝ s ((0:ℝ) • v) from (zero_smul ℝ v).symm ▸ hd.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt (0:ℝ) ((hasDerivAt_id' _).smul_const v)) -- zero_smul rewrite may need
 rw [dirT_one,← h.unique hx]
 ext ⟨x,i⟩ j; exact (congr_fun (Work.F04.parts_stretch B Y v j) _).symm

lemma beam_adhesion (v:M₁)(k:ℕ) (M:Matrix (Body 1 c) (Body 1 m) ℝ) (P Q:PathData G)
  (hw:force (intended p P (m:=c) - intended p Q))
  (hh:AnalyticAt ℝ ((AT c p P) -(AT c p Q)) 0)
  (hb:Quiets (intended p P (m:=c) - intended p Q) k) : dirT (coreS p P Q c) k 0 (directed M v)=dirT (coreS p P Q c) k 0 (directed (extracted S B M) v):=by
 let D:=intended p P (m:=c) - intended p Q
 let z : BaseSites G c := uniformM (straighten S B M) ((arm G m 1).symm v)
 have hd (x:fieldDir G c 1): dirT (coreS p P Q c) k 0 x = dirT D k 0 ((arm G c 1).symm x):=by
   have hxo : D=coreS p P Q c ∘ (arm G c 1).toContinuousLinearMap:=rfl
   have he:= wired (f:=coreS p P Q c) ((arm G c 1).toContinuousLinearMap) (x:=0) (by rw [map_zero]; apply hh) k (fun _=> (arm G c 1).symm x)
   rw [hxo]; unfold dirT; simpa only [map_zero,ContinuousLinearEquiv.coe_coe,Function.comp_def,ContinuousLinearEquiv.apply_symm_apply] using he.symm

 rw [hd,hd]
 let y:= uniformM M ((arm G m 1).symm v)
 have ht : AnalyticAt ℝ D 0:=by change AnalyticAt ℝ (coreS p P Q c ∘ arm G c 1) 0; exact AnalyticAt.comp (show AnalyticAt ℝ ((AT c p P) -(AT c p Q)) _ from (arm G c 1).map_zero.symm ▸ hh) ((arm G c 1).analyticAt _)
 have he := adhesion D (n:=k) (fun _=>(-z,y)) hw ht hb
 have hF : y-gradientA G c (-z)=uniformM (extracted S B M) ((arm G m 1).symm v):= by
   rw [extracted,first_uniform,map_neg,sub_neg_eq_add]; funext x
   change (M *ᵥ parts G 1 _ x.2.2) _ + ((Exterior.d 0 c) *ᵥ parts G 0 _ x.2.2) _ = ((M+ (Exterior.d 0 c) * _)*ᵥ parts G 1 _ x.2.2) _
   rw [add_mulVec,← Matrix.mulVec_mulVec,show z=uniformM (straighten S B M) _ from rfl,uniformC]; rfl
 rw [directed,directed,(arm G c 1).symm_apply_apply,(arm G c 1).symm_apply_apply]
 change dirT D k 0 y=dirT D k 0 (uniformM (extracted S B M) _); rw [← hF]; exact he.symm
end consumption
#print axioms log_dir
end YM.Extension.UV.StationaryData
namespace YM.Extension.UV.StationaryData
open Exterior Laurent RG Tree WilsonStartup.Change Stationary
variable {G:Gauge} {c m:Side} {p p':Clip}{S:StepData m c} (B:Forest S.ratio) (P Q P' Q':PathData G) {η η':ℝ} {A: Crossover (S:=S) p p' P P' η B} {b:Crossover (S:=S) p p' Q Q' η' B}
  {k : ℕ} (W:ℕ→ Matrix (Body 1 c) (Body 1 m) ℝ)
local notation "M₁" => fieldDir G m 1
local notation "X₂"=>AxisChart G B
lemma base_response {u u':ℕ→M₁→X₂}(ha:Crossover.Accepts B A u)(hb:Crossover.Accepts B b u') (hx:Matches (k+2) (AT c p P) (AT c p Q) 0)
   (hk:k≤1) (hw:force (intended p P (m:=c) - intended p Q)) (v:M₁)(q:ℕ→ℝ) (s:ℝ) (price: (fun n=>dirT (coreS p P Q c) (k+3) 0 (directed (W n) v)) ≤ᶠ[atTop] q) (hq:Tendsto q atTop (nhds s))
   (hg:∀ᶠ n in atTop, HasDerivAt (fun t:ℝ=> (u n) (t•v)) (relative B (W n) v) 0 ∧ ContDiffAt ℝ ω (u n) 0):
   dirT (coreS p' P' Q' m) (k+3) 0 v ≤ s:=by
 have e (b:X₂): fderiv ℝ (YM.WilsonStartup.Change.graph A.choice) 0 v=(v,dirT A.choice 1 0 v):= by
   rw [dirT_one]; exact DFunLike.congr_fun ((hasFDerivAt_id (0:M₁)).prodMk ((ha.crit.2.1.differentiableAt (by simp)).hasFDerivAt)).fderiv _
 have H : Continuous fun w : X₂=>Bid.stretch B (v,w) := by
   refine continuous_pi (fun j=>?_); unfold Bid.stretch; dsimp; split <;> first | exact continuous_const | exact continuous_const.add (continuous_apply _)
 have huh : dirT (coreS p P Q c) (k+3) 0 = fun x=>iteratedFDeriv ℝ (k+3) (coreS p P Q c) 0 (fun j=>x):=rfl
 have hz:Quiets (intended p P (m:=c) - intended p Q) (k+3):=by
   intro j hj _
   let x:Matches (k+2) (intended p P (m:=c)) (intended p Q) 0:=(show Matches _ _ _ ((arm G c 1) 0) from (arm G c 1).map_zero.symm ▸ hx).comp_refl (arm G c 1).contDiff.contDiffAt
   rw [iteratedFDeriv_sub_apply (x.left.of_le le_top) (x.right.of_le le_top),x.jets j (by omega),sub_self]
 have h : Continuous (dirT (coreS p P Q c) (k+3) 0):= (iteratedFDeriv ℝ (k+3) (coreS p P Q c) 0).cont.comp (continuous_pi fun _=> continuous_id')
 apply le_of_tendsto_of_tendsto ?_ hq price
 have θ:=Classical.arbitrary S.Choices
 rw [test_rate B θ k v P Q P' Q' hx.left hx.right ha.crit hb.crit hx (definite_of ha.gap ha.positive _ ((ha.crit.2.2 _).1)) (ha.result θ) (hb.result θ) (by omega),e 0] -- e has b unused; Lean explicit?
 apply Tendsto.congr' ?_
 · exact (h.comp H).continuousAt.tendsto.comp (ha.travel 1 v)
 filter_upwards [hg] with n ⟨hn,hd⟩
 exact congr_arg _ (directed_rate B (u n) hn hd).symm |>.trans (beam_adhesion B v (k+3) (W n) P Q hw ((hx.left.sub hx.right).analyticAt) hz).symm


#print axioms base_response
end YM.Extension.UV.StationaryData
