import YM.RemainderComparison.Cadence.Beat
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Afresh
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Price
/-!
 # Screen at b = 0. Prove ∫ζ of horizontal / varying determinant uncut
 BEFORE using parity. Constants from moving Gaussian domination
 possibly enormous and period-specific; not used in quantitative AUTH.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence.Glade
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush Shield Flux Progress.StationaryScenes Green
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n j : ℕ} {v u D d x e c C A B : ℝ} {Q : E → Matrix ι ι ℝ} {ρ : E→Body ι} {ϕ ψ:E×Body ι→ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι
variable (h : Lantern.Golf ϕ ψ ρ Q n D d d C)
local notation "Mt"=> (fun x=>(Q x)⁻¹)
local notation "μ₀" => sweep (Q 0)⁻¹
local notation "g₁"=> Lantern.grace ϕ ψ ρ Q
local notation "Y'"=> fun (x:E) z=> Real.exp (g₁ z (0,x))
local notation "Y"=> (Y')
include h
lemma jetH (i j:ι) : ContDiffAt ℝ n (fun x=>Q x i j) 0:= by
    have hz : ‖(0:E)‖<d:= norm_zero.trans_lt h.pos; have hv : ‖(0:ℝ)‖<d:= norm_zero.trans_lt h.pos
    obtain ⟨hp,-⟩:= h.color 0 0 (0,0) (norm_zero.trans_le h.off) (by simp) hv hz
    rw [show Lantern.visit ρ 0 0 (0,0)=(0,ρ 0) from by simp [Lantern.visit]] at hp
    let H x (z:ι→ℝ):= dotProduct z ((Q x) *ᵥ z)
    have hh:∀ᶠ x in 𝓝 (0:E), ‖x‖<d:= by simpa only [← mem_ball_zero_iff] using! Metric.ball_mem_nhds 0 h.pos -- edit
    have hk (v:ι→ℝ) : ContDiffAt ℝ n (fun x=> H x v) 0:= by
       let z:= WithLp.toLp 2 v; let L: E→ E × Ξ:=fun y=>(y,ρ y); have he:L 0=(0,ρ 0):=rfl
       have hy : ContDiffAt ℝ (↑n) (fderiv ℝ (fderiv ℝ ϕ)) (0,ρ 0):= (Lantern.norm_F (Lantern.norm_F hp)).smooth
       have ht : ContDiffAt ℝ n L 0:= contDiffAt_id.prodMk ((h.curve _ hz).smaller (show n≤n+2 by omega)|>.smooth)
       have hy : ContDiffAt ℝ n (scratch (0,z) ϕ ∘ L) 0:= (((he.symm ▸ hy).comp (f:=L) _ ht).clm_apply contDiffAt_const).clm_apply contDiffAt_const -- ed
       exact hy.congr_of_eventuallyEq (hh.mono fun x hx=> (h.station x hx z).2)
    let a:ι→ℝ:=Pi.single i (1:ℝ); let b:ι→ℝ:=Pi.single j (1:ℝ)
    apply ((((hk (a+b)).sub (hk a)).sub (hk b)).div_const (2:ℝ)).congr_of_eventuallyEq
    filter_upwards [hh] with x hx
    have hp : Q x j i= Q x i j:= isHermitian_iff_isSymm.mp (h.gram x hx).1.isHermitian|>.apply i j
    have hf : ∀ i j, dotProduct (Pi.single i (1:ℝ)) (Q x *ᵥ (Pi.single j (1:ℝ)))=Q x i j := fun i j=> by simp
    unfold H a b
    rw [mulVec_add, dotProduct_add,add_dotProduct,add_dotProduct,hf,hf,hf,hf,hp]; ring
variable (hv:Germ.Contract (Q 0)⁻¹ c)(hc:0<c)
include hc hv
lemma protection : ∃ M:Ξ→ℝ, Integrable M μ₀ ∧ ∀ᶠ y:E in 𝓝 0, (∀ a, Brush n (M a) 1 (fun x=> Y x a) y) ∧ StronglyMeasurable (Y y) ∧ ∫ z,Y y z ∂μ₀=1:=by
    have hh:∀ᶠ x in 𝓝 (0:E), ‖x‖<d:= by simpa only [← mem_ball_zero_iff] using! Metric.ball_mem_nhds 0 h.pos
    have hD : ∀ x: E, ‖x‖<d→(Q x).PosDef:=fun x hx=> (h.gram x hx).1
    have hp:= hD 0 hh.self_of_nhds; have hy : Zest (fun a : Ξ=>fun _ : E=> a-a) 0 n:= by simp only [sub_self]; exact ⟨0,le_rfl, Eventually.of_forall fun x i=> (Brush.certified zero_le_one (x:=x) (k:=n) (0:Ξ)).climb (norm_zero.le) le_rfl⟩
    have he' : Bottom ((Q 0)⁻¹)⁻¹ c⁻¹ := (SectorTools.PhysicalGaussianInsertion.inv_gap (A:=(Q 0)⁻¹) hp.inv hv hc).lower
    obtain ⟨M,hM,hM',hy'⟩:= Flux.winglet (x:=(0:E)) (A:=Mt) (V:=fun z _=>z) (Z:=fun i:Ξ=>i) hp.inv he' (inv_pos.mpr hc) (jetBack (jetH h) (isUnit_iff_ne_zero.mpr hp.det_pos.ne')) hy
    refine ⟨M,hM',?_⟩
    have hp' (x:E)(hx:‖x‖<d)(z:Ξ) : lens₀ ((Q 0)⁻¹) z* Y x z=lens₀ (Mt x) z:= Lantern.meter ϕ ψ ρ Q z (fun v hv=> by
       simp only [mem_insert_iff, mem_singleton_iff] at hv
       have he : ‖v‖<d:= hv.elim (fun h=>h.symm ▸ hh.self_of_nhds) (fun h=>h.symm ▸ hx)
       exact ⟨hD v he,fun z=> (h.station v he z).2⟩)
    have hR x (hx:‖x‖<d)(z:Ξ) : Y x z = lens₀ (Mt x) z /lens₀ ((Q 0)⁻¹) z:= (eq_div_iff (fullFuel ..).ne').mpr (by rw [mul_comm]; exact hp' x hx z)
    filter_upwards [hh,eventually_eventually_nhds.mpr hh,hy'] with y hy H hY
    have hb (S: Matrix ι ι ℝ) : Measurable (lens₀ S):= bulbB (S:=fun _ : Ξ=>S) (z:=fun v=>v) (fun i j=> measurable_const) measurable_id
    have hr : Y y=(fun z=>lens₀ (Mt y) z / lens₀ ((Q 0)⁻¹) z):=funext (hR y hy)
    refine ⟨fun a=>(hY a).shimmy (H.mono fun x hx=> hR x hx a), by change StronglyMeasurable ((Y) y); rw [hr]; exact ((hb (Mt y)).div (hb ((Q 0)⁻¹))).stronglyMeasurable,?_⟩
    have h' : (∫ z,lens₀ (Mt y) z)=1:=by
       have he := Shield.recommends (Mt y) (hD y hy).inv (fun _=>1); simp at he; exact he.symm -- edit
    rw [Shield.recommends _ hp.inv,← h']; exact integral_congr_ae (ae_of_all _ (hp' y hy))

variable [FiniteDimensional ℝ E]
lemma sheltered (i:ℕ)(hui: 0 < i)(hi:i ≤ n)(x : E): let W z := (iteratedFDeriv ℝ i (fun y=> Y y z) 0) (fun _=> x);
      Integrable W μ₀ ∧ ∫ z,W z ∂μ₀=0:= by
    obtain ⟨M,hM,hp⟩:= protection h hv hc
    let A x:= ∫ z,Y x z ∂μ₀
    have hp' : A =ᶠ[𝓝 0] (fun _=>1):= hp.mono fun x hx=> hx.2.2
    have hb : Meristem Y (0:E) μ₀ n:= Relative.test_domination hM (hp.mono fun _ he=> he.1) (hp.mono fun _ he=>he.2.1)
    let U:= JetF Y i 0; obtain ⟨hk,hQ⟩:= hb.calls.2 i hi
    have he : (∫ z,U z ∂μ₀)=0:= by rw [show _= iteratedFDeriv ℝ i A 0 from hQ.symm,(hp'.iteratedFDeriv ℝ i).self_of_nhds,iteratedFDeriv_const_of_ne hui.ne']; rfl
    intro W; let L:= ContinuousMultilinearMap.apply ℝ (fun _:Fin i=> E) ℝ (fun _=> x)
    exact ⟨L.integrable_comp hk, (L.integral_comp_comm hk).trans ((congr_arg L he).trans (map_zero _))⟩
end YM.RemainderComparison.Cadence.Glade
