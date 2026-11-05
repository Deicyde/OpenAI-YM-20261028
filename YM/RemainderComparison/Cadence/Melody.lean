import YM.RemainderComparison.Cadence.Echoes
import YM.RemainderComparison.Cadence.Vigor
/-!
 # Smooth p2 ordinate of pure log. Relative scalar collected in AUTH.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace Germ
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
local notation "Vp"=> (fun z:Ξ => Real.exp ∘ Lantern.grace ϕ ψ ρ Q z)
local notation "y'"=> Germ.primary ϕ ψ ρ Q
local notation "L₁"=> warrant ((Q 0)⁻¹) y' 2 0
variable (hv:Germ.Contract (Q 0)⁻¹ c)(hc:0<c)
open WilsonStartup.Change
lemma log_motif (f:E→ℝ)(x:E)(h:ContDiffAt ℝ ω f x)(ht:f x=0) (hp:fderiv ℝ f x=0): Matches 2 (fun x=>Real.log (1+f x)) f x:=by
   let b i:=(1+f i); let c:=Real.log ∘ b
   have hc : ContDiffAt ℝ ω b x:= contDiffAt_const.add h; have hs:b x=1:= by simp [b,ht]
   have hh : ContDiffAt ℝ ω c x:= hc.log (hs ▸ one_ne_zero)
   have he: fderiv ℝ c =ᶠ[𝓝 x] (fun y=>(b y)⁻¹ • fderiv ℝ f y):=by
     filter_upwards [hc.continuousAt.eventually (lt_mem_nhds (show 0<b x from hs ▸ zero_lt_one)),h.eventually (by simp)] with y hy hF
     have hk := (((hasFDerivAt_const (𝕜:=ℝ) (1:ℝ) y).add (hF.differentiableAt (by norm_num)).hasFDerivAt).log hy.ne').fderiv
     rw [zero_add] at hk; exact hk
   have hf:fderiv ℝ c x=0:= he.self_of_nhds.trans (by simp only [hp,smul_zero]); have hF : ContDiffAt ℝ ω (fderiv ℝ f) x:= h.fderiv_right le_top
   refine Matches.behind (k:=1) (f:=c) (Matches.behind (k:=0) ?_ (hh.fderiv_right le_top) (h.fderiv_right le_top) (hf.trans hp.symm)) hh h ?_
   · have hv: fderiv ℝ (fderiv ℝ c) x=fderiv ℝ (fderiv ℝ f) x := by
        rw [he.fderiv_eq,fderiv_fun_smul (c:=fun i=>(b i)⁻¹) ((hc.differentiableAt (by norm_num)).inv (hs ▸ one_ne_zero)) (hF.differentiableAt (by norm_num)),hp,hs]; simp
     refine ⟨(hh.fderiv_right le_top).fderiv_right le_top,hF.fderiv_right le_top,fun i hi=>?_⟩
     have ha:= Nat.eq_zero_of_le_zero hi; subst i; ext; rw [iteratedFDeriv_zero_apply,iteratedFDeriv_zero_apply,hv]
   unfold c; rw [Function.comp_apply,hs,ht,Real.log_one] -- unfold
include hv hc h
variable [FiniteDimensional ℝ E]
lemma song (h':2≤ n)(z:E) : Matches 2 (Real.log ∘ Germ.early ((Q 0)⁻¹) (Germ.primary ϕ ψ ρ Q) 2) (fun x:ℰ=> x.1^2*L₁) (0,z):=by -- actually for all x:E. adjust.
    let L:= warrant ((Q 0)⁻¹) y'; let F:= Germ.early ((Q 0)⁻¹) y' 2; let P z:=(z:ℰ).1^2*L₁
    have hp (x:E):L 0 x =1 := by
      have hz z:Trace.coefficient (fun x=> y' x z) 0 x=1:=by unfold Trace.coefficient Trace.plain; simp [Germ.anchor]
      unfold L warrant; simp_rw [hz]; simp
    have hk:F=(fun z=>1+P z):=by
      funext z; obtain ⟨h₁,h₂⟩:= Glade.earned h hv hc h' z.2; unfold F Germ.early Trace.polyeval
      change ∑ i∈ range _, z.1^i • L i z.2=1+ _
      change L 1 z.2=0 at h₁; change L 2 z.2= L 2 0 at h₂
      simp only [sum_range_succ,pow_zero,one_smul,hp,h₁,smul_zero,sum_range_zero,zero_add,add_zero,h₂]; rfl
    have he : ContDiff ℝ ω P:= (contDiff_fst.pow 2).mul contDiff_const
    change Matches 2 (Real.log ∘ F) P _; rw [hk]; refine log_motif _ _ he.contDiffAt ?_ ?_
    · unfold P; simp
    unfold P; rw [fderiv_fun_mul (by fun_prop) (by fun_prop), fderiv_fun_pow 2 (show DifferentiableAt ℝ (Prod.fst:ℰ→ℝ) ((0:ℝ),z) from by fun_prop)]; simp -- edit name
end YM.RemainderComparison.Cadence
