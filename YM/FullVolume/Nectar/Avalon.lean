import YM.FullVolume.Nectar.Sweeps
import YM.FullVolume.Spiral.Dome
/-! Uniform all-config (including nonlocal off-ray zeros in dummy rows). This is not an a.e. Lp. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray
open Finset Function Filter Set MeasureTheory Push.AbsoluteSums Lattice RG PhysicalNext.Repeat.Jams
open scoped Topology BigOperators Classical ENNReal ContDiff
variable (I E Y:Type) [NormedAddCommGroup E]
abbrev Glacier:= lp (fun _:I=> lp (fun _:Y=> E) ∞) 1
namespace Glacier
open PhysicalNext.Repeat.Luna
variable {I E Y}[NormedSpace ℝ E] [CompleteSpace E]
local notation "W"=> Glacier I E Y
lemma points (f:W): HasSum (fun i=> ‖f i‖) ‖f‖ :=by simpa using lp.hasSum_norm (by simp) f
lemma footage (f:W) [Fintype I] :∑ i, ‖f i‖=‖f‖:= by have h:= (points f).tsum_eq; rwa [tsum_fintype] at h
variable (E)
def seesG (i:I)(y:Y): W →L[ℝ] E:=
   (lp.evalCLM ℝ (fun _:Y=> E) ∞ y).comp (lp.evalCLM ℝ (fun _:I=> lp (fun _:Y=> E) ∞) 1 i)
variable {E}
variable [Fintype I]
def Bagged (F:I→Y→E) := ∀ i:I, ∃ v:ℝ,0≤v ∧ ∀ y, ‖F i y‖≤ v
def castle (F:I→Y→E):Glacier I E Y:= if h: Bagged F then
    ⟨fun i=>⟨F i,memℓp_infty ⟨(h i).choose,Set.forall_mem_range.mpr (h i).choose_spec.2⟩⟩,memℓp_gen (by apply Summable.of_finite)⟩ else 0
lemma unity (F:I→Y→E)(h:Bagged F)(i:I)(y:Y): seesG E i y (castle F)=F i y:=by unfold castle; rw [dif_pos h]; rfl
section
variable {v:I→ℝ}{b q:ℝ} {Z:I→Y→E} {R:sun→ I→ Y→E}
lemma rent (hv:0 ≤ v)(h:∀ i y, ‖Z i y‖≤v i): ‖castle Z‖ ≤ ∑ i,v i:=by
     let u:=castle Z; let r:Bagged Z:= fun i=> ⟨_,hv i,h i⟩; rw [←footage]; exact sum_le_sum (fun i _=>lp.norm_le_of_forall_le (hv i) (fun p=>(by change ‖seesG E i p u‖ ≤ _; unfold u;rw [unity _ r];exact h i p)))
lemma compass (hp:1≤q)(hv:0≤v)(h:∑ i,v i≤ b)(hr:∀ i p, Scout q (phraseS fun x=> R x i p) (v i)): (∀ t, Bagged (R t))∧ Rebar q (phraseS fun t=>castle (R t)) b :=by
    have hc(s):Bagged (R s):=fun i=> ⟨v i,hv i,fun p=> PhysicalNext.Repeat.Pass.solo ((hr i p).boom) s⟩
    let F:sun→W:=fun t=>castle (R t)
    refine ⟨hc, hp,(sum_nonneg (fun i _=>hv i)).trans h,fun w η hT=>?_⟩
    have he:=stripe_pos hT
    rw [mix_made,← footage]; refine le_trans (b:=η*∑ i,v i) ?_ (mul_le_mul_of_nonneg_left h he); rw [mul_sum]; apply Finset.sum_le_sum; intro i _
    refine lp.norm_le_of_forall_le (mul_nonneg he (hv i)) (fun y=>?_)
    have hK(z): seesG E i y (F z)=R z i y:=unity _ (hc z) _ _; change ‖seesG E i y (mix w F)‖ ≤ _; unfold mix; rw [map_sum]; simp_rw [map_smul,hK]; exact mix_d _ hT (hr i y)
-- equality budget pointwise polynomials into Banach frame. Cost.H.
lemma equal {f g:W} (h:∀ i y, f i y=g i y) : f=g:=by -- f g metas
    apply Subtype.ext; apply funext; intro i; apply Subtype.ext; funext y; exact h i y
end
end Glacier
end YM.FullVolume.Ray
