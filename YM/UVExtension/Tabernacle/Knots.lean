import YM.UVExtension.Tabernacle.Sway
import YM.UVExtension.Oriel.Dial

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Tabernacle
open Function Set Filter Metric Lattice RG Precision Wilson Ovens
open Progress.DirectedRecipe Whirl Push Push.AbsoluteSums
open AnalyticBridge VerifiedReset Lamppost Concert BoundedContinuousFunction
open Oriel Oriel.Charted Complex
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators Classical

-- real image and complex density toolkit. fixed currencies, no volume compactness.
section basis
variable {X Y R: Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X] [AddCommGroup R] [Module ℝ R] (L:R→ₗ[ℝ] X)

def Box := (undertone L).topologicalClosure
-- notation Lean.Box
def tin : R→ₗ[ℝ] (Tabernacle.Box L) where
    toFun u:= ⟨L u,(undertone L).le_topologicalClosure (inkwell L u)⟩
    map_add' _ _:= by ext; apply map_add
    map_smul' _ _:= by ext; apply map_smul

def joint : (ℝ × R)→ₗ[ℝ] (ℂ × X) := LinearMap.prodMap Complex.ofRealCLM.toLinearMap L
variable (h:∀ a b:R, let z:=L a+Complex.I • L b; ‖L a‖≤ ‖z‖∧ ‖L b‖≤‖z‖)
include h
lemma delivered : Firm (tin L):=by
    constructor
    · exact h
    rw [Metric.dense_iff]; intro x ε he
    obtain ⟨v,hv,hq⟩:= Metric.mem_closure_iff.mp x.property _ he
    let u: (Tabernacle.Box L):= ⟨v,(undertone L).le_topologicalClosure hv⟩
    refine ⟨u,(dist_comm u x).trans_lt hq,?_⟩
    obtain ⟨a,b,hk⟩:=show Oriel.paint L v from hv
    exact ⟨a,b,Subtype.ext hk⟩
omit h
omit [IsScalarTower ℝ ℂ X] in
lemma wed (he:Firm L):Firm (joint L):=by
  constructor
  · rintro ⟨a,v⟩ ⟨b,w⟩; have hz : ↑a+I • Complex.ofReal b=((a:ℂ)+I*(b:ℂ)):= rfl; let z:= (a:ℂ)+I*(b:ℂ); have hp : ‖(a:ℂ)‖≤ ‖z‖:=by simpa [z] using abs_re_le_norm z
    have hv : ‖(b:ℂ)‖≤‖z‖:= by simpa [z] using abs_im_le_norm z
    have ht:= he.ink v w; exact ⟨max_le_max hp ht.1, max_le_max hv ht.2⟩
  rw [Metric.dense_iff] at *
  rintro ⟨x,y⟩ ε hε
  obtain ⟨w,hh,⟨a,b,hv⟩⟩:= Metric.dense_iff.mp he.runs y ε hε
  exact ⟨(x,w),max_lt (show dist x x<ε from (dist_self x).trans_lt hε) hh,⟨(x.re,a),(x.im,b),Prod.ext (show x=↑x.re+I*(x.im:ℂ) from (by rw [mul_comm I,re_add_im])) hv⟩⟩
end basis

section along
variable {ι : Type}[TopologicalSpace ι] -- reorder
lemma tones (f g:ι→ᵇℂ)(hf:∀ i,(f i).im=0)(hg:∀ i,(g i).im=0):‖f‖≤‖f+I • g‖∧ ‖g‖≤‖f+I • g‖:=by
   refine ⟨(BoundedContinuousFunction.norm_le (norm_nonneg _)).2 (fun i=> ?_), (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 (fun i=> ?_)⟩; all_goals
    let K:= f+I • g
    apply le_trans _ ((f+I • g).norm_coe_le_norm i)
    have hx:(K i).re=(f i).re:=by simp [K,hg]
    have ht:(K i).im=(g i).re:=by simp [K,hf]
    first
    | exact Eq.trans_le (show ‖f i‖ = |(f i).re| from (by conv_lhs => rw [← re_add_im (f i),hf]; simp)) (hx ▸ abs_re_le_norm (K i))
    | exact Eq.trans_le (show ‖g i‖ = |(g i).re| from (by conv_lhs => rw [← re_add_im (g i),hg]; simp)) (ht ▸ abs_im_le_norm (K i))
end along
lemma lands {Y Z:Type}(V:Meter.{0,0,0} Y Z)(g:V.Slot)(i): (vibe V g i).im=0:=by by_cases hv:∃ b,V.MeasureP g b; rw [puts _ hv]; rfl; unfold vibe; rw [dif_neg hv]; rfl
variable {G:Gauge}{n:Side}{p:BudgetPoint}
namespace Charm
variable (d:Tabernacle.Charm G p n) (σ τ:ℝ)
abbrev Hall := ↥(Tabernacle.Box (d.hue p σ τ))
instance : CompleteSpace (d.Hall σ τ):= isClosed_closure.completeSpace_coe

def embed := tin (d.hue p σ τ)
lemma height (x y:d.Shed p): let L:= d.hue p σ τ; let z:=L x+I • L y
    ‖L x‖≤ ‖z‖∧ ‖L y‖≤ ‖z‖:=by
   intro L z
   have he(t:d.Shed p)(i): ((L t).1 i).im=0:=by change (σ⁻¹ • vibe _ _ i).im=0; rw [smul_im,lands,smul_zero]
   have ht(t:d.Shed p)(i): ((L t).2 i).im=0:=by change (τ⁻¹ • vibe _ _ i).im=0; rw [smul_im,lands,smul_zero]
   have hx:= tones _ _ (he x) (he y); have hv:= tones _ _ (ht x) (ht y); exact ⟨max_le_max hx.1 hv.1,max_le_max hx.2 hv.2⟩
lemma weather : Firm (joint (d.embed σ τ)) := wed _ (delivered _ (height d σ τ))
end Charm
end YM.UVExtension.Tabernacle
