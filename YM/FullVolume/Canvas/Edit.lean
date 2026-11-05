import YM.FullVolume.Canvas.Twig
/-! Canons cost different widths; Bluff.Vow means unpenalized jet no wander.No Stature.Assembles. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Shade
open Filter Set Function lp Lattice Laurent Bloch Exterior RG Precision Wilson Tralis
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius NNReal ENNReal
variable {G:Gauge}{t:ℕ}[NeZero t]{σ:ℝ}{C:Side}
structure Vow (G:Gauge)(t:ℕ)[NeZero t] where
    δ:ℝ
    hired:0<δ
    s:Submodule ℝ (Cameo G t)
    quiet:IsClosed (s:Set (Cameo G t))

def core (G:Gauge)(t:ℕ)[NeZero t](σ:ℝ)(h:0<σ): Vow G t:=⟨σ,h,(senses G t σ).choose,(senses G t σ).choose_spec.1⟩
def cut (G:Gauge)(σ:ℝ)(h:0<σ): Vow G 1:=⟨σ,h,(clocks (G:=G) h).choose,(clocks (G:=G) h).choose_spec.1⟩
lemma gold (h:0<σ)(F:Cameo G t): F∈ (core G t σ h).s ↔ ∀ i,(ringT σ F i).Invariant:= (senses ..|>.choose_spec.2 F)
lemma silver (h:0<σ)(F:Cameo G 1): F∈ (cut G σ h).s ↔ Bs G (ringT σ F) ∧ ∀ i,(ringT σ F i).Invariant:= (clocks h |>.choose_spec.2 F)

namespace Vow
variable (V:Vow G t) (S:ℕ→Side)
def freeze (c:Side): Cameo G t→L[ℝ] Tensor.T (Link G c) ℝ (t+1) := (fibres (m:=c) V.hired _).choose
lemma tells (C:Cameo G t)(m:Side): V.freeze m C= iteratedFDeriv ℝ (t+1) (turnSeries (ringT V.δ C)) 0:=(fibres V.hired _ |>.choose_spec C)
def flow := V.s⊓ ⨅ n,(V.freeze (S n)).ker
lemma own (C) : C∈ V.flow S ↔ C∈ V.s ∧ ∀ n,V.freeze (S n) C=0:=by rw [flow,Submodule.mem_inf,Submodule.mem_iInf]; rfl
lemma park : IsClosed (V.flow S:Set (Cameo G t)):= by rw [flow,Submodule.coe_inf,Submodule.coe_iInf]; exact V.quiet.inter (isClosed_iInter fun n=>(V.freeze _).isClosed_ker)

def royal :Submodule ℝ (Cameo G t):= V.s ⊓ (V.flow S)ᗮ
lemma lands : IsClosed (V.royal S:Set (Cameo G t)):= V.quiet.inter (Submodule.isClosed_orthogonal _)
lemma special {C} (h:C∈V.royal S): C∈ V.s:=h.1
lemma necessary {C D}(h:C∈ V.royal S)(hx:D∈V.royal S)(he:∀ n, V.freeze (S n) C=V.freeze (S n) D): C=D:=by
     have hh: C-D∈V.flow S := (V.own S _).mpr ⟨Submodule.sub_mem _ h.1 hx.1,fun n=> by rw [map_sub,he,sub_self]⟩
     have hi : C-D∈ (V.flow S)ᗮ:= Submodule.sub_mem _ h.2 hx.2
     exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜:=ℝ)).mp (hi _ hh))
lemma recruit {C} (h:C∈V.s): ∃ D∈ V.royal S, ‖D‖≤ ‖C‖ ∧ ∀ n,V.freeze (S n) D=V.freeze (S n) C:=by
     let M:=V.flow S; haveI : CompleteSpace M := (V.park S).completeSpace_coe
     let D:= C-M.starProjection C
     have hi : M.starProjection C∈ V.flow S := (M.orthogonalProjectionOnto C).property
     have he:= (V.own S _).mp hi
     refine ⟨D,⟨V.s.sub_mem h he.1,M.sub_starProjection_mem_orthogonal _⟩,?_,fun i=>by rw [show D=C-_ from rfl,map_sub,he.2,sub_zero]⟩
     change ‖C-M.starProjection C‖≤‖C‖
     rw [← M.starProjection_orthogonal_val]; apply (ContinuousLinearMap.le_opNorm _ _).trans; exact mul_le_of_le_one_left (norm_nonneg _) Mᗮ.starProjection_norm_le
lemma recurrences {f:ℕ→Cameo G t}{F b} (h:∀ᶠ i in atTop, f i∈ V.royal S)(hv:Gleam f F b): F∈V.royal S:=by
     let M:= V.royal S; haveI : CompleteSpace M:= (V.lands S).completeSpace_coe
     have he y (hy:y∈Mᗮ) : ⟪y,F⟫_ℝ=0:=by
         rw [real_inner_comm]; exact tendsto_nhds_unique_of_eventuallyEq (hv.testing y) tendsto_const_nhds (h.mono fun i hi=> hy _ hi)
     have hm : F∈ Mᗮᗮ:= he
     rwa [Submodule.orthogonal_orthogonal] at hm
-- Put chron sorted m.Dependency measurable.Prop
protected def Visible (X:ℕ→Atom G (t+1)):=∃ C∈V.royal S, X=ringT V.δ C
lemma presented (X:ℕ→Atom G (t+1))(B:ℝ)(hp:∃ C∈V.s, ‖C‖≤ B ∧ X=ringT V.δ C): ∃ P∈V.royal S,‖P‖≤ B∧∀ i, iteratedFDeriv ℝ (t+1) (turnSeries X (m:=S i)) 0= iteratedFDeriv ℝ (t+1) (turnSeries (ringT V.δ P)) 0:=by
     obtain ⟨Q,h,hC,rfl⟩:=hp; obtain ⟨D,hD,H,H'⟩:= V.recruit S h; exact ⟨D,hD,H.trans hC,fun i=> (V.tells ..).symm.trans ((H' i).symm.trans (V.tells _ _))⟩
end Vow
end YM.Stationary.Shade
