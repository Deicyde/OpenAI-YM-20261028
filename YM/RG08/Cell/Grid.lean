import YM.RG08.Cell.Bundle

/-!
# Exact packed periodizations including paths across corners
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
variable {α β:Type} {c f L:Side}{K:Kernel α β}

lemma convert_origin (S:StepData c f)(x:Market (Co S.patch.L α)) : (splitCo S.ratio α).symm (wrap c x.1,x.2)=(wrap f (column S.patch.L _ x).1,(column S.patch.L _ x).2) := by
    erw [un_tone]
    refine Prod.ext ?_ rfl
    dsimp [Ratio.assemble,column]; rw [Ratio.embed_wrap,map_add]; exact add_comm _ _
lemma convert_target (S:StepData c f)(x:Co c (Co S.patch.L α)) : let v:=((lift x.1,x.2):Market (Co S.patch.L α));
    (splitCo S.ratio α).symm x=(wrap f (column S.patch.L _ v).1,v.2.2):=by
  intro v; have ht:= convert_origin S v; unfold v at *; dsimp only at ht; rw [wrap_lift] at ht; exact ht

lemma tile_tagged (L:Side) (A:∀ n:Side,Matrix (Co n α) (Co n β) ℝ)(P:Patch)(M:KernelChoices)(he:L=P.L){σ τ p:ℝ}(hs:Tagged σ p K A)(hτ:0≤τ)(ht:τ≤L.val*σ) :
    Tagged τ (Real.exp (8*τ)*p) (tile P.L K) (fun n => let S:=habitat P M n; repackM (splitCo S.ratio _) (splitCo S.ratio _) (A (n*P.L))) := by subst L; exact ⟨tile_price _ hτ ht hs.toPriced,fun _=>tile_torus (habitat P M _) (hs.seen _)⟩
end YM.RG08.Cell
