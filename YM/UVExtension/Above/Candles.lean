import YM.UVExtension.Above.Facets
import YM.UVExtension.Whirl.Layer

/-! Original stamped pot. Widening/costs are before path. -/
noncomputable section
set_option autoImplicit false
namespace YM.UVExtension.Above
open Function Filter Set RG Wilson Lattice MeasureTheory Precision Metric
open WilsonStartup Start Lamppost Timing Whirl
open Progress.DirectedRecipe Ovens Ovens.Pipes Planned.Port
open Real (log exp)
open scoped Matrix.Norms.Frobenius Topology Classical
variable {G : Gauge}
section base
variable {c : Clip}{p : BudgetPoint}{n:Side}
private def mirror (β:ℝ) (s:Signed)(x:Site n): Takes s x (dictionary G n) (payload c p G n β) := by
  refine ⟨{ ep:= Padded.sends (sheetAction s x), kp:=Padded.sends (footAction s x), reg_site:=fun i=> ?_,reg_support:=fun i=>?_, forced_support:=fun i=>?_,forced_inventory:=fun i=> ?_, forced_tests:=fun i U=> Iff.rfl, valuesE:=fun i U=>?_,valuesK:=fun i U=>?_ }, Padded.sends (reachAction s x),fun i=> ?_, fun i V=>rfl⟩
  · change (eInfo _).site = affine s x (eInfo _).site; rw [Padded.name_sends,eInfo_transport]
  · change (eInfo _).support = Finset.image _ (eInfo _).support; rw [Padded.name_sends,eInfo_transport]
  · change (Padded.name (Start.Foot n) _).val.1 = (Padded.name (Start.Foot n) i).val.1.image _; rw [Padded.name_sends,foot_trans]
  · change (Padded.name (Start.Foot n) _).val.2 = (Padded.name (Start.Foot n) i).val.2.image _; rw [Padded.name_sends,foot_trans]
  · simp only [pours,payload,Padded.name_sends,Padded.fixed_sends]; split <;> first | exact written_oriented .. | exact rfl
  · simp only [pours,payload,Padded.name_sends,Padded.fixed_sends]; split <;> first | exact paid_oriented .. | exact rfl
  change (Padded.name (Reach n) _).val=Finset.image _ (Padded.name (Reach n) _).val; rw [Padded.name_sends]; exact supports_apply ..
end base
variable {a : Levels G} {P:Horizon a} {X:ChartRatio G}
    (k: Kin P X) (N n:ℕ) (s : Signed)(x: Site (a.S.side N n))
def sail (β:ℝ): (temple k N n β).activities.Moves s x := Whirl.pellet (folio _ _) _ (Whirl.widened (mirror β s x))
lemma masts (β v:ℝ): Twins (sail k N n s x β) (sail k N n s x v):= fuseTwins (folio _ _) _ _ _ (wideTwins (mirror ..) _ ⟨⟨rfl,rfl⟩,rfl⟩)
open RG.Shoot
variable (ht: AtTop k) (hp : Allows a N)
include ht hp
lemma sitting {β:ℝ} (hb: β∈band a N): SurfacePay k (permissions a) N n β (pot a N n) (kettle a N n β):= let h:= (Planned.Port.card (k:=k) (p:=n) hp (permissions a) ht).law β hb; ⟨h.ingredients,h.matches_raw,trivial⟩
end YM.UVExtension.Above
