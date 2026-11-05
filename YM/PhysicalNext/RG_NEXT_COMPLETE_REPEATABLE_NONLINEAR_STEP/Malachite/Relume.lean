import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orb
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Mineral
import YM.Planned.ATOM_REGULAR_ESTIMATE.Localization

/-!
# Actual V_gauge at a station supplies both mean readings at once

On the fixed stencil Active. Includes physical wake with different Y. No
Stained.vary x not on its fixed sector. Use ANY Y,d pairs in mean comp,
only χ6 variation; don't drop non-Seeds. Rotated Y via `pairs` actual E6
array. V9 must use A *bare*, recomputed Γ separately via Addressed. Tablet
probe sizes valid at native periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Placement
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {E : Support f} {V : Config G c}
    {W : Config G f} {w d t : ℝ}

section Stations
variable (a : Museum F X.x (bareStores S) E Y I) (k : I) (q : Chi)
abbrev pole := S.ratio.parent (a.address k).1

def volume6 (k : I) (V : Config G c) := voltage (vary X V) (a.address k)
def volume9 (W : Config G f) (d : ℝ) (k : I) (V : Config G c) : G.Color := tape (Offset.mean T X.x X.k (bareStores S) F q d (Folio.leaf (bareStores S) F X.x W) V) (a.seat k)
def spot6 (b : Directions G c) := erect G (study X b) (a.seat k)
def spot9 (b : Directions G c) := tape (forecast T X.x F X.k b) (a.seat k)

variable (hB : Room P S T X.x) (b : Folio.Bulletin X.x P T) (hX : ShellAccess S G X.x w X.width t)
    (hy : Disjoint X.seeds.place Y) (g : Site c → G.El) (B : Directions G c) (he : AgreeNear id (pole X a k) (reach X.x) (gauge g V) (increment 1 B))
include he hy
lemma station_charge :
    let Z:= sluice (vary X V) g
    Zone Z (gem Z B) (pole X a k) (reach X.x) := by
  intro Z; refine ⟨rfl,rfl,rfl, fun y hh=> ⟨fun hz=> (Finset.disjoint_left.mp hy hz ?_).elim,fun hz=> ?_⟩,fun _ _=>rfl,he,fun _ _=>rfl,fun _ _=> rfl⟩
  · exact a.stores k (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,hh.trans (by omega)⟩)
  · simp [gem, dry,vary, blank, place] at hz

-- explicitly compare not by definitional equality of dry Coats; Y rotated there.
include hB hX
lemma light6 : G.adjoint (g (pole X a k)) (volume6 X a k V)=spot6 X a k B := by
  let Z:= sluice (vary X V) g
  have hp:= (fastens (vary X V) hB.accepted (show ShellAccess S G (vary X V).x w (vary X V).width t from hX) g).2.2
  change spinRow S g (voltage (vary X V)) (a.address k)=voltage (gem X B) (a.address k)
  rw [← hp]; have hv := local_voltage (show Room P S T Z.x from hB) (station_charge X a k hy g B he) (a.address k) rfl
    (show 17*Z.B≤reach X.x by change 17*radiusB X.x ≤ _; unfold Heir.reach; omega)
  change voltage Z _=voltage _ _; rw [hv]
  suffices hF : bar (gem Z B) 0=bar (gem X B) 0 by unfold voltage well leanB; rw [hF]; rfl
  funext i; unfold bar; rw [if_pos (show (gem X B).selected i.1 (spot S i.2) from X.blank_all _ _),if_pos (show (gem Z B).selected i.1 (spot S i.2) from Z.blank_all _ _),gem,sprig Z _ i hB.accepted,gem,sprig X _ i hB.accepted]; rfl

omit hy hX hB
include b
lemma light9 (d) (W : Config G f) : G.adjoint (g (pole X a k)) (volume9 X a q W d k V)=spot9 X a k B := by
  let Y' := gauge (g ∘ S.ratio.parent) W; let K:= a.seat k
  have hr : Museum.Station Y X.x (pole X a k):= (Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (a.stores _)
  have hx := (a.near_forecast (q:=q) (d:=d) (k:=X.k) b hr B he K (show separation (pole X a k) (pole X a k) ≤ _ by simp) Y')
  rw [(carry_model (q:=q) (d:=d) (A:=bareStores S) (F:=F) (k:=X.k) g V W b.priced).1,ascent_read] at hx
  change G.adjoint (g (pole X a k)) (volume9 X a q W d k V)=expandBare F X.x (forecast T X.x F X.k B) (a.address k) at hx
  rw [hx]; change awaken _ _ _ _=tape _ _; unfold awaken; rw [dif_pos (a.seat k).val.2]; rfl
end Stations
end YM.PhysicalNext.Repeat.Malachite
