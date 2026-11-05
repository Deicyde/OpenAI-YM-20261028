import YM.TraceExtension.Swift.Beak
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Swift
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Matrix Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory
open PhysicalNext.JointLoad.Heir
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{k m:ℕ}{n:Side}
/-- negative action unmasked *in core* (uses associated stencil Y.Prior(P0)) -/
def ochre (R:Rep G n)(x:ℝ)(L:Finset GreenA)(U:Finset ℕ): Peat G n:= -R.beta • mainP R x L-loopP R x U
def relic (R:Rep G n)(J:Dart G n)(x:ℝ)(L:Finset GreenA)(b:Axis):Peat G n:= R.beta • (boom (Meld J x) b 0-rill (mainP R x L) (YCore x J b))
-- Combining. Keep cards actual.Invariant state. L2 records tied on BOTH sets.
lemma rocket(G:Gauge)(h:G.Simple)(S:Stage)(A Y:ℝ)(hp:1 ≤ A)(k m:ℕ)(hk:5≤ k)(hm:48≤ m): ∃ D C:ℝ,0≤ D∧0≤ C ∧ Y≤ C∧∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n)(J:Dart G n), Made S x R→Sight x R J→ |R.beta|≤4*x→
    let p:=k+m+1; let e:= ExtS n x; let y:= high x; let f:=thetaP x
    Craft S x R J p C ∧ ∀ᶠ l:Finset GreenA in atTop,∀ᶠ v:Finset ℕ in atTop,
       let X:=ochre R x l v; Splendor X e p (shear x) C ∧ Drift _ X ∧
       (∀ i, Castle m k (YCore x J i) X x R S D A) ∧
       ∀ i:Axis, ∀ t:Directions G n,‖t‖≤ A→ Allows p (minor (relic R J x l i) (sash S x)) t (swole x):=by
    let p:= k+m+1; obtain ⟨D,C,hD,hC,H⟩:= bravo m k hm A hp G h S
    obtain ⟨E,hE,H'⟩:=stem h S p (by omega) A hp
    let K:=max (max C Y) E; have hv:C≤ K:= le_trans (le_max_left C Y) (le_max_left _ E)
    refine ⟨D,K,hD,hC.trans hv,le_trans (le_max_right ..) (le_max_left ..),?_⟩
    filter_upwards [H,H',creation G h S K p (hC.trans hv),rim_gt 10,Work.E01.radiusB_tendsto.eventually_ge_atTop 2] with x hx hh ht hc hM n R J hS ht' hR
    intro d W; have hT := ht n R J hS ht'; refine ⟨hT,?_⟩
    have hp': puff x+1+4 ≤ high x:=by unfold high; omega
    filter_upwards [hT.cores] with l hl; obtain ⟨h1,h₂,h₃,h₄,h₅⟩:= hl; filter_upwards [hT.milks] with L hL; obtain ⟨ht1,hT2,_⟩:= hL
    intro X; let z:= mainP R x l; let v:=loopP R x L
    have hu: Splendor X W d (shear x) K:= (((h1.scale (- R.beta)).lapse ht1).up (fun _ h=>h) (by rw [abs_neg]; exact add_le_add_left (mul_le_mul_of_nonneg_right hR (le_of_lt (Zn.wake ..))) (wideM x)))
    have hd:Drift _ X:= fun W _ _ F y hp=> ((h₂ W F y hp).const_smul (-R.beta)).sub (hT2 W F y hp)
    refine ⟨hu,hd,fun i=> ?_,fun i=>?_⟩
    · let Y:= YCore x J i; have ht':Clouded Y W:= (hT.cloud i).wider (sprout_mono _ (show puff x≤high x from by omega))
      exact hx n R Y X (Zn.post d X _ _ _ _ W hv hu le_rfl) hd ht' (Zn.follower Y p _ _ _ _ hv (hT.climate i) le_rfl)
    exact hh n R J z i hS hR (mot p _ _ _ _ _ W (le_max_right ..) (h₄ i) le_rfl) (Zn.post _ _ _ _ _ _ W (le_max_right ..) (((hT.bounce i).read 0).up (sprout_mono _ hp') le_rfl) le_rfl) (h₅ i)
end YM.Trace.Swift
#print axioms YM.Trace.Swift.rocket
