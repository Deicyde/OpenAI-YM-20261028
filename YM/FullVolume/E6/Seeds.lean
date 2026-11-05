import YM.FullVolume.E6.Choirs
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
set_option linter.unusedSectionVars false
variable {ι κ θ:Type}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{j:ℕ}{x:E}{r η B:ℝ}{m:ℕ}
abbrev Buds (φ:Filter ℕ)(j:ℕ)(x:E)(A B:ℕ→E→ Matrix ι κ ℝ):=∀ i k,Frill φ j x (fun n y=> A n y i k) (fun n y=> B n y i k)
variable {A B':ℕ→E→ Matrix ι κ ℝ} {K H:ℕ→ E→ Matrix ι ι ℝ}
namespace Buds
lemma pairs (h:Buds φ j x A B') {C D:ℕ→ E→ Matrix κ θ ℝ}(hp:Buds φ j x C D)[Fintype κ] : Buds φ j x (fun n y=>A n y*C n y) (fun n y=>B' n y* D n y) :=fun i k=> Frill.buds Finset.univ fun a _=> (h i a).times (hp _ k)
lemma opp (h:Buds φ j x A B') : Buds φ j x (fun n y=> (A n y).transpose) (fun n y=> (B' n y).transpose) := fun i k=> h k i
lemma append (h:Buds φ j x A B'){C D:ℕ→ E→Matrix ι κ ℝ}(hp:Buds φ j x C D): Buds φ j x (fun n y=>A n y+C n y) (fun n y=>B' n y+D n y) := fun i k=> (h i k).add (hp i k)
lemma below (h:Buds φ j x K H) (f:κ→ι) : Buds φ j x (fun n y=> (K n y).submatrix f f) (fun n y=> (H n y).submatrix f f):= fun i k=>h (f i) (f k)
lemma glintP (h:Buds φ j x A B') : Glints φ (fun n=> A n x) (fun n=> B' n x) :=Glints.fibers fun i=> Glints.fibers fun j=> (h i j|>.crest)
variable {a:ι→ Site c} [Fintype ι]
private lemma lamp (h:Buds φ j x K H) : Frill φ j x (fun n y i k=> K n y i k) (fun n y i k=> H n y i k):= Frill.stocks fun i=> Frill.stocks fun k=>h i k
-- limits are used with actual lower spectral bounds (Age). Don't evaluate det zero
lemma assured [φ.NeBot] {A:ℕ→Matrix ι ι ℝ}{K:Matrix ι ι ℝ}(he:∀ᶠ i in φ,Allow (A i) a m η r B)(h:Tendsto A φ (𝓝 K)): K.PosDef:=by
    have hh i k:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h i) k
    have hp:=he.exists.choose_spec
    refine Control.definite ?_ (fun v=> ?_) hp.down
    · ext i k; simp only [conjTranspose_apply,star_trivial]; refine tendsto_nhds_unique_of_eventuallyEq (hh k i) (hh i k) ?_
      exact he.mono fun n h=> (show A n k i= A n i k from h.symmetry.apply i k)
    exact ge_of_tendsto ((show Continuous (fun x: Matrix ι ι ℝ=>dotProduct v (x *ᵥ v)) by fun_prop).continuousAt.tendsto.comp h) (he.mono fun i hi=> hi.ground v)
variable [DecidableEq ι]
lemma restoreP [φ.NeBot](h:Buds φ j x K H)(he:∀ᶠ n in φ,Allow (K n x) a m η r B): Buds φ j x (fun n y=> (K n y)⁻¹) (fun n y=> (H n y)⁻¹):=by
    intro i k; refine (lamp h).fares (Q:=fun A : ι → ι→ℝ => (Matrix.of A)⁻¹ i k) fun g hg=>?_
    apply jetBack (k:=↑j) (A:=fun s:ι→ι→ℝ=>Matrix.of s) (fun p q=>?_) (isUnit_iff_ne_zero.mpr ((assured he (K:=Matrix.of g) hg).det_pos.ne'))
    · change ContDiffAt _ _ (fun s:ι→ι→ℝ=>s p q) _; fun_prop
lemma renting [φ.NeBot](h:Buds φ j x K H)(he:∀ᶠ n in φ,Allow (K n x) a m η r B): Frill φ j x (fun n y=> Real.log (K n y).det) (fun n y=>Real.log (H n y).det):=by
    refine (lamp h).fares (Q:=fun A:ι→ι→ℝ=> Real.log (Matrix.of A).det) fun g hg=>?_
    refine ((determinant (k:=↑j) (A:=fun s:ι→ι→ℝ=> Matrix.of s) ?_).log (by exact (assured he (K:=Matrix.of g) hg).det_pos.ne'))
    intro p q; change ContDiffAt _ _ (fun s:ι→ι→ℝ=>s p q) _; fun_prop
end Buds
end YM.ConnectedActivityE6.Lim
