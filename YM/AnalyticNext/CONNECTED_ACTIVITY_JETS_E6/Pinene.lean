import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Duster
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ryme

/-! # Uniform flows at fixed evaluation (arbitrary held Y). This cannot
 drive any Ext.Hit purchases; use only in integrable domination duty.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Glass
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine  Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art  Poll Pond   
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {I : Finset (Bond f)} {η r Q q a β b p v d t W σ : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Y : A→ F.Slice G} (u : A→ E → Directions G f) (hq : Room P S T X.x)
include H

lemma brews : (∀ᶠ i in 𝓝 x,(vary X (C i)).Noncrystal) ∧ ∀ p q, ContDiffAt ℝ (↑j) (fun i=> (vary X (C i)).kernelA p q) x := by
  let f i:= (vary X (C i)).plate; have hx : ∀ i, IsUnit (X.shutter.principal (f x) i).det := by
    rw [show f x=X.plate from by unfold f; rw [H.lifts]; rfl]; exact H.minted
  exact ⟨puncture (A:=f) X.shutter hx (fun i k=>H.vest i k), fun p q=> Vine.orbit X.shutter f (fun i j=> H.vest i j) hx p q⟩

lemma relate (p q) : ContDiffAt ℝ (↑j) (fun i=> (vary X (C i)).relating p q) x :=
    (((H.brews.2 p q).add (H.brews.2 q p)).const_smul (1/2:ℝ))


include hq
lemma fellows (i : Mention c f) (he : X.selected i.1 (spot S i.2)) (hp : Zest u x j) :
    Zest (fun a t=> strain (Art.drive X (C t) (Y a)) i.1 i.2 (u a t)) x j := by
  let p a t:= Art.drive X (C t) (Y a)
  have hh : Zest (fun a t=> (p a t).signal (u a t)) x j := by
    let D:Directions G f →ₗ[ℝ] Directions G f :=
      { toFun:= X.lens
        map_add' g u:= by funext i; by_cases h:X.Hot i <;> simp [Coat.lens,h]
        map_smul' q v:= by funext i; by_cases h:X.Hot i <;> simp [Coat.lens,h] }
    exact (H.weather.via Y).together (hp.replay D.toContinuousLinearMap)
  refine ((Zest.single (H.scroll _ _ he))).together (?_ : Zest (fun a y=> straightened T X.R (pull i.1 0 (C y))
    (displacement i.1 ((p a y).signal (u a y)) (replica S.ratio (C y))) i.2) x j)
  obtain ⟨v,hV⟩:=H.sails
  let s:= v+1; have hs:0≤s:= add_nonneg hV.pos zero_le_one
  obtain ⟨B,hB,hΨ⟩:= hh.post
  obtain ⟨d,hD,hT⟩:= bounded_stencils P S.patch (hq.accepted.knobs ▸ funds_branch hq.accepted)
  let E':= royalty G; have hE :1≤ E':= royalty_ge G
  let D:= 4*(radiusB X.x:ℝ)*(s*royalty G); let X':=d*(E'*(E'*(B*E')*E')); let C':= X'*(1+(D+(s+1+s)+D))^j
  have hZ : 0≤ C':= by
    have hz :0≤D:=mul_nonneg (by positivity) (mul_nonneg hs (zero_le_one.trans hE))
    unfold C' X'; positivity
  refine ⟨C',hZ,?_⟩
  filter_upwards [hΨ,widen_mode hV (show v<s from lt_add_of_pos_right _ zero_lt_one)] with y hh hM a
  have he jp : Brush j B 1 (fun t=> (p a t).signal (u a t) jp) y := by
    let P':Directions G f→L[ℝ]G.Color:=ContinuousLinearMap.proj jp
    have hp: ‖P'‖≤1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u=> by rw [one_mul]; exact norm_le_pi_norm u jp)
    have h := (hh a).report P' hp; rw [one_mul] at h; exact h
  exact (hard_turn i.2 hq (show 0 ≤ E'*(B*E') by positivity) (by positivity : 0≤s+1+s)
    (fun j hj=> Vine.displacement_pay i.1 j B 1 hM (he (Channel.edge i.1 j))) (Blaze.turn hM _) (hT _ _ S T rfl hq.accepted) hD.le).trim

lemma settles : Zest (fun a t=> Vine.voltage (Art.drive X (C t) (Y a))) x j := by
  let g a t := Art.drive X (C t) (Y a)
  have hp i: Zest (fun a y=> Vine.bar (g a y) 0 i) x j := by
    change Zest (fun a y=> if X.selected _ _ then _ else 0) x j; split_ifs
    next ht=> exact (H.fellows (u:=fun _ _=>0) (Y:=Y) hq i ht (Zest.still _)).scalar Coat.scale
    next => exact Zest.still _
  have hL i : Zest (fun a y=> Vine.leanB (g a y) i) x j := Zest.total univ _ (fun t _=> (Zest.single (H.figures t.1 i t.2)).paint
    ((hp t.1).replay (EuclideanSpace.proj (𝕜:=ℝ) (ι:=G.ColorIndex) t.2)))
  have hS i:Zest (fun a t=> Vine.well (g a t) i) x j := (Zest.total univ _ (fun j _=> (Zest.single (H.brews.2 _ _)).paint (hL j))).against
  let P' : (Tubular f G→ℝ) →ₗ[ℝ] Directions G f := { toFun i := erect G i, map_add' x y:=rfl, map_smul' x y:=rfl }
  exact (Zest.folds (f:=fun a t=> well (g a t)) hS).replay P'.toContinuousLinearMap
end YM.ConnectedActivityE6.Blaze.Glass
