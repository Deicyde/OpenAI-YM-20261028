import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Choir
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ryme


/-!
# Coloring analytic lifts

Gauge covariance on a whole Rx neighborhood with flags held fixed, including
for log trajectories. Interchange finite block trace with contour integrals
ONLY on singular-free probes, even if completion no longer enjoys Area
bounds at these points. Require no actual pricing on full gauges off Health.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Stained
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond  Eider  Hues Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {X : Coat T F} {I : Finset (Tubular f G)} {η r Q Y W : ℝ}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : E → Config G c} {x : E}

def Hue (X : Coat T F) := ContinuousOn (fun s=> X.shutter.pad (glide X.plate s)) (Set.uIcc (0:ℝ) 1)
lemma eventual_hue (h : Glass P X V x j W) (p : Rotator P L η r Q Y X) : ∀ᶠ y in 𝓝 x,Hue (vary X (V y)) := by
  let D:= X.shutter; let U:=Set.uIcc (0:ℝ) 1; let A i:=(vary X (V i)).plate
  have hf : ContinuousAt A x := continuousAt_pi.mpr fun i=> continuousAt_pi.mpr fun j=> (h.vest i j).continuousAt
  have hx : A x=X.plate := by unfold A; rw [h.lifts]; rfl
  have hh k : ∀ᶠ y in 𝓝 x,∀ t∈U,IsUnit (D.principal (glide (A y) t) k).det := by
    let f' (z:E×ℝ):=(D.principal (glide (A z.1) z.2) k).det; let s:={z|IsUnit (f' z)}
    have he t (ht:t∈U) : s∈ 𝓝 (x,t) := by
      have hv : ContinuousAt (uncurry fun i t=> glide (A i) t) (x,t) := continuousAt_const.add (continuous_snd.continuousAt.smul ((show ContinuousAt (A ∘ Prod.fst) (x,t) from ContinuousAt.comp hf continuousAt_fst).sub continuousAt_const))
      have hg:Continuous (fun M : Itinerary.Mat f G=> (D.principal M k).det) := (continuous_id.matrix_submatrix _ _).matrix_det
      have hy:IsUnit (f' (x,t)) := by
        unfold f'; rw [hx]; exact Matrix.isUnit_det_of_right_inverse (((p.scale.glide p.full.hv p.full.hQ t (Set.uIcc_of_le (zero_le_one (α:=ℝ)) ▸ ht)).sub (Embedding.subtype (·∈D.take k))).initial.1)
      filter_upwards [(show ContinuousAt f' (x,t) from hg.continuousAt.comp hv).eventually_ne hy.ne_zero] with v hv using (isUnit_iff_ne_zero.mpr hv)
    obtain ⟨u,v,hu,-,hv,ht',hV⟩:= generalized_tube_lemma (isCompact_singleton (x:=x)) (show IsCompact U from isCompact_uIcc) (isOpen_interior (s:=s))
      (show Set.prod {x} U ⊆ interior s from by rintro ⟨y,z⟩ ⟨hy,hz⟩; have hy:y=x:=Set.mem_singleton_iff.mp hy; subst y; exact mem_interior_iff_mem_nhds.mpr (he z hz))
    filter_upwards [hu.mem_nhds (hv (Set.mem_singleton x))] with y hy t ht using (show (y,t)∈s from interior_subset (hV (show (y,t)∈u.prod v from ⟨hy,ht' ht⟩)))
  filter_upwards [eventually_all.mpr hh] with y hy
  change ContinuousOn (fun t=> D.pad (glide (A y) t)) U; apply continuousOn_pi.mpr; intro i; apply continuousOn_pi.mpr; intro k'; change ContinuousOn (fun t=> D.pad (glide (A y) t) i k') U
  by_cases he : i∈D.take k'
  · let g s:= D.principal (glide (A y) s) k'
    have ht : Continuous g := (strung _).matrix_submatrix _ _
    have hp := flowing _ ht (hy k'); simp only [Window.pad, of_apply,dif_pos he]; exact continuousOn_pi.mp (continuousOn_pi.mp hp ⟨i,he⟩) ⟨k',D.here k'⟩
  simp_rw [D.outside (glide (A y) _) i k' he]; exact continuousOn_const

variable (X : Coat T F) (z : Site c→ G.El) (p : P.Funds S T)
include p
lemma shading (h : Hue X) : Hue (sluice X z) := by
  let E := Hues.sheen X z; let A:= X.plate; let B:= (sluice X z).plate; let D:= X.shutter
  have he t : D.pad (glide B t)=E*D.pad (glide A t)*Eᵀ := by
    let Y:= D.pad (glide B t); have hg : Y*E=E*D.pad (glide A t) := (Hues.commutes X z p t).1 1
    change Y=_; rw [← hg, mul_assoc,Rotation.upside,mul_one]
  change ContinuousOn (fun t=> D.pad (glide B t)) _; simp_rw [he]; exact (continuousOn_const.mul h).mul continuousOn_const
lemma royals (h : Hue X) : let Y:=sluice X z
    (∀ i,ArmA Y.shutter Y.plate i=ArmA X.shutter X.plate i) ∧ (∀ i,ArmS Y.shutter Y.plate i=ArmS X.shutter X.plate i) ∧
    ∀ i, Y.condensation i=X.condensation i := by
  intro Y; let D:=X.shutter; let Z:=Set.uIcc (0:ℝ) 1
  have ha (P: Mat f G) (hh : ContinuousOn (fun t=> D.pad (glide P t)) Z) (s : ℕ) : ContinuousOn
      (fun t=> aSeq D P t s) Z := by
    match s with
    | 0 => exact continuousOn_const
    | 1=> exact hh
    | _+2=> exact ContinuousOn.neg (ContinuousOn.sub ((strung P).continuousOn.mul hh) continuousOn_const)
  have hh (P : Mat f G) (s : ℕ) : ContinuousOn (fun t=> sSeq D P t s) Z := by
    cases s
    · exact continuousOn_const
    · exact ContinuousOn.neg (continuousOn_id.smul continuousOn_const)
  have hx:= shading X z p h; let E:= Hues.sheen X z; have hE i j (ht:Prod.fst i≠Prod.fst j) : E i j=0 := Rotation.off (z ∘ atEdge S) i j ht
  refine ⟨fun i=> stamps_turn _ _ hE (aSeq D Y.plate) (aSeq D X.plate) (fun t i _=> (commutes X z p t).1 i)
    (inverse_up _) (fun i _ => ha _ hx i) (fun i _=> ha _ h i), fun i=> stamps_turn _ _ hE (sSeq D Y.plate)
      (sSeq D X.plate) (fun t i _=> (commutes X z p t).2 i) (inverse_up _) (fun i _=> hh _ i) (fun i _=> hh _ i),fun i=>?_⟩
  let A:=X.plate; let B:=Y.plate
  have hP (P: Mat f G) (hh : ContinuousOn (fun t=> D.pad (glide P t)) Z) : Batch.joint P D i=∫ t in (0:ℝ)..1, (∑ j:G.ColorIndex,intensity D P t 0 (i,j) (i,j)) := by
    have hx : ContinuousOn (fun t=> intensity D P t 0) Z := by simp only [intensity,pow_zero,mul_one]; exact continuousOn_const.mul hh
    exact (intervalIntegral.integral_finsetSum (f:=fun j s=>intensity D P s 0 (i,j) (i,j))
      (fun j _=> (continuousOn_pi.mp (continuousOn_pi.mp hx (i,j)) (i,j)).intervalIntegrable)).symm
  have hf : Batch.joint B D i= Batch.joint A D i := by
    rw [hP _ hx,hP _ h]; refine intervalIntegral.integral_congr (fun t ht=>?_)
    let X' P:= intensity D P t 0
    have hg := (commutes X z p t).1
    have hk:X' B*E=E*X' A := by
      have h₁ : (B-1)*E=E*(A-1):=hg 0; have h₂ : D.pad (glide B t)*E=E*D.pad (glide A t):= hg 1
      simp only [X',intensity,pow_zero,mul_one]; rw [mul_assoc,h₂, ← mul_assoc,h₁,mul_assoc]
    let L (P: Mat f G):= Itinerary.restrict P i i
    change trace (L (X' B))=trace (L (X' A))
    have hb : L (X' B)*L E=L E*L (X' A) := by unfold L; rw [← cross_right hE,← cross_left hE,hk]
    have hC : (L E)ᵀ*L E=1:= pools i hE (inverse_up _); have hv:= mul_eq_one_comm.mp hC
    rw [← Matrix.mul_one (L (X' B)), ← hv, ← mul_assoc, hb,Matrix.trace_mul_comm, ← mul_assoc,hC,Matrix.one_mul]
  have hq : Y.blank.plate=X.blank.plate := neutral Y X rfl
  unfold condensation; change (Batch.joint Y.blank.plate D i-Batch.joint B D i)/_= _; rw [hf,hq]
end YM.ConnectedActivityE6.Blaze.Stained
