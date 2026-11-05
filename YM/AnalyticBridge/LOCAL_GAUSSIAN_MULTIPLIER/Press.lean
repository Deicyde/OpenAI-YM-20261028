import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Shutter
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.TicketsChart



/-!
# Cost the copy and the snap which stay in the consumer

No-hole flat inverse currencies can't be automatically used; first pass
separate bought mean/dressing tests AT the same reread. Constants in
`Studio` buy from compactness per **link**, not over all torus configs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson ProjectorNext.Equivariance Next.SectorChange
  Next.SectorChange.Gaussian Next.SectorChange.Rows YM.Push.SectorMeasure
  YM.Next.Foundations Precision MeasureTheory Metric Curtain
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

section linkage
open YM.Work.G07
variable {G : Gauge} {c f : Side} (P : BudgetPoint)

def expenditure (G : Gauge) (o u : Site c) := G.colorScale * (P.threshold * (1+(separation u o:ℝ))^P.power)
lemma spend_pos (G : Gauge) (o u : Site c) : 0 < expenditure P G o u := by
  unfold expenditure; apply mul_pos G.colorScale_pos; exact mul_pos P.threshold_pos (by positivity)

lemma edge_rate (e : Edge (Site c)) (o : Site c) (k : ℕ) (U : Config G c) :
    Ticket (P.dirBound o) k U ‖(1:G.Mat)‖ (expenditure P G o e.1) (fun V => G.mat (V e)) := by
  let B := expenditure P G o e.1
  have hb := (spend_pos P G o e.1).le
  refine ⟨?_,norm_nonneg _,hb,fun l hl H => ?_⟩
  · exact ((smooth_link (k:=k) e [] (by simp) U).of_le (budgetThrough _)).contDiffAt
  rw [left_link,Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  induction l with
  | nil => simp [linkPrefix]
  | cons A l ih =>
    have he : ‖G.colorMat (A e)‖ ≤ B := (G.colorMat_norm _).trans_le (mul_le_mul_of_nonneg_left (H A (by simp) _ ) G.colorScale_pos.le)
    rw [linkPrefix_cons,List.length_cons, pow_succ,← mul_assoc]; exact (norm_mul_le ..).trans
      (mul_le_mul (ih (by simp at hl; omega) (fun i hi => H _ (List.mem_cons_of_mem _ hi))) he (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (pow_nonneg hb _)))

lemma copied_price {S : StepData c f} (e : Edge (Site f)) (o : Site c) (k : ℕ) (U : Config G c) :
    Ticket (P.dirBound o) k U ‖(1:G.Mat)‖ (expenditure P G o (S.ratio.parent e.1)) (fun V => G.mat (replica S.ratio V e)) := by
  unfold replica; split
  · simp only [G.mat_one]; exact Ticket.pure (spend_pos ..).le _
  exact edge_rate P (S.ratio.parent e.1,e.2) o ..

lemma carrier (u : G.El) : ‖G.mat u‖ = ‖(1:G.Mat)‖ := (Gauge.unitary_frob (G.mat_mul_star u)).trans (Gauge.unitary_frob (G.mat_mul_star 1)).symm

def mirror (G : Gauge) : G.Mat →L[ℝ] G.Mat := (starL' ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap
def backFactor (G : Gauge) : ℝ := ‖(1:G.Mat)‖ * ‖(1:G.Mat)‖
lemma plate_income {S : StepData c f} (i : Edge (Site f)) (T : G.El) (U : Config G c) (o : Site c) (k : ℕ) :
    Ticket (P.dirBound o) k U (backFactor G) (expenditure P G o (S.ratio.parent i.1))
      (fun V => G.mat (T * (replica S.ratio V i)⁻¹)) := by
  have hv : Ticket (P.dirBound o) k U ‖(1:G.Mat)‖ (expenditure P G o (S.ratio.parent i.1)) (f:=fun V => G.mat (replica S.ratio V i)) := copied_price ..
  have he : Ticket (P.dirBound o) k U ‖(1:G.Mat)‖ (expenditure P G o (S.ratio.parent i.1)) (fun V => (mirror G) (G.mat (replica S.ratio V i))) := by
    refine ⟨(hv.linear (mirror G)).smooth,hv.price_nonneg,hv.radius_nonneg,fun l hl hi => ?_⟩
    erw [linear_parts (mirror G) hv.smooth hl]
    let C := leftDerivs (fun V : Config G c => G.mat (replica S.ratio V i)) l U
    change ‖star C‖ ≤ _; rw [norm_star]; exact hv.price _ hl hi
  exact ((Ticket.pure (le_refl (0:ℝ)) (G.mat T)).mul he).mono (le_of_eq (by rw [carrier T]; rfl)) (by rw [zero_add])
end linkage

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S} {u u' : Spot d}
    {H R K : Type} {X : Support c} {l : Viewport u X H R K}
    {r : ℝ} {k : ℕ} {Z : ChartRatio G}

/-- Uniform receipts for the later charge on plog and the *reciprocal*
profile log used by Fker. Need hZ Ready separately. -/
structure Studio (Z : ChartRatio G) (r : ℝ) (k : ℕ) (L W : ℝ) : Prop where
  size : r<firstRadius G
  patch : r<Z.radius
  frame : ∀ A ∈ G.mat '' (G.lieExp '' closedBall 0 r),Farewell G.plog A k L
  price : ∀ A ∈ closedBall 0 r,Farewell (fun x => -Real.log (Z.scale*Z.J x)) A k W

lemma Studio.make (hp : LocalRatio Z) (hr : r < firstRadius G) (hs : r < Z.radius) (k : ℕ) :
    ∃ L W, Studio Z r k L W := by
  let t := closedBall (0:G.Color) r
  let p := G.lieExp '' t
  have ht : p ⊆ firstChart G := image_mono (closedBall_subset_ball hr)
  let p' := G.mat '' p; have hv : IsCompact p' := ((isCompact_closedBall _ _).image G.lieExp_cont).image G.continuous_mat
  obtain ⟨L,hL,hA⟩ := Farewell.shelf (f:=G.plog) (k:=k) hv (fun i hi => by
    obtain ⟨j,hj,rfl⟩ := hi
    exact ((first_geom G).2.2.2.2.2.2 _ (ht hj)).of_le le_top)
  let f := fun x => -Real.log (Z.scale*Z.J x)
  obtain ⟨W,hW,hB⟩ := Farewell.shelf (p:=t) (f:=f) (k:=k) (isCompact_closedBall _ _) (fun i hi => by
    have he : i∈ball 0 Z.radius := closedBall_subset_ball hs hi
    exact (((contDiffAt_const.mul (hp.germ _ he)).log (mul_pos hp.scale (hp.pos _ he)).ne').neg).of_le le_top)
  exact ⟨L,W,hr,hs,hA,hB⟩

namespace Notice
variable (l) (p : Reel G H R K)

def pressing (U : Config G c) (i : H) := peek G (p.2.2 i*(l.copy U i)⁻¹)

variable {l} {p} {L W : ℝ}

def rung (o : Site c) (i : H) (k : ℕ) := climbing k ((1+backFactor G)*expenditure d.out G o (S.ratio.parent (l.edges (.inl i)).1))



lemma warming (h : Studio d.chart r k L W) (U : Config G c) (ht : Needed l r U p) (i : H) (o : Site c) :
    Ticket (d.out.dirBound o) k U L (rung (l:=l) o i k) (fun V => pressing l p V i) := by
  let B (V : Config G c) := p.2.2 i * (l.copy V i)⁻¹
  let A (V : Config G c) := G.mat (B V)
  let e := l.edges (Sum.inl i)
  have he : Ticket (d.out.dirBound o) k U (backFactor G) (expenditure d.out G o (S.ratio.parent e.1)) A := plate_income (S:=S) d.out e (p.2.2 i) U o k
  have hJ : B U ∈ firstChart G := escape ht h.size i
  have hs : ContDiffAt ℝ k G.plog (A U) := ((first_geom G).2.2.2.2.2.2 _ hJ).of_le le_top
  have hh : Farewell G.plog (A U) k L := h.frame _ (mem_image_of_mem G.mat (ht i))
  refine (he.tip.inspect hh hs).agree ?_
  filter_upwards [(show Continuous B by unfold B; fun_prop).continuousAt ((first_geom G).1.mem_nhds hJ)] with t ht
  exact (peek_ok (le_refl _) (show B t ∈ patchGeom G (firstRadius G) from ht)).symm


end Notice
end YM.AnalyticBridge.LocalGaussian
