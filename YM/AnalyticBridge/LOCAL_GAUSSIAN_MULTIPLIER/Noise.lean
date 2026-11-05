import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Hard
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Survey

/-!
# The committed bend of the noise gate with ALL possible U inputs held

The hold proof uses the actual tag stencils even if likelihoods have
vanished. Pre-L chart bounds and geometry weights explicit. Bill at
this height (width w = W*fire), no pre-L assumptions on the ratios of
widths. Analogous price for any similarly extended displacement switch.
Never into the sharp derivative budgets without the marked footprints. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure ProjectorNext.Equivariance Next.SectorChange
  Next.SectorChange.Gaussian Next.SectorChange.Rows YM.Push.SectorMeasure
  YM.Next.Foundations Precision MeasureTheory Metric Curtain
open Spot Viewport Notice
open scoped Topology BigOperators Matrix.Norms.Frobenius YM.Push.SectorMeasure ContDiff Classical
attribute [local instance] Gauge.frobInner

variable {c f : Side} {G : Gauge}

private def place (G : Gauge) (q : Chi) (x : G.Mat) := q.read (‖x‖^2)
private lemma places_diff (G : Gauge) (q : Chi) : ContDiff ℝ ∞ (place G q) :=
    q.smooth.comp (contDiff_id.norm_sq ℝ)
private lemma places (G : Gauge) (q : Chi) (k : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ x,Farewell (place G q) x k C := by
  obtain ⟨c,h1,he⟩ := Farewell.shelf (isCompact_closedBall (0:G.Mat) 2) (fun i _ => ((places_diff G q).of_le (budgetThrough k)).contDiffAt)
  refine ⟨c,h1,fun i => ?_⟩
  by_cases h : ‖i‖ ≤ 2
  · exact he _ (by simpa)
  apply Farewell.dead (zero_le_one.trans h1)
  filter_upwards [continuous_norm.continuousAt (x:=i) |>.eventually (lt_mem_nhds (lt_of_not_ge h))] with j hj
  exact q.to_zero _ (by nlinarith only [show 2<‖j‖ from hj])

def participation (χ : Chi) (w : ℝ) (Q : Config G c) (i : Bond c) (U : Config G c) := χ.innerShare w (wire Q U i)

private def observed (Q : Config G c) (i : Bond c) (U : Config G c) := G.mat (U i*(Q i)⁻¹)-1

def rayCost (G : Gauge) (w t : ℝ) := (1+backFactor G+‖(1:G.Mat)‖)* (max 1 ‖(w*G.colorScale)⁻¹‖ * t)

lemma participates (C : Chi) (k : ℕ) : ∃ K : ℝ,1 ≤ K ∧ ∀ (w : ℝ), 0<w →
    ∀ (c : Side) (i : Bond c) (Q : Config G c) (t : BudgetPoint) (o : Site c) (U : Config G c),
    let u := climbing k (rayCost G w (expenditure t G o i.1))
    Ticket (t.dirBound o) k U 1 ((1+K)*u) (participation C w Q i) ∧
      Ticket (t.dirBound o) k U 1 ((1+K)*u) ((fun _ => 1)-participation C w Q i) := by
  obtain ⟨L,hL,hh⟩ := places G C k
  refine ⟨L,hL,?_⟩
  intro w hw c i Q t o U R
  let E := t.dirBound o (G:=G); let r := expenditure t G o i.1
  let e := (w*G.colorScale)⁻¹; let f := fun V => e • observed Q i V
  have hx : Ticket E k U (backFactor G) r (fun V => G.mat (V i*(Q i)⁻¹)) := ((edge_rate t i o k U).mul
    (Ticket.pure (le_refl 0) (G.mat (Q i)⁻¹))).mono (le_of_eq (by rw [carrier]; rfl)) (by rw [add_zero])
  have hp := ((hx.sub (Ticket.pure hx.radius_nonneg (1:G.Mat))).tip).indiv e
  have hi : Ticket E k U L R (place G C ∘ f) := by
    refine (hp.inspect (hh _) ((places_diff G C).of_le (budgetThrough _)).contDiffAt).mono le_rfl (le_of_eq ?_)

    unfold R rayCost e; congr 1; ring
  have he : participation C w Q i=place G C ∘ f := by
    ext x
    simp only [participation,place,f,comp_apply,Chi.innerShare, norm_smul,Real.norm_eq_abs]
    rw [abs_of_pos (inv_pos.mpr (mul_pos hw G.colorScale_pos))]
    change C.read ((‖observed Q i x‖ / G.colorScale / _ )^2)= _
    congr 1; rw [mul_inv_rev]; ring
  rw [he]
  obtain ⟨ha,hb⟩ := C.range (‖f U‖^2)
  refine ⟨hi.tip.with_one ((Real.norm_of_nonneg ha).trans_le hb) le_rfl,?_⟩
  let f' := place G C ∘ f
  rw [sub_eq_add_neg]
  refine ((Charge.freeze _ (le_refl 0)).add hi.tip.left_neg).radius (by rw [zero_add]) |>.with_one ?_ le_rfl
  change ‖1 + -f' U‖ ≤ 1; rw [← sub_eq_add_neg]
  exact (Real.norm_of_nonneg (sub_nonneg.mpr hb)).trans_le (sub_le_self _ ha)

variable {S : StepData c f} {d : Desk G S} {u : Spot d} {H R K : Type} {X : Support c}
    {l : Viewport u X H R K} {p : Reel G H R K} [Fintype H] [Fintype R]
namespace Notice
variable (a : Notice l)

def forward (j : Bond c) (V : Config G c) (p : Display G H R K) := u.noiseBit j V (a.pad V p)
lemma forward_agrees (j : Bond c) (hS : S.patch.Branches S.kernel G) {Q Q' : Config G f}
    (hq : Agrees (predictorUses S j) Q Q') (V : Config G c) : u.noiseBit j V Q=u.noiseBit j V Q' := by
  unfold noiseBit wire; rw [show S.prediction Q _ j=S.prediction Q' u.k j from knows_bond u j hS _ _ hq]
lemma forecast (k : ℕ) (hS : S.patch.Branches S.kernel G) : ∃ W : ℝ,1 ≤ W ∧
    ∀ (j : Bond c) (U : Config G c) (o : Site c) (p : Reel G H R K) (r : ℝ),
    Ready d.chart d.g r → Notice.Had (l:=l) r U p → l.Latches (predictorUses S j) →
    let t := d.W*fiery G d.betaHat S.patch.L
    Ticket (d.out.dirBound o) k U 1 ((1+W)*climbing k (rayCost G t (expenditure d.out G o j.1)))
      (fun V => a.forward j V (p.1,a.imprint V p)) ∧ (u.Clearing U → ∀ P : Visual u,
      a.forward j U (l.info P)=u.noiseBit j U (u.hard U P)) := by
  obtain ⟨v,hv,he⟩ := participates (G:=G) d.profile k
  refine ⟨v,hv,?_⟩
  intro j U o p r hr hp hh t
  refine ⟨?_,fun hf P => forward_agrees j hS
    (a.enables U P _ hf hh) _⟩
  let B := a.pad U (p.1,a.imprint U p)
  let Q := S.prediction B u.k
  obtain ⟨hA,hV⟩ := he t (mul_pos d.paidW d.paidScale) c j Q d.out o U
  have hi : Ticket (d.out.dirBound o) k U 1 ((1+v)*climbing k (rayCost G t (expenditure d.out G o j.1)))
    (fun V => u.noiseBit j V B) := by unfold noiseBit; dsimp only; split <;> first | exact hV | exact hA
  apply hi.agree
  filter_upwards [still hr.ins hp] with W hW
  exact forward_agrees j hS (a.holds hr U W p hp hW hh) _
end Notice
end YM.AnalyticBridge.LocalGaussian
