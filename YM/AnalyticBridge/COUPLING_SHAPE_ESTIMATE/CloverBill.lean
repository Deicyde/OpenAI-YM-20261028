import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Delta
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local
import YM.UVNext.PRICED_KERNELS.MaskE


/-! # Normalized curvature subtraction, on the actual flag-read halo.
`shape` is a *value* target but this choice of subtraction also affords
successive left increments and the required zero-affine-Hessian tests of output E. The BILL
here still needs support mass before use, done downstream.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Filter Lattice RG Wilson Work.G07 UVNext.PricedKernels StressFlux Next.Scheduling.Wages
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {p : BudgetPoint} {f : Config G n→ℝ}

lemma needles_local (o : Site n) : LocalOn (ringlet o) (needles (G:=G) o) := by
  intro U V hv
  have he (a b : Step) (h : a.dir≠b.dir) : plate U o a b=plate V o a b := congr_arg G.curvature
    (travel_local _ _ U V (fun e hx hy=>hv e (neighbors o a b h (List.mem_toFinset.mpr hx)) (neighbors o a b h (List.mem_toFinset.mpr hy))))
  funext i; unfold needles clover stencil
  rw [he _ _ i.property.ne,he _ _ i.property.ne,he _ _ i.property.ne,he _ _ i.property.ne]
lemma needles_cont (o : Site n) : Continuous (needles (G:=G) o) := continuous_pi fun i => by
  unfold needles clover stencil plate; fun_prop

def leafPrice (G : Gauge) (p : BudgetPoint) := G.colorScale⁻¹ * feeWalk G 4 p.power p.order

lemma leaf_bill (a b : Step) (ha : a.dir < b.dir) (p : BudgetPoint) (o : Site n) :
    bill p.order (p.dirBound o) (Healthy p.threshold (ringlet o)) (leafPrice G p*p.threshold) (fun U : Config G n => plate U o a b) := by
  let l:=Lattice.oriented a b
  have he := (word_fund o l p (Healthy (G:=G) p.threshold (ringlet o)) (fun U hu => chord_leaf o a b ha hu)).postcomp (projector G)
  have ht (U : Config G n) : (projector G) (wordStamp o l U) = plate U o a b := by
    rw [wordStamp,map_sub]
    change G.curvature _ - _ = _
    have hp : (projector G) 1=0 := by change G.projectColor ((1/2:ℝ) • (1-star 1))=0; simp
    rw [hp,sub_zero]; rfl
  have hu : LeftBound p.order (p.dirBound o) (Healthy p.threshold (ringlet o)) 1
      (G.colorScale⁻¹*(feeWalk G 4 p.power p.order*p.threshold)) (fun U=> projector G (wordStamp o l U)) :=
    bill.le he (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_le_bound (projector G) (inv_nonneg.mpr G.colorScale_pos.le)
      (norm_projector G)) (mul_nonneg (feeWalk_nonneg G 4 p.power p.order) p.threshold_pos.le))
  unfold leafPrice; rw [mul_assoc]; simpa only [ht] using hu

lemma thorn_bill (i : PlaqAxes) (p : BudgetPoint) (o : Site n) :
    bill p.order (p.dirBound o) (Healthy p.threshold (ringlet o)) (leafPrice G p*p.threshold)
      (fun U : Config G n => needles o U i) := by
  let f (a b : Step) (U : Config G n) := plate U o a b
  let Z := Healthy (G:=G) p.threshold (ringlet o); let a:=i.val.1; let b:=i.val.2
  let S:=leafPrice G p*p.threshold; let D := p.dirBound (n:=n) (G:=G) o
  have hs (x y : Step) (h : x.dir < y.dir) : bill p.order D Z S (f x y) := leaf_bill x y h ..
  have he := (hs (posDir a) (posDir b) i.property).add (bill_scalar (-1) (hs (posDir a) (negDir b) i.property))
  have hh := (hs (negDir a) (posDir b) i.property).add (bill_scalar (-1) (hs (negDir a) (negDir b) i.property))
  have hk := bill_scalar ((4:ℝ)⁻¹) (he.add (bill_scalar (-1) hh))
  change bill _ D Z S _
  unfold needles clover stencil
  norm_num [f,sub_eq_add_neg] at hk ⊢
  rw [show (1:ℝ)/4*(S+S+(S+S))=S by ring] at hk; simp only [a,b] at hk; convert hk using 2; abel

private lemma stacked {k : ℕ} {O : Directions G n → Prop} {P : Config G n → Prop} {z : ℝ}
    {f : Config G n → Flux G} (h : ∀ i, bill k O P z fun U => f U i) : bill k O P z f := by
  have hh (l : List (Directions G n)) (hl : l.length ≤ k) (U : Config G n) :
      leftDerivs f l U=fun i => leftDerivs (fun U => f U i) l U := by
    induction l generalizing U with
    | nil => rfl
    | cons A l ih =>
      have hu : l.length ≤ k := by simp at hl; omega
      exact (show HasDerivAt (fun t : ℝ => leftDerivs f l (increment U (t • A))) _ 0 from (hasDerivAt_pi ..).mpr
        fun i => by simp_rw [ih hu]; exact (h i).smooth.has hu U A).deriv
  refine ⟨fun l hl U => ?_,(h probePair).nonneg,fun l hl hL U hU => ?_⟩
  · simp_rw [hh l hl]; exact contDiff_pi.mpr fun i=> (h i).smooth l hl U
  rw [hh l hl, one_pow,mul_one]
  exact (pi_norm_le_iff_of_nonneg (h probePair).nonneg).2 fun i => by simpa using (h i).bound l hl hL U hU

lemma needles_bill (p : BudgetPoint) (o : Site n) : bill p.order (p.dirBound o) (Healthy p.threshold (ringlet o))
    (leafPrice G p*p.threshold) (needles (G:=G) o) := stacked fun i => thorn_bill i p o

/-- Half, because `H` is the Hessian, not the second Taylor coefficient. -/
def cut (f : Config G n→ℝ) (o : Site n) (X : Support n) (U : Config G n) := (1/2:ℝ)* stripJet f o X (needles o U) (needles o U)

def cutPrice (G : Gauge) (p : BudgetPoint) := (1/2:ℝ)* (2^p.order*96) * leafPrice G p^2
lemma cutPrice_nonneg (G : Gauge) (p : BudgetPoint) : 0 ≤ cutPrice G p := by unfold cutPrice; positivity

lemma cut_gi {X} (hs : G.Simple) (h : p.Regular X f) (o) : GaugeInvariant (cut f o X) := by
  intro k U
  have he : needles o (gauge k U)=dye (k o) (needles o U) := needles_mono ..
  simp only [cut,he]; rw [strip_color hs h]

lemma cut_billed {X} (hs : G.Simple) (h : p.Regular X f) (o) {c : ℝ} (hb : p.supBounds o X f c) :
    p.Regular (ringlet o) (cut f o X) ∧ p.supBounds o (ringlet o) (cut f o X) (cutPrice G p*c) := by
  have he := needles_bill (G:=G) p o; let q := stripJet f o X
  have hx := bill_scalar (1/2) (bill_pair he he q)
  have hp : 0 ≤ leafPrice G p := by unfold leafPrice; have := feeWalk_nonneg G 4 p.power p.order; have := G.colorScale_pos; positivity
  have ht:= p.threshold_pos
  refine ⟨reg_bill p _ (fun U V hu=> by unfold cut; rw [needles_local o _ _ hu]) ?_ (cut_gi hs h _) hx, sup_larger (sup_of_bill hx) ?_⟩
  · have hh := needles_cont (G:=G) o; exact continuous_const.mul ((q.continuous.comp hh).clm_apply hh)
  rw [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  calc
    _ ≤ (1/2:ℝ) * (2^p.order*((96/p.threshold^2*c)*(leafPrice G p*p.threshold))*(leafPrice G p*p.threshold)) := by
      gcongr; exact strip_bill hs h o hb
    _ = _ := by unfold cutPrice; field_simp

lemma cut_nil (X) (o) : cut f o X 1=0 := by simp only [cut,clover_zero,map_zero,mul_zero]

lemma cut_jet (hn : 2≤n.val) (hs : G.Simple) {o} {X Y} (ht : X ⊆ Y) (hx : Nonwrapping Y o) (hy : ringlet o ⊆ Y)
    {h : p.Regular X f} (hc : p.Regular (ringlet o) (cut f o X))
    {A B c d e u} (hA : OnStencil o Y c d A) (hB : OnStencil o Y e u B) : H f A B = H (cut f o X) A B := by
  have hh : Nonwrapping X o := fun x he => hx x (ht he)
  let Q := cut f o X; let L:=stripJet f o X
  have hk {C a b} (Hc : OnStencil o Y a b C) : H f C C=H Q C C := by
    let r := fun t : ℝ => needles o (increment 1 (t • C))
    have hp : Tendsto (fun t : ℝ => t⁻¹ • r t) (𝓝[≠] 0) (𝓝 (skew b)) := by
      simpa only [zero_smul,at_zero_increment,clover_zero,sub_zero,zero_add] using (hasDerivAt_iff_tendsto_slope_zero.mp (clover_jet o hn hx Hc hy))
    have hl : Continuous fun w : Flux G => L w w := by fun_prop
    have hu := ((hl.tendsto _).comp hp).const_mul ((1:ℝ)/2)
    have he : Tendsto (fun t : ℝ => Q (increment 1 (t • C)) / t^2) (𝓝[≠] 0) (𝓝 (1/2*L (skew b) (skew b))) := by
      apply hu.congr'; filter_upwards with t; unfold Q cut
      change 1/2*L (t⁻¹ • r t) (t⁻¹ • r t)=1/2*L (r t) (r t) / t^2
      simp only [map_smul,smul_apply,smul_eq_mul]; ring
    rw [from_ray (f:=Q) hs hc he,strip_affine hn hh hs h (Hc.mono ht) (Hc.mono ht)]; unfold L; ring
  have hp := hk (hA.add hB); rw [polar h, polar (f:=Q) hc,hk hA,hk hB] at hp; change _ = H Q A B; linarith
end YM.AnalyticBridge.CouplingShape
