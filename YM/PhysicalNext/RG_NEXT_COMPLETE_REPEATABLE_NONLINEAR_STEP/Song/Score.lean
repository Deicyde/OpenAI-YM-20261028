import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels



/-!
# One canonical regular side before reset
 Keep *all* V-dependent masks, and then (with full V and forecast point available)
 enable symmetry average. No multiplier cost in number of periods: weighted
 outputs apply after averaging. This file is generic on campus, enabling grouped
 reformed incidence and not just tuples. Kept supports use regular exact masks.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Song
open Function Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint} {ι κ : Type}

-- lift scalar exact sup costs via given theorem
variable {f : Config G n→ℝ} {X : Support n} {o : Site n}
lemma transSup (θ : Seat n) {a : ℝ} (h : p.Regular X f) (ha : p.supBounds o X f a) :
    p.supBounds (affine θ.1 θ.2 o) (θ.spread X) (f ∘ θ.view) (turnFee p*a) := by
  apply (sup_real (θ.regular h)).1
  exact Push.Local.bound_pull (regular_mapped Complex.ofRealCLM h) ((sup_real h).2 ha) θ.1 θ.2

-- always full-product average: f fixed. Moves on regenerated β do
-- NOT choose an off-mask extension across repeated tags again.
abbrev Rim (n : Side) := (Fintype.card (Seat n):ℝ)⁻¹
lemma balance (n : Side) : (Fintype.card (Seat n):ℝ) * Rim n=1 := mul_inv_cancel₀ (show (Fintype.card (Seat n):ℝ)≠0 from by positivity)
lemma rim_nn (n : Side) : 0 ≤ Rim n:= by unfold Rim; positivity

variable (A : ι → RegularAddress n) (f : ι → Config G n → ℝ)

def line (A : RegularAddress n) (θ : Seat n) : RegularAddress n := ⟨affine θ.1 θ.2 A.site,θ.spread A.support, mem_image_of_mem _ A.anchor⟩
def revolve (j : Seat n × ι) : RegularAddress n := line (A j.2) j.1
def choir (j : Seat n × ι) : Config G n → ℝ := Rim n • (f j.2 ∘ j.1.view)
def whirl (s : Signed) (b : Site n) : Equiv.Perm (Seat n × ι) := Equiv.prodCongr (Seat.move s b) (Equiv.refl _)
lemma spirit (s : Signed) (b : Site n) (i : Seat n × ι) : (revolve A (whirl s b i)).site=affine s b (revolve A i).site ∧
    (revolve A (whirl s b i)).support=(revolve A i).support.image (affine s b) ∧ choir f (whirl s b i)=choir f i ∘ pull s b := by
  refine ⟨?_, i.1.spread_move ..,?_⟩
  · change affine (s*i.1.1) (affine s b i.1.2) (A i.2).site=_
    unfold revolve line
    simp only [affine,Signed.act_add,Signed.act_mul,add_assoc]
  change Rim n • (show Config G n→ℝ from f i.2 ∘ Seat.view (Seat.move s b i.1)) = _; rw [i.1.view_move s b]; rfl
lemma tune (θ : Seat n) (i : ι) (U) (p : BudgetPoint) : masked p.threshold (revolve A (θ,i)).support (choir f (θ,i)) U = Rim n* masked p.threshold (A i).support (f i) (θ.view U) := by
  rw [show masked p.threshold (revolve A (θ,i)).support (choir f (θ,i)) U= _ from mask_mul _ _ (Rim n) _ (f i ∘ θ.view), show (revolve A (θ,i)).support=θ.spread (A i).support from rfl, θ.distribute]; rfl
lemma voices (p : BudgetPoint) (U) (x : ℝ) (H : ∀ θ : Seat n, HasSum (fun i=> masked p.threshold (A i).support (f i) (θ.view U)) x) :
    HasSum (fun i => masked p.threshold (revolve A i).support (choir f i) U) x := by
  have he θ := (H θ).mul_left (Rim n)
  convert Raw.finite_start (κ:=Seat n) (fun i : Seat n × ι=> masked p.threshold (revolve A i).support (choir f i) U) (fun _=> Rim n*x) (fun θ=> by simpa only [tune] using he θ) using 1 with a
  simp only [Finset.sum_const,card_univ,nsmul_eq_mul, ← mul_assoc,balance,one_mul]
lemma spiral {p : BudgetPoint} (k : ι → ℝ) {Z : ℝ} (h : ∀ i,p.Regular (A i).support (f i)) (hp : ∀ i,p.supBounds (A i).site (A i).support (f i) (k i)) (hz : Quotes.early p A k Z) :
    let g (i:Seat n×ι):= Rim n*(turnFee p*k i.2)
    (∀ i, p.Regular (revolve A i).support (choir f i) ∧ p.supBounds (revolve A i).site (revolve A i).support (choir f i) (g i)) ∧
      Quotes.early p (revolve A) g (turnFee p * Z) := by
  intro g
  constructor
  · intro i; obtain ⟨θ,i⟩:=i
    have he:= CouplingShape.sup_scale (Rim n) (transSup θ (h i) (hp i)); rw [abs_of_nonneg (rim_nn _)] at he; exact ⟨CouplingShape.reg_scale _ (θ.regular (h i)),he⟩
  intro x
  let t:= turnFee p; let d:= Rim n; have he:0≤Z:= Cost.nonneg (hz (0:Site n)); have hb:0 ≤ d:= rim_nn _; have ht:0≤t:= (turnFee_pos _).le
  rw [show t*Z=(Fintype.card (Seat n):ℝ)*(d*t*Z) by rw [← mul_assoc, ← mul_assoc,balance]; simp]
  refine Cost.product (Cost.finite _ (by positivity : 0 ≤ d*t*Z)) fun i=> ?_
  let y:= StepData.sendSites i.1 i.2
  have hu : ∀ j, affine i.1 i.2 j=x ↔ j=y.symm x:= fun j=> y.apply_eq_iff_eq_symm_apply
  have hh j : (revolve A (i,j)).site=x ↔ (A j).site = y.symm x := hu _
  have hv j : coverNumber p.B (revolve A (i,j)).support = coverNumber p.B (A j).support := Seat.visit_count i _
  have hx := Cost.scale (hz (y.symm x)) (d*t) (mul_nonneg hb ht)
  convert hx using 2 with r
  dsimp only [g] at *
  simp_rw [hh,hv]; unfold d t; split <;> ring
end YM.PhysicalNext.Repeat.Song
