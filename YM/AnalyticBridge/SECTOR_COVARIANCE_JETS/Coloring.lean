import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Stead
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion
import YM.Work.B16


set_option warningAsError false

/-!
# Identity completion with the delays still after L

Sorted full keys include tree and frozen slots, allΠ endpoint comparisons
also there. Don't price any Gaussian/Jacobian from these *completion*
adjoins. Work to use as needed in comparisons/det calculations beyond the
active proof. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice RG Wilson Pressure Pressure.Tube Precision Exterior Bloch Tree Matrix
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Completion FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent (native Bundle Cost tagPrice)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k n : ℕ} {σ d r C V η u x : ℝ}
variable {ι κ α : Type} [Fintype ι] [Fintype κ]

/-- Zero injection into a WIDE layer in counted coordinates. -/
def paint (A : Directions G c → Matrix ι ι ℝ) (g : Matrix κ κ ℝ) (x : Directions G c) :=
  wide (A x) g

private def coatLeft (ι κ : Type) [Fintype ι] [Fintype κ] : Matrix ι ι ℝ →L[ℝ] Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  LinearMap.toContinuousLinearMap ({
    toFun := fun A => wide A 0
    map_add' := by
      intro a b; ext (i|i) (j|j) <;> simp [wide]
    map_smul' := by
      intro r a; ext (i|i) (j|j) <;> simp [wide] } :
    Matrix ι ι ℝ →ₗ[ℝ] Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
private lemma off_white (p : ι ⊕ κ → Site c) (_ : 0 ≤ C) (l : List (Atom G c)) (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hp : FreeResolvent.Mark.Rates (meterMark G c d) (native c) (p ∘ Sum.inl) (p ∘ Sum.inl) l d C A)
    (hb : FreeResolvent.Mark.Rates (meterMark G c d) (native c) (p ∘ Sum.inr) (p ∘ Sum.inr) l d C B) :
    FreeResolvent.Mark.Rates (meterMark G c d) (native c) p p l d C (wide A B) := by
  constructor; intro i; cases i with
  | inl i =>
    rw [Fintype.sum_sum_type]; simpa only [wide, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
      Function.comp_apply, Matrix.fromBlocks_apply₁₁,abs_zero,mul_zero,Finset.sum_const_zero, add_zero] using hp.rows i
  | inr i =>
    rw [Fintype.sum_sum_type]; simpa only [wide,Matrix.fromBlocks_apply₂₁,Matrix.zero_apply,Function.comp_apply, Matrix.fromBlocks_apply₂₂,abs_zero,mul_zero,
      Finset.sum_const_zero,zero_add] using hb.rows i

lemma white (p : ι ⊕ κ → Site c) (h : 0 ≤ C) (l : List (Atom G c)) (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hp : Bill (meterMark G c d) (native c) (p ∘ Sum.inl) (p ∘ Sum.inl) l d C A)
    (hb : Bill (meterMark G c d) (native c) (p ∘ Sum.inr) (p ∘ Sum.inr) l d C B) :
    Bill (meterMark G c d) (native c) p p l d C (wide A B) := by
  have ht : (wide A B).transpose=wide A.transpose B.transpose := by unfold wide; rw [fromBlocks_transpose,transpose_zero,transpose_zero]
  refine ⟨off_white p h l _ _ hp.1 hb.1,?_⟩
  rw [ht]; exact off_white p h l _ _ hp.2 hb.2
lemma blank_pay [DecidableEq κ] {A : Directions G c → Matrix ι ι ℝ} {B : Directions G c} (p : ι ⊕ κ → Site c)
    (h : RatesPaid (p ∘ Sum.inl) (p ∘ Sum.inl) d C k A B) :
    RatesPaid p p d (max 1 C) k (paint A (1:Gaussian.Table κ)) B := by
  have hl : 1 ≤ max 1 C := le_max_left ..
  let D := fun b => coatLeft ι κ (A b)
  have hx : ContDiffAt ℝ k D B := (coatLeft ι κ).contDiff.contDiffAt.comp B h.smooth
  have ht : paint A (1:Gaussian.Table κ)=fun b => D b+wide 0 1 := by
    apply funext; intro x; unfold paint D; change wide _ _=wide _ _+_
    ext (i|i) (j|j) <;> simp [wide]
  constructor
  · rw [ht]; exact hx.add contDiffAt_const
  intro l he
  have hp := Bundle.mono h le_rfl (le_max_right 1 C)
  by_cases hw : l=[]
  · subst l
    have hs := hp.bound [] he; rw [zeroth] at hs ⊢
    have hr := Cost.Schur.one (D:=native c) (a:=p ∘ Sum.inr) (σ:=d)
    exact white p (zero_le_one.trans hl) [] _ _ hs (Bill.origin _ (hr.mono le_rfl hl))
  rw [ht,jet_add atom l (smooth_of_le hx he) contDiffAt_const,jet_const atom l hw,add_zero]
  rw [show jet atom D l B=wide (jet atom A l B) 0 from jet_linear atom l (coatLeft ι κ) (smooth_of_le h.smooth he)]
  exact white p (zero_le_one.trans hl) l _ _ (hp.bound l he) (Bill.zero (zero_le_one.trans hl))

section slots
abbrev Layer (G : Gauge) (A : Stores S) (F : Forest S.ratio) (x : ℝ) := In x A F (G:=G) ⊕ vacant A F x G

def start (A : Stores S) (F : Forest S.ratio) (i : Layer G A F x) : Site c := S.ratio.parent (sorted A F i).1.1


def painted (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t:S.Choices) (x:ℝ) (V : Config G c) :=
  paint (pilot T A F t x V) (1:Gaussian.Table (vacant A F x G))

lemma even_painted (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t:S.Choices) (x : ℝ) (V : Config G c) :
    ∀ B : Directions G c, (painted T A F t x V B).IsSymm := by
  intro B; unfold painted paint wide Matrix.IsSymm; rw [pilot_eq,fromBlocks_transpose]
  rw [transpose_mul,transpose_transpose,transpose_one, transpose_zero,transpose_zero]
lemma reachLayers (A : Stores S) (F : Forest S.ratio) (hb : 120≤radiusB x) :
    Bars (allPanels A F) (start (G:=G) A F (x:=x)) (radiusB x/60) := by
  intro i j he y hy z hz
  have hv := meetings _ hy; have hp := meetings _ hz
  let u := start A F i; let v := start A F j
  apply (separation_triangle y v z).trans; apply (Nat.add_le_add
    ((separation_triangle y u v).trans (Nat.add_le_add (show separation y u ≤ 1 from (separation_comm ..).trans_le hv) he)) hp).trans
  omega
lemma whole_site (S : StepData c f) (G : Gauge) (v : ℝ) (hv : 0<v) :
    (native c).Volume (fun i : Bond f × G.ColorIndex => S.ratio.parent i.1.1) v (geography S.patch G v) := by
  constructor; intro i
  let w y := rate (-v) (separation i y)
  have hm : ∑ j : Site c, w j ≤ Tier.wealth v := by unfold w; simp_rw [separation_comm i]; exact Tier.land hv _
  change (∑ j : ((Site f × Axis) × G.ColorIndex), w (S.ratio.parent j.1.1)) ≤ _
  calc
    _ = ((Fintype.card G.ColorIndex:ℝ)*(Fintype.card Axis:ℝ))* ∑ j,w (S.ratio.parent j) := by
          simp [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc,mul_left_comm]
    _ = ((Fintype.card G.ColorIndex:ℝ)* ((Fintype.card (Site S.patch.L):ℝ)*(Fintype.card Axis:ℝ)))*∑ j,w j := by
          rw [Work.F01.sum_parent S.ratio w, show S.ratio.count=S.patch.L from rfl]; ring
    _ ≤ _ := le_max_of_le_left (mul_le_mul_of_nonneg_left hm (by positivity))
lemma whole_start (A : Stores S) (F : Forest S.ratio) (x v : ℝ) (hv : 0<v) :
    (native c).Volume (start (G:=G) A F (x:=x)) v (geography S.patch G v) :=
  (whole_site S G v hv).comp (sorted A F).injective
end slots
end YM.AnalyticBridge.Covariance
