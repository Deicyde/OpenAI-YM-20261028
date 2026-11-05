import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Choir
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Hues

/-! # Color-block charges on all choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Hues
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented  Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll  
open Gas Ursell Trees    Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C η r Q Y : ℝ} {R : Rep G f} {L : Side} {B : ℕ}
variable (X : Coat T F) (z : Site c→ G.El) (p : P.Funds S T) (ht : ShellAccess S G X.x W X.width C)
variable (β a : ℝ) (w : Air f G)

private lemma restr (p : Bond f) (v) : (fun i : G.ColorIndex=> (sheen X z*ᵥ v) (p,i))= restrict (sheen X z) p p *ᵥ fun i=> v (p,i) := by
  funext i; simp only [Matrix.mulVec, dotProduct]; rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single p]
  · rfl
  · intro b _ h; apply sum_eq_zero; intro l _; simp only [sheen, Rotation.off (z ∘ atEdge S) (p,i) (b,l) (show p≠b from Ne.symm h),zero_mul]
  simp
private lemma norms (H : Mat f G) (p : Bond f) (he : Hᵀ*H=1) (hh : ∀ i j:Tubular f G,i.1≠j.1 → H i j=0)
    (u v : G.ColorIndex→ℝ) :
    dotProduct (restrict H p p *ᵥ u) (restrict H p p *ᵥ v)=dotProduct u v := by
  let E := restrict H p p; have hg : Eᵀ*E=1 := pools p hh he
  have ht : Eᵀ *ᵥ (E *ᵥ v)=v := by rw [Matrix.mulVec_mulVec,hg,Matrix.one_mulVec]
  conv_rhs => rw [← ht, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
lemma binding (b : ℝ) (u : Directions G f) (i : Bond f) : (sluice X z).cone b (spinRow S z u) i=X.cone b u i := by unfold cone spinRow; rw [G.norm_adjoint]; rfl
lemma mandate (b : ℝ) (u : Directions G f) (Z : Finset (Bond f)) : (sluice X z).enforce b (spinRow S z u) Z=X.enforce b u Z := by unfold enforce; simp_rw [binding]
include p ht
lemma ignition (i : Bond f) : (sluice X z).aperture β (weep X z w) a i=X.aperture β w a i := by
  unfold aperture; rw [fullA X z p ht, binding]; rfl
lemma influence (i : Bond f) : (sluice X z).qfirst β (weep X z w) a i=X.qfirst β w a i := by
  unfold qfirst; rw [ignition X z p ht]; apply congr_arg
  let Y:=sluice X z; let J:=weep X z w; let A:= sheen X z
  let G':= restrict A i i
  have he : A*ᵥ X.hatted β=Y.hatted β := by
    unfold hatted; rw [bCon X z p ht, Matrix.mulVec_smul,(slopeC X z p ht).1, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, show Y.plate*A=A*X.plate from plate_con X z p]
  let u := fun j:G.ColorIndex=>w (i,j); let v:= fun j:G.ColorIndex=> X.hatted β (i,j)
  have hu : (fun j:G.ColorIndex=> J (i,j))=G' *ᵥ u := restr X z i _
  have hv : (fun j:G.ColorIndex=>Y.hatted β (i,j))=G' *ᵥ v := by rw [← he]; exact restr X z i _
  change dotProduct (fun j:G.ColorIndex=> J (i,j)) (fun j:G.ColorIndex=> Y.hatted β (i,j))=dotProduct u v
  rw [hu,hv]; exact norms A i (inverse_up _) (Rotation.off (z ∘ atEdge S)) u v

lemma joinsD (i : Ledger f 2) : (sluice X z).chain β (weep X z w) a i=X.chain β w a i := by
  unfold Coat.chain; rw [ignition X z p ht,ignition X z p ht]; apply congr_arg
  unfold qunique circle; apply congr_arg
  let q:= i.2.1; let l:= i.2.2; let j:= arrive q l; let Y:= sluice X z; let E:= sheen X z; let J:= weep X z w
  let K:= combo q l (X.finale i.1); let L:=combo q l (Y.finale i.1)
  let B:= restrict E q q
  let C:= restrict E j j
  have he : L*C=B*K := by
    refine combo_respects q l (Rotation.off (z ∘ atEdge S)) _ _ ?_; intro t _
    unfold finale; split
    next hr => rw [neg_mul,mul_neg, show Y.shreds*sheen X z = sheen X z * X.shreds from shredsG X z p]
    next => exact plate_con X z p
  let u (j : Bond f) (k:G.ColorIndex) := w (j,k)
  have hh : (fun k:G.ColorIndex=> J (j,k))= C *ᵥ u j := restr X z j _
  have hx : (fun k:G.ColorIndex=> J (q,k))= B *ᵥ u q := restr X z q _
  change dotProduct (fun k:G.ColorIndex=> J (q,k)) (L *ᵥ fun k:G.ColorIndex=> J (j,k))=dotProduct (u q) (K *ᵥ u j)
  rw [hx,hh,Matrix.mulVec_mulVec,he, ← Matrix.mulVec_mulVec]; exact norms E q (inverse_up _) (Rotation.off (z ∘ atEdge S)) _ _

lemma price_halo {Ñ : ChartRatio G} (hÑ : LocalRatio Ñ) (_hP : Room P S T X.x) (hp : 0 < a*X.t) (hx : 4*a*X.t < Ñ.radius)
    (i : Bond f) :
    (sluice X z).gentry Ñ a ((sluice X z).liftA β (weep X z w)) i=X.gentry Ñ a (X.liftA β w) i := by
  let Y:=sluice X z; let k:=X.liftA β w
  unfold gentry; rw [fullA X z p ht,binding]
  by_cases he : X.cone (2*a) k i=0
  · rw [he,zero_mul,zero_mul]
  have hf : k i∈Metric.ball (0:G.Color) Ñ.radius := by
    have he := X.amount (show 0 < 2*a*X.t by rw [mul_assoc]; positivity) _ _ he
    apply Metric.mem_ball.mpr; rw [dist_zero_right]; nlinarith only [hx,he]
  change _ * Real.log (Ñ.J (skew (z _) (k i)))= _
  rw [keyship hÑ _ _ hf]
end YM.ConnectedActivityE6.Hues
