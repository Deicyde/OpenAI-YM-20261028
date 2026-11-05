import YM.AnalyticBridge.RESET_INCOME_PORT.LocalPrice
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Plot
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Poles

/-!
# Read both at the physical V-panes. One lambda at **all** probes

Rate on coarse chart variations same for E6 wind & verified Heir kernel.
No smoothing over equality decisions. Even off-support response tests from
V0 priced in same Φ. Lamellar includes smallness on b and orientation costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Malachite
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Placement
open WardBin.Lies Offset Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {X : Coat T F} {I : Type} {Y : Support c} {E : Support f} {V : Config G c}
variable {w d t r Q v m K : ℝ} {n j : ℕ}

lemma sym6 (X : Coat T F) (a : Museum F X.x (bareStores S) E Y I) (V : Config G c) : (lamp6 X a V)ᵀ = lamp6 X a V := by
  exact ((Matrix.isHermitian_iff_isSymm.mp (Window.twin (vary X V).shutter (vary X V).plate)).submatrix _).eq
lemma symR (X : Coat T F) (a : Museum F X.x (bareStores S) E Y I) (B : Directions G c) : (porch6 X a B)ᵀ= porch6 X a B := by
  have hp:= sym6 (gem X B) (show Museum F (gem X B).x (bareStores S) E Y I from a) (increment (1:Config G c) B); exact hp

section grain
variable {I κ : Type} [Fintype I] [NormedAddCommGroup κ] [NormedSpace ℝ κ] {A : Matrix I I ℝ} {q : κ} {B : κ → Matrix I I ℝ} {C : Matrix I I ℝ}
lemma impetus (h : ∀ i j, ‖A i j‖ ≤ 1) (b : ∀ i j, Brush n v r (fun x=> B x i j) q) (i j : I) :
    Brush n ((Fintype.card I:ℝ)*v) r (fun x=> (A * B x) i j) q := by
  simp only [Matrix.mul_apply]; apply Brush.climb (spree Finset.univ _ (fun l=>v) (b i j).pos (fun l _=>?_)) (by simp) le_rfl
  exact ((b l j).smul (A i l)).climb (mul_le_of_le_one_left (b i j).nonneg (h ..)) le_rfl
lemma indent (h : ∀ i j,‖A i j‖≤1) (hc : ∀ i j, ‖C i j‖≤1) (b : ∀ i j,Brush n v r (fun x=> B x i j) q) :
    ∀ i j, Brush n ((Fintype.card I:ℝ)*((Fintype.card I:ℝ)*v)) r (fun x=> (Aᵀ * B x*C) i j) q := by
  intro i j; have he:= impetus (A:=Cᵀ) (fun i j=> hc j i) (B:=fun x=>(Aᵀ*B x)ᵀ) (fun i j=> impetus (A:=Aᵀ) (fun i j=> h j i) b j i) j i
  refine he.shimmy (Eventually.of_forall fun x=>?_); exact congr_fun (congr_fun (transpose_mul (Aᵀ * B x) C) j) i
end grain

section pillar
variable (X : Coat T F) (a : Museum F X.x (bareStores S) E Y I) (k : I) (q : Chi)
    {g : Site c → G.El} {o : Site c} {B : BudgetPoint} (U : Slab G c j)
    (hB : Room P S T X.x) (b : Folio.Bulletin X.x P T) (hX : ShellAccess S G X.x w X.width t)
    (hy : Disjoint X.seeds.place Y)
    (h : Canvas B (pole X a k) (reach X.x) V g n m) (ht : Photic X v r Q n)
    (hx : 2 ≤ n) (hm : 1 ≤ m) (hv : loom B (reach X.x) m*spine B.power (pole X a k) o ≤ v) (he : v ≤ 1)
    (hA : j≤n) (hU : ∀ i,B.dirBound o (U i))

abbrev offsetRun (D : ℝ) (W : Config G f) := volume9 X a q W D k - volume6 X a k
def shot (G : Gauge) (Q r v : ℝ) (n : ℕ) := (Fintype.card G.ColorIndex:ℝ)*sewn 1 (Q*(r+v)*v+Q*v^2) n
include hB b hX hy hA h ht hx hm hv he hU
lemma pounds (D : ℝ) (W : Config G f) : Brush n (shot G Q r v n) 1 (offsetRun X a k q D W ∘ journey V j U) 0 := by
  let H:= launch V (pole X a k) (Heir.reach X.x) g U
  have hg:= dimming (onJourney h U hm hv hA hU) ht.light he hx
  let R:= G.adjoint (g (pole X a k)); let R':= (G.adjoint (g (pole X a k))⁻¹).toContinuousLinearMap
  let Y v:= spot9 X a k (H v)-spot6 X a k (H v)
  have hp: Brush n (shot G Q r v n) 1 Y 0 := by
    refine tie G _ hg.nonneg zero_le_one fun i=>?_
    have he' (p) : Y p i= diver X (H p) (a.seat k,i) := rfl
    simp_rw [he']; let L: Prices G (JointLoad.Heir.clear S X.x F)→L[ℝ]ℝ := ContinuousLinearMap.proj (a.seat k,i)
    have hv : ‖L‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun j=> (norm_le_pi_norm j (a.seat k,i)).trans_eq (one_mul _).symm
    exact ((hg.report L hv).climb (le_of_eq (one_mul _)) le_rfl)
  refine ((hp.report R' (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=>by rw [one_mul]; exact (G.norm_adjoint _ _).le))).climb (le_of_eq (one_mul _)) le_rfl).shimmy ((flowJourney V U |>.eventually h.seen).mono (fun z hz=> ?_))
  unfold Function.comp; unfold Y; rw [← light6 X a k hB hX hy _ (H z) hz, ← light9 X a k q b _ (H z) hz D W]; change _= G.adjoint (g _)⁻¹ (R _ -R _)
  rw [← R.map_sub]; unfold R; rw [← G.adjoint_mul, inv_mul_cancel,G.adjoint_one]; rfl

omit hX
variable [Fintype I] [DecidableEq I]
abbrev sectorRise (g : Site c→G.El) j := zone j j (a.toned g)
omit hB b hy hA h ht hx hm hv he hU k in
lemma radial (g : Site c→ G.El) (j : I) (p q : G.ColorIndex) : ‖sectorRise X a g j p q‖ ≤ 1 := by
  unfold sectorRise Museum.toned; rw [tonewise,poreG]; apply le_trans (PiLp.norm_apply_le ..)
  rw [G.norm_adjoint,ConnectedActivityE6.dot]; exact (OrthonormalBasis.norm_eq_one ..).le

def chordPay (G : Gauge) (Q r v : ℝ) (n : ℕ) := (Fintype.card G.ColorIndex:ℝ)*((Fintype.card G.ColorIndex:ℝ)*sewn 1 (r+(Q+Q)*v) n)
lemma latitude (l : I) (i j' : G.ColorIndex) : Brush n (chordPay G Q r v n) 1 (fun z=> (lamp6 X a-lamp9 X a) (journey V j U z) (k,i) (l,j')) 0 := by
  let H:= launch V (pole X a k) (Heir.reach X.x) g U
  let K:=onJourney h U hm hv hA hU
  let A B := zone k l ((porch6 X a-porch9 X a) (H B)); let T j:= sectorRise X a g j
  have hx' : 1 ≤ n:= by omega
  have he' (p q : G.ColorIndex) : Brush n (sewn 1 (r+(Q+Q)*v) n) 1 (fun x=> A x p q) 0 := by
    refine inclined (f:=fun B => zone k l ((porch6 X a B)-(porch9 X a B)) p q) K he (fun u hu=> ?_) ?_ hx'
    · exact settled.mp ((ht.horizon u (a.colorSeat G (k,p)) (a.colorSeat G (l,q)) hu).separating (ht.peak u (a.colorSeat G (k,p)) (a.colorSeat G (l,q)) hu))
    exact only_price ht.shade.1 le_rfl (a.colorSeat G (k,p)) (a.colorSeat G (l,q))
  apply Brush.shimmy (indent (radial X a g k) (radial X a g l) he' i j')
  refine ((flowJourney V U |>.eventually h.seen).mono (fun z hz=> ?_)); let W:= journey V j U z; have hh := ray6 X a k hB hy g (H z) hz l
  have hp : zone k l (lamp6 X a W)=(T k)ᵀ * zone k l (porch6 X a (H z))* T l:= by
    have hf := congr_arg Matrix.transpose hh; simp only [transpose_mul, transpose_transpose] at hf
    rw [← mul_assoc] at hf; change zone k l (lamp6 X a W)ᵀ= (T k)ᵀ * zone k l (porch6 X a (H z))ᵀ*T l at hf
    rwa [symR, sym6] at hf
  change zone k l (lamp6 X a W) i j'-zone k l (lamp9 X a W) i j'= ((T k)ᵀ * A z * T l) i j'
  have hx := ray9 X a k b g (H z) hz l; rw [hp,hx]
  rw [show A z= zone k l (porch6 X a (H z))-zone k l (porch9 X a (H z)) from rfl,mul_sub,sub_mul]; rfl
end pillar
end YM.PhysicalNext.Repeat.Malachite
