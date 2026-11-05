import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Castro
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Checkered

/-!
# Moment budget for real shift and absorptive ratio

Output wants smallness even with η entries from complete V extension, at
measurement point. Includes ν vehicles and V quoting. Direction budgets high; no
normalization divisor except g per coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen Frond Gate Scroll Vine Tablet
variable {v z r Q s y η γ : ℝ} {j m : ℕ} {U : E → Config G c} {x : E}

lemma tie (G : Gauge) (a : E→ G.Color) (_hv : 0≤v) (he : 0≤r) (hp : ∀ i:G.ColorIndex, Brush j v r (fun x=> a x i) x) :
    Brush j ((Fintype.card G.ColorIndex:ℝ)*v) r a x := by
  let f i (x:E):= a x i • EuclideanSpace.basisFun G.ColorIndex ℝ i
  have hf : (fun x=> ∑ i:G.ColorIndex,f i x)=a := funext fun x=> by
    have he := (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (a x); simpa only [f, EuclideanSpace.basisFun_repr] using! he
  have he' i : Brush j v r (f i) x := by
    let L:= (ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.basisFun G.ColorIndex ℝ i)
    have he := (hp i).report L (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
      intro x; change ‖x • EuclideanSpace.basisFun G.ColorIndex ℝ i‖≤1* _; rw [norm_smul, OrthonormalBasis.norm_eq_one,one_mul,mul_one])); rw [one_mul] at he; exact he
 
  refine Brush.shimmy (spree (Finset.univ (α:=G.ColorIndex)) f (fun _=> v) he (fun i _=> he' i) |>.climb ?_ le_rfl) (Eventually.of_forall fun i=> congr_fun hf.symm i)
  simp

lemma shiver (X : Coat T F) (hA : Allow (vary X (U x)).plate (along S) m η r Q) (hv : γ ≤ retain η r Q)
    (hp : Tablet j γ v z (fun y=> (vary X (U y)).plate) (along S) (along S) x)
    (hs : ∀ i, Brush j s 1 (fun y=> leanB (vary X (U y)) i) x) (hS : 0≤s) (p : Tubular f G) :
    let f:=payE η r Q m; let H:=token j v f; let Y:=tidal γ v (facePrice j X.B m v f) X.B
    let K:= driftP j z
    Brush j (v*((H*Y)*s)) (z+((K+(z+K))+1)) (fun y=> let i := vary X (U y); (i.plate*ᵥ well i+leanB i) p) x := by
  intro f H Y K
  let A y:= (vary X (U y)).plate
  let P y:= X.shutter.pad (A y) - (A y)⁻¹
  let Z y:= leanB (vary X (U y))
  have hv:= treasure X.shutter hp hA hv
  have he := beam_vec (u:=fun y=> (P y).transpose*ᵥ Z y) (hp.tilt le_rfl le_rfl hv.scale (half_le_self hp.scale))
    (mul_nonneg hv.basis hS) (add_nonneg hv.pos zero_le_one) (fun i=>beam_vec hv.reverse hS zero_le_one hs i) p
  refine he.opposite.shimmy ?_
  filter_upwards [(determinant (fun i j=> (hp.singular i j).smooth)).continuousAt.eventually_ne
    (isUnit_det_of_right_inverse hA.initial.1).ne_zero] with y hy
  let i:= vary X (U y)
  have hb : (A y)*ᵥ well i+Z y= -((A y)*ᵥ ((P y).transpose *ᵥ Z y)) := by
    have hy : (A y)*(A y)⁻¹=1 := Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hy)
    have hz : ((A y)⁻¹).transpose=(A y)⁻¹ := by ext s t; simpa only [conjTranspose_apply,transpose_apply,star_trivial] using! (show IsHermitian (A y) from i.balanced).inv.apply s t
    change A y *ᵥ (-(i.kernelA.transpose*ᵥ Z y))+Z y = _
    rw [Matrix.mulVec_neg]; unfold P
    rw [transpose_sub,hz, Matrix.sub_mulVec, Matrix.mulVec_sub,mulVec_mulVec (Z y) (A y) (A y)⁻¹, hy,one_mulVec, show X.shutter.pad (A y)=i.kernelA from rfl]; abel
  exact congr_fun hb p

-- grants pure pricing (no χ equality assumptions elsewhere)
lemma vines (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (K γ W : ℝ) (χ : Chi) (j : ℕ) {η r Q : ℝ} (hT : Torch η r Q)
    {V : ℝ→ℝ} (h : Rate G L (-(1/2)) V) (hv : ∀ᶠ x in atTop,0≤V x) (a : ℝ) :
    ∃ b C : ℝ→ℝ, Rate G L (-(1/2)) b ∧ Rate G L a C ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→ ShellAccess S G x W K γ →
    ∀ (F : Forest S.ratio) (Y : Coat T F) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → Config G c) (z : E), Y.x=x → Y.width=K → Y.χ=χ → Mode U z j (V x) →
      let p i:= vary Y (U i); let X := p z
      X.manifest → Allow X.plate (along S) (tubularPrice G L) η r Q →
        (∀ i, Brush j (|b x|) 1 (fun y => voltage (p y) i) z) ∧
          ∀ β,0<β → β≤2*betaF G x L → ∀ i, Brush j (|C x|) 1 (fun y=> shimmer (p y) β i) z := by
  obtain ⟨Z,hZ,Ha⟩:=bounded_stencils P D hD
  let e := retain η r Q; let t:= P.top.width; let s:= min e (t/2)
  have hs : 0<s := lt_min hT.prices (half_pos P.top.width_pos); have ht : s<t := (min_le_right ..).trans_lt (by unfold t; linarith [P.top.width_pos])
  obtain ⟨M,hM,hp⟩:= luster P L D hD K γ W χ j h hv
  let k:= carat D P L s Z; let m:= tubularPrice G L; let A:=k*k+1; let w:=payE η r Q m
  let b x:= kernelGrowth (radiusB x) G (V x); let g x:= k*|M x| *(1+(b x+1))^j
  let d x:= b x+b x; let l x:= facePrice j (radiusB x) m A w; let p x:=driftP j (d x)
  let f x:= (Fintype.card G.ColorIndex:ℝ) * ((l x*g x)*(1+(p x+1))^j)
  let q x:=tidal s A (l x) (radiusB x); let u x:= A*((token j A w * q x)*g x)
  let H x:= u x*(1+(d x+((p x + (d x+p x))+1)))^j; let D' x:= burst G L x*H x
  have he (g : ℝ→ℝ) (hp : Rate G L 0 g) : Rate G L 0 (fun x=> (1+g x)^j) := by
    simpa only [zero_mul] using! (((Rate.const 1).add hp).pow j)
  have hk:= (jet_growth G L h).weaken (b:=0) (by norm_num)
  have hq := swims G L a (polynomial G L j m A w) hs A
  have hM : Rate G L (-(1/2)) g := by
    unfold g; simp only [mul_assoc]
    have hh:= hM.compare (v:=fun x=> |M x|) (Eventually.of_forall (fun x => (abs_abs _).le))
    simpa only [add_zero] using! ((hh.mul (he _ (hk.add (Rate.const 1)))).mul_left k)
  have hh := hk.add hk; have hd : Rate G L 0 p := hh.mul_left _
  refine ⟨f,D',?_,?_,?_⟩
  · simpa only [add_zero,zero_add] using! ((((polynomial G L j m A w).mul hM).mul (he _ (hd.add (Rate.const 1)))).mul_left (Fintype.card G.ColorIndex))
  · unfold D' H u; convert ((Coat.burst_rate G L).mul (((((hq.mul_left _).mul hM).mul_left A).mul
      (he _ (hh.add ((hd.add (hh.add hd)).add (Rate.const 1))))))) using 1; ring
  filter_upwards [hp,room G P L] with x Hx HZ c f' S T hS hY hF F Y E _ _ U z hx hy he hV V' X h hX
  subst x; let x:= Y.x
  have hz:=Ha _ _ S T hS hY.funds
  have ht := replicaM Y D hS hY.length_eq (HZ _ _ _ _ hY) hV Z hZ hz hs.le ht
  have ha := plates Y D hS hY.length_eq (HZ _ _ _ _ hY) hV Z hZ hz hs.le ‹s<t›
  have hL i : Brush j (g x) 1 (fun y=>leanB (V' y) i) z := (beam_vec ht.reverse
    (u:=fun y i=> stand (bar (V' y) 0) i) (abs_nonneg _) zero_le_one (Hx _ _ S T hS hY hF F Y E U z rfl hy he hV h) i).trim
  have hp : 0 ≤ g x := by dsimp only [g]; have hh : 0≤k:=ht.basis; have he : 0≤ b x:= ht.pos; positivity
  constructor
  · intro i
    have hh:=padjets Y.shutter ha hX (show s≤e from min_le_left ..)
    have he (p) := (beam_vec hh.reverse hp zero_le_one (u:=fun i => leanB (V' i)) hL p).trim
    have hv : Brush j (f x) 1 (fun t=>voltage (V' t) i) z := tie G _ (mul_nonneg (mul_nonneg hh.basis hp) (pow_nonneg (add_nonneg zero_le_one (add_nonneg hh.pos zero_le_one)) j)) zero_le_one (fun p=> (he (i,p)).opposite)
    exact hv.climb (le_abs_self _) le_rfl
  intro β hb hx i
  have hr : 0< (gStep β)⁻¹ := inv_pos.mpr (inv_pos.mpr (Real.sqrt_pos.mpr hb))
  have hh : Brush j (H x) 1 _ z := (shiver Y hX (show s≤e from min_le_left ..) ha hL hp i).trim
  have he := burst_h hx
  apply (hh.smul (-(gStep β)⁻¹)).climb _ le_rfl
  rw [norm_neg,Real.norm_of_nonneg hr.le]; exact (mul_le_mul_of_nonneg_right he hh.nonneg).trans (le_abs_self _)
end YM.ConnectedActivityE6.Blaze
