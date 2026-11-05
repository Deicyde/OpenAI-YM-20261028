import YM.Extra.SOURCE_HISTORIES.Pencil
import YM.Next.FREE_KERNELS.Amend
import YM.Planned.PRIMARY_INTEGRAL_295.Carrier


/-!
# Torus geometry for the actual linear stationary predictor `A0`

All store edges positive with true start. Fourier normalization inherited
from `Carrier`, ALL torus displacement wrap, including repeated lifts.
T.P.E Tension: at each θ use the ACTUAL block ratio (c=n output) and
operator on `Body`, pull it back when certifying warm/test b via lift
and genuine `T.stencil`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Streets
open Function Filter Set Metric Lattice RG Wilson Labels Source
open Precision Exterior Bloch Work.F08 Tree Next.Free Carrier Place 
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {c f : Side} {S : StepData c f} {G : Gauge} {T : Finset Cover}

section Walk
variable (g : Ratio c f)

lemma around (x : Cover) : wrap f x=g.assemble (wrap c (cellar g.count x),wrap g.count x) := by
  unfold Ratio.assemble; conv_lhs => arg 2; rw [balance g.count x]
  rw [map_add,g.embed_wrap]; abel
lemma owner (x : Cover) : g.parent (wrap f x) = wrap c (cellar g.count x) := by rw [around,g.assemble_parent]
lemma residue (x : Cover) : g.residue (wrap f x) = wrap g.count x := by rw [around,g.assemble_res]
end Walk

abbrev Dir (G : Gauge) (c : Side) := fieldDir G c 1

/- Finite scalar A or coordinate stencil CLM. -/
section Shape
variable {α β : Type*} [Fintype α] [Fintype β]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pledge (W : Matrix α β ℝ) : (β→E) →L[ℝ] (α→E) :=
    ContinuousLinearMap.pi fun i=>∑ j,W i j • ContinuousLinearMap.proj j
omit [Fintype α] in
lemma tagged (W : Matrix α β ℝ) (v:β→E) (i : α) : pledge W v i=∑ j,W i j • v j := by simp [pledge,sum_apply]
omit [Fintype α] in
lemma code (W : Matrix α β ℝ) (v:β→G.Color) (i : α) (j : G.ColorIndex) : pledge W v i j =
    (W.mulVec (fun i=>v i j)) i := by
  let P := EuclideanSpace.proj (𝕜:=ℝ) j
  change P (pledge W v i) = _; rw [tagged, map_sum]; unfold Matrix.mulVec dotProduct; simp only [map_smul]; rfl
end Shape

def aboard (G : Gauge) (c : Side) (b : Dir G c) : Window G.Color := fun x i => collect G b (wrap c x,i)
lemma fare_on (v : Dir G c) : Carries (aboard G c v) 0 ‖v‖ := by
    refine ⟨norm_nonneg _,fun x i=>?_⟩; unfold aboard collect; simpa only [liftCost,pow_zero,mul_one] using norm_le_pi_norm v (wrap c x,Exterior.coord i)

lemma street (g : Ratio c f) (W : Lines g.count) (h : Whole W) (v : Dir G c) :
    aboard G f (pledge (installed g W) v)=applyLine W (aboard G c v) := by
  obtain ⟨σ,C,hσ,hC⟩:= h
  ext1 x; ext1 i; ext j
  let b:=aboard G c v
  change (pledge (installed g W) v) (wrap f x, Exterior.coord i) j= _
  rw [code]; let r:= g.count; let w:=wrap r x; let e:=cellar r x
  unfold Matrix.mulVec dotProduct; rw [Fintype.sum_prod_type, Finset.sum_comm]
  let P:= EuclideanSpace.proj (𝕜:=ℝ) j
  change (∑ α: TypeFace 1,_) = P (∑ s:Axis,stream (member W x i s) e fun z=> b z s)
  rw [map_sum,Fintype.sum_equiv axisEquiv.symm (fun _=>_) (fun s=>∑ y:Site c,(installed g W (wrap f x, Exterior.coord i) (y,Exterior.coord s))*(v (y,Exterior.coord s) j)) ?_]
  · apply Finset.sum_congr rfl; intro k _
    let q:=member W x i k
    have ht : Laurent.Width σ C q:= hC _ _
    have hi := fare_on v
    have hs:= (stream_income hσ ht e 0 hi.1 (fun x=>hi.2 x k)).2.1.of_norm
    unfold stream; rw [P.map_tsum hs]
    simp_rw [installed_sift,owner,residue]
    let g (y:Site c):= v (y,Exterior.coord k) j
    change (∑ x_1,sift q c (wrap c e) x_1 * g x_1) =_
    rw [sift_action (ht.summable hσ.le)]; refine tsum_congr fun z=>?_;
    rw [map_smul]; dsimp only [aboard,collect,g]; simp [P,map_add]
  intro s; rw [show Exterior.coord _ = s from axisEquiv.apply_symm_apply s] -- Coord

section Rig
variable (S)

def cellc {c f : Side} (g : Ratio c f) : Dir G c →L[ℝ] Directions G f :=
    LinearMap.toContinuousLinearMap {
      toFun b := linearCopy g (collect G b)
      map_add' b c := by funext i; unfold linearCopy; split<;>simp [collect, *]
      map_smul' r b := by funext i; unfold linearCopy; split<;>simp [collect, *] }

def tapes (W : Lines S.ratio.count) : Dir G c →L[ℝ] Directions G f :=
    (ContinuousLinearMap.pi fun e:Edge (Site f)=> ContinuousLinearMap.proj (e.1,Exterior.coord e.2)).comp
      (pledge (installed S.ratio W))

variable (F : Forest S.ratio)

/-- backGauge, all endpoints even wrapped. -/
def axisPhi (W : Lines S.ratio.count) : Dir G c →L[ℝ] (Site f→G.Color) :=
    (ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (i,Exterior.vac)).comp
       (pledge (straighten S F (installed S.ratio W)))

-- price before φ removal at e
def tr (W : Lines S.ratio.count) : Dir G c →L[ℝ] Directions G f :=
    (ContinuousLinearMap.pi fun i:Edge (Site f)=>ContinuousLinearMap.proj (i.1,Exterior.coord i.2)).comp
      (pledge (extracted S F (installed S.ratio W)))

def crick (W : Lines S.ratio.count) : Dir G c →L[ℝ] AxisChart G F :=
    (ContinuousLinearMap.pi fun e : F.Free=> ContinuousLinearMap.proj e.val).comp (tr S F W - cellc S.ratio)

lemma crick_relative (W : Lines S.ratio.count) (v : Dir G c) : crick S F W v = relative F (installed S.ratio W) v := by
  ext1 e; ext i; change (tr S F W v e.val - linearCopy S.ratio (collect G v) e.val) i= _
  rw [PiLp.sub_apply]; change (pledge (extracted S F (installed S.ratio W)) v) _ i - ((linearCopy S.ratio (collect G v)) e.val i)= _; rw [code]; rfl

/-- Extend a axisChart with zero trunks. -/
def streamFill : AxisChart G F →L[ℝ] Directions G f := ContinuousLinearMap.pi
  fun e => if h:e ∈ F.trunks then 0 else ContinuousLinearMap.proj ⟨e,h⟩

lemma step_straight (W : Lines S.ratio.count) (b : Dir G c) (e : Edge (Site f)) :
    tr S F W b e = tapes S W b e + axisPhi S F W b (e.1+step e.2)-axisPhi S F W b e.1 := by
  let A:=installed S.ratio W
  ext i; simp only [PiLp.sub_apply,PiLp.add_apply]
  change pledge (extracted S F A) b _ i=pledge A b _ i + (pledge (straighten S F A) b) (e.1+step e.2,Exterior.vac) i - (pledge (straighten S F A) b) (e.1,Exterior.vac) i
  simp_rw [code,extracted,Matrix.add_mulVec]; rw [←Matrix.mulVec_mulVec]; simp only [Pi.add_apply,Exterior.d_sites]; abel

lemma fill_linear (W : Lines S.ratio.count) (b : Dir G c) (e : Edge (Site f)) :
    streamFill S F (crick S F W b) e = tr S F W b e - cellc S.ratio b e := by
  unfold streamFill; rw [ContinuousLinearMap.pi_apply]; split<;> rename_i h; swap; · rfl
  change 0 = _
  rw [show cellc S.ratio b e=0 from if_pos (F.trunk_internal (show _ from h)),sub_zero]; ext i
  change 0 = pledge (extracted S F (installed S.ratio W)) b _ i; rw [code]
  exact (Precision.stays F (installed S.ratio W) (parts G 1 b i) e h).symm


end Rig
end YM.Planned.PrimaryIntegral295.Streets
