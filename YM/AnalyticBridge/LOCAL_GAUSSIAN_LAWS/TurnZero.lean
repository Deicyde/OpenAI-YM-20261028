import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Residue
import YM.Progress.STATIONARY_SCENES.Response


/-!
# Expend and identify the full affine correction

Orders here post-L also in Cost of Lubricant. True signed link
stencil rules. No change of basis in Room (actual tower coefficients
and area-order release). Don't spend tag probabilities. Test physical
positive directions including on crossings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Function Filter Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Tree Bloch Bid Matrix
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Push.SectorMeasure 
open Progress.StationaryScenes
open scoped Topology InnerProductSpace BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- link convention bookkeeping

lemma swapped (a : Dir G n) (s : Signed) : ‖pulled a s‖ ≤ ‖a‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by unfold pulled; dsimp only; split <;> first | rw [norm_neg]; exact norm_le_pi_norm a _ | exact norm_le_pi_norm a _
lemma converted (x : Dir G n) : Flat.labels (collect G x)=x := by
  funext i; change x (i.1,coord (axisEquiv.symm i.2))=x i; rw [← coord_map,axisEquiv.apply_symm_apply]
lemma turned_repr (a : Dir G n) (s : Signed) : represent (pulled a s)=pull s 0 (represent a) := by
  exact (by simpa using (Work.F03.represent_pulled s a 1).symm)

def blueprint (S : StepData c f) (v : Dir G c) : Dir G f := Flat.labels (linearCopy S.ratio (collect G v))
lemma replica_rep (v : Dir G c) : replica S.ratio (represent v)=represent (blueprint S v) := by
  funext e
  unfold represent; rw [show collect G (blueprint S v)=_ from Flat.collected (linearCopy S.ratio (collect G v))]
  unfold replica increment linearCopy; split <;> simp
lemma blueprint_bill (v : Dir G c) : ‖blueprint S v‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun e => ?_
  unfold blueprint Flat.labels linearCopy; split
  · rw [norm_zero]; exact norm_nonneg _
  exact norm_le_pi_norm v _
lemma sense (G : Gauge) : ∃ N : ℝ, 0≤N ∧ ∀ i : G.Color, ‖i‖ ≤ N*‖i.ofLp‖ := by
  let L := (WithLp.linearEquiv 2 ℝ (G.ColorIndex → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact ⟨‖L‖, norm_nonneg _, fun i => L.le_opNorm i.ofLp⟩

section solve
variable (T : Tube G S) (F : Forest S.ratio) (v : Dir G c)

def doc : Directions G f := collect G (low T F v-blueprint S v)
lemma doc_trunk (i) (h : i∈F.trunks) : doc T F v i=0 := by
  unfold doc low collect stretch blueprint Flat.labels
  dsimp only [Pi.sub_apply]; rw [show axisEquiv.symm (coord i.2)=i.2 from axisEquiv.symm_apply_apply _]; rw [Prod.mk.eta,dif_pos h]; simp

theorem carry_summary (G : Gauge) (P : Patch) (K : KernelChoices) (Pt : Teller G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → S.kernel=K → Pt.Funds S T →
      ∀ (F : Forest S.ratio) (v : Dir G c), ‖doc T F v‖ ≤ C*‖v‖ := by
  obtain ⟨N,hN,he⟩ := sense G
  let C := |Response.total Pt.j 0 Pt.C|; have hc : 0≤C := abs_nonneg _
  refine ⟨N*C+1,by positivity,?_⟩
  intro c f S T hh h0 H F v
  have hP : S.patch.J=Pt.j := H.atStep
  have hv (i : Body 1 f) :
      ∑ b : Body 1 c, |extracted S F (installed S.ratio T.R.A0) i b| ≤ C := by
    let L:=S.patch.L
    have hh : T.R.A0.strip 0 (Pt.C/(L.val:ℝ)) := by
      have ht := H.crosses.2.2.2 [] (by simp)
      simp only [advanceC,List.length_nil,Nat.add_zero,pow_one] at ht
      exact Work.F08.strip_mono ht.1 Pt.width.le le_rfl
    have ht := Response.response_price S le_rfl hh F i
    simp only [Free.crossW,zero_mul, Real.exp_zero,one_mul,Real.norm_eq_abs,hP] at ht
    exact ht.trans (le_abs_self _)
  have hB : ‖low T F v‖ ≤ N*C*‖v‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => (he _).trans ?_
    have hh : ‖(low T F v j).ofLp‖ ≤ C*‖v‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
      change ‖parts G 1 (low T F v) i j‖≤_
      unfold low; rw [Work.F04.parts_stretch,mulVec,dotProduct,Real.norm_eq_abs]
      refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun b => |extracted S F (installed S.ratio T.R.A0) j b| * ‖v‖) (fun b _ => ?_)).trans ?_)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (v b) i).trans (norm_le_pi_norm v b)) (abs_nonneg _)
      rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hv j) (norm_nonneg _)
    exact (mul_le_mul_of_nonneg_left hh hN).trans_eq (by ring)
  unfold doc
  have hℓ (w : Dir G f) : ‖collect G w‖ ≤ ‖w‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm w (i.1,coord i.2)
  apply (hℓ _).trans
  exact (norm_sub_le ..).trans ((add_le_add hB (blueprint_bill v)).trans_eq (by ring))
end solve
-- combine rowzero with exact addition in D channels
lemma xLin_add (n : Side) (W : PathData G) (p : Clip) {C σ Λ : ℝ} (h : W.Bounds p σ C Λ) (H : Bed) (hA : Attached H W) (v w : Dir G n) : xLin p W (v+w) = xLin p W v+xLin p W w := by
  ext i j; change (xLin p W (v+w) i) j=(xLin p W v i) j+(xLin p W w i) j
  simp_rw [xLin_component p W H h hA]; rw [show parts G 1 (v+w) j= parts G 1 v j+parts G 1 w j from rfl,Matrix.mulVec_add]; rfl
lemma pulled_add (s : Signed) (v w : Dir G n) : pulled (v+w) s=pulled v s+pulled w s := by
  funext i; unfold pulled; dsimp only [Pi.add_apply]; split; abel; rfl
lemma zLin_joint (S : StepData c f) (u v : Dir G f) (b : Dir G c) : zLin S (u+v) b = zLin S u b+zLin S v 0 := by
  ext i j
  have h {r n} (x y : Exterior.fieldDir G n r) : ∀ i, Exterior.parts G r (x+y) i = Exterior.parts G r x i + Exterior.parts G r y i := fun k => by ext; rfl
  let X (w : Dir G f) := probe S *ᵥ parts G 1 w j; let k:=Real.sqrt S.kernel.penalty
  change k*(b (pole i) j-X (u+v) (pole i)) = k*(b (pole i) j-X u (pole i))+k*(0-X v _)
  unfold X; rw [h,Matrix.mulVec_add,Pi.add_apply]; ring

/-- Linear *base* at no clipping, no mask, uncut. Uses actual
full Roll transports, not Hodge residual or scalar vision. -/
def firstTerm (T : Tube G S) (v : Dir G c) : LogArray G (Slots S) := fun i =>
  let x := pulled (blueprint S v) i.1; let b := pulled v i.1
  let q:= xLin T.low T.down b
  i.2.elim (fun j => xLin T.high T.up x j-zip (flatF T) q j)
    (fun j => zLin S x b j - zip (flatI T) q j)

theorem rowzero (T : Tube G S) (F : Forest S.ratio) (k : S.Choices) (v : Dir G c) (H L : Bed)
    (hS : S.patch.Branches S.kernel G) {σ C v0 : ℝ}
    (hH : Attached H T.up) (hp : T.up.Bounds T.high σ C v0) {a b : ℝ} (hp' : Floor H T.high f a b) (hb : Sworn H f G)
    {τ E t d b' : ℝ} (hC : Attached L T.down) (hc : T.down.Bounds T.low τ E t) (he : Floor L T.low c d b') (hJ : Sworn L c G)
    (hw : Towers.Diagonal S H L T.R) (hr : Towers.Roll S H L T.R T.high T.low) :
    Flat.ideal T (doc T F v)+firstTerm T v = 0 := by
  funext ⟨s,j⟩
  change Flat.ideal T _ (s,j)+firstTerm T _ (s,j)=0
  let D:=low T F v; let b:=blueprint S v
  have hv : Flat.labels (doc T F v)=D-b := converted _
  obtain ⟨hX,hZ,-⟩ := uncut s T F k hS hw hr v hH hp hp' hb hC hc he hJ
  let B:=pulled v s; let q:=xLin T.low T.down B
  have hV : pulled D s=pulled b s+pulled (D-b) s := by rw [← pulled_add]; congr 1; abel
  unfold Flat.ideal firstTerm; simp only [hv]
  cases j
  next j =>
    set X:=pulled (D-b) s
    change xLin _ _ (pulled D s)=zip (flatF T) q at hX
    rw [hV,xLin_add _ T.up T.high hp H hH] at hX; rw [← hX]; change xLin T.high T.up X j+(xLin T.high T.up (pulled b s) j-(xLin T.high T.up (pulled b s) j+xLin T.high T.up X j))=0; abel
  next j =>
    change zLin _ (pulled D s) B=zip (flatI T) q at hZ
    rw [hV,zLin_joint] at hZ; rw [← hZ]; change zLin S (pulled (D-b) s) 0 j+(zLin S (pulled b s) B j-(zLin S (pulled b s) B j+ zLin S (pulled (D-b) s) 0 j))=0; abel
end YM.AnalyticBridge.LocalGaussianLaws.Lift
