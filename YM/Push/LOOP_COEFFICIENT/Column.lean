import YM.Push.LOOP_COEFFICIENT.DriftWard
import YM.Work.F04.Pairing

/-!
# From the supplied critical branch on a tree to the rooted linear background

E `(A0,0)` in centered, here `(A0,fixRoot * A0)` in rooted conventions;
the latter term is essential. Compare modulo the *actual* linear joint gauge,
consume (do not construct) `Critical` and `Guessed`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Lattice RG Wilson Precision Tree Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f}

def layer (G : Gauge) (c : Side) (i : G.ColorIndex) : Loops.Links G c →ₗ[ℝ] form 1 c :=
    (LinearMap.pi (fun e => LinearMap.proj ((e.1,axisEquiv.symm e.2),i)))

lemma layer_eq (x : Loops.Links G c) (i : G.ColorIndex) : layer G c i x = parts G 1 (chartEquiv G c x) i := by
  funext e; obtain ⟨a,ha⟩ := axisEquiv.surjective e.2
  obtain ⟨y,j⟩ := e; dsimp only at ha; subst j
  simp only [parts, coord_map, chartEquiv_apply]; change x ((y,axisEquiv.symm (coord a)),i) = x ((y,a),i)
  rw [show axisEquiv.symm (coord a) = a from axisEquiv.symm_apply_apply a]

def liftMatrix (G : Gauge) (W : Matrix (Body 1 f) (Body 1 c) ℝ) : Matrix (BondKey G f) (BondKey G c) ℝ :=
    LinearMap.toMatrix' (LinearMap.pi fun i : BondKey G f => (LinearMap.proj (i.1.1,coord i.1.2)).comp (W.mulVecLin.comp (layer G c i.2)))

def liftNodes (G : Gauge) (W : Matrix (Body 0 f) (Body 1 c) ℝ) : Matrix (SiteKey G f) (BondKey G c) ℝ :=
    LinearMap.toMatrix' (LinearMap.pi fun i : SiteKey G f => (LinearMap.proj (i.1,vac)).comp (W.mulVecLin.comp (layer G c i.2)))

lemma liftMatrix_apply (W : Matrix (Body 1 f) (Body 1 c) ℝ) (v : Loops.Links G c) (i) :
    (liftMatrix G W *ᵥ v) i = (W *ᵥ (layer G c i.2 v)) (i.1.1,coord i.1.2) := by rw [liftMatrix,LinearMap.toMatrix'_mulVec]; rfl

lemma liftNodes_apply (W : Matrix (Body 0 f) (Body 1 c) ℝ) (v : Loops.Links G c) (i) :
    (liftNodes G W *ᵥ v) i = (W *ᵥ (layer G c i.2 v)) (i.1,vac) := by rw [liftNodes,LinearMap.toMatrix'_mulVec]; rfl

def rootedMap (G : Gauge) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (φ : Matrix (Body 0 c) (Body 1 c) ℝ) : Matrix (JointKey G c f) (BondKey G c) ℝ :=
    of fun i j => Sum.elim (fun e => liftMatrix G W (e,i.2) j) (fun u => liftNodes G φ (u,i.2) j) i.1

def graph (G : Gauge) (W : Matrix (Body 1 f) (Body 1 c) ℝ) (φ : Matrix (Body 0 c) (Body 1 c) ℝ) :=
    (ContinuousLinearMap.id ℝ (Loops.Links G c)).prod (clm (rootedMap G W φ))

lemma graph_left (W : Matrix (Body 1 f) (Body 1 c) ℝ) (φ : Matrix (Body 0 c) (Body 1 c) ℝ) (v : Loops.Links G c) (i) j :
    (graph G W φ v).2 (.inl i,j) = (W *ᵥ layer G c j v) (i.1,coord i.2) := liftMatrix_apply W v _
lemma graph_right (W : Matrix (Body 1 f) (Body 1 c) ℝ) (φ : Matrix (Body 0 c) (Body 1 c) ℝ) (v : Loops.Links G c) (i) j :
    (graph G W φ v).2 (.inr i,j) = (φ *ᵥ layer G c j v) (i,vac) := liftNodes_apply φ v _

def graft (G : Gauge) (S : StepData c f) (W : Matrix (Body 1 f) (Body 1 c) ℝ) := graph G W (fixRoot S * W)

def sampled (F : Forest S.ratio) (ρ : fieldDir G c 1 → AxisChart G F) (x : Loops.Links G c) : Scene G c f :=
    (x, displacement 1 (mounted F (vary 1 x) (ρ (chartEquiv G c x))))

variable (F : Forest S.ratio) {p : Clip} {W : PathData G} {ρ : fieldDir G c 1 → AxisChart G F}

lemma mounted_flat : mounted F (1:Config G c) 0 = 1 := by
  ext1 (x|x)
  · change lifting F _ _ _ = _; rw [lifted,replica_one]; rfl
  rfl

lemma sampled_zero (hr : Critical F p W ρ) : sampled F ρ 0 = 0 := by
  rw [sampled,vary_zero,map_zero,hr.1,mounted_flat,displacement_self]; rfl

lemma sampled_diff (hr : Critical F p W ρ) : ContDiffAt ℝ ω (sampled F ρ) 0 :=
  contDiffAt_id.prodMk ((matDiffAt_const _).displacement (mounted_diff F ((show ContDiffAt ℝ ω ρ (chartEquiv G c 0) by simpa using hr.2.1).comp
    (f:=chartEquiv G c) 0 (chartEquiv G c).contDiff.contDiffAt) vary_diff) (by simp only [map_zero,hr.1,vary_zero,mounted_flat]))

lemma sampled_joint (hr : Critical F p W ρ) : ∀ᶠ x in 𝓝 0, vary 1 (sampled F ρ x).2 = mounted F (represent (chartEquiv G c x)) (ρ (chartEquiv G c x)) := by
  filter_upwards [(((chartEquiv G c).continuous.tendsto 0).eventually (by rw [map_zero]; exact (mounted_home hr).eventually (vary_displacement 1)))] with x hx
  simpa only [sampled,represent_chart] using! hx

lemma sampled_stationary (A : Matrix (Body 1 f) (Body 1 c) ℝ) (hr : Critical F p W ρ) (hg : Guessed F A ρ) (x : Loops.Links G c) :
    fderiv ℝ (sampled F ρ) 0 x = graph G (extracted S F A) 0 x := by
  let y := chartEquiv G c x
  let V (t : ℝ) := vary (1:Config G c) (t • x)
  let H (t : ℝ) := mounted F (V t) (ρ (chartEquiv G c (t • x)))
  have hH : H 0 = 1 := by simp [H,V,hr.1,mounted_flat]
  let z := (graph G (extracted S F A) 0 x).2
  have hv (i : Bonds f) : paint G _ z (.inl i) = linearCopy S.ratio (collect G y) i + if h : i∈F.trunks then 0 else relative F A y ⟨i,h⟩ := by
    ext j; unfold z; rw [paint_apply,graph_left,layer_eq, ← Work.F04.parts_stretch (S:=S) F A]
    simp only [parts, Bid.stretch, show axisEquiv.symm (coord i.2) = i.2 from axisEquiv.symm_apply_apply _, Prod.mk.eta]
    rfl
  have hz (i : Site c) : paint G _ z (.inr i) = 0 := by ext j; unfold z; rw [paint_apply,graph_right,Matrix.zero_mulVec]; rfl
  have hb := hg y
  have hb (i : F.Free) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp ((ρ (chartEquiv G c (t • x))) i))) (G.colorMat (relative F A y i)) 0 := by
    simp only [map_smul]; have hd := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : F.Free => G.Color) i).hasFDerivAt.comp_hasDerivAt 0 hb
    have he : HasFDerivAt (fun b => G.mat (G.lieExp b)) G.colorMat.toContinuousLinearMap ((ρ ((0:ℝ) • y)) i) := by rw [zero_smul,hr.1, Pi.zero_apply]; exact G.expDiff_zero
    exact he.comp_hasDerivAt 0 hd
  have hd (i : Joint c f) : HasDerivAt (fun t => delta (1:G.El) (H t i)) (paint G _ z i) 0 := by
    refine (show HasDerivAt (fun t => delta (H 0 i) (H t i)) _ _ from delta_rate ?_) |> fun h => by simpa only [hH,Pi.one_apply] using! h
    rw [hH,Pi.one_apply,G.mat_one,mul_one]
    cases i with
    | inr i => rw [hz,map_zero]; exact hasDerivAt_const ..
    | inl i =>
      rw [hv i]
      split
      next hi =>
        have ht (t) : H t (.inl i) = 1 := F.on_tree _ ⟨i,hi⟩
        simp_rw [ht,linearCopy, if_pos (F.trunk_internal (i:=i.2) (by simpa using hi)), add_zero,map_zero]
        exact hasDerivAt_const ..
      next hi =>
        let j : F.Free := ⟨i,hi⟩
        have ht (t) : H t (.inl i) = _ := mounted_free F (V t) (ρ _) j
        have he : HasDerivAt (fun t => G.mat (replica S.ratio (V t) i)) (G.colorMat (linearCopy S.ratio (collect G y) i)) 0 := by
          unfold replica linearCopy; split
          · rw [map_zero]; exact hasDerivAt_const ..
          simp_rw [V, ← represent_chart, map_smul]; exact Work.F03.represent_rate y _
        simp_rw [ht,G.mat_mul]; convert! (hb j).mul he using 1
        have h0 : V 0=1 := by simp [V]
        rw [zero_smul,map_zero,hr.1,Pi.zero_apply, G.mat_lieExp_zero,G.mat_one,one_mul,h0,replica_one,Pi.one_apply,G.mat_one,mul_one,map_add,add_comm]
  refine (side _ ((sampled_diff F hr).differentiableAt (by simp)) x).unique (HasDerivAt.prodMk ?_ ?_)
  · simpa using! (hasDerivAt_id' (0:ℝ)).smul_const x
  simpa only [show fromColor G (Joint c f) (paint G _ z) = z from (paint G _).symm_apply_apply z] using!
    (fromColor G (Joint c f)).hasFDerivAt.comp_hasDerivAt (l:=fromColor G _) (0:ℝ) (hasDerivAt_pi.mpr hd)

lemma centered_graph (A : Matrix (Body 1 f) (Body 1 c) ℝ) (x : Loops.Links G c) :
    graft G S A x = graph G (extracted S F A) 0 x + generator S (0,liftNodes G (straighten S F A) *ᵥ x) := by
  rw [generator_fine,R_tot,LinearMap.toMatrix'_mulVec]; refine Prod.ext (add_zero _ |>.symm) ?_
  funext ⟨i,j⟩; cases i with
  | inl i =>
    change (graph G A _ x).2 _ = _ + paint G _ (braceJoint _ _ _) _ _
    rw [graph_left,graph_left,paint_braceJoint_left, paint_brace]; simp only [positions,Function.comp_apply,Pi.one_apply,G.adjoint_one,
      PiLp.sub_apply,paint_apply,liftNodes_apply, extracted, add_mulVec, ← Matrix.mulVec_mulVec,Pi.add_apply, Exterior.d_sites]; abel
  | inr i =>
    change (graph G A _ x).2 _ = _ + paint G _ (braceJoint _ _ _) _ _
    rw [graph_right,graph_right,paint_braceJoint_right]; simp only [auxiliaries,Function.comp_apply,Pi.one_apply,G.adjoint_one,Matrix.zero_mulVec,Pi.zero_apply,
      zero_add,PiLp.neg_apply,paint_apply,liftNodes_apply, ← Matrix.mulVec_mulVec]
    have hh := congr_fun (Precision.centers F A (layer G _ j x)) (i,vac)
    simp only [centered, Pi.neg_apply] at hh
    rw [hh,neg_neg]
end YM.Push.Loops
