import YM.Push.LOOP_COEFFICIENT.Moves
import YM.Push.LOOP_COEFFICIENT.Shell

/-!
# Exact finite gauge covariance of the scalar matrices

Uses left increments, with the adjoint at the initial site, NOT linear gauge
substitution in exponential coordinates. Includes off-shell rules (around
regular points) for the rooted drift test. Fine reference also uses initial-site
convention for its mass.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Set Function Filter Lattice RG Wilson Precision Tree Exterior
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {m : Type} [Fintype m] [DecidableEq m]
variable {c f n : Side} {S : StepData c f}

def adjoints (u : m → G.El) := direct id (G.adjoint ∘ u)

lemma adjoints_ortho (u : m → G.El) : ortho (adjoints u) := direct_ortho id Function.bijective_id _ (fun _ _ => G.norm_adjoint ..)

@[simp] lemma paint_adjoints (u : m → G.El) (a : Array G m) (x) : paint G m (adjoints u *ᵥ a) x = G.adjoint (u x) (paint G m a x) :=
  paint_direct ..

def linkAdj (u : NodeField G n) := adjoints (u ∘ (Prod.fst : Bonds n → Site n))

def jointAdj (k : NodeField G f) (u : NodeField G c) := adjoints ((k ∘ (Prod.fst : Bonds f → Site f)) ⊕ᵥ u)

lemma vary_gauge (U : Config G n) (k : NodeField G n) (a : Loops.Links G n) :
    vary (Lattice.gauge k U) (linkAdj k *ᵥ a) = Lattice.gauge k (vary U a) := by
  funext i; unfold linkAdj Lattice.gauge vary; rw [paint_adjoints,Function.comp_apply,bump_transform]

lemma vary_joint (U : Loops.Inputs G c f) (k : NodeField G f) (u : NodeField G c) (a : Loops.Dual G c f) :
    vary (gaugeJoint S k u U) (jointAdj k u *ᵥ a) = gaugeJoint S k u (vary U a) := by
  funext i; rw [vary, jointAdj,paint_adjoints]; cases i with
  | inl i => exact bump_transform (U _) _ _ _
  | inr i => exact bump_transform (U _) _ _ _

lemma portion_linkAdj (k : NodeField G n) (i : Axis) (a : Loops.Links G n) : portion i (linkAdj k *ᵥ a) = adjoints k *ᵥ portion i a := by
  funext ⟨j,a'⟩; change paint G _ (adjoints (k ∘ (Prod.fst : Bonds n → Site n)) *ᵥ a) (j,i) a' = paint G _ (adjoints k *ᵥ portion i a) j a'; simp only [paint_adjoints]; rfl

lemma R_g_carries (k : NodeField G n) (U : Config G n) : Carries (linkAdj k) (adjoints k) (R_g U) (R_g (Lattice.gauge k U)) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, R_g,R_g,LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
  apply (paint G (Bonds n)).injective; ext1 i
  simp only [linkAdj,paint_brace,paint_adjoints,Function.comp_apply,map_sub,Lattice.gauge,← G.adjoint_mul,inv_mul_cancel_right]

lemma projectFine_carries (k : NodeField G f) (u : NodeField G c) : Carries (linkAdj k) (jointAdj k u)
    (projectFine G c f) (projectFine G c f) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, projectFine,LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]; funext i
  change paint G _ (adjoints _ *ᵥ _) _ _ = paint G _ (adjoints _ *ᵥ _) _ _
  simp only [paint_adjoints]; rfl

/-- Regularity window for all the rooted rules. -/
structure Beam (t : S.Choices) (U : Loops.Inputs G c f) : Prop where
  bonds : MatDiffAt (Zmap t ∘ vary U) 0
  patch : MatDiffAt (Psi t ∘ vary U) 0

lemma beam_near (h : S.patch.Branches S.kernel G) (t : S.Choices) : ∀ᶠ U in 𝓝 1, Beam t (G:=G) U := by
  have hu : ∀ᶠ U : Loops.Inputs G c f in 𝓝 1, MatDiffAt (Zmap t ∘ vary U) 0 := eventually_all.mpr fun i =>
    smooth_near (f:=fun U => G.mat (Zmap t U i)) ((Zmap_diff h t (by simp) vary_diff) i)
  have hx : ∀ᶠ U : Loops.Inputs G c f in 𝓝 1, MatDiffAt (Psi t ∘ vary U) 0 := eventually_all.mpr fun i =>
    smooth_near (f:=fun U => G.mat (Psi t U i)) ((Psi_diff h t (by simp) vary_diff) i)
  filter_upwards [hu,hx] with U hu hx; exact ⟨hu,hx⟩

lemma X₀_carries (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    {U : Loops.Inputs G c f} (h1 : Beam t U) (h2 : Beam t (gaugeJoint S k u U)) :
    Carries (adjoints k) (jointAdj k u) (X₀ t U) (X₀ t (gaugeJoint S k u U)) := by
  have hv {U : Loops.Inputs G c f} (he : Beam t U) : MatDiffAt (fun a => (Psi t (vary U a))⁻¹) 0 := fun i => mat_inv_diff (he.patch i)
  refine carries_linear (localize_diff (hv h1)) (localize_diff (hv h2)) (localize_motion _ _ (φ:=fun V x => k x * V x * (u (S.ratio.parent x))⁻¹) (hv h1) ?_ ?_)
  · refine Filter.Eventually.of_forall (fun v => ?_); rw [vary_joint]; ext1 x
    change (Psi t _ x)⁻¹ = _
    rw [Psi_gauge h,Pi.inv_apply]; group
  intro v; ext1 x
  simp only [vary,paint_adjoints, Pi.inv_apply,Psi_gauge h, _root_.mul_inv_rev, inv_inv]
  rw [← mul_assoc,bump_transform]

lemma completion_carries (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    {U : Loops.Inputs G c f} (h1 : Beam t U) (h2 : Beam t (gaugeJoint S k u U)) :
    Carries (adjoints k) (jointAdj k u) (completion t U) (completion t (gaugeJoint S k u U)) := by
  have hR := R_g_carries k (positions U)
  have hA := dressing_motion hR (adjoints_ortho _) (adjoints_ortho _) (mu S)
  exact (((regulation_motion hA).mul (hR.adj (adjoints_ortho _) (adjoints_ortho _))).mul (projectFine_carries k u)).add
    (((hA.pow depth).mul (X₀_carries h t k u h1 h2)).smul _)

lemma Zmap_motion (h : S.patch.Branches S.kernel G) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    {U : Loops.Inputs G c f} (h1 : Beam t U) :
    localize (Zmap t) (gaugeJoint S k u U) ∘ clm (jointAdj k u) =ᶠ[𝓝 0] clm (linkAdj u) ∘ localize (Zmap t) U :=
  localize_motion _ _ (φ:=Lattice.gauge u) h1.bonds (Filter.Eventually.of_forall (fun v => by rw [vary_joint,Zmap_gauge h]))
    (fun v => by rw [Zmap_gauge h,vary_gauge])

lemma acceleration_carries (h : S.patch.Branches S.kernel G) (t : S.Choices) (v : Loops.Links G c) (k : NodeField G f) (u : NodeField G c)
    {U : Loops.Inputs G c f} (h1 : Beam t U) (h2 : Beam t (gaugeJoint S k u U)) :
    Carries (jointAdj k u) (jointAdj k u) (acceleration (Zmap t) U v) (acceleration (Zmap t) (gaugeJoint S k u U) (linkAdj u *ᵥ v)) :=
  carries_twist (adjoints_ortho _) (adjoints_ortho _) (localize_diff h1.bonds) (localize_diff h2.bonds) (Zmap_motion h t k u h1) v

lemma penalty_gauge (k : NodeField G c) (V U : Config G c) : penalty S (Lattice.gauge k V) (Lattice.gauge k U) = penalty S V U := by
  unfold penalty
  exact congr_arg (S.kernel.penalty * ·) (Finset.sum_congr rfl (fun i _ => by
    simp only [Lattice.gauge]; rw [show (k _ * V i * _⁻¹ * (k _ * U i * _⁻¹)⁻¹ : G.El) = k i.1 * (V i * (U i)⁻¹) * (k i.1)⁻¹ by group,G.price_conj]))

variable {p : Clip} {W : PathData G} {σ C Λ : ℝ}

lemma reference_carries (hw : W.Bounds p σ C Λ) (μ : ℝ) (k : NodeField G n) (U : Config G n) :
    Carries (linkAdj k) (linkAdj k) (reference μ p W U) (reference μ p W (Lattice.gauge k U)) :=
  reference_motion (adjoints_ortho _) (adjoints_ortho _) (R_g_carries k U) (portion_linkAdj k)
    (invariant_cost (adjoints_ortho _) (Work.F02.mainTerm_contDiffAt hw vary_diff)
      (Eventually.of_forall fun v => congr_arg (mainTerm p W) (vary_gauge U k v) |>.trans (Work.F05.mainTerm_gauge hw _ k))) μ

lemma vector_carries (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    (V : Config G c) {U : Loops.Inputs G c f} (h1 : Beam t U) (h2 : Beam t (gaugeJoint S k u U)) :
    let V' := Lattice.gauge u V; let U' := gaugeJoint S k u U; let g := jointAdj k u
    Carries g g (vector p W t V U) (vector p W t V' U') ∧ Carries g g (baseVector p W t V U) (baseVector p W t V' U') := by
  intro V' U' g
  have hc := completion_carries h t k u h1 h2
  have ha := (hc.adj (adjoints_ortho _) (adjoints_ortho _)).mul hc
  have hf : ContDiffAt ℝ ω ((mainTerm p W ∘ positions) ∘ vary U') 0 := Work.F02.mainTerm_contDiffAt hw (A:=positions ∘ vary U') (fun _ => vary_diff _)
  have hb : Carries g g (cost (mainTerm p W ∘ positions) U) (cost (mainTerm p W ∘ positions) U') :=
    invariant_cost (adjoints_ortho _) hf (Eventually.of_forall fun v => by change mainTerm _ _ (positions (vary U' (g *ᵥ v))) = _;
                                                                            unfold U' g; rw [vary_joint]; exact Work.F05.mainTerm_gauge hw _ k)
  have hd := carries_linear (localize_diff h1.bonds) (localize_diff h2.bonds) (Zmap_motion h t k u h1)
  refine ⟨(invariant_cost (adjoints_ortho _) (hf.add (penalty_diff S (matDiffAt_const _) h2.bonds)) (Eventually.of_forall fun v => ?_)).add ha,
    (hb.add (((hd.adj (adjoints_ortho _) (adjoints_ortho _)).mul (invariant_cost (adjoints_ortho _) (penalty_diff S (matDiffAt_const _) vary_diff)
      (Eventually.of_forall fun v => ?_))).mul hd)).add ha⟩
  · change completed p W t _ (vary _ (jointAdj k u *ᵥ v)) = _
    rw [vary_joint]; exact completed_gauge h hw t k u V _
  change penalty S V' (vary (Zmap t U') (linkAdj u *ᵥ v)) = _
  rw [show Zmap t U'=Lattice.gauge u (Zmap t U) from Zmap_gauge h ..,vary_gauge]; exact penalty_gauge ..

lemma scalar_gauge (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    (V : Config G c) {U : Loops.Inputs G c f} (h1 : Beam t U) (h2 : Beam t (gaugeJoint S k u U)) :
    scalar p W t (Lattice.gauge u V) (gaugeJoint S k u U) = scalar p W t V U := by
  have hg := ghost_motion (R_g_carries k (positions U)) (adjoints_ortho _) (adjoints_ortho _) (mu S)
  unfold scalar
  rw [(vector_carries h hw t k u V h1 h2).1.det (adjoints_ortho _), show positions (gaugeJoint S k u U) = Lattice.gauge k (positions U) from rfl,
    hg.det (adjoints_ortho _)]

lemma Yresp_gauge (h : S.patch.Branches S.kernel G) (hw : W.Bounds p σ C Λ) (t : S.Choices) (k : NodeField G f) (u : NodeField G c)
    (V : Config G c) {U : Loops.Inputs G c f} (h1 : Beam t U) (h2 : Beam t (gaugeJoint S k u U)) (v : Loops.Links G c) :
    Yresp p W t (Lattice.gauge u V) (gaugeJoint S k u U) (linkAdj u *ᵥ v) = Yresp p W t V U v :=
  (((vector_carries h hw t k u V h1 h2).2.inv (adjoints_ortho _)).mul (acceleration_carries h t v k u h1 h2)).trace (adjoints_ortho _)

lemma scalarRef_gauge (hw : W.Bounds p σ C Λ) (μ : ℝ) (k : NodeField G n) (U : Config G n) :
    scalarRef μ p W (Lattice.gauge k U) = scalarRef μ p W U := by
  have hg := ghost_motion (R_g_carries k U) (adjoints_ortho _) (adjoints_ortho _) μ
  rw [scalarRef, scalarRef, (reference_carries hw μ k U).det (adjoints_ortho _),hg.det (adjoints_ortho _)]
end YM.Push.Loops
