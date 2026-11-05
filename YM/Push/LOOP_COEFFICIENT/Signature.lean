import YM.Push.LOOP_COEFFICIENT.Balanced
import YM.Push.LOOP_COEFFICIENT.LimitRules

/-!
# Limit signature of the true charge scalar and of the fine reference

Conditional on analytic comparisons supplied on a cofinal mesh with COMMON
limiting symbol. No restriction of the heat transform to a transverse
subspace. Orientation of the auxiliary uses just permutations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent RG Wilson Precision Tree Exterior Complex
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {s f : ℕ → Side}

structure Signature (G : Gauge) (signed : Bool) (V : Momentum → Matrix (Axes G) (Axes G) ℂ) : Prop where
  symmetric p : star p = p → (V p).transpose = V (-p)
  hermitian p : star p = p → (V p).IsHermitian
  ward p : star p = p → V p * longitudinal G p = 0
  spin (s : Signed) : (signed = true ∨ (∀ i, s.flip i = false)) → ∀ p, star p = p → (orbitSymbol G s (-p)).transpose * V (s⁻¹.act p) * orbitSymbol G s p = V p
  color p : star p = p → ∀ u, (fiberColor G u).transpose * V p * fiberColor G u = V p

variable {V : Momentum → Matrix (Axes G) (Axes G) ℂ} {p : Clip} {W : PathData G} {S : ∀ i, StepData (s i) (f i)}
  {F : ∀ i, Forest (S i).ratio} {ρ : ∀ i, fieldDir G (s i) 1 → AxisChart G (F i)}
    {A : ∀ i, Matrix (Body 1 (f i)) (Body 1 (s i)) ℝ} {P : ChartRatio G}

def actualPairs (s : Side) (u : Loops.Links G s → ℝ) := bilinearAt u 0

lemma branch_signature (hs : Expands s) (h : ∀ i, Admission (F i) (ρ i) p W (A i) P)
    (hV : ∀ t : ∀ i, (S i).Choices, LinkMirror (fun i => actualPairs (s i) (onBranch (t i) p W (A i))) V) : Signature G true V := by
  let t (i : ℕ) : (S i).Choices := Classical.arbitrary _
  have ht i : ContDiffAt ℝ ω (onBranch (t i) p W (A i)) 0 := by
    apply ContDiffAt.comp (g:=charge (t i) p W) (f:=graft G _ _) 0 (by rw [map_zero]; exact ((h i).charge_balanced (t i)).smooth) (ContinuousLinearMap.contDiff ..).contDiffAt
  have he := (hV t)
  refine ⟨fun _ hp => he.symmetric hs hp (fun i => of_bend_symm (ht i)), fun _ hp => he.hermitian hs hp (fun i => of_bend_symm (ht i)),
    fun _ hp => he.ward hs hp (fun i => of_bend_null _ _ fun v x => ?_),
    fun a _ _ hp => he.spin hs hp a (hV fun i => (S i).withinChoice a 0 (t i)) (fun i => of_bend_congruence _ ((h i).charge_orientation (t i) a)),
    fun _ hp u => he.color hs hp (fun i v => of_bend_congruence _ ((h i).charge_color (t i) v)) u⟩
  exact ((ht i).isSymmSndFDerivAt_of_omega ..).trans ((h i).graft_null (t i) ((h i).charge_balanced (t i)) v x)

lemma fee_signature {μ σ C Λ : ℝ} (hμ : 0<μ) (hG : G.Simple) (hw : W.Bounds p σ C Λ) (hs : Expands s)
    (h : ∀ i, IsUnit (reference μ p W (1 : Config G (s i)))) (he : LinkMirror (fun i => actualPairs (s i) (fee μ p W)) V) : Signature G false V := by
  have ht i := fee_diff hw hμ (h i)
  have h1 (i) (u : G.El) : Lattice.gauge (constantGauge u) (1:Config G (s i)) = 1 := by ext1; simp [constantGauge,Lattice.gauge]
  have h2 i (a : Signed) : pull a 0 (1:Config G (s i)) = 1 := by ext1; simp [pull, Step.read]
  refine ⟨fun _ hp => he.symmetric hs hp (fun i => of_bend_symm (ht i)), fun _ hp => he.hermitian hs hp (fun i => of_bend_symm (ht i)),
    fun _ hp => he.ward hs hp (fun i => of_bend_null _ _ fun v x => ((ht i).isSymmSndFDerivAt_of_omega ..).trans
      ((Work.F05.bend_apply ..).trans (fee_ward hw hμ (h i) hG v x))),
    fun a ha _ hp => he.spin hs hp a he (fun i => of_bend_congruence _ (fun x y => ?_)),
    fun _ hp u => he.color hs hp (fun i v => of_bend_congruence _ (fun x y => ?_)) u⟩
  · rw [show ∀ M : Matrix _ _ ℝ, M *ᵥ x = clm M x from fun M => rfl,
      show linkSpin a (1:Config G (s i)) *ᵥ y = clm (linkSpin a (1:Config G (s i))) y from rfl,← bend_linear _ (ht i)]
    have eq : (fee μ p W ∘ clm (linkSpin a (1:Config G (s i)))) = fee μ p W := by
      funext v
      change scalarRef μ p W (vary 1 (linkSpin a 1 *ᵥ v)) = _
      rw [show vary (1:Config G (s i)) (linkSpin a 1 *ᵥ v) = _ from h2 i a ▸ vary_pull a (1:Config G (s i)) v]
      exact scalarRef_pull a (ha.resolve_left (by decide)) hw μ _
    rw [eq]
  change Work.F05.bend _ _ (clm (linkAdj (constantGauge v)) x) (clm (linkAdj (constantGauge v)) y) = _
  rw [← bend_linear _ (ht i)]; have eq : (fee μ p W ∘ clm (linkAdj (constantGauge (n:=s i) v))) = fee μ p W := by
    funext w
    change scalarRef μ p W (vary 1 (linkAdj (constantGauge v) *ᵥ w)) = _
    rw [show vary (1:Config G (s i)) _ = Lattice.gauge (constantGauge v) _ from h1 i v ▸ vary_gauge _ _ w]; exact scalarRef_gauge hw μ _ _
  rw [eq]

variable {b : Bool}
lemma Signature.color_scalar (h : Signature G b V) (hG : G.Simple) {p : Momentum} (hp : star p = p) (i j : Axis) :
    ∃ c : ℂ, ∀ a b, V p (i,a) (j,b) = if a=b then c else 0 := by
  let J (i : Axis) := (paint G Axis).symm.toLinearMap.comp (LinearMap.single ℝ (fun _ => G.Color) i)
  let K (i : Axis) := ((Complex.ofRealAm.toLinearMap.compLeft _).comp (J i))
  let S := Matrix.toLinearMap₂' ℂ (S₁:=ℂ) (S₂:=ℂ) (V p)
  let T := LinearMap.mk₂ ℝ (fun (x y : G.Color) => S (K i x) (K j y))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  have he v (a : Axis) (x : G.Color) : K a (G.adjoint v x) = fiberColor G v *ᵥ K a x := by
    change cvec (J _ _) = fiberColor G v *ᵥ cvec _
    rw [fiberColor,cmat_mulVec]
    congr 1; apply (paint G Axis).injective; ext1 b
    rw [paint_adjoints]
    change paint G Axis ((paint G Axis).symm _) _ = G.adjoint _ (paint G Axis ((paint G Axis).symm _) _)
    rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    by_cases hb : b=a <;> simp [*, LinearMap.single_apply]
  obtain ⟨z,hz⟩ := scalar_complex hG T (fun u x y => by
    change S _ _ = S _ _; unfold S; rw [he,he, Matrix.toLinearMap₂'_apply',Matrix.toLinearMap₂'_apply']
    conv_rhs => rw [← h.color p hp u,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose])
  let e := EuclideanSpace.basisFun G.ColorIndex ℝ
  have hb (i : Axis) a : K i (e a) = Pi.single (i,a) 1 := by
    ext1 ⟨k,l⟩; change Complex.ofReal ((Pi.single i (e a) : Axis → G.Color) k l) = _
    by_cases h : k=i <;> by_cases h' : l=a <;> simp [*, e]
  refine ⟨z,fun a b => ?_⟩
  have he := hz (e a) (e b)
  change S (K i _) (K j _) = _ at he
  unfold S at he
  rw [hb,hb, Matrix.toLinearMap₂'_apply', Matrix.mulVec_single_one,single_dotProduct,one_mul] at he
  split
  next h => simpa only [h,e.inner_eq_one,ofReal_one,mul_one,Matrix.col_apply] using he
  next h => simpa only [e.orthonormal.2 h,ofReal_zero,mul_zero,Matrix.col_apply] using he
end YM.Push.Loops
