import YM.Push.LOOP_COEFFICIENT.AliasJets
import YM.Push.LOOP_COEFFICIENT.ChargeStrip
import YM.Push.LOOP_COEFFICIENT.MirrorOperations


/-!
# The gradient correction has zero kinetic jet at period limit

No bound uniform in scale is needed in its rooted-coordinate test. Pass
first to the limiting kernel of the map-response on the same periods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Lattice RG Wilson Precision Tree Exterior Bloch Laurent
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

def driftKernel (J Y C : Momentum → Matrix a a ℂ) (p : Momentum) := (J (-p)).transpose * Y p + (Y (-p)).transpose * J p - (J (-p)).transpose * C p * J p

section analytic
open scoped Matrix.Norms.L2Operator
variable {X Y : Momentum → Matrix a b ℂ} (hx : ContDiffAt ℂ ω X 0) (hy : ContDiffAt ℂ ω Y 0) {p : Momentum} {n m : ℕ} {H : Row (TypeFace 2) (TypeFace 2)}
include hx hy
omit [DecidableEq a] in
lemma UnderMatrix.add (h : UnderMatrix X p n) (h' : UnderMatrix Y p n) : UnderMatrix (fun z => X z + Y z) p n := fun i j k hk =>
  (line_add (analyticComponent hx i j) (analyticComponent hy i j) p k).trans (by rw [h i j k hk,h' i j k hk,add_zero])
omit [DecidableEq a] in
lemma UnderMatrix.sub (h : UnderMatrix X p n) (h' : UnderMatrix Y p n) : UnderMatrix (fun z => X z - Y z) p n := fun i j k hk =>
  (line_sub (analyticComponent hx i j) (analyticComponent hy i j) p k).trans (by rw [h i j k hk,h' i j k hk,sub_zero])
omit hx hy [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
lemma UnderMatrix.mono (h : UnderMatrix X p n) (he : m ≤ n) : UnderMatrix X p m := fun i j k hk => h i j k (hk.trans_le he)
omit hx hy [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
lemma UnderMatrix.neg (h : UnderMatrix X p n) : UnderMatrix (fun z => -X z) p n := fun i j k hk => (show lineD (fun z => (-X z) i j) p k = - lineD (fun z => X z i j) p k by simpa using line_const_mul (f:=fun z => X z i j) (-1) p k).trans (by rw [h i j k hk,neg_zero])

omit hx hy
lemma kinetic_short (h : ContDiffAt ℂ ω (Row.read H) 0) (p : Momentum) : UnderMatrix (kineticSymbol G H) p 2 := by
  have he := (under_negate (X:=symbol 1) (p:=p) (fun i j => symbol_below 1 _ i j)).mul (analyticTranspose (symbol_diff.comp (f:=(-·)) 0 (by fun_prop))) h (UnderMatrix.zero _ _)
  intro i j; change Below (fun z => if i.2 = j.2 then _ else _) p 2
  split; exact (he.mul (analyticMul (analyticTranspose (symbol_diff.comp (f:=(-·)) 0 (by fun_prop))) h) symbol_diff (fun i j => symbol_below 1 p i j)) _ _
  exact fun k _ => line_vac ..

lemma drift_short {J Y C : Momentum → Matrix a a ℂ} (hj : ContDiffAt ℂ ω J 0) (hy : ContDiffAt ℂ ω Y 0) (hc : ContDiffAt ℂ ω C 0) (h0 : Y 0 = 0)
    (h : ∀ p, UnderMatrix J p 2) (p : Momentum) : UnderMatrix (driftKernel J Y C) p 3 := by
  have h₁ := analyticTranspose ((show ContDiffAt ℂ ω J (-0) by simpa using hj).comp (f:=(-·)) 0 (by fun_prop)); have h₂ := analyticTranspose ((show ContDiffAt ℂ ω Y (-0) by simpa using hy).comp (f:=(-·)) 0 (by fun_prop))
  have he := under_negate (p:=p) (h (-p)); have hY (p) := UnderMatrix.one (p:=p) h0
  exact ((he.mul h₁ hy (hY p)).add (analyticMul h₁ hy) (analyticMul h₂ hj) ((under_negate (hY (-p))).mul (r:=1) (s:=2) h₂ hj (h p))).sub ((analyticMul h₁ hy).add (analyticMul h₂ hj)) (analyticMul (analyticMul h₁ hc) hj) (((he.mul h₁ hc (UnderMatrix.zero _ _)).mul (analyticMul h₁ hc) hj (h p)).mono (by decide))
end analytic

section mesh
variable {s f : ℕ → Side} {S : ∀ i, StepData (s i) (f i)} {F : ∀ i, Forest (S i).ratio} {ρ : ∀ i, fieldDir G (s i) 1 → AxisChart G (F i)} {P : ChartRatio G} {p : Clip} {W : PathData G}
    {A : ∀ i, Matrix (Body 1 (f i)) (Body 1 (s i)) ℝ} (t : ∀ i, (S i).Choices) {B : ∀ i, Grid (s i) (JointKey G (s i) (f i)) b} {V : Vertex (Axes G) b b} {η C σ M : ℝ} {H : Bed}
    (hs : Expands s) (h : ∀ i, Admission (F i) (ρ i) p W (A i) P) (ht : ∀ i, Charged (linksGrid G (s i)) (B i) (observed p W (t i) (A i)) V) (hv : ChargeStrip V η C)
include h hs ht hv
lemma respKernel_ward {z : Momentum} (hz : star z=z) : kernelOf (respTrace V) z * longitudinal G z = 0 := LinkMirror.ward (hv.reflects hs ht).1 hs hz (fun i => observed_ward (t i) (h i))

open scoped Matrix.Norms.L2Operator in
lemma drift_mirror {U} (hU : Mirrors (fun i => linksGrid G (s i)) (fun i => linksGrid G (s i)) (fun i => Coeff (fun b => Real.log (onBase p W (t i) (A i) b).det)) U)
    (hA : ∀ i, mean (S i) * (A i) = 1 - (S i).kernel.penalty⁻¹ • Precision.K (H.metric.acts (s i))) (hh : H.metric.strip σ M) (hσ : 0<σ) :
    Mirrors (fun i => linksGrid G (s i)) (fun i => linksGrid G (s i)) (fun i => Coeff (fun b => Real.log (onVector p W (t i) (A i) b).det))
      (U + driftKernel (-kineticSymbol G H.metric) (kernelOf (respTrace V)) (kernelOf (reverseTrace V))) := by
  obtain ⟨he,hf⟩ := hv.reflects hs ht
  simp only [Coeff,observed_drift _ (h _) _ (hA _),map_add,map_sub,cmat_mul,map_neg]
  let U := -kineticSymbol G H.metric
  have hu (p) (hp : star p = p) : ContinuousAt U p := (kinetic_diff (G:=G) hh hσ (Work.F07.realStrip _ (half_pos hσ) hp)).neg.continuousAt
  have hr (i p k) (hk : Matches (n:=s i) p k) := (kinetic_routed G H.metric (Row.rights _ _ hh hσ.le) hk).neg
  have heq (x : Side) : cmat (-KRow G H x).transpose = (-cmat (KRow G H x)).transpose := by rw [← map_neg]; rfl
  simp_rw [show ∀ n : Side, cmat (-liftMatrix G (Precision.K (H.metric.acts n))).transpose = _ from heq]
  exact hU.add (((he.routed_transpose_mul hu hr).add (he.transpose.mul_routed hu hr)).sub ((hf.routed_transpose_mul hu hr).mul_routed hu hr))

open scoped Matrix.Norms.L2Operator in
lemma drift_probe (hh : ContDiffAt ℂ ω (Row.read H.metric) 0) (a : G.ColorIndex) : probe₂ (driftKernel (-kineticSymbol G H.metric) (kernelOf (respTrace V)) (kernelOf (reverseTrace V))) a = 0 := by
  have hY := Integrand.smooth_mean hv.resp (Work.F07.realStrip _ hv.width (star_zero (R:=Momentum)))
  have h0 := value_ward (Y:=fun p i j => kernelOf (respTrace V) p i j) (fun _ hp => respKernel_ward t hs h ht hv hp) (analyticComponent hY)
  have hJ : ContDiffAt ℂ ω (kineticSymbol G H.metric) 0 := analyticMatrix fun i j => by
    unfold kineticSymbol paintSymbol; simp only [of_apply]; split
    · exact analyticComponent (analyticMul (analyticMul (analyticTranspose (symbol_diff.comp (f:=(-·)) 0 (by fun_prop))) hh) symbol_diff) _ _
    exact contDiffAt_const
  exact div_eq_zero_iff.mpr (Or.inl (drift_short hJ.neg hY (Integrand.smooth_mean hv.rev (Work.F07.realStrip _ (half_pos hv.width) (star_zero (R:=Momentum)))) h0 (fun p => (kinetic_short hh p).neg) (unitAxis 0) (1,a) (1,a) 2 (by decide)))
end mesh
end YM.Push.Loops
