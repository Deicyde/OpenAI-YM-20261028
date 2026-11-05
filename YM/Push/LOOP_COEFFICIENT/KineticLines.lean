import YM.Push.LOOP_COEFFICIENT.KineticReal
import YM.Push.LOOP_COEFFICIENT.ZeroLayers
import YM.Work.F07.Read


/-!
# Quadratic coefficient of the actual Fourier coboundary + color metric kinetic row
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice RG Wilson Precision Exterior Bloch Laurent Bid Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {G : Gauge} {n : Side} {H : Bed} {η C : ℝ} {z : Momentum}

lemma row_analytic {a b : Type} [Fintype a] [Fintype b] [DecidableEq b] {R : Row a b}
    (h : R.strip η C) (hη : 0 < η) (hz : z ∈ Tube (η/2)) : ContDiffAt ℂ ω (Row.read R) z :=
  analyticMatrix (fun i j => ((PolyDisc.finiteD _ (eventually_of_mem ((Work.F07.stripOpen _).mem_nhds hz) (fun _ hp =>
    (Work.F07.readDeriv (R.constant_strip h i j) (half_pos hη) (half_lt_self hη) hp).1))).contDiffAt))

lemma symbol_diff {r} : ContDiffAt ℂ ω (symbol r) z := analyticMatrix (fun i j => by
  simp only [symbol,wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]; exact ContDiffAt.sum fun k _ => (q_diff k).contDiffAt.mul contDiffAt_const)

lemma kinetic_diff (h : H.metric.strip η C) (hη : 0 < η) (hz : z ∈ Tube (η/2)) : ContDiffAt ℂ ω (kineticSymbol G H.metric) z :=
  analyticMatrix (fun i j => by
    unfold kineticSymbol paintSymbol; simp only [Matrix.of_apply]; split
    · exact analyticComponent (analyticMul (analyticMul (analyticTranspose ((symbol_diff (r:=1)).comp z (f:=(-·)) (by fun_prop))) (row_analytic h hη hz)) symbol_diff) _ _
    exact contDiffAt_const)

lemma symbol_below (r) (p) (i j) : Below (fun z => symbol r z i j) p 1 := below_one (by simp [symbol,wedge,q])
lemma symbol_first (r) (i : Axis) (a b) : lineD (fun z => symbol r z a b) (unitAxis i) 1 = I * left ℂ r i a b := by
  have hf k : ContDiffAt ℂ ω (fun p => q p k * left ℂ r k a b) 0 := (q_diff k).contDiffAt.mul contDiffAt_const
  simp only [symbol,wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,line_sum _ _ (fun i _ => hf i)]
  have he k : lineD (fun p => q p k * left ℂ r k a b) (unitAxis i) 1 = I * unitAxis i k * left ℂ r k a b := by
    rw [mul_comm I]
    simpa only [Nat.add_zero,Nat.choose_self,Nat.cast_one,one_mul,line_zero,q_first,mul_comm I] using!
      Below.product (q_diff k).contDiffAt (contDiffAt_const (c:=left ℂ r k a b)) (q_below (p:=unitAxis i) k) below_zero
  simp only [he]; simp [unitAxis,Pi.single_apply,mul_ite,ite_mul]
lemma symbol_first_neg (r) (i : Axis) (a b) : lineD (fun z => symbol r (-z) a b) (unitAxis i) 1 = -(I * left ℂ r i a b) := by
  rw [show lineD (fun z => symbol r (-z) a b) (unitAxis i) 1 = lineD (fun z => symbol r z a b) (-unitAxis i) 1 by simp [lineD],line_neg,symbol_first]; simp

lemma blade_corner (S : TypeFace 2) : left ℂ 1 (0:Axis) S (coord 1) = if S = plaquette ⟨(0,1),by decide⟩ then 1 else 0 := by
  simp only [left, Matrix.of_apply]
  split
  next h =>
    have hp : parity S.val 0 ℂ = 1 := by simp [parity,pre, Finset.filter_false_of_mem]
    have he : remove 0 S h = coord 1 ↔ S = plaquette ⟨(0,1),by decide⟩ := by
      simp only [remove,coord, plaquette, Subtype.ext_iff]; constructor
      · intro h'; rw [← h']; exact (Finset.insert_erase h).symm
      intro h'; rw [h']; decide
    simp only [hp,he]
  next h => rw [if_neg (show S ≠ plaquette ⟨(0,1),by decide⟩ from fun he => h (by simp [he,plaquette]))]

lemma kinetic_probe {R : Row (TypeFace 2) (TypeFace 2)} (hr : ContDiffAt ℂ ω (Row.read R) 0) (he : R.read 0 = 1) (a : G.ColorIndex) : probe₂ (kineticSymbol G R) a = 1 := by
  let f (i : TypeFace 2) (z : Momentum) := symbol 1 (-z) i (coord 1)
  let g (i : TypeFace 2) (z : Momentum) := symbol 1 z i (coord 1)
  let p := unitAxis 0
  have hf i : ContDiffAt ℂ ω (f i) 0 := (analyticComponent symbol_diff i (coord 1)).comp 0 (f:=(-·)) (by fun_prop)
  have hg i : ContDiffAt ℂ ω (g i) 0 := analyticComponent symbol_diff ..
  have ha i : Below (f i) p 1 := below_one (by simp [f,symbol,wedge,q]);
  let u i (z : Momentum) := ∑ j, f j z * R.read z j i
  have hu i : ContDiffAt ℂ ω (u i) 0 := ContDiffAt.sum fun j _ => (hf j).mul (analyticComponent hr j i)
  have hb i : Below (u i) p 1 := below_one (by simp [u,f,symbol,wedge,q])
  have h₁ (i j : TypeFace 2) := Below.product (hf j) (analyticComponent hr j i) (ha j) below_zero
  have hU i : lineD (u i) p 1 = -(I * left ℂ 1 0 i (coord 1)) := by
    rw [line_sum Finset.univ _ (fun j _ => (hf j).mul (analyticComponent hr j i))]
    simp [h₁,f,p,symbol_first_neg,he, Matrix.one_apply,mul_ite]
  have h₂ (i : TypeFace 2) : lineD (fun z => u i z * g i z) p 2 = if i=plaquette ⟨(0,1),by decide⟩ then 2 else 0 := by
    rw [Below.product (a:=1) (b:=1) (hu i) (hg i) (hb i) (symbol_below 1 p i (coord 1)), hU]
    dsimp [g,p]; rw [symbol_first,blade_corner]; split <;> simp; linear_combination -2*I_mul_I
  have hh := line_sum Finset.univ (fun i z => u i z * g i z) (fun j _ => (hu j).mul (hg j)) p 2
  rw [show probe₂ (kineticSymbol G R) a = lineD (fun z => ∑ i,u i z * g i z) p 2 / 2 by
    simp only [probe₂, mark, kineticSymbol,paintSymbol,of_apply,Matrix.mul_apply]; rfl, hh]; simp only [h₂]; simp

lemma kinetic_signature {s : ℕ → Side} (hs : Expands s) (h : H.metric.strip η C) (hη : 0 < η)
    (hh : ∀ i, (H.metric.acts (s i)).IsSymm) (hS : ∀ i, Sworn H (s i) G) : Signature G true (kineticSymbol G H.metric) := by
  have he : LinkMirror (fun i => KRow G H (s i)) (kineticSymbol G H.metric) := compares_mirror (fun _ => Compares.of_routed
    (fun _ _ => kinetic_routed G _ (Row.rights _ _ h hη.le))) (fun _ hp => (kinetic_diff h hη (Work.F07.realStrip _ (half_pos hη) hp)).continuousAt) tendsto_const_nhds
  exact ⟨fun _ hp => he.symmetric hs hp (fun i => KRow_symm _ (hh i)),fun _ hp => he.hermitian hs hp (fun i => KRow_symm _ (hh i)),
    fun _ hp => he.ward hs hp (fun _ => KRow_ward H),fun a _ _ hp => he.spin hs hp a he (fun i => KRow_spin (hS i) a),
    fun _ hp => he.color hs hp (fun _ u => (KRow_color H u).left_eq (adjoints_ortho _))⟩
end YM.Push.Loops
