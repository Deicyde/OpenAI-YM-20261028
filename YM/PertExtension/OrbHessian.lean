import YM.PertExtension.OrbFlat
import YM.Gauge.Chart
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Taylor input for the inversion-quotient Wilson rule. In particular `fiscal`
is the actual bare Wilson action (with the factor 1/2 on the full torus,
restricting links to inversion-equivariant ones and tree links to the
identity), not an infrared-regulator mass insertion. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.PertExtension.Orb
open Set MeasureTheory Lattice Gauge Wilson Function
open scoped ContDiff Topology Matrix.Norms.Frobenius BigOperators Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge}{n : Side}

/-- Variables in physical color normalization, on non-tree edge orbits. -/
abbrev Dir (G : Gauge)(n : Side) := Cotree n → G.Color

def representative (A : Dir G n) := links 1 (fun i=> G.lieExp (A i))
def fiscal (A : Dir G n) : ℝ := energy (representative A)/2
@[simp] lemma representative_zero : representative (0:Dir G n)=1 := by
  funext i; unfold representative links liftLinks; split<;>simp only [splitLink,Pi.one_apply]
  all_goals split <;> simp
@[simp] lemma fiscal_zero : fiscal (0:Dir G n)=0 := by unfold fiscal representative; convert (div_eq_zero_iff.mpr (Or.inl (flat_at_zero (n:=n) (G:=G)))) using 2; apply congr_arg energy; apply congr_arg (links 1); funext i; change G.lieExp 0=1; simp

@[fun_prop] lemma rep_cont : Continuous (representative (n:=n) (G:=G)) := by
  apply continuous_pi; intro e; unfold representative links liftLinks splitLink; split <;> split
  all_goals first | exact continuous_const | fun_prop

@[fun_prop] lemma matrix_smooth (e : Edge (Site n)): ContDiff ℝ ω (fun x : Dir G n=>G.mat (representative x e)) := by
  have he (i : Cotree n) : ContDiff ℝ ω (fun x : Dir G n=>G.mat (G.lieExp (x i))) := G.exp_jet.comp (contDiff_apply _ G.Color i)
  unfold representative links liftLinks splitLink; split <;> split
  · exact contDiff_const
  · exact he _
  · exact contDiff_const
  simp only [G.mat_inv]; exact ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (he _))

lemma smooth_walk (x : Site n)(w) : ContDiff ℝ ω (fun A : Dir G n=>G.mat (travel (representative A) x w)) := by
  induction w generalizing x with
  | nil => exact contDiff_const
  | cons d w ih =>
    have ha :ContDiff ℝ ω (fun A : Dir G n=>G.mat (d.read (representative A) x)) := by
      unfold Step.read; split
      · simp only [G.mat_inv]; exact ((starL' ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.comp (matrix_smooth _))
      exact matrix_smooth _
    simp only [travel,G.mat_mul]; exact ha.mul (ih _)
lemma face_smooth (p) : ContDiff ℝ ω (fun A : Dir G n=>G.price (faceValue (representative A) p)) := by
  have ht (u : G.El) : G.price u= (‖G.mat u-1‖^2)/G.repDim/2 := by rw [← colorScale_sq,← div_pow];change _=G.chord u^2/2;rw [G.chord_price];ring
  simp_rw [ht,faceValue]; exact (((contDiff_norm_sq ℝ).comp ((smooth_walk (G:=G) _ _).sub (contDiff_const (c:=1)))).div_const _).div_const _
lemma fiscal_smooth : ContDiff ℝ ω (fiscal (G:=G) (n:=n)) :=
  .div_const (.sum fun i _=>face_smooth i) _

lemma at_identity (z : Dir G n)(i) : HasDerivAt (fun r : ℝ => G.mat (representative (r • z) i)) (G.colorMat (variation z i)) 0 := by
  have hy (i : Cotree n): HasDerivAt (fun r : ℝ=>G.mat (G.lieExp (r • z i))) (G.colorMat (z i)) 0 := by
    let f:=fun r: ℝ=> r • z i
    have ht : HasFDerivAt (fun a:G.Color => G.mat (G.lieExp a)) G.colorMat.toContinuousLinearMap (f 0) := by dsimp only [f];rw [zero_smul];exact G.expDiff_zero
    exact ht.comp_hasDerivAt 0 (show HasDerivAt f (z i) 0 from by simpa only [one_smul] using! (hasDerivAt_id' (0:ℝ)).smul_const (z i))
  unfold variation genJet representative links liftLinks splitLink;dsimp only [LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply];split_ifs
  all_goals first
  | simp only [map_zero,neg_zero]; exact hasDerivAt_const ..
  | exact hy _
  | simp only [G.mat_inv,map_neg, ← G.colorMat_skew]; exact (hy ..).star

@[simp] private lemma flat_walk {K : Type*}[Group K] (y : Site n)(w) : travel (1 : Links _ K) y w = 1 := by
  induction w generalizing y <;> simp_all [travel,Step.read]
lemma first_walk (z : Dir G n)(y w) : HasDerivAt (fun r : ℝ => G.mat (travel (representative (r • z)) y w))
    (G.colorMat (line (variation z) y w)) 0 := by
  have hs (x d) : HasDerivAt (fun r : ℝ=> G.mat (Step.read d (representative (r • z)) x)) (G.colorMat (cash (variation z) d x)) 0 := by
    unfold Step.read cash
    split
    · simp only [G.mat_inv,map_neg, ← G.colorMat_skew]; exact (at_identity ..).star
    exact at_identity ..
  induction w generalizing y with
  | nil => simp [travel,line]; exact hasDerivAt_const ..
  | cons d w ih =>
    have ht := (hs y d).mul (ih (y+d.vec))
    simp only [zero_smul,representative_zero] at ht
    have hz : d.read (representative (0:Dir G n)) y=1 := by rw [representative_zero];unfold Step.read;split<;>simp
    rw [representative_zero] at hz; rw [hz,flat_walk,mat_one,one_mul,mul_one] at ht
    simp only [travel,line,G.mat_mul,map_add,add_comm];exact ht
lemma face_line {E : Type*}[AddCommGroup E](A : Links (Per n) E)(x i j) : line A x (square i j)=Curl A x i j := by
  simp [line,square,Curl,add_right_comm x ((step i : Site n)) (step j)]; abel

def letter (z : Dir G n)(p : Face (Per n)) := Curl (variation z) p.1 p.2.val.1 p.2.val.2
abbrev contribution (z : Dir G n)(p) := G.price (faceValue (representative z) p)
lemma face_grades (p)(z : Dir G n) : iteratedDeriv 2 (fun r : ℝ=> contribution (r • z) p) 0 = ‖letter z p‖^2 ∧
    deriv (fun r : ℝ=> contribution (r • z) p) 0=0 := by
  let f : ℝ → G.Mat := fun r => G.mat (faceValue (representative (r • z)) p)-1
  have ht := first_walk z p.1 (square p.2.val.1 p.2.val.2)
  rw [face_line] at ht
  have h0:HasDerivAt f (G.colorMat (letter z p)) 0 := ht.sub_const _
  have hf0 : f 0=0 := by simp [f, faceValue,flat_walk]
  have h2 : ContDiff ℝ (1+1) f := ((smooth_walk (G:=G) p.1 (square _ _)).of_le le_top|>.comp ((contDiff_id (E:=ℝ)).smul contDiff_const)).sub contDiff_const
  have hd (r : ℝ):DifferentiableAt ℝ f r:=h2.differentiable (by norm_num) r
  have HH := h2.deriv'.differentiable (by simp) 0
  let c := ((2:ℝ)*G.repDim)⁻¹
  have H : (fun r:ℝ=>contribution (r • z) p)=fun r=>c*(inner ℝ (f r) (f r)) := by
    funext r; rw [real_inner_self_eq_norm_sq,show ‖f r‖^2=G.chord (faceValue (representative (r • z)) p)^2*(G.repDim:ℝ) from by
      unfold chord; rw [div_pow,Real.sq_sqrt (by positivity)]; exact (div_mul_cancel₀ _ (show (G.repDim:ℝ)≠0 from Nat.cast_ne_zero.mpr G.dimPos.ne')).symm]; rw [G.chord_price];unfold contribution c; field_simp
  have hL (r : ℝ) : HasDerivAt (fun r=> contribution (r • z) p) (c*(inner ℝ (f r) (deriv f r)+ inner ℝ (deriv f r) (f r))) r := by
    rw [H]; exact ((hd _).hasDerivAt.inner ℝ (hd _).hasDerivAt).const_mul _
  have hQ :deriv (fun r=> contribution (r • z) p) = fun r=>c*(inner ℝ (f r) (deriv f r)+ inner ℝ (deriv f r) (f r)):=funext fun r=>(hL r).deriv
  refine ⟨?_,by simp [hQ,hf0]⟩
  rw [show 2 = 1+1 from rfl, iteratedDeriv_succ,iteratedDeriv_one, hQ]
  have he := ((h0.inner ℝ HH.hasDerivAt).add (HH.hasDerivAt.inner ℝ h0)).const_mul c|>.deriv
  change deriv (fun r : ℝ=>c * (inner ℝ (f r) (deriv f r)+_)) 0 = _ at he
  refine he.trans ?_; rw [hf0,h0.deriv,inner_zero_right,inner_zero_left,real_inner_self_eq_norm_sq,G.colorMat_norm]
  simp only [zero_add,add_zero]
  rw [mul_pow, G.colorScale_sq]
  unfold c;field_simp
  ring

def Q (z : Dir G n):= (∑ p : Face (Per n), ‖letter z p‖^2)/2
lemma fiscal_grades (z : Dir G n) : iteratedDeriv 2 (fun r : ℝ=>fiscal (r • z)) 0=Q z ∧
    iteratedDeriv 1 (fun r : ℝ=>fiscal (r • z)) 0=0 := by
  have h2 (k : ℕ) (p : Face (Per n)) : ContDiffAt ℝ k (fun r : ℝ=> contribution (r • z) p) 0 := ((face_smooth (G:=G) p).of_le le_top |>.comp ((contDiff_id (E:=ℝ)).smul contDiff_const)).contDiffAt
  unfold fiscal energy Q; change _ ∧ _
  simp_rw [div_eq_mul_inv]
  constructor
  · rw [iteratedDeriv_mul_const_field,iteratedDeriv_fun_sum (by exact fun i _=>h2 2 i)]
    simp only [(fun i=>(face_grades i z).1),contribution, division_def]
  rw [iteratedDeriv_mul_const_field, iteratedDeriv_fun_sum (by exact fun i _=>h2 1 i)]
  simp_rw [show ∀ i, iteratedDeriv 1 (fun r=> contribution (r • z) i) (0:ℝ)= deriv _ _ from by intro i; rw [iteratedDeriv_one],(fun i=>(face_grades i z).2)]; simp

lemma Q_pos (even : Even n.val) {z : Dir G n} (h : z ≠ 0) : 0<Q z := by
  by_contra! ht
  apply h
  apply curl_gap even
  have hy p :letter z p=0 := by
    refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
    have he := Finset.single_le_sum (s:=Finset.univ) (fun i _=>sq_nonneg ‖letter z i‖) (Finset.mem_univ p)
    unfold Q at ht; nlinarith only [he,ht]
  intro y i j; rcases lt_trichotomy i j with hj|hj|hj
  · exact hy (y,⟨(i,j),hj⟩)
  · subst j; unfold Curl; abel
  have he : Curl (variation z) y i j = -Curl (variation z) y j i:=by unfold Curl; abel
  rw [he,show Curl (variation z) y j i=0 from hy (y,⟨(j,i),hj⟩),neg_zero]
end YM.PertExtension.Orb
