import YM.Next.RANK.Radian.Heat

/-!
# Positive exponential convention through any elementary partials
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Filter Maxwell Topology Analysis Asymptotics Set Real Beamer Lattice  VectorFourier
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
local notation "𝑒" => Real.exp
local notation "ℑ" => Complex.I

variable {F G : E4 → ℂ}

def chirp (i : Axis) (x : E4) : ℂ := 2*(π:ℂ)*ℑ*x i
def crank (i : Axis) (F : E4→ℂ) : E4 → ℂ := chirp i * F
lemma loud (i : Axis) (x : E4) : ‖chirp i x‖ ≤ (2*π)*‖x‖ := by
  unfold chirp; repeat rw [norm_mul]
  rw [Complex.norm_two,Complex.norm_real,Complex.norm_real,Complex.norm_I, Real.norm_eq_abs,abs_of_pos pi_pos,mul_one]
  have he := abs_real_inner_le_norm (YM.basis i) x; rw [basis_inner,basis_norm,one_mul] at he; exact mul_le_mul_of_nonneg_left he (by positivity)
lemma Moment.tends (h : Moment F) (i : Axis): Moment (crank i F):= by
  let v:=crank i F
  have hp: AEStronglyMeasurable v:= ((show Continuous (chirp i) by unfold chirp; fun_prop).aestronglyMeasurable).mul h.integral.aestronglyMeasurable
  have ht n : Integrable (fun x => ‖x‖^n * ‖v x‖):= by
    refine ((h.price (n+1)).const_mul (2*Real.pi)).mono' ((continuous_norm.aestronglyMeasurable.pow n).mul hp.norm) (Eventually.of_forall ?_)
    intro x; rw [Real.norm_of_nonneg (by positivity)]; change ‖x‖^n * ‖chirp i x*F x‖ ≤ _; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (loud i x) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) _)).trans; apply le_of_eq; rw [pow_succ];ring
  exact ⟨(integrable_norm_iff hp).1 (by simpa only [pow_zero,one_mul] using ht 0), ht⟩
lemma Moment.sub (hx : Moment F) (h : Moment G) : Moment (F-G):= by
  have he:=hx.integral.sub h.integral
  refine ⟨he,fun i=> ?_⟩
  refine ((hx.price i).add (h.price i)).mono' ((continuous_norm.aestronglyMeasurable.pow i).mul he.norm.aestronglyMeasurable) (Eventually.of_forall fun x=> ?_)
  rw [Real.norm_of_nonneg (by positivity)]; change _ ≤ ‖x‖^i*‖F x‖+(‖x‖^i*‖G x‖); rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_sub_le ..) (by positivity)
lemma Moment.zero : Moment 0:=by refine ⟨integrable_zero _ _ _ , fun i=>?_⟩; simp
lemma harmon_sub (h : Integrable F) (hg : Integrable G) : harmon (F-G)=harmon F-harmon G:= by
  ext1 t; change _=harmon F t-harmon G t;rw [wind,wind,wind,← integral_sub]
  · exact integral_congr_ae (Eventually.of_forall fun u=>mul_sub ..)
  · exact h.bdd_mul (by unfold wave;fun_prop) (Eventually.of_forall (p:=fun u=>‖wave t u‖≤ 1) (by simp))
  · exact hg.bdd_mul (by unfold wave;fun_prop) (Eventually.of_forall (p:=fun u=>‖wave t u‖≤ 1) (by simp))
lemma harmon_scale (f : E4→ℂ) (i : ℂ): harmon (i • f)=i • harmon f:= by
  funext x; rw [wind];change _=i*harmon _ _; rw [wind,← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun _ => mul_left_comm ..)
lemma harmon_zero : harmon (fun _=>0)=0:= by funext x; rw [wind]; simp

lemma harmonious (H : Moment F) (i : Axis) : grad i (harmon F)=harmon (crank i F):= by
  let L:= innerSL (E:=E4) ℝ
  let M:=fourierSMulRight L F
  have h : Integrable (fun x=> ‖x‖*‖F x‖):= by simpa only [pow_one] using H.price 1
  have hv : Integrable M:= by
    refine (h.const_mul ((2*π)*‖L‖)).mono' (H.integral.1.fourierSMulRight  ) (Eventually.of_forall fun x=>?_)
    exact (norm_fourierSMulRight_le L F x).trans (le_of_eq (by ring))
  have hi (x : E4):HasFDerivAt (harmon F) ((𝓕 M (-x)).comp (-ContinuousLinearMap.id ℝ E4)) x:= (Real.hasFDerivAt_fourier H.integral h _).comp x (hasFDerivAt_id x).neg
  ext1 x
  rw [grad,D,(hi x).fderiv]; simp only [ContinuousLinearMap.comp_apply,neg_apply, ContinuousLinearMap.id_apply, Real.fourier_continuousLinearMap_apply hv]
  change (𝓕 (fun p => M p (-YM.basis i)) (-x))=_; unfold harmon
  apply congr_arg (fun f:E4→ℂ=> 𝓕 f (-x)); ext1 y; unfold M crank;rw [fourierSMulRight_apply]; change (-(2*(π:ℂ)*ℑ)) • inner ℝ y (-basis i) • F y = 2*(π:ℂ)*ℑ* (y i:ℂ)* F y; rw [inner_neg_right,real_inner_comm,basis_inner]; push_cast; simp [Complex.real_smul];ring

-- Use sequence derivatives in both actual and symbolic. Tensor b. Order from layout via foldr. n..0

def press (l : List Axis) (F : E4 →ℂ) := l.foldr crank F
def dV {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (t : List Axis) (F : E4→ Z) := t.foldr grad F
lemma Moment.pressed (l : List Axis) (H : Moment F): Moment (press l F):= by
  induction l with
  | nil=> exact H
  | cons=> exact Moment.tends (by assumption) _
lemma takes (l : List Axis) (h : Moment F) : harmon (press l F)=dV l (harmon F):= by
  induction l with
  | nil=> rfl
  | cons a l H=> rw [show press _ _= _ from (show press (a::l) F=crank a (press l F) from rfl), ← harmonious (Moment.pressed l h), H]; rfl

end YM.Next.Rank.Radian
