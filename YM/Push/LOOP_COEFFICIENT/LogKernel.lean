import YM.Push.LOOP_COEFFICIENT.MeanCalculus
import YM.Push.LOOP_COEFFICIENT.Samples
import YM.Push.LOOP_COEFFICIENT.TraceRead
import YM.Push.LOOP_COEFFICIENT.Tubes

/-!
# Strip and mesh comparison for a single log det

Unweighted costs here. Used with post-L constants in the finite period test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators ContDiff

variable {d a b : Type} [Fintype d] [DecidableEq d] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {V : Vertex d a a} {η C : ℝ}

def logKernel (V : Vertex d a a) (p : Momentum) : Matrix d d ℂ := of fun i j => boxMean (bubbleTrace V (Pi.single i 1) (Pi.single j 1) p)

section op
open scoped Matrix.Norms.L2Operator

structure LogStrip (V : Vertex d a a) (η C : ℝ) : Prop where
  width : 0 < η
  lit : Lit V η
  unit q : q∈Tube η → IsUnit (V.base q)
  invert q : q∈Tube η → ‖(V.base q)⁻¹‖ ≤ C
  one q p v : q∈Tube η → p∈ Tube η → (∀ i, ‖v i‖ ≤ 1) → ‖V.one q p v‖ ≤ C
  two q p s v w : q∈Tube η → p∈ Tube η → s∈Tube η → (∀ i, ‖v i‖ ≤ 1) → (∀ i, ‖w i‖ ≤ 1) → ‖V.two q p s v w‖ ≤ C

omit [DecidableEq a] in
lemma component_norm (M : Matrix a b ℂ) (i j) : ‖M i j‖ ≤ ‖M‖ := by
  have he := M.l2_opNorm_mulVec (PiLp.single 2 j (1:ℂ))
  rw [PiLp.norm_single,norm_one,mul_one, PiLp.ofLp_single, Matrix.mulVec_single_one] at he
  exact le_trans (PiLp.norm_apply_le ((EuclideanSpace.equiv a ℂ).symm (M.col j)) i) he

lemma trace_norm (M : Matrix a a ℂ) : ‖M.trace‖ ≤ Fintype.card a * ‖M‖ := by
  rw [Matrix.trace]; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => ‖M‖) (fun i _ => component_norm _ _ _)).trans_eq (by simp))

lemma op_cost {n m k : Type} [Fintype n] [Fintype m] [Fintype k] [DecidableEq n] [DecidableEq k]
    {X : Matrix m n ℂ} {Y : Matrix n k ℂ} {C D : ℝ} (h : ‖X‖≤ C) (h' : ‖Y‖≤ D) : ‖X * Y‖ ≤ C*D :=
  (Matrix.l2_opNorm_mul ..).trans (mul_le_mul h h' (norm_nonneg _) ((norm_nonneg _).trans h))

namespace LogStrip
variable (h : LogStrip V η C)
include h
omit [Fintype d] [DecidableEq d] in
lemma mono {σ D : ℝ} (hσ : 0<σ) (hη : σ≤η) (hD : C≤D) : LogStrip V σ D :=
  ⟨hσ, h.lit.mono hη,fun _ hx => h.unit _ (tube_mono hη hx),fun _ hx => (h.invert _ (tube_mono hη hx)).trans hD,
    fun _ _ _ hx hy hv => (h.one _ _ _ (tube_mono hη hx) (tube_mono hη hy) hv).trans hD,
    fun _ _ _ _ _ hx hy hz hv hw => (h.two _ _ _ _ _ (tube_mono hη hx) (tube_mono hη hy) (tube_mono hη hz) hv hw).trans hD⟩

omit [Fintype d] [DecidableEq d] h in
lemma bubble_expr (V : Vertex d a a) (q p : Momentum) (v w : CSpace d) :
    bubble V q (-p) p v w = (V.base q)⁻¹ * V.two q (-p) p v w - (V.base q)⁻¹ * V.one (q+p) (-p) v * (V.base (q+p))⁻¹ * V.one q p w := by
  rw [bubble,neg_add_cancel_right,add_neg_cancel_right]

omit [Fintype d] [DecidableEq d] in
lemma bubble_bound (v w : CSpace d) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1) {p q : Momentum} (hp : p∈Tube (η/2)) (hq : q∈Tube (η/2)) :
    ‖bubbleTrace V v w p q‖ ≤ Fintype.card a * (C^2+C^4) := by
  have hs := tube_mono (show η/2≤η by linarith [h.width]); have ht : q+p∈ Tube η := tube_mono (by linarith) (tube_add hq hp)
  refine (trace_norm _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [bubble_expr]
  exact (norm_sub_le ..).trans ((add_le_add (op_cost (h.invert q (hs hq)) (h.two _ _ _ _ _ (hs hq) (tube_neg (hs hp)) (hs hp) hv hw))
    (op_cost (op_cost (op_cost (h.invert _ (hs hq)) (h.one _ _ _ ht (tube_neg (hs hp)) hv)) (h.invert _ ht)) (h.one _ _ _ (hs hq) (hs hp) hw))).trans_eq (by ring))

omit [Fintype d] [DecidableEq d] in
lemma bubble_analytic (v w : CSpace d) {p q : Momentum} (hp : p∈Tube (η/2)) (hq : q∈Tube (η/2)) : ContDiffAt ℂ ω (Function.uncurry (bubbleTrace V v w)) (p,q) := by
  have hs := tube_mono (show η/2≤η by linarith [h.width]); have ht : q+p∈ Tube η := tube_mono (by linarith) (tube_add hq hp)
  unfold bubbleTrace Function.uncurry; simp only [bubble_expr]
  have hq := hs hq; have hp := hs hp; have H := tube_neg hp
  have he := analyticInv (h.lit.zeroD (q:=Prod.snd) (x:=(p,q)) contDiffAt_snd hq) (h.unit q hq)
  refine analyticTrace ((analyticMul he (h.lit.twoD (q:=Prod.snd) (p:=fun x => -x.1) (s:=Prod.fst) (x:=(p,q)) contDiffAt_snd contDiffAt_fst.neg contDiffAt_fst hq H hp v w)).sub ?_)
  exact analyticMul (analyticMul (analyticMul he (h.lit.oneD (q:=fun x => x.2+x.1) (p:=fun x => -x.1) (x:=(p,q)) (by fun_prop) (by fun_prop) ht H v))
    (analyticInv (h.lit.zeroD (q:=fun x => x.2+x.1) (x:=(p,q)) (by fun_prop) ht) (h.unit _ ht)))
    (h.lit.oneD (q:=Prod.snd) (p:=Prod.fst) (x:=(p,q)) (by fun_prop) (by fun_prop) hq hp w)

omit [Fintype d] [DecidableEq d] in
lemma bubble_periods (v w : CSpace d) {p q : Momentum} (hp : p∈Tube (η/2)) (hq : q∈Tube (η/2)) (x y : Cover) :
    bubbleTrace V v w (p+reciprocal x) (q+reciprocal y) = bubbleTrace V v w p q := by
  have hs := tube_mono (show η/2≤η by linarith [h.width]); have ht : q+p∈ Tube η := tube_mono (by linarith) (tube_add hq hp)
  have hq := hs hq; have hp := hs hp; have H := tube_neg hp
  simp only [bubbleTrace,bubble_expr]; rw [show q+reciprocal y + (p+reciprocal x) = q+p+reciprocal (y+x) by rw [reciprocal_add]; abel,
    show -(p+reciprocal x)=-p+reciprocal (-x) by rw [reciprocal_neg]; abel, (h.lit.base _ hq).2 y, (h.lit.base _ ht).2 (y+x),
    (h.lit.two _ _ _ _ _ hq H hp).2 y (-x) x,(h.lit.one _ _ _ ht H).2 (y+x) (-x),(h.lit.one _ _ _ hq hp).2 y x]

omit [Fintype d] in
lemma log_vane (i j) : Vane (fun p => logKernel V p i j) (η/2) := by
  have he p (hp : p∈Tube (η/2)) k := h.bubble_analytic (Pi.single i 1) (Pi.single j 1) hp (radians_strip k (half_pos h.width))
  refine ⟨half_pos h.width,fun p hp => (boxMean_derivative ((Work.F07.stripOpen _).mem_nhds hp) he).differentiableAt, fun p hp x => zone_congr (fun q _ => ?_)⟩
  simpa only [reciprocal_zero,add_zero] using! h.bubble_periods (Pi.single i 1) (Pi.single j 1) hp (radians_strip q (half_pos h.width)) x 0

omit h [Fintype d] in lemma single_bounded (i j : d) : ‖(Pi.single i 1 : d → ℂ) j‖ ≤ 1 := by simp [Pi.single_apply]; split <;> simp

omit [Fintype d] in
lemma log_bound (i j) {p : Momentum} (hp : p∈Tube (η/2)) : ‖logKernel V p i j‖ ≤ Fintype.card a * (C^2+C^4) :=
    boxMean_norm (fun _ _ => h.bubble_bound _ _ (single_bounded i) (single_bounded j) hp (radians_strip _ (half_pos h.width)))
end LogStrip
end op

open scoped Matrix.Norms.Frobenius
variable {n : Side} {J E : Type} [Fintype E] [Fintype J] [DecidableEq E] [DecidableEq J] {A : Grid n J d} {M : Grid n E a}

def logError (a : Type) [Fintype a] (η C : ℝ) := Fintype.card a * (C^2+C^4) * (2*((1+η/8)/(η/8)))^4


lemma log_compares {f : (J → ℝ) → Matrix E E ℝ} (hf : ContDiffAt ℝ ω f 0) (hF : Synced A M M (actualMatrix f) V) (h : LogStrip V η C) :
    Compares A A (Coeff (fun z => Real.log (f z).det)) (logKernel V) (logError a η C * Real.exp (-(η/8)*n.val)) := by
  have hk k i (ht : Matches (n:=n) k i) : IsUnit (V.base k) := h.unit _ (Work.F07.realStrip _ h.width ht.bar)
  have hv : IsUnit (f 0) := by
    have hv := Routed.isUnit (fun i => hF.base (mon_matches i)) (fun i => hk _ i (mon_matches i))
    change IsUnit (Complex.ofRealHom.mapMatrix (f 0)) at hv
    rw [isUnit_iff_isUnit_det,← RingHom.map_det, isUnit_iff_ne_zero] at hv
    exact (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (fun he => hv (by rw [he,map_zero])))
  constructor
  · intro i j he; refine pairing_ext (Y:=0) (fun x y => ?_)
    rw [Matrix.zero_mulVec,dotProduct_zero,sample_actual,actual_log_pair hF hf hv hk i j (mon_matches j),if_neg he,mul_zero]
  intro p i hp j k
  let u := bubbleTrace V (Pi.single j 1) (Pi.single k 1) p
  have hη := h.width; have hP := Work.F07.realStrip _ (half_pos hη) hp.bar
  have he : Vane u (η/2) := ⟨half_pos hη,fun q hq => ((h.bubble_analytic _ _ hP hq).comp (f:=fun q => (p,q)) q (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp), fun _ hq _ => by
    simpa only [reciprocal_zero,add_zero] using! h.bubble_periods (Pi.single j 1) (Pi.single k 1) hP hq 0 _⟩
  have hK := fun q hq => h.bubble_bound _ _ (LogStrip.single_bounded j) (LogStrip.single_bounded k) hP (show q ∈ Tube _ from hq)
  have ht := mesh_error (σ:=η/8) (b:=η/8) n he hK (by linarith) (by linarith) (by linarith)
  have hs := sample_actual (M:=A) (fun z => Real.log (f z).det) (-i) i (Pi.single j 1) (Pi.single k 1)
  rw [single_dotProduct,one_mul, Matrix.mulVec_single_one, Matrix.col_apply,actual_log_pair hF hf hv hk _ _ hp,if_pos (neg_add_cancel _)] at hs
  rw [hs]; exact ht
end YM.Push.Loops
