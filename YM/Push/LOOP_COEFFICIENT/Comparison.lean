import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
import YM.Push.LOOP_COEFFICIENT.Thin


/-!
# Cauchy price for the subtracted residue determinant

Allow opposite normalizations at every routed endpoint (e.g., distributed
coarse aliases and real elliptic weights). No analyticity of those normalizers
needed. Telescoping BEFORE the trace-size estimate. Not applicable to the
N-N_b gradient correction, for which there is a separate Ward argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Set Complex MeasureTheory Bloch Laurent Lattice
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {G : Gauge} {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
variable {p q : Momentum}

structure Normalization (b : Type) [Fintype b] [DecidableEq b] where
  into : Momentum → Matrix b b ℂ
  fromCov : Momentum → Matrix b b ℂ
  hinto p : IsUnit (into p)
  hfrom p : IsUnit (fromCov p)

def Normalization.clean (P : Normalization b) (s q : Momentum) (X : Matrix b b ℂ) := P.fromCov s * X * P.into q

def Vertex.clean (X : Vertex a b b) (P : Normalization b) : Vertex a b b :=
  ((Vertex.const P.fromCov).mul X).mul (Vertex.const P.into)

variable (X : Vertex a b b) (P : Normalization b)

omit [Fintype a] [DecidableEq a] in
lemma clean_base (q) : (X.clean P).base q = P.clean q q (X.base q) := rfl
omit [Fintype a] [DecidableEq a] in
lemma clean_one (q p v) : (X.clean P).one q p v = P.clean (q+p) q (X.one q p v) := by simp [Vertex.clean, Normalization.clean, Vertex.const,Vertex.mul,matrixMulLinear]
omit [Fintype a] [DecidableEq a] in
lemma clean_two (q p s v w) : (X.clean P).two q p s v w = P.clean (q+p+s) q (X.two q p s v w) := by simp [Vertex.clean, Normalization.clean, Vertex.const,Vertex.mul,matrixMulLinear]
lemma Normalization.contract (P : Normalization b) (p) (M : Matrix b b ℂ) : (P.fromCov p)⁻¹ * (P.fromCov p * M) = M := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp (P.hfrom p)),Matrix.one_mul]
lemma Normalization.contract' (P : Normalization b) (p) (M : Matrix b b ℂ) : P.into p * ((P.into p)⁻¹ * M) = M := by rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (P.hinto p)),Matrix.one_mul]
lemma Normalization.loop (P : Normalization b) (p) (M : Matrix b b ℂ) : ((P.into p)⁻¹ * M * P.into p).trace = M.trace := by rw [Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp (P.hinto p)),Matrix.one_mul]

omit [Fintype a] [DecidableEq a] in
lemma clean_trace (v w p q) : bubbleTrace (X.clean P) v w p q = bubbleTrace X v w p q := by
  unfold bubbleTrace; simp only [LogStrip.bubble_expr, clean_base,clean_one,clean_two, neg_add_cancel_right,add_neg_cancel_right,Normalization.clean, Matrix.mul_inv_rev]
  rw [show ∀ A B C D E : Matrix b b ℂ,
      ((P.into q)⁻¹ * (A * (P.fromCov q)⁻¹)) * (P.fromCov q * B * P.into q) -
        (P.into q)⁻¹ * (A * (P.fromCov q)⁻¹) * (P.fromCov q * C * P.into (q+p)) * ((P.into (q+p))⁻¹ * (D * (P.fromCov (q+p))⁻¹)) * (P.fromCov (q+p) * E * P.into q) =
      (P.into q)⁻¹ * (A * B - A * C * D * E) * P.into q from fun A B C D E => by simp only [mul_assoc,P.contract,P.contract',mul_sub,sub_mul]]
  exact P.loop ..

variable {η M : ℝ} {P} {X Y : Vertex a b b}

structure Comparison (X Y : Vertex a b b) (P : Normalization b) (η M : ℝ) : Prop where
  width : 0<η
  litX : Lit X η
  litY : Lit Y η
  unitX q : q∈Tube η → IsUnit (X.base q)
  unitY q : q∈Tube η → IsUnit (Y.base q)
  invX q : q∈Tube η → ‖((X.clean P).base q)⁻¹‖ ≤ M
  invY q : q∈Tube η → ‖((Y.clean P).base q)⁻¹‖ ≤ M
  base q : q∈Tube η → Thin ((X.clean P).base q - (Y.clean P).base q) M
  one q p v : q∈Tube η → p∈Tube η → (∀ i, ‖v i‖≤1) → CoveredPair ((X.clean P).one q p v) ((Y.clean P).one q p v) M M
  two q p s v w : q∈Tube η → p∈Tube η → s∈Tube η → (∀ i, ‖v i‖≤1) → (∀ i, ‖w i‖≤1) → CoveredPair ((X.clean P).two q p s v w) ((Y.clean P).two q p s v w) M M

namespace Comparison
variable (h : Comparison X Y P η M)
include h
omit [Fintype a] [DecidableEq a] in
lemma resolvent (hq : q∈Tube η) : CoveredPair ((X.clean P).base q)⁻¹ ((Y.clean P).base q)⁻¹ M (M*M*M) := by
  let he {X : Matrix b b ℂ} (hx : IsUnit X) : IsUnit (P.clean q q X) := ((P.hfrom q).mul hx).mul (P.hinto q)
  exact CoveredPair.inv (h.base q hq) (he (h.unitX q hq)) (he (h.unitY q hq)) (h.invX q hq) (h.invY q hq)
omit [Fintype a] [DecidableEq a] in
lemma bubble_gap (hp : p∈Tube (η/2)) (hq : q∈Tube (η/2)) {v w : CSpace a} (hv : ∀ i, ‖v i‖≤1) (hw : ∀ i, ‖w i‖≤1) :
    ‖bubbleTrace X v w p q - bubbleTrace Y v w p q‖ ≤ M^2+3*M^4+2*M^6 := by
  have he := h.width; have hs := tube_mono (show η/2≤η by linarith)
  have ht := tube_mono (show η/2+η/2≤η by linarith) (tube_add hq hp)
  have h₀ := h.resolvent (hs hq)
  have h₁ := h₀.mul (h.two _ _ _ _ _ (hs hq) (hs (tube_neg hp)) (hs hp) hv hw)
  have h₂ := ((h₀.mul (h.one _ _ _ ht (hs (tube_neg hp)) hv)).mul (h.resolvent ht)).mul (h.one _ _ _ (hs hq) (hs hp) hw)
  rw [← clean_trace X P, ← clean_trace Y P,bubbleTrace,bubbleTrace,← trace_sub,LogStrip.bubble_expr,LogStrip.bubble_expr, sub_sub_sub_comm]
  exact (h₁.gap.sub h₂.gap).trace.trans_eq (by ring)
end Comparison

omit [Fintype a] [DecidableEq a] in
lemma smooth_bubble (he : 0<η) (h : Lit X η) (hu : ∀ q∈Tube η, IsUnit (X.base q)) {v w : CSpace a} (hp : p∈Tube (η/2)) (hq : q∈Tube (η/2)) :
    ContDiffAt ℂ ω (uncurry (bubbleTrace X v w)) (p,q) := by
  have hs := tube_mono (show η/2≤η by linarith)
  have ht := tube_mono (show η/2+η/2≤η by linarith) (tube_add hq hp)
  unfold bubbleTrace Function.uncurry; simp only [LogStrip.bubble_expr]
  have hq := hs hq; have hp := hs hp; have H := tube_neg hp
  have he := analyticInv (h.zeroD (q:=Prod.snd) (x:=(p,q)) contDiffAt_snd hq) (hu q hq)
  refine analyticTrace ((analyticMul he (h.twoD (q:=Prod.snd) (p:=fun x => -x.1) (s:=Prod.fst) (x:=(p,q)) contDiffAt_snd contDiffAt_fst.neg contDiffAt_fst hq H hp v w)).sub ?_)
  exact analyticMul (analyticMul (analyticMul he (h.oneD (q:=fun x => x.2+x.1) (p:=fun x => -x.1) (x:=(p,q)) (by fun_prop) (by fun_prop) ht H v))
    (analyticInv (h.zeroD (q:=fun x => x.2+x.1) (x:=(p,q)) (by fun_prop) ht) (hu _ ht)))
    (h.oneD (q:=Prod.snd) (p:=Prod.fst) (x:=(p,q)) (by fun_prop) (by fun_prop) hq hp w)




end YM.Push.Loops
