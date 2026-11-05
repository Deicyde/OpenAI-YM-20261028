import YM.Push.LOOP_COEFFICIENT.Vertex

/-!
# One routed logarithmic loop at finite period

Actual trace with ordered mixed derivative inputs. The summand for the
opposite pair has internal variable over the *whole* reciprocal torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n : Side} {J E a d : Type} [Fintype J] [Fintype E] [Fintype a] [Fintype d]
  [DecidableEq J] [DecidableEq E] [DecidableEq a] [DecidableEq d] {A : Grid n J d} {M : Grid n E a}

-- note: choose momentum p on second external input y (M(p) tested by x at -p).
-- ordered logdet_variation second factor is D_x→following D_y.
def bubble (V : Vertex d a a) (q k p : Momentum) (x y : CSpace d) :=
  (V.base (q+k+p))⁻¹ * V.two q k p x y -
    (V.base (q+p+k))⁻¹ * V.one (q+p) k x * (V.base (q+p))⁻¹ * V.one q p y

def bubbleTrace (V : Vertex d a a) (x y : CSpace d) (p q : Momentum) := (bubble V q (-p) p x y).trace

omit [DecidableEq J] [Fintype J] in
lemma bubble_read {V : Vertex d a a} {X : Jet J (Matrix E E ℂ)} (h : Synced A M M X V) (hv : IsUnit X.base)
    (hV : ∀ q k, Matches (n:=n) q k → IsUnit (V.base q)) {q s p : Momentum} {k i j : Site n}
    (hk : Matches q k) (hi : Matches s i) (hj : Matches p j) (x y : CSpace d) :
    let a := plane A i *ᵥ x; let b := plane A j *ᵥ y
    Routed M M (k+(i+j)) k (X.base⁻¹ * X.quad a b - X.base⁻¹ * X.lin a * X.base⁻¹ * X.lin b) (bubble V q s p x y) := by
  have he {k q} (hk : Matches q k) := (h.base hk).inv hv (hV q k hk)
  intro a b
  simp only [bubble,sub_eq_add_neg]
  apply Routed.add
  · rw [← add_assoc]; exact (he (hk.add hi |>.add hj)).mul (h.two hk hi hj x y)
  · rw [add_comm i j,← add_assoc]; exact ((((he (hk.add hj |>.add hi)).mul (h.one (hk.add hj) hi x)).mul (he (hk.add hj))).mul
      (h.one hk hj y)).neg

omit [DecidableEq J] [Fintype J] in
lemma logVariation_read {V : Vertex d a a} {X : Jet J (Matrix E E ℂ)} (h : Synced A M M X V) (hv : IsUnit X.base)
    (hV : ∀ q k, Matches (n:=n) q k → IsUnit (V.base q)) {s p : Momentum} {i j : Site n}
    (hi : Matches s i) (hj : Matches p j) (x y : CSpace d) :
    logVariation X (plane A i *ᵥ x) (plane A j *ᵥ y) = if i+j=0 then ∑ k : Site n,(bubble V (mon k) s p x y).trace else 0 := by
  rw [logVariation_apply,← Matrix.trace_sub]
  exact Routed.trace (fun k => bubble_read h hv hV (mon_matches k) hi hj x y)

lemma actual_log_pair {V : Vertex d a a} {f : (J → ℝ) → Matrix E E ℝ} (h : Synced A M M (actualMatrix f) V)
    (hf : ContDiffAt ℝ ω f 0) (hv : IsUnit (f 0)) (hV : ∀ q k, Matches (n:=n) q k → IsUnit (V.base q))
    (i j : Site n) {p : Momentum} (hp : Matches p j) (x y : CSpace d) :
    (actualScalar (fun z => Real.log (f z).det)).quad (plane A i *ᵥ x) (plane A j *ᵥ y) =
      if i + j = 0 then ∑ k : Site n, bubbleTrace V x y p (mon k : Momentum) else 0 := by
  rw [actualScalar_log hf hv]
  by_cases hi : i + j = 0
  · rw [eq_neg_of_add_eq_zero_left hi,neg_add_cancel,if_pos rfl,logVariation_read h (cmat_unit hv) hV hp.neg hp,if_pos (neg_add_cancel _)]; rfl
  · rw [if_neg hi,logVariation_read h (cmat_unit hv) hV (mon_matches i) hp, if_neg hi]
end YM.Push.Loops
