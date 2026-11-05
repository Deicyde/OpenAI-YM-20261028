import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Powers

set_option warningAsError false

/-!
# Translation lowers certain position degrees

All expressions at real positions first, so we can account grad
and averaged link calculus. Neither translation nor gradient in
this file is modulo a periodic torus. Shift along the full UNIT
segment (not necessarily times L^-1), giving power with values in
bounded continuous paths for later hol. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Powers
open Function Filter Finset Tensor Work Set MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def shade (n : ℕ) : E →L[ℝ] C(unitInterval,E) :=
    let f : E →ₗ[ℝ] C(unitInterval,E) := {toFun := fun x => ⟨fun t => (t:ℝ)^n • x,(continuous_subtype_val.pow n).smul continuous_const⟩,
                                               map_add' := fun i j => ContinuousMap.ext fun t => (by change ((t:ℝ)^n) • (i+j)=((t:ℝ)^n) • i+((t:ℝ)^n) • j; rw [smul_add]),
                                               map_smul' := fun r j => ContinuousMap.ext fun t => (by change ((t:ℝ)^n) • (r•j)=r • (((t:ℝ)^n) • j); rw [smul_comm]) }
    f.toContinuousLinearMap


private def picks {k : ℕ} (A : T V E k) (x : V) (f : Finset (Fin k)) (v : V) := A (f.piecewise (fun _ => v) (fun _ => x))

variable {k d : ℕ}
omit [FiniteDimensional ℝ E] in
private theorem scaling (A : T V E k) (x : V) (f : Finset (Fin k)) (t : ℝ) (v : V) :
    picks A x f (t • v) = t^f.card • picks A x f v ∧ picks A (t • x) f v=t^fᶜ.card • picks A x f v := by
  unfold picks
  let Y := f.piecewise (fun _ => v) (fun _ => x)
  have hh (s : Finset (Fin k)) : A (fun i => (if i∈s then t else 1) • Y i)=t^s.card • A Y := by
    rw [A.map_smul_univ, prod_ite_mem]; simp
  constructor
  · rw [← hh f]
    apply congrArg A; funext i; by_cases H:i∈f <;> simp [Y,H,Finset.piecewise]
  rw [← hh fᶜ]; apply congrArg A; funext i; by_cases H:i∈f <;> simp [Y,H,Finset.piecewise]

omit [FiniteDimensional ℝ E] in
private lemma blend (A : T V E k) (x : V) (f : Finset (Fin k)) : home (picks A x f) f.card := by
  refine ⟨A.contDiff.comp (contDiff_pi.mpr (fun i => ?_)),fun t v => (scaling A x f t v).1⟩
  change ContDiff ℝ ω fun v : V => f.piecewise (fun _ => v) (fun _ => x) i
  by_cases he : i∈ f
  · simp only [Finset.piecewise,if_pos he]; exact contDiff_id
  simp only [Finset.piecewise,if_neg he]; exact contDiff_const

/-- Power into time-polynomial paths. -/
private def sprig (A : T V E k) (x : V) (B : Finset (Fin k)) (v : V) : C(unitInterval,E) := shade Bᶜ.card (picks A x B v)

def sparse (A : T V E k) (x v : V) : C(unitInterval,E) := ∑ B ∈ Finset.univ.erase (Finset.univ : Finset (Fin k)), sprig A x B v

lemma sparse_mem (A : T V E k) (x : V) : (fun v => sparse A x v)∈ space V C(unitInterval,E) (k-1) := by
  unfold sparse; refine sums (k:=k-1) _ (sprig A x) fun i hi => ?_
  refine carried (shade iᶜ.card) (residence (blend A x i) ?_)
  have he := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ i,(mem_erase.mp hi).1⟩)
  rw [card_univ,Fintype.card_fin] at he; omega

lemma diag_sparse (A : T V E k) (x : V) (v : V) (s : unitInterval) :
    diagonal A (v + (s:ℝ) • x) = diagonal A v + sparse A x v s := by
  let f (B) := picks A ((s:ℝ) • x) B v
  change A ((fun _ => v)+(fun _ => (s:ℝ) • x)) = _
  rw [A.map_add_univ]; change ∑ B,f B= _
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ (Finset.univ : Finset (Fin k))),
    show f _=diagonal A v from congrArg A (by ext; simp [Finset.piecewise])]
  unfold sparse; rw [ContinuousMap.sum_apply]; apply congrArg (Tensor.diagonal A v+·); exact sum_congr rfl fun i _ => (scaling A x i (s:ℝ) v).2

/-- Differencing an arbitrary polynomial yields polynomial of one lower degree. -/
lemma discrete {f : V → E} (x : V) (h : f ∈ space V E k) : (fun v => f (v+x)-f v)∈space V E (k-1) := by
  let Q (f : V→E) := (fun v => f (v+x)-f v)∈space V E (k-1)
  refine next (p:=Q) (k:=k) ?_ ?_ ?_ ?_ h
  · rintro f ⟨i,hi,hf⟩
    let A := Tensor.coeff f i 0
    have hp : f=diagonal A := tensor_form hf
    let L : C(unitInterval,E) →L[ℝ] E := ContinuousMap.evalCLM ℝ 1
    have he : (fun v => f (v+x)-f v)=(fun v => L (sparse A x v)) := funext fun v => by
      change _ = sparse A x v 1; conv_lhs => rw [hp, ← one_smul ℝ x, ← show ((1:unitInterval):ℝ)=1 from rfl,diag_sparse,add_sub_cancel_left]
    unfold Q; rw [he]; exact widen _ _ (Nat.sub_le_sub_right hi _) (carried L (sparse_mem A x))
  · unfold Q; simp only [Pi.zero_apply,sub_zero]; exact constants 0 _
  · intro u v hu hv; unfold Q; rw [show (fun i => (u+v) (i+x) - (u+v) i)=(fun i => u (i+x)-u i + (v (i+x)-v i)) from funext fun i => by simp; abel]
    exact add hu hv
  intro c u hu; unfold Q; simp only [Pi.smul_apply,← smul_sub]; exact smul hu c
end YM.MultiNext.SignedSource.Powers
