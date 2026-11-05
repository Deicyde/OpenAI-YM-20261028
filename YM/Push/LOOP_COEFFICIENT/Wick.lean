import YM.Push.LOOP_COEFFICIENT.DriftKernels
import YM.Push.LOOP_COEFFICIENT.Envelope
import YM.Push.LOOP_COEFFICIENT.Orders


/-! # Bounded analytic matrix space with order filter -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Matrix Filter Set Lattice Laurent Bloch Exterior Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
    {X Y : Momentum → Matrix a b ℂ} {η η' C C' D : ℝ} {m n : ℕ}

structure Wick (X : Momentum → Matrix a b ℂ) (η C : ℝ) (m : ℕ) : Prop where
  side : 0 < η
  budget : 0 ≤ C
  smooth p : p∈Tube η → ContDiffAt ℂ ω X p
  reset p v : p∈Tube η → X (p+reciprocal v) = X p
  estimate p : p∈Tube η → Entries (X p) C
  order p : UnderMatrix X p m

namespace Wick
variable (h : Wick X η C m)
include h
omit [DecidableEq a] in lemma atZero : ContDiffAt ℂ ω X 0 := h.smooth 0 (Work.F07.realStrip _ h.side (star_zero _))
omit [DecidableEq a] in lemma mono (hη : 0<η') (he : η'≤η) (hC : C≤C') (hn : n≤m) : Wick X η' C' n := ⟨hη,h.budget.trans hC,fun _ hp => h.smooth _ (tube_mono he hp),fun _ _ hp => h.reset _ _ (tube_mono he hp),fun _ hp => (h.estimate _ (tube_mono he hp)).mono hC,fun _ => (h.order _).mono hn⟩
omit [DecidableEq a] in lemma add (h' : Wick Y η D m) : Wick (X+Y) η (C+D) m := ⟨h.side,add_nonneg h.budget h'.budget,fun p hp => (h.smooth p hp).add (h'.smooth p hp), fun p v hp => congr_arg₂ (·+·) (h.reset p v hp) (h'.reset p v hp), fun p hp => (h.estimate p hp).add (h'.estimate p hp), fun p => (h.order p).add h.atZero h'.atZero (h'.order p)⟩
omit [DecidableEq a] in lemma sub (h' : Wick Y η D m) : Wick (X-Y) η (C+D) m := ⟨h.side,add_nonneg h.budget h'.budget,fun p hp => (h.smooth p hp).sub (h'.smooth p hp), fun p v hp => congr_arg₂ (·-·) (h.reset p v hp) (h'.reset p v hp), fun p hp => (h.estimate p hp).sub (h'.estimate p hp), fun p => (h.order p).sub h.atZero h'.atZero (h'.order p)⟩

omit [DecidableEq a] in lemma reverse : Wick (fun p => X (-p)) η C m := ⟨h.side,h.budget,fun p hp => (h.smooth _ (tube_neg hp)).comp p (f:=(-·)) (by fun_prop), fun p v hp => by rw [neg_add,← reciprocal_neg, h.reset _ _ (tube_neg hp)],fun p hp => h.estimate _ (tube_neg hp),fun p i j => under_negate (X:=fun p => (X p).transpose) (fun a b => h.order (-p) b a) i j⟩
omit [DecidableEq a] in lemma mul {Y : Momentum → Matrix b c ℂ} (h' : Wick Y η D n) : Wick (fun p => X p * Y p) η (Fintype.card b * (C*D)) (m+n) :=
  ⟨h.side,mul_nonneg (by positivity) (mul_nonneg h.budget h'.budget),fun p hp => analyticMul (h.smooth p hp) (h'.smooth p hp),fun p v hp => congr_arg₂ (·*·) (h.reset p v hp) (h'.reset p v hp),fun p hp => (h.estimate p hp).mul (h'.estimate p hp),fun p => (h.order p).mul h.atZero h'.atZero (h'.order p)⟩
omit [DecidableEq a] in lemma vane (i j) : Vane (fun p => X p i j) η := ⟨h.side,fun p hp => (analyticComponent (h.smooth p hp) i j).differentiableAt (by simp),fun p hp v => congr_fun (congr_fun (h.reset p v hp) i) j⟩
omit h [DecidableEq a] in lemma zero (hη : 0 < η) (a b m) [Fintype a] [Fintype b] [DecidableEq b] : Wick (fun _ => (0:Matrix a b ℂ)) η 0 m := ⟨hη,le_rfl,fun _ _ => contDiffAt_const,fun _ _ _ => rfl,fun _ _ => ⟨le_rfl,fun _ _ => norm_zero.le⟩,fun p _ _ k _ => line_vac p k⟩
omit h [DecidableEq a] in lemma const (hη : 0<η) {X : Matrix a b ℂ} (hX : Entries X C) : Wick (fun _ => X) η C 0 := ⟨hη,hX.nonneg,fun _ _ => contDiffAt_const,fun _ _ _ => rfl,fun _ _ => hX,fun p => UnderMatrix.zero _ p⟩
end Wick

def evalAxis (i : Axis) (X : Momentum → Matrix a b ℂ) (p : Momentum) := X (mask i p)
omit [DecidableEq a] in lemma Wick.evalAxis (h : Wick X η C m) (i : Axis) : Wick (Loops.evalAxis i X) η C m :=
  ⟨h.side,h.budget,fun p hp => (h.smooth _ (mask_tube i hp)).comp p (mask_diff i).contDiffAt,fun p v hp => by unfold Loops.evalAxis; rw [mask_period,h.reset _ _ (mask_tube i hp)],fun p hp => h.estimate _ (mask_tube i hp),fun p a b k hk => by simpa [lineD,Loops.evalAxis,mask_ray] using h.order (mask i p) a b k hk⟩

def divideAxis (i : Axis) (X : Momentum → Matrix a b ℂ) (p : Momentum) := of fun a b => divided i (fun p => X p a b) p
omit [DecidableEq a] in lemma Wick.divideAxis (h : Wick X η C (m+1)) (i : Axis) : Wick (Loops.divideAxis i X) (η/6) (divisionCost η 1 * C) m := by
  have he := h.side; have hC := h.budget
  have hb i j p hp := (h.estimate p hp).entry i j
  exact ⟨by linarith, by unfold divisionCost; positivity,fun p hp => analyticMatrix (fun a b => division_diff i (h.vane a b) (hb a b) hp), fun p v _ => by ext; exact division_period i v,
    fun p hp => ⟨by unfold divisionCost; positivity,fun a b => (division_bound i (h.vane a b) (hb a b) hp).trans_eq (by unfold divisionCost; ring)⟩,
    fun p a b => division_order i (h.vane a b) (hb a b) (fun p => h.order p a b) p⟩

omit [DecidableEq a] in lemma Wick.divide_eq (h : Wick X η C m) (i : Axis) {p} (hp : p∈Tube (η/6)) : q p i • (Loops.divideAxis i X p) = X p - Loops.evalAxis i X p := by
  ext a b; exact division_mult i (h.vane a b) (fun p hp => (h.estimate p hp).entry a b) hp
end YM.Push.Loops
