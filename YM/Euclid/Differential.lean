import YM.Euclid.Lift
import YM.Analysis.SmoothJets

/-!
# All-spectator differentiation interface

Make producer's obligation about equality of kernels; algebraic
composition/compatibility and translations follow from faithfulness. Real and H
compatibility stated separately. Companions expressed with respect to the same
hypothetical quotient fields, not their own. Distributional differentiation on
Conf (so ordinary derivative of smooth kernels, tested only within Conf).
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter Analysis
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {S : Table L}

structure DiffPlan (S : Table L) where
  rise {d e : ℕ} (h : d ≤ e) : S.Field d →ₗ[ℂ] S.Field e
  deriv (d : ℕ) (a : Axis) : S.Field d →ₗ[ℂ] S.Field (d+1)

variable (P : DiffPlan S)

namespace Points
variable {n : ℕ}

def direction (i : Fin n) (a : Axis) : Points n := PiLp.single 2 i (basis a)

def gradient (i : Fin n) (a) := @D (Points n) ℂ _ _ _ _ (direction i a)

def arrangeL (p : Equiv.Perm (Fin n)) : Points n →L[ℝ] Points n := LinearMap.toContinuousLinearMap
  { toFun := rearrange p
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem directed (p : Equiv.Perm (Fin n)) (i : Fin n) (a : Axis) :
    arrangeL p (direction (p i) a) = direction i a := by
  ext1 j
  change direction (p i) a (p j) = _
  simp [direction,PiLp.single_apply]

@[simp] theorem arranged (p : Equiv.Perm (Fin n)) (x : Points n) : arrangeL p x = rearrange p x := rfl

/-- Chain rule for reordering, useful also beyond perm invariance. -/
theorem placement (p : Equiv.Perm (Fin n)) (i : Fin n) (a) (f : Points n → ℂ) (x : Points n)
    (H : DifferentiableAt ℝ f (arrangeL p x)) :
    gradient (p i) a (fun y => f (rearrange p y)) x = gradient i a f (rearrange p x) := by
  change fderiv ℝ (f ∘ arrangeL p) x _ = _
  rw [fderiv_comp x H (arrangeL p).differentiableAt,(arrangeL p).fderiv,
    ContinuousLinearMap.comp_apply,directed]; rfl
end Points

namespace DiffPlan
open Points
variable (T : Table L)
structure Inclusions : Prop where
  kernels {d e : ℕ} (h : d ≤ e) (B : S.Field d) {n : ℕ} {x : Points (n+1)} (hx : x ∈ conf (n+1)) (w : Fin n → S.Tag) :
    S.useAt T x (Fin.cons ⟨e,P.rise h B⟩ w) = S.useAt T x (Fin.cons ⟨d,B⟩ w)
structure Derivatives : Prop where
  kernels (d a) (B : S.Field d) {n : ℕ} {x : Points (n+1)} (hx : x ∈ conf (n+1)) (w : Fin n → S.Tag) :
    S.useAt T x (Fin.cons ⟨d+1,P.deriv d a B⟩ w) =
      gradient 0 a (fun y => S.useAt T y (Fin.cons ⟨d,B⟩ w)) x

structure Orientation (P : DiffPlan S) (hp : S.RealSpin) : Prop where
  realInc {d e : ℕ} (h : d ≤ e) (B : S.Field d) : S.conj hp e (P.rise h B) = P.rise h (S.conj hp d B)
  realDer d a (B : S.Field d) : S.conj hp (d+1) (P.deriv d a B) = P.deriv d a (S.conj hp d B)
  mirrorInc {d e : ℕ} (h : d ≤ e) (s : Signed) (B : S.Field d) :
    S.mirror hp e s (P.rise h B) = P.rise h (S.mirror hp d s B)
  mirrorDer d b (s : Signed) (B : S.Field d) : S.mirror hp (d+1) s (P.deriv d b B) =
    ∑ a : Axis, (s.matrix a b : ℂ) • P.deriv d a (S.mirror hp d s B)

section Ext
variable (h : S.Symmetric) (hm : P.Inclusions S)
include h hm

theorem through_limit {d e : ℕ} (H : d ≤ e) (v : S.Field d) : S.spectra e (P.rise H v) = S.spectra d v := by
  funext x; rcases x with ⟨n,x,w,hx⟩
  rw [← Table.through S h, ← Table.through S h]; exact hm.kernels H v hx _

theorem inject {d e : ℕ} (H : d ≤ e) : Injective (P.rise H) := by
  intro a b he
  apply S.faithfully
  rw [← P.through_limit h hm H a, ← P.through_limit h hm H b, he]

theorem transit {d e l : ℕ} (H : d ≤ e) (J : e ≤ l) (p : S.Field d) :
    P.rise J (P.rise H p) = P.rise (H.trans J) p := by
  apply S.faithfully; simp only [P.through_limit h hm]

theorem arrival {d : ℕ} (p : S.Field d) : P.rise (show d ≤ d from le_rfl) p = p :=
  S.faithfully d (P.through_limit h hm _ _)

omit h in
lemma fixs (H : S.Basic) {d e : ℕ} (w : d ≤ e) : P.rise w (S.unit d) = S.unit e := by
  apply S.field_ext H.toSymmetric
  intro n q x hx
  rw [hm.kernels w _ hx, S.at_unit H hx, S.at_unit H hx]
end Ext

variable {T} {n : ℕ}
private lemma swap_fix (i : Fin (n+1)) (B : S.Tag) (w : Fin (n+1) → S.Tag) :
    update w i B ∘ Equiv.swap 0 i = Fin.cons B (Fin.tail (w ∘ Equiv.swap 0 i)) := by
  funext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp [Fin.tail]
  rw [Function.update_of_ne]
  exact fun H => Fin.succ_ne_zero _ ((Equiv.swap 0 i).injective (H.trans (Equiv.swap_apply_left 0 i).symm))

theorem inclusion_slot (h : P.Inclusions T) (hp : T.Symmetric) {d e : ℕ} (H : d ≤ e) {x : Points n}
    (hx : x ∈ conf n) (i : Fin n) (w : Fin n → S.Tag) (p : S.Field d) :
    S.useAt T x (update w i ⟨e,P.rise H p⟩) = S.useAt T x (update w i ⟨d,p⟩) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    conv_lhs => rw [← Table.class_perm S T hp (Equiv.swap 0 i) hx]
    conv_rhs => rw [← Table.class_perm S T hp (Equiv.swap 0 i) hx]
    rw [swap_fix,swap_fix]; apply h.kernels H p (rearrange_in _ hx)

theorem derivative_slot (h : P.Derivatives T) (hp : T.Symmetric) (hs : T.Smooth)
    {d : ℕ} {x : Points n} (hx : x ∈ conf n) (i : Fin n) (w : Fin n → S.Tag) (p : S.Field d) (a : Axis) :
    S.useAt T x (update w i ⟨d+1,P.deriv d a p⟩) =
      gradient i a (fun y => S.useAt T y (update w i ⟨d,p⟩)) x := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let r := Equiv.swap 0 i
    rw [← Table.class_perm S T hp r hx]
    have he := h.kernels d a p (rearrange_in r hx) (Fin.tail (w ∘ r))
    change S.useAt T (rearrange r x) (update w i _ ∘ Equiv.swap 0 i) = _
    rw [swap_fix,he]
    let v := Fin.cons (α := fun _ : Fin (n+1) => S.Tag) ⟨d,p⟩ (Fin.tail (w ∘ r))
    let f := fun x : Points (n+1) => S.useAt T x v
    have hw : DifferentiableAt ℝ f (rearrange r x) :=
      ((S.class_smooth T hs v _ (rearrange_in r hx)).contDiffAt ((conf_open _).mem_nhds (rearrange_in r hx))).differentiableAt (by simp)
    change gradient 0 a f (rearrange r x) = _
    rw [← placement r 0 a f x hw, show r 0 = i from Equiv.swap_apply_left _ _]
    apply GermD
    filter_upwards [(conf_open _).mem_nhds hx] with y hy
    change S.useAt T (rearrange r y) v = _
    rw [show v = update w i (⟨d,p⟩ : S.Tag) ∘ r from (swap_fix ..).symm]
    exact Table.class_perm S T hp r hy _

theorem commute_rise (h : S.Symmetric) (hr : P.Inclusions S) (hp : P.Derivatives S)
    {d e : ℕ} (hv : d ≤ e) (A : S.Field d) (a : Axis) :
    P.rise (Nat.succ_le_succ hv) (P.deriv d a A) = P.deriv e a (P.rise hv A) := by
  apply S.field_ext h; intro n q x hx
  rw [hr.kernels (Nat.succ_le_succ hv) _ hx, hp.kernels (d := d) a A hx q,
    hp.kernels (d := e) a _ hx]
  symm
  apply GermD
  filter_upwards [(conf_open _).mem_nhds hx] with y hy
  exact hr.kernels hv A hy q

theorem abelian (h : S.Symmetric) (hp : P.Derivatives S) (hs : S.Smooth)
    {d : ℕ} (A : S.Field d) (a b : Axis) :
    P.deriv _ a (P.deriv d b A) = P.deriv _ b (P.deriv d a A) := by
  apply S.field_ext h; intro n q x hx
  have hU := (conf_open _).mem_nhds hx
  let f := fun y : Points (n+1) => S.useAt S y (Fin.cons ⟨d,A⟩ q)
  have hf : ContDiffAt ℝ ∞ f x := ((S.class_smooth S hs _ x hx).contDiffAt hU)
  have hw (b a : Axis) :
      S.useAt S x (Fin.cons ⟨_,P.deriv _ a (P.deriv d b A)⟩ q) = gradient 0 a (gradient 0 b f) x := by
    rw [hp.kernels _ _ _ hx]
    apply GermD
    filter_upwards [hU] with y hy
    exact hp.kernels d b A hy _
  rw [hw b a,hw a b]
  exact commuteD (hf.of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from
    WithTop.coe_le_coe.mpr le_top)) ..

theorem unit_drop (h : S.Basic) (hp : P.Derivatives S) (hs : S.Smooth) (d : ℕ) (a : Axis) :
    P.deriv d a (S.unit d) = 0 := by
  apply S.faithfully
  rw [map_zero]
  funext v
  rcases v with ⟨n,x,w,hx⟩
  rw [← Table.through S h.toSymmetric, hp.kernels _ _ _ hx]
  let F := fun y : Points n => S.useAt S y (S.classTokens ∘ w)
  let l : Points (n+1) →L[ℝ] Points n := LinearMap.toContinuousLinearMap { toFun := tail,
                                                                             map_add' := fun _ _ => rfl,
                                                                             map_smul' := fun _ _ => rfl }
  have he : (fun y => S.useAt S y (Fin.cons ⟨d,S.unit d⟩ (S.classTokens ∘ w))) =ᶠ[𝓝 x] F ∘ l := by
    filter_upwards [(conf_open _).mem_nhds hx] with y hy
    exact S.at_unit h hy _ d
  rw [gradient,GermD _ he, D, fderiv_comp x (show DifferentiableAt ℝ F (l x) from
    ((S.class_smooth S hs _ _ (tail_in hx)).contDiffAt ((conf_open _).mem_nhds (tail_in hx))).differentiableAt
      (by simp)) l.differentiableAt, l.fderiv,ContinuousLinearMap.comp_apply]
  rw [show l (direction 0 a)=0 by ext1 i; change direction (n := n+1) 0 a i.succ = _; simp [direction]]
  exact map_zero _
end DiffPlan
end YM
