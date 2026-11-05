import YM.Push.LOOP_COEFFICIENT.Vertex

/-!
# Analytic vertex domains at fixed stage and their shift calculus

Unweighted periodic cell conventions. No assertion here that rates survive
iteration. Losses apply on a finite number of row operations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Bloch Lattice Laurent
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator

abbrev Tube (η : ℝ) := Laurent.strip (α:=Axis) η
lemma tube_mono {η σ : ℝ} (h : η ≤ σ) : Tube η ⊆ Tube σ := fun _ ha i => (ha i).trans_le h
lemma tube_neg {p : Momentum} {η} (h : p ∈ Tube η) : -p ∈ Tube η := by intro i; simpa using h i
lemma tube_add {p q : Momentum} {η σ} (h : p ∈ Tube η) (h' : q ∈ Tube σ) : p+q∈Tube (η+σ) := fun i =>
  (abs_add_le ..).trans_lt (add_lt_add (h i) (h' i))
lemma tube_reciprocal {p : Momentum} {η} (h : p∈Tube η) (x : Cover) : p+reciprocal x∈Tube η := by intro i; simpa [reciprocal] using h i
lemma reciprocal_add (x y : Cover) : reciprocal (x+y) = reciprocal x + reciprocal y := by ext1 i; simp [reciprocal,mul_add]
lemma reciprocal_neg (x : Cover) : reciprocal (-x) = -reciprocal x := by ext1 i; simp [reciprocal]
@[simp] lemma reciprocal_zero : Laurent.reciprocal (0:Cover) = 0 := by ext1; simp [reciprocal]

variable {X a b c d : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  {V W : Vertex d a b} {η σ : ℝ} {x : X}

-- periodicity only required on the respective strips
structure Lit (V : Vertex d a b) (η : ℝ) : Prop where
  base q : q∈Tube η → ContDiffAt ℂ ω V.base q ∧ ∀ x : Cover, V.base (q+reciprocal x) = V.base q
  one q p v : q∈Tube η → p∈ Tube η → ContDiffAt ℂ ω (fun z : Momentum × Momentum => V.one z.1 z.2 v) (q,p) ∧
    ∀ x y : Cover, V.one (q+reciprocal x) (p+reciprocal y) v = V.one q p v
  two q p p' v w : q∈Tube η → p∈ Tube η → p'∈Tube η → ContDiffAt ℂ ω (fun z : Momentum × Momentum × Momentum => V.two z.1 z.2.1 z.2.2 v w) (q,p,p') ∧
    ∀ x y z : Cover, V.two (q+reciprocal x) (p+reciprocal y) (p'+reciprocal z) v w = V.two q p p' v w

omit [DecidableEq a] in
lemma analyticMatrix {f : X → Matrix a b ℂ} (hf : ∀ i j, ContDiffAt ℂ ω (fun x => f x i j) x) : ContDiffAt ℂ ω f x :=
  (Matrix.ofLinearEquiv ℂ (α:=ℂ) (m:=a) (n:=b)).toContinuousLinearEquiv.contDiff.contDiffAt.comp (f:=fun x : X => fun i j => f x i j) x (contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr (hf i))

omit [DecidableEq a] in
lemma analyticComponent {f : X → Matrix a b ℂ} (hf : ContDiffAt ℂ ω f x) (i j) : ContDiffAt ℂ ω (fun x => f x i j) x :=
  contDiffAt_pi.mp (contDiffAt_pi.mp (show ContDiffAt ℂ ω (fun x i j => f x i j) x from (Matrix.ofLinearEquiv ℂ (m:=a) (n:=b) (α:=ℂ)).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x hf) i) j

omit [DecidableEq a] in
lemma analyticMul {f : X → Matrix a b ℂ} {g : X → Matrix b c ℂ} (hf : ContDiffAt ℂ ω f x) (hg : ContDiffAt ℂ ω g x) :
    ContDiffAt ℂ ω (fun y => f y * g y) x := analyticMatrix (fun i j => ContDiffAt.sum (fun k _ => (analyticComponent hf i k).mul (analyticComponent hg k j)))

lemma analyticTranspose {f : X → Matrix a b ℂ} (hf : ContDiffAt ℂ ω f x) : ContDiffAt ℂ ω (fun y => (f y).transpose) x := analyticMatrix fun i j => analyticComponent hf j i

lemma analyticInv {f : X → Matrix a a ℂ} (hf : ContDiffAt ℂ ω f x) (h : IsUnit (f x)) : ContDiffAt ℂ ω (fun y => (f y)⁻¹) x := by
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  exact (contDiffAt_ringInverse ℂ h.unit).comp (f:=f) x hf

lemma analyticTrace {f : X → Matrix a a ℂ} (hf : ContDiffAt ℂ ω f x) : ContDiffAt ℂ ω (fun y => (f y).trace) x :=
  ContDiffAt.sum fun i _ => analyticComponent hf i i

namespace Lit
omit [DecidableEq a] in
lemma mono (h : Lit V η) (hs : σ≤η) : Lit V σ :=
  ⟨fun _ ha => h.base _ (tube_mono hs ha), fun _ _ _ ha hb => h.one _ _ _ (tube_mono hs ha) (tube_mono hs hb),
    fun _ _ _ _ _ ha hb hc => h.two _ _ _ _ _ (tube_mono hs ha) (tube_mono hs hb) (tube_mono hs hc)⟩
omit [DecidableEq a] in
lemma const {f : Momentum → Matrix a b ℂ} (h : ∀ q∈ Tube η, ContDiffAt ℂ ω f q ∧ ∀ z : Cover,f (q+reciprocal z) = f q) : Lit (Vertex.const (d:=d) f) η :=
  ⟨h,fun _ _ _ _ _ => ⟨contDiffAt_const,by intros; rfl⟩,fun _ _ _ _ _ _ _ _ => ⟨contDiffAt_const,by intros; rfl⟩⟩
omit [DecidableEq a] in
lemma inc (h : Lit V η) : Lit V.inc η := ⟨fun _ _ => ⟨contDiffAt_const,by intros; rfl⟩, h.one,h.two⟩
omit [DecidableEq a] in
lemma firstOrder (h : Lit V η) : Lit V.firstOrder η := ⟨fun _ _ => ⟨contDiffAt_const,by intros; rfl⟩, h.one,fun _ _ _ _ _ _ _ _ => ⟨contDiffAt_const,by intros; rfl⟩⟩

omit [DecidableEq a] in
lemma add (h : Lit V η) (h' : Lit W η) : Lit (V.add W) η :=
  ⟨fun _ ha => ⟨(h.base _ ha).1.add (h'.base _ ha).1,fun _ => congr_arg₂ (· + ·) ((h.base _ ha).2 _) ((h'.base _ ha).2 _)⟩,
    fun _ _ _ ha hb => ⟨(h.one _ _ _ ha hb).1.add (h'.one _ _ _ ha hb).1, fun _ _ => congr_arg₂ (· + ·) ((h.one _ _ _ ha hb).2 _ _) ((h'.one _ _ _ ha hb).2 _ _)⟩,
    fun _ _ _ _ _ ha hb hc => ⟨(h.two _ _ _ _ _ ha hb hc).1.add (h'.two _ _ _ _ _ ha hb hc).1,fun _ _ _ => congr_arg₂ (· + ·) ((h.two _ _ _ _ _ ha hb hc).2 _ _ _) ((h'.two _ _ _ _ _ ha hb hc).2 _ _ _)⟩⟩
omit [DecidableEq a] in
lemma neg (h : Lit V η) : Lit V.neg η := ⟨fun _ ha => ⟨(h.base _ ha).1.neg, fun _ => congr_arg (-·) ((h.base _ ha).2 _)⟩,
    fun _ _ _ ha hb => ⟨(h.one _ _ _ ha hb).1.neg,fun _ _ => congr_arg (-·) ((h.one _ _ _ ha hb).2 _ _)⟩,
    fun _ _ _ _ _ ha hb hc => ⟨(h.two _ _ _ _ _ ha hb hc).1.neg,fun _ _ _ => congr_arg (-·) ((h.two _ _ _ _ _ ha hb hc).2 _ _ _)⟩⟩

-- Helpers to avoid reasoning about operator norms under analytic substitutions.
omit [DecidableEq a] in
lemma zeroD (h : Lit V η) {q : X → Momentum} (hq : ContDiffAt ℂ ω q x) (ht : q x ∈ Tube η) : ContDiffAt ℂ ω (fun x => V.base (q x)) x :=
  (h.base _ ht).1.comp x hq
omit [DecidableEq a] in
lemma oneD (h : Lit V η) {q p : X → Momentum} (hq : ContDiffAt ℂ ω q x) (hp : ContDiffAt ℂ ω p x)
    (ht : q x∈ Tube η) (hu : p x ∈ Tube η) (v) : ContDiffAt ℂ ω (fun x => V.one (q x) (p x) v) x :=
  (h.one _ _ v ht hu).1.comp (f:=fun x => (q x,p x)) x (hq.prodMk hp)
omit [DecidableEq a] in
lemma twoD (h : Lit V η) {q p s : X → Momentum} (hq : ContDiffAt ℂ ω q x) (hp : ContDiffAt ℂ ω p x) (hs : ContDiffAt ℂ ω s x)
    (ht : q x∈ Tube η) (hu : p x ∈ Tube η) (hv : s x∈Tube η) (v w) : ContDiffAt ℂ ω (fun x => V.two (q x) (p x) (s x) v w) x :=
  (h.two _ _ _ _ _ ht hu hv).1.comp (f:=fun x => (q x,p x,s x)) x (hq.prodMk (hp.prodMk hs))

private lemma sums {p q : Momentum} (h : p∈Tube (η/3)) (h' : q∈Tube (η/3)) : p+q∈Tube (η/3+η/3) := tube_add h h'
private lemma sums' (hp : 0 < η) {p q : Momentum} (h : p∈Tube (η/3)) (h' : q∈Tube (η/3)) : p+q∈Tube η := tube_mono (by linarith) (sums h h')
private lemma sums₃ {p q s : Momentum} (h : p∈Tube (η/3)) (h' : q∈Tube (η/3)) (h₃ : s∈Tube (η/3)) : p+q+s∈Tube η := tube_mono (by linarith) (tube_add (sums h h') h₃)
private lemma recv (x y : Cover) (p q : Momentum) : p+reciprocal x + (q + reciprocal y) = p+q+reciprocal (x+y) := by rw [reciprocal_add]; abel


omit [DecidableEq a] in
lemma mul {W : Vertex d b c} (h : Lit V η) (h' : Lit W η) (hη : 0 < η) : Lit (V.mul W) (η/3) := by
  have hl := tube_mono (show η/3 ≤ η by linarith)
  constructor
  · intro q hq
    exact ⟨analyticMul (h.base _ (hl hq)).1 (h'.base _ (hl hq)).1,fun x => congr_arg₂ (· * ·) ((h.base _ (hl hq)).2 x) ((h'.base _ (hl hq)).2 x)⟩
  · intro q p v hq hp
    simp only [Vertex.mul,LinearMap.add_apply,LinearMap.comp_apply, matrixMulLinear, LinearMap.mk₂_apply,LinearMap.flip_apply]
    refine ⟨(analyticMul (h.zeroD (x:=(q,p)) (q:=fun x => x.1 + x.2) (contDiffAt_fst.add contDiffAt_snd) (sums' hη hq hp))
      ((h'.one q p v (hl hq) (hl hp)).1)).add (analyticMul (h.one q p v (hl hq) (hl hp)).1 (h'.zeroD (q:=Prod.fst) (x:=(q,p)) contDiffAt_fst (hl hq))),?_⟩
    intro x y; rw [recv,(h.base _ (sums' hη hq hp)).2, (h'.one _ _ _ (hl hq) (hl hp)).2,(h.one _ _ _ (hl hq) (hl hp)).2,(h'.base _ (hl hq)).2]
  intro q p r v w hq hp hr
  simp only [Vertex.mul, LinearMap.add_apply,LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, matrixMulLinear,LinearMap.mk₂_apply,LinearMap.flip_apply]
  have ha := sums₃ hq hp hr; have hb := sums' hη hq hr; have hc := sums' hη hq hp
  refine ⟨(((analyticMul (h.zeroD (q:=fun x : Momentum × Momentum × Momentum => x.1+x.2.1+x.2.2) (x:=(q,p,r)) (by fun_prop) ha)
      (h'.two q p r v w (hl hq) (hl hp) (hl hr)).1).add (analyticMul
        (h.oneD (x:=(q,p,r)) (q:=fun x => x.1+x.2.2) (p:=fun x => x.2.1) (by fun_prop) (by fun_prop) hb (hl hp) v) (h'.oneD (x:=(q,p,r)) (p:=fun x => x.2.2) contDiffAt_fst contDiffAt_snd.snd (hl hq) (hl hr) w))).add
        (analyticMul (h.oneD (x:=(q,p,r)) (q:=fun x => x.1+x.2.1) (p:=fun x => x.2.2) (by fun_prop) (by fun_prop) hc (hl hr) w) (h'.oneD (x:=(q,p,r)) (p:=fun x => x.2.1) contDiffAt_fst contDiffAt_snd.fst (hl hq) (hl hp) v))).add
        (analyticMul (h.two q p r v w (hl hq) (hl hp) (hl hr)).1 (h'.zeroD (q:=Prod.fst) (x:=(q,p,r)) contDiffAt_fst (hl hq))),?_⟩
  intro x y z; rw [recv,recv,recv,(h.base _ ha).2, (h'.two _ _ _ _ _ (hl hq) (hl hp) (hl hr)).2,
    (h.one _ _ _ hb (hl hp)).2,(h'.one _ _ _ (hl hq) (hl hr)).2, (h.one _ _ _ hc (hl hr)).2,(h'.one _ _ _ (hl hq) (hl hp)).2,
    (h.two _ _ _ _ _ (hl hq) (hl hp) (hl hr)).2,(h'.base _ (hl hq)).2]




end Lit
end YM.Push.Loops
