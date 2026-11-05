import YM.Push.LOOP_COEFFICIENT.Fine.Operators

/-!
# Continuing routed products on domains with all shifts active
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Set Function Filter Matrix Lattice Laurent RG Wilson Bloch Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d E : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {S T : Set Momentum}

def Active₁ (S : Set Momentum) (q p : Momentum) := q∈S ∧ q+p∈S
def Active₂ (S : Set Momentum) (q p s : Momentum) := q∈S ∧ q+p∈S ∧ q+s∈S ∧ q+p+s∈S
structure StripLaw (R : Vertex d a b) (S T : Set Momentum) : Prop where
  base q : q∈S → ContDiffAt ℂ ω R.base q ∧ ∀ x, R.base (q+reciprocal x) = R.base q
  one q p v : Active₁ S q p → p∈T → ContDiffAt ℂ ω (fun z : Momentum × Momentum => R.one z.1 z.2 v) (q,p) ∧
    ∀ x y, R.one (q+reciprocal x) (p+reciprocal y) v = R.one q p v
  two q p s v w : Active₂ S q p s → p∈T → s∈T → ContDiffAt ℂ ω (fun z : Momentum × Momentum × Momentum => R.two z.1 z.2.1 z.2.2 v w) (q,p,s) ∧
    ∀ x y z, R.two (q+reciprocal x) (p+reciprocal y) (s+reciprocal z) v w = R.two q p s v w

namespace StripLaw
variable {R R' : Vertex d a b} {η : ℝ} {x : E}
omit [DecidableEq a] in
lemma of_lit (h : Lit R η) (hS : S ⊆ Tube η) (hT : T ⊆ Tube η) : StripLaw R S T := ⟨fun _ h' => h.base _ (hS h'),fun _ _ _ ha hb => h.one _ _ _ (hS ha.1) (hT hb),fun _ _ _ _ _ ha hb hc => h.two _ _ _ _ _ (hS ha.1) (hT hb) (hT hc)⟩
omit [DecidableEq a] in
lemma lit (h : StripLaw R (Tube η) (Tube η)) (he : 0<η) : Lit R (η/3) :=
  let hl := tube_mono (show η/3 ≤ η by linarith)
  let ha {p q : Momentum} (hp : p∈Tube (η/3)) (hq : q∈Tube (η/3)) := tube_mono (show η/3+η/3≤η by linarith) (tube_add hp hq)
  ⟨fun _ hp => h.base _ (hl hp),fun _ _ _ hq hp => h.one _ _ _ ⟨hl hq,ha hq hp⟩ (hl hp),fun _ _ _ _ _ hq hp hs => h.two _ _ _ _ _ ⟨hl hq, ha hq hp,ha hq hs,tube_mono (by linarith) (tube_add (tube_add hq hp) hs)⟩ (hl hp) (hl hs)⟩
omit [DecidableEq a] in
lemma zeroD (h : StripLaw R S T) {q : E → Momentum} (hq : ContDiffAt ℂ ω q x) (he : q x ∈ S) : ContDiffAt ℂ ω (fun z => R.base (q z)) x := (h.base _ he).1.comp x hq
omit [DecidableEq a] in
lemma oneD (h : StripLaw R S T) {q p : E → Momentum} (hq : ContDiffAt ℂ ω q x) (hp : ContDiffAt ℂ ω p x) (he : Active₁ S (q x) (p x)) (h' : p x ∈ T) (v) : ContDiffAt ℂ ω (fun z => R.one (q z) (p z) v) x := (h.one _ _ v he h').1.comp (f:=fun z => (q z,p z)) x (hq.prodMk hp)
omit [DecidableEq a] in
lemma twoD (h : StripLaw R S T) {q p s : E → Momentum} (hq : ContDiffAt ℂ ω q x) (hp : ContDiffAt ℂ ω p x) (hs : ContDiffAt ℂ ω s x) (he : Active₂ S (q x) (p x) (s x)) (h' : p x∈T) (h'' : s x∈T) (v w) : ContDiffAt ℂ ω (fun z => R.two (q z) (p z) (s z) v w) x := (h.two _ _ _ v w he h' h'').1.comp (f:=fun z => (q z,p z,s z)) x (hq.prodMk (hp.prodMk hs))

omit [DecidableEq a] in
lemma const {M : Momentum → Matrix a b ℂ} (h : ∀ q∈S, ContDiffAt ℂ ω M q ∧ ∀ x, M (q+reciprocal x) = M q) : StripLaw (Vertex.const (d:=d) M) S T := ⟨h,fun _ _ _ _ _ => ⟨contDiffAt_const,by intros; rfl⟩,fun _ _ _ _ _ _ _ _ => ⟨contDiffAt_const,by intros; rfl⟩⟩
omit [DecidableEq a] in
lemma add (h : StripLaw R S T) (h' : StripLaw R' S T) : StripLaw (R.add R') S T := ⟨fun _ hq => ⟨(h.base _ hq).1.add (h'.base _ hq).1,fun _ => congr_arg₂ (· + ·) ((h.base _ hq).2 _) ((h'.base _ hq).2 _)⟩, fun _ _ _ hq hp => ⟨((h.one _ _ _ hq hp).1.add (h'.one _ _ _ hq hp).1),fun _ _ => congr_arg₂ (· + ·) ((h.one _ _ _ hq hp).2 _ _) ((h'.one _ _ _ hq hp).2 _ _)⟩,fun _ _ _ _ _ hq hp hs => ⟨(h.two _ _ _ _ _ hq hp hs).1.add (h'.two _ _ _ _ _ hq hp hs).1,fun _ _ _ => congr_arg₂ (· + ·) ((h.two _ _ _ _ _ hq hp hs).2 ..) ((h'.two _ _ _ _ _ hq hp hs).2 ..)⟩⟩
omit [DecidableEq a] in
lemma smul (h : StripLaw R S T) (c : ℂ) : StripLaw (R.smul c) S T := ⟨fun _ hq => ⟨(h.base _ hq).1.const_smul c,fun _ => congr_arg (c • ·) ((h.base _ hq).2 _)⟩, fun _ _ _ hq hp => ⟨(h.one _ _ _ hq hp).1.const_smul c,fun _ _ => congr_arg (c • ·) ((h.one _ _ _ hq hp).2 ..)⟩,fun _ _ _ _ _ hq hp hs => ⟨(h.two _ _ _ _ _ hq hp hs).1.const_smul c,fun _ _ _ => congr_arg (c • ·) ((h.two _ _ _ _ _ hq hp hs).2 ..)⟩⟩
private lemma recv (q p : Momentum) (x y : Cover) : q+reciprocal x + (p+reciprocal y)=q+p+reciprocal (x+y) := by rw [reciprocal_add]; abel
omit [DecidableEq a] in
lemma mul {V : Vertex d b c} (h : StripLaw R S T) (h' : StripLaw V S T) : StripLaw (R.mul V) S T := by
  constructor
  · intro q hq; exact ⟨analyticMul (h.base q hq).1 (h'.base q hq).1,fun _ => congr_arg₂ (· * ·) ((h.base q hq).2 _) ((h'.base q hq).2 _)⟩
  · intro q p v hq hp; simp only [Vertex.mul,LinearMap.add_apply,LinearMap.comp_apply,matrixMulLinear,LinearMap.mk₂_apply,LinearMap.flip_apply]; exact ⟨(analyticMul (h.zeroD (q:=fun z : Momentum × Momentum => z.1+z.2) (x:=(q,p)) (by fun_prop) hq.2) (h'.one q p v hq hp).1).add (analyticMul (h.one q p v hq hp).1 (h'.zeroD (q:=Prod.fst) (x:=(q,p)) (by fun_prop) hq.1)),fun _ _ => by rw [recv,(h.base _ hq.2).2,(h'.one _ _ _ hq hp).2,(h.one _ _ _ hq hp).2,(h'.base _ hq.1).2]⟩
  intro q p s v w hq hp hs; simp only [Vertex.mul,LinearMap.add_apply,LinearMap.compr₂_apply,LinearMap.compl₁₂_apply,matrixMulLinear,LinearMap.mk₂_apply,LinearMap.flip_apply]
  let z := (q,p,s)
  have ht : Active₁ S (q+s) p := ⟨hq.2.2.1,add_right_comm q s p ▸ hq.2.2.2⟩
  have hu : Active₁ S (q+p) s := ⟨hq.2.1,hq.2.2.2⟩
  refine ⟨(((analyticMul (h.zeroD (x:=z) (q:=fun z => z.1+z.2.1+z.2.2) (by fun_prop) hq.2.2.2) (h'.two _ _ _ _ _ hq hp hs).1).add (analyticMul (h.oneD (x:=z) (q:=fun z => z.1+z.2.2) (p:= fun z => z.2.1) (by fun_prop) (by fun_prop) ht hp v) (h'.oneD (x:=z) (q:=Prod.fst) (p:=fun z => z.2.2) (by fun_prop) (by fun_prop) ⟨hq.1,hq.2.2.1⟩ hs w))).add (analyticMul (h.oneD (x:=z) (q:=fun z => z.1+z.2.1) (p:= fun z => z.2.2) (by fun_prop) (by fun_prop) hu hs w) (h'.oneD (x:=z) (q:=Prod.fst) (p:=fun z => z.2.1) (by fun_prop) (by fun_prop) ⟨hq.1,hq.2.1⟩ hp v))).add (analyticMul (h.two _ _ _ _ _ hq hp hs).1 (h'.zeroD (x:=z) (q:=Prod.fst) (by fun_prop) hq.1)),fun _ _ _ => ?_⟩
  rw [recv,recv,recv,(h.base _ hq.2.2.2).2,(h'.two _ _ _ _ _ hq hp hs).2,(h.one _ _ _ ht hp).2,(h'.one q s _ ⟨hq.1,hq.2.2.1⟩ hs).2,(h.one _ _ _ hu hs).2,(h'.one q p _ ⟨hq.1,hq.2.1⟩ hp).2,(h.two _ _ _ _ _ hq hp hs).2,(h'.base _ hq.1).2]

lemma inv {R : Vertex d a a} (h : StripLaw R S T) (hu : ∀ q∈S, IsUnit (R.base q)) : StripLaw R.inv S T := by
  have hi : StripLaw R.inc S T := ⟨fun _ _ => ⟨contDiffAt_const,by intros; rfl⟩,h.one,h.two⟩
  have hc : StripLaw (Vertex.const (d:=d) fun q => (R.base q)⁻¹) S T := StripLaw.const (fun _ hq => ⟨analyticInv (h.base _ hq).1 (hu _ hq),fun _ => by rw [(h.base _ hq).2]⟩)
  have he (U : Vertex d a a) : U.neg = U.smul (-1) := by unfold Vertex.neg Vertex.smul; congr 1 <;> (ext; simp)
  convert hc.add ((((hc.smul (-1)).mul hi).mul hc).add ((((hc.mul hi).mul hc).mul hi).mul hc)) using 1; dsimp only [Vertex.inv]; rw [he]
lemma pow {R : Vertex d a a} (h : StripLaw R S T) (k) : StripLaw (R.pow k) S T := by induction k with
                                                                               | zero => exact StripLaw.const fun _ _ => ⟨contDiffAt_const,by intros; rfl⟩
                                                                               | succ k ih => exact ih.mul h
lemma upper {R : Vertex d a a} (h : StripLaw R S T) (k) : StripLaw (R.upper k) S T := by induction k with
                                                                                     | zero => exact StripLaw.const fun _ _ => ⟨contDiffAt_const,by intros; rfl⟩
                                                                                     | succ k ih => exact ih.add (h.pow (k+1))

open Fine
lemma lift {G : Gauge} {R : GhostRoot G} (h : StripLaw R S T) : StripLaw (Fine.lift R) S T := by
  let L := (onAxis G).toContinuousLinearMap
  exact ⟨fun _ hq => ⟨L.contDiff.contDiffAt.comp _ (h.base _ hq).1,fun _ => congr_arg (onAxis G) ((h.base _ hq).2 _)⟩,
    fun q p v hq hp => ⟨L.contDiff.contDiffAt.comp (f:=fun z : Momentum × Momentum => R.one z.1 z.2 v) (q,p) (h.one q p v hq hp).1, fun _ _ => congr_arg (onAxis G) ((h.one _ _ _ hq hp).2 ..)⟩,
    fun q p s v w hq hp hs => ⟨L.contDiff.contDiffAt.comp (f:=fun z : Momentum × Momentum × Momentum => R.two z.1 z.2.1 z.2.2 v w) (q,p,s) (h.two q p s v w hq hp hs).1, fun _ _ _ => congr_arg (onAxis G) ((h.two _ _ _ _ _ hq hp hs).2 ..)⟩⟩
end StripLaw
namespace Fine
open Paths Continuum
variable {G : Gauge} {W : PathData G} {p : Clip} {S T : Set Momentum} {μ η : ℝ}



end Fine
end YM.Push.Loops
