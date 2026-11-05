import YM.Push.LOOP_COEFFICIENT.Block.Service

/-!
# Ordinary chart receipts and the drift response amplifier
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Function Matrix Filter Set Lattice Laurent RG Bloch Complex Portal Fine
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a d : Type} [Fintype a] [DecidableEq a] [Fintype d] {η A B D δ C e : ℝ}
variable {X Y Z : Vertex d a a}
structure Yard (X : Vertex d a a) (η C : ℝ) : Prop where
  grows : Grows X η
  charge : Quanta X (Tube η) (Tube η) 1 C
  unit q : q∈Tube η → IsUnit (X.base q)
  invert q : q∈Tube η → ‖(X.base q)⁻¹‖≤C

namespace Yard






end Yard
private lemma recv (q p : Momentum) (x y : Cover) : q+reciprocal x + (p+reciprocal y)=q+p+reciprocal (x+y) := by rw [reciprocal_add]; abel
omit [Fintype d] in
lemma amplify_grows (h : Grows X η) (h' : Grows Y η) : Grows (X.amplify Y) η := by
  simp only [Vertex.amplify]
  refine ⟨fun _ _ => ⟨contDiffAt_const,fun _ => rfl⟩, fun q p v hq hp => ⟨analyticMul (h.zeroD (x:=(q,p)) (q:=fun z => z.1+z.2) (by fun_prop) hq.2) (h'.one _ _ v hq hp).1,fun _ _ => congr_arg₂ (· * ·) ?_ ((h'.one _ _ v hq hp).2 ..)⟩, fun q p s v w hq hp hs => ?_⟩
  · rw [recv,(h.base _ hq.2).2]
  let x := (q,p,s)
  have ht : Active₁ (Tube η) q p := ⟨hq.1,hq.2.1⟩; have hu : Active₁ (Tube η) (q+p) s := ⟨hq.2.1,hq.2.2.2⟩
  exact ⟨(analyticMul (h.zeroD (q:=fun z => z.1+z.2.1+z.2.2) (x:=x) (by fun_prop) hq.2.2.2) (h'.two q p s v w hq hp hs).1).add (analyticMul (h.oneD (q:=fun z => z.1+z.2.1) (p:=fun z => z.2.2) (x:=x) (by fun_prop) (by fun_prop) hu hs w) (h'.oneD (q:=Prod.fst) (p:=fun z => z.2.1) (x:=x) (by fun_prop) (by fun_prop) ht hp v)),fun _ _ _ => congr_arg₂ (· + ·) (congr_arg₂ (· * ·) (by rw [recv,recv,(h.base _ hq.2.2.2).2]) ((h'.two _ _ _ _ _ hq hp hs).2 ..)) (congr_arg₂ (· * ·) (by rw [recv,(h.one _ _ _ hu hs).2]) ((h'.one _ _ _ ht hp).2 ..))⟩

end YM.Push.Loops.Block
