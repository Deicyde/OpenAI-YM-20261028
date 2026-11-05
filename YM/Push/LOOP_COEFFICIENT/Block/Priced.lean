import YM.Push.LOOP_COEFFICIENT.Block.Portal
import YM.Push.LOOP_COEFFICIENT.Fine.Quanta
import YM.Push.LOOP_COEFFICIENT.Thin


/-!
# Two-sided internal weights throughout the route
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Matrix Function Filter Set Lattice Laurent RG Bloch Wilson Complex Portal
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] {η A B D e : ℝ}
variable {X X' : Vertex d a b} {P : Portal a} {Q : Portal b} {S : Portal c}

/-- Input chart Q, output chart P (inverse acting on left!). r=1 on Quanta,
so all slots are measured for unit coarse backgrounds. -/
abbrev Charge (P : Portal a) (Q : Portal b) (X : Vertex d a b) (η A : ℝ) := Quanta (weigh P Q X) (Tube η) (Tube η) 1 A

lemma neg_active₁ {q p : Momentum} (h : Active₁ (Tube η) q p) : Active₁ (Tube η) (-(q+p)) p := ⟨tube_neg h.2,by simpa [neg_add_rev] using tube_neg h.1⟩
lemma neg_active₂ {q p s : Momentum} (h : Active₂ (Tube η) q p s) : Active₂ (Tube η) (-(q+p+s)) p s :=
    ⟨tube_neg h.2.2.2,(show -(q+p+s)+p=-(q+s) by abel) ▸ tube_neg h.2.2.1, (show -(q+p+s)+s=-(q+p) by abel) ▸ tube_neg h.2.1, (show -(q+p+s)+p+s=-q by abel) ▸ tube_neg h.1⟩

namespace Charge












end Charge

/-- Summable-factor bounds on the dual trace norm at each routing. -/
structure TraceQuanta (X : Vertex d a b) (η A : ℝ) : Prop where
  nonneg : 0≤A
  base q : q∈Tube η → Thin (X.base q) A
  one q p v : Active₁ (Tube η) q p → p∈Tube η → ‖v‖≤1 → Thin (X.one q p v) A
  two q p s v w : Active₂ (Tube η) q p s → p∈Tube η → s∈Tube η → ‖v‖≤1 → ‖w‖≤1 → Thin (X.two q p s v w) A
abbrev Pay (P : Portal a) (Q : Portal b) (X : Vertex d a b) (η A : ℝ) := TraceQuanta (weigh P Q X) η A
namespace Pay









end Pay
end YM.Push.Loops.Block
