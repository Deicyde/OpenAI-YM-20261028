import YM.Push.LOOP_COEFFICIENT.Fine.Domain
import YM.Push.LOOP_COEFFICIENT.Paths.Strip

/-!
# Scaled envelopes for routed vertices in fixed or shrinking domains
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Set Filter Function Matrix Lattice Laurent RG Bloch Complex
open scoped Topology Matrix.Norms.L2Operator BigOperators
variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [DecidableEq a] [DecidableEq b] [DecidableEq c] {S T : Set Momentum} {r A B e : ℝ}

structure Quanta (X : Vertex d a b) (S T : Set Momentum) (r A : ℝ) : Prop where
  nonneg : 0≤A
  base q : q∈S → ‖X.base q‖ ≤ A
  one q p v : Active₁ S q p → p∈T → ‖v‖ ≤ 1 → ‖X.one q p v‖ ≤ A/r
  two q p s v w : Active₂ S q p s → p∈T → s∈T → ‖v‖≤1 → ‖w‖≤1 → ‖X.two q p s v w‖ ≤ A/r^2
namespace Quanta
variable {X Y : Vertex d a b}
omit [DecidableEq a] in
lemma mono (h : Quanta X S T r A) (hA : A≤B) (hr : 0≤r) : Quanta X S T r B := ⟨h.nonneg.trans hA,fun q hq => (h.base q hq).trans hA,fun _ _ _ hq hp hv => (h.one _ _ _ hq hp hv).trans (by gcongr),fun _ _ _ _ _ hq hp hs hv hw => (h.two _ _ _ _ _ hq hp hs hv hw).trans (by gcongr)⟩
omit [DecidableEq a] in
lemma add (hx : Quanta X S T r A) (hy : Quanta Y S T r B) : Quanta (X.add Y) S T r (A+B) := ⟨add_nonneg hx.nonneg hy.nonneg,fun _ hq => (norm_add_le ..).trans (add_le_add (hx.base _ hq) (hy.base _ hq)),fun _ _ _ hq hp hv => (norm_add_le ..).trans ((add_le_add (hx.one _ _ _ hq hp hv) (hy.one _ _ _ hq hp hv)).trans_eq (add_div ..).symm),fun _ _ _ _ _ hq hp hs hv hw => (norm_add_le ..).trans ((add_le_add (hx.two _ _ _ _ _ hq hp hs hv hw) (hy.two _ _ _ _ _ hq hp hs hv hw)).trans_eq (add_div ..).symm)⟩
omit [DecidableEq a] in
lemma smul (hx : Quanta X S T r A) (z : ℂ) : Quanta (X.smul z) S T r (‖z‖*A) := by
  have he {C} {M : Matrix a b ℂ} (h : ‖M‖≤C) := norm_smul z M |>.trans_le (mul_le_mul_of_nonneg_left h (norm_nonneg _))
  exact ⟨mul_nonneg (norm_nonneg _) hx.nonneg,fun _ hq => he (hx.base _ hq),fun _ _ _ hq hp hv => (he (hx.one _ _ _ hq hp hv)).trans_eq (mul_div_assoc ..).symm,fun _ _ _ _ _ hq hp hs hv hw => (he (hx.two _ _ _ _ _ hq hp hs hv hw)).trans_eq (mul_div_assoc ..).symm⟩
omit [DecidableEq a] in
lemma mul {Y : Vertex d b c} (hx : Quanta X S T r A) (hy : Quanta Y S T r B) (hr : 0<r) : Quanta (X.mul Y) S T r (4*A*B) := by
  have h1 := hx.nonneg; have h2 := hy.nonneg
  refine ⟨by positivity,fun _ hq => (op_cost (hx.base _ hq) (hy.base _ hq)).trans (by gcongr; linarith),fun q p v hq hp hv => ?_, fun q p s v w hq hp hs hv hw => ?_⟩
  · exact (norm_add_le ..).trans ((add_le_add (op_cost (hx.base _ hq.2) (hy.one _ _ _ hq hp hv)) (op_cost (hx.one _ _ _ hq hp hv) (hy.base _ hq.1))).trans (by field_simp; nlinarith))
  have h3 := op_cost (hx.base _ hq.2.2.2) (hy.two _ _ _ _ _ hq hp hs hv hw)
  have h4 := op_cost (hx.one (q+s) p v ⟨hq.2.2.1,add_right_comm q s p ▸ hq.2.2.2⟩ hp hv) (hy.one q s w ⟨hq.1,hq.2.2.1⟩ hs hw)
  have h5 := op_cost (hx.one (q+p) s w ⟨hq.2.1,hq.2.2.2⟩ hs hw) (hy.one q p v ⟨hq.1,hq.2.1⟩ hp hv)
  have h6 := op_cost (hx.two _ _ _ _ _ hq hp hs hv hw) (hy.base _ hq.1)
  exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add h3 h4)) h5)) h6).trans_eq (by field_simp; ring))
omit [DecidableEq a] in
lemma const {M : Momentum → Matrix a b ℂ} (hr : 0<r) (hA : 0≤A) (h : ∀ q∈S, ‖M q‖ ≤ A) : Quanta (Vertex.const (d:=d) M) S T r A := ⟨hA,h,fun _ _ _ _ _ _ => by simp [Vertex.const]; positivity,fun _ _ _ _ _ _ _ _ _ _ => by simp [Vertex.const]; positivity⟩
omit [DecidableEq a] in
lemma inc (h : Quanta X S T r A) : Quanta X.inc S T r A := ⟨h.nonneg,fun _ _ => by simpa [Vertex.inc] using h.nonneg,h.one,h.two⟩






open Fine
lemma lift (G : Gauge) : ∃ K>0,∀ {V : GhostRoot G} {S T r A}, Quanta V S T r A → Quanta (lift V) S T r (K*A) := by
  let L := (onAxis G).toContinuousLinearMap
  refine ⟨max 1 ‖L‖,one_pos.trans_le (le_max_left ..),fun {V S T r A} h => ?_⟩
  have he {B} {x : Matrix G.ColorIndex G.ColorIndex ℂ} (hb : ‖x‖ ≤ B) := (show ‖L x‖ ≤ max 1 ‖L‖ * B from L.le_opNorm x |>.trans (mul_le_mul (le_max_right ..) hb (norm_nonneg x) (by positivity)))
  have ha := h.nonneg; exact ⟨by positivity,fun _ hq => he (h.base _ hq),fun _ _ _ hq hp hv => (he (h.one _ _ _ hq hp hv)).trans_eq (by rw [mul_div_assoc]),fun _ _ _ _ _ hq hp hs hv hw => (he (h.two _ _ _ _ _ hq hp hs hv hw)).trans_eq (by rw [mul_div_assoc])⟩

omit [DecidableEq a] in
lemma of_packet (h : Packet X e A) (hS : S ⊆ Tube e) (hT : T ⊆ Tube e) : Quanta X S T 1 A := ⟨h.nonneg,fun _ hq => h.zeroBound _ (hS hq),fun _ _ _ hq hp hv => by simpa using h.oneBound _ _ _ (hS hq.1) (hT hp) hv,fun _ _ _ _ _ hq hp hs hv hw => by simpa using h.twoBound _ _ _ _ _ (hS hq.1) (hT hp) (hT hs) hv hw⟩
omit [DecidableEq a] in
lemma packet (he : 0<e) (h : StripLaw X (Tube e) (Tube e)) (hx : Quanta X (Tube e) (Tube e) 1 A) : Packet X (e/3) A := by
  have hl := tube_mono (show e/3≤e by linarith)
  have ha {q p} (hq : q∈Tube (e/3)) (hp : p∈Tube (e/3)) := tube_mono (show e/3+e/3≤e by linarith) (tube_add hq hp)
  exact ⟨h.lit he,by positivity,hx.nonneg,fun _ hq => hx.base _ (hl hq),fun _ _ _ hq hp hv => (hx.one _ _ _ ⟨hl hq,ha hq hp⟩ (hl hp) hv).trans_eq (by simp),fun _ _ _ _ _ hq hp hs hv hw => (hx.two _ _ _ _ _ ⟨hl hq,ha hq hp,ha hq hs,tube_mono (by linarith) (tube_add (tube_add hq hp) hs)⟩ (hl hp) (hl hs) hv hw).trans_eq (by simp)⟩
end Quanta
end YM.Push.Loops
