import YM.RG08.Curl.Moor
/-! # Renderable formal supplies in actual coefficient costs. Pure reference
 F at q=0 (Wilson). Combine to powers g_i^(e-r) exactly through the jets. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Virtue
open Filter MeasureTheory Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free Conductor UVExt.Paths Push.AbsoluteSums Staffer Matrix
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
open Chain Wings Summit
variable {X : Chain}{G : Gauge}{P: Panel G}{d q r:ℕ}{A B σ:ℝ}{ν:G.ColorIndex}
-- for maximal path-root or fixed slot output, it's enough to take actual Artery moment SumBudget. If a different slot root is held instead of translation origin, translation uniquely determined by this same label; length unchanged.
lemma Artefact.orders {T : Flotilla G}(h: Artefact P d σ A T)(he:0<σ)(hh:r≤d)(k:ℕ):
    let L:=Stationary.issue (T r)
    SumBudget (fun j=> (L j).magnitude * (1+(L j).length:ℝ)^k) ((σ⁻¹^k*k.factorial*Real.exp σ)*(A*inkCost G (r+1) σ)) := by
    intro L
    have hx:= (h.lanes r (by simp only [embark,mem_Ico]; omega)).pathways.1; let B:= σ⁻¹^k*k.factorial*Real.exp σ; have hb : 0 ≤ B:=by unfold B; positivity
    apply budget_mono (budget_scale hb hx) (fun j=>by unfold Atom.magnitude; positivity) fun j=> ?_
    change (L j).magnitude*_ ≤ B*(L j).budget σ; rw [Atom.budget,mul_left_comm]; exact mul_le_mul_of_nonneg_left (polynomial_cost he (by positivity) k) (by unfold Atom.magnitude; positivity)
lemma ref_score (v:G.ColorIndex)(q:ℕ)(m:Side)(r): recital (reference v q r) m=Tensor.coeff (if q=0 then WilsonQ G m else 0) r 0:= by
   -- true E Wilson
   cases q with
   | zero=> rw [if_pos rfl, (sugar_value v).2 m]; unfold reference
            match r with
            | 0=> rw [sector,recital_zero,← (sugar_value v).2 m]; ext x; rw [Tensor.coeff_apply_zero,(outright G m).1]; rfl
            | 1=> unfold sector; simp [wilsonTop,recital_zero]; rw [← (sugar_value v).2 m]; ext x; simp [Tensor.coeff,iteratedFDeriv_one_apply,(outright G m).2.1]
            | r+2=> cases r with
                    | zero=> rw [Reflect.sector_t]
                    | succ r=> rw [sector,if_neg (by omega),wilsonTop,if_pos (by omega)]
   | succ q=>
     rw [if_neg (by omega),show Tensor.coeff (0:Link G m→ℝ) r 0=0 from Tensor.coeff_zero r _]; unfold reference; match r with
     | 0=>rw [sector,recital_zero]
     | 1=> rw [sector,wilsonTop, if_neg (by omega),recital_zero]
     | j+2=> rw [sector,if_neg (by omega),wilsonTop, if_neg (by omega),recital_zero]

theorem reformed {P:Panel G}{T:Flotilla G}(h:Artefact (P-reference ν q) d σ B T) (hp:0<σ)
    (hp':∀ i≤ d+2,Summable (P i))(hr:∀ i≤ d+2,Summable (reference ν q i)): ∀ m j, j≤d+2 → let F:Link G m→ℝ:= if q=0 then WilsonQ G m else 0; Tensor.coeff (F+shores T (embark 0 (d+1)) m) j 0= recital (P j) m := by
    intro m j hj F; have hx:= (portside h.lanes hp m|>.analytic)
    rw [Tensor.coeff_add _ (hx.contDiffAt.of_le le_top),← show recital (reference ν q j) m= _ from ref_score ν q m j,h.value _ _ hj, Pi.sub_apply, recital_sub (hp' _ hj) (hr _ hj)]; abel
    unfold F; split; exact Wilson_witness.analytic.contDiffAt.of_le le_top; exact contDiffAt_const
end YM.RG08.Virtue
