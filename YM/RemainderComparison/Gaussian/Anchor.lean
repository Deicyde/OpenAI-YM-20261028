import YM.RemainderComparison.Gaussian.Warp

/-!
 # Core factor and expenditures in path geometry.
 Before Laplace value and rough comparison for actual window.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Germ
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums Pressure ConnectedActivityE6 Trace
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {f p q w r : ℝ → ℝ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {h : Bolt G L p} {B u d D c C : ℝ} {t j n : ℕ}

lemma expenseF (j : ℕ) (hp : Reserve G L p) (hw : Reserve G L w) : Reserve G L fun x=> fee j (p x) (w x) := by
  have hc := ((Reserve.const (G:=G) (L:=L) 1).add hp).add hw; have hQ:= Reserve.comp j (hc.add hc) hp
  have hh:= hw.mul (hw.mul hQ); exact ((hp.add hp).add (hh.add hh)).add (hQ.add hQ)
lemma growthC (j : ℕ) (hw : Reserve G L p) (hv : Reserve G L w) (hp : Reserve G L q) : Reserve G L fun x=> canopy j (p x) (w x) (q x) := by
  have hc := ((Reserve.mul (Reserve.const 1) ((Reserve.const 1).add hv))).mul (Reserve.const (3^j))
  exact Reserve.comp j (hc.add hc) (expenseF j hp hw)

def primary (ϕ ψ:E×Body ι→ℝ) (ρ : E→Body ι) (Q:E→Matrix ι ι ℝ) (x:ℝ×E) (z:Body ι) := Real.exp (coloring ϕ ψ ρ Q x z)
lemma anchor (ϕ ψ:E×Body ι→ℝ) (ρ:E→Body ι) (Q:E→Matrix ι ι ℝ) (x:E) (z:Body ι) : primary ϕ ψ ρ Q (0,x) z=1:= by
  unfold primary coloring; rw [kite,zero_smul,Lantern.zeroC,Real.exp_zero]

theorem inside (G:Gauge) (L:Side) (j:ℕ) (hj:1≤j) (p w r:ℝ→ℝ) (hp:Reserve G L p) (hc:Reserve G L w) (hr:Reserve G L r) :
    ∃ f : ℝ→ℝ, Reserve G L f ∧ ∀ᶠ x : ℝ in atTop,
      let Z:= Sienna.eaves G L x; let B:=Access.apron G L x
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (ι:Type) [Fintype ι] [DecidableEq ι] (ϕ ψ:E×Body ι→ℝ) (ρ:E→Body ι) (Q:E→Matrix ι ι ℝ),
        0<r x → Lantern.Golf ϕ ψ ρ Q j (w x) Z Z (p x) → Cloud (primary ϕ ψ ρ Q) (w x) B (r x) j ((j+2)*j) (f x) := by
  let f t:= canopy j (w t) (r t) (p t)+canopy j 1 (r t) (p t+1)
  have hf : Reserve G L f:= (growthC j hc hr hp).add (growthC j (Reserve.const _) hr (hp.add (Reserve.const _)))
  obtain ⟨u,hu,hU⟩:= Brush.compact (f:=Real.exp) (s:=Set.Icc (-1:ℝ) 1) (k:=j) isCompact_Icc fun i _=> Real.contDiff_exp.contDiffAt
  have he := ((expenseF j hp hc).rate).mul (Sienna.edge G L)|>.below (by rw [zero_add]; exact Sienna.vow_ok) _ zero_lt_one
  refine ⟨_,Reserve.comp j hf (Reserve.const u),?_⟩
  filter_upwards [he,Access.wide hr.rate] with x hv hx Z B E _ _ _ ι _ _ ϕ ψ ρ Q hQ hp
  have hC : B*r x ≤ Z:= by rw [abs_of_pos hQ] at hx; exact hx.1.2.2.2.le
  refine (far_closure hp hx.1.2.1.le hC hQ).exponents ?_ hU ?_
  · intro i hi z hz; have h:= (patch_test ..).1 (kite_moves hx.1.2.1.le hC hi)
    exact abs_le.mpr (ether _ hp h.2 h.1 hj (by rw [max_self]; exact (le_abs_self _).trans hv) _ hz)
  intro i hi z; unfold coloring; rw [kite, zero_smul,Lantern.zeroC,abs_zero]; norm_num
end YM.RemainderComparison.Germ
