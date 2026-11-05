import YM.Push.LOOP_COEFFICIENT.Envelope
import YM.Push.LOOP_COEFFICIENT.Fine.Inverses
import YM.Push.LOOP_COEFFICIENT.Fine.Proxy
import YM.Push.LOOP_COEFFICIENT.Fine.Sprout
import YM.Push.LOOP_COEFFICIENT.PeriodStep

/-!
# Inverse fibers on fine discs and inherited coarse width
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Fine
open Function Filter Set Matrix Complex Metric Lattice Laurent Bloch RG Exterior Precision Wilson Bid Paths Continuum Kernel
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator
variable {G : Gauge} {H : Precision.Bed} {r η μ b A C u v σ Λ : ℝ} {z : Momentum} {p : Clip} {W : PathData G}

structure Holds (G : Gauge) (H : Bed) (r b : ℝ) : Prop where
  width : 0<r
  lower : 0<b
  spectrum {k z μ} : Windowed k → 0<μ → μ≤1 → z∈ball k (r*ruler μ k) → Gap (proxy G H μ z) (b * ruler μ k ^2) ∧ Gap ((gauged G μ).base z) (b * ruler μ k ^2)



def shade (z : Momentum) : Momentum := fun i => ((z i).re:ℂ)
lemma shade_dist (hη : 0<η) (hz : z∈Tube η) : dist z (shade z) < η := by
  rw [dist_eq_norm,pi_norm_lt_iff hη]; intro i
  rw [Pi.sub_apply,show z i - shade z i = (z i).im * I from sub_eq_of_eq_add' (re_add_im _).symm,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs]; exact hz i
lemma center_window (hz : z∈Center η) : Windowed (shade z) := ⟨by ext; simp [shade], fun i => by simpa [shade] using hz.2 i⟩
lemma long_period (G : Gauge) (z : Momentum) (t : Cover) : longitudinal G (z+reciprocal t) = longitudinal G z := Matrix.ext fun i j => show (root G).base _ i j = (root G).base _ i j by simp only [root_base_entry,freq_period]
lemma gauged_period (G : Gauge) (μ : ℝ) (z : Momentum) (t : Cover) : (gauged G μ).base (z+reciprocal t) = (gauged G μ).base z := by simp only [gauged,ghostFree,Vertex.mul,Vertex.transpose,Vertex.add,Vertex.smul,Vertex.const,Vertex.id,root,Pi.add_apply,Pi.smul_apply,long_period, neg_add,← reciprocal_neg]
lemma proxy_period (G : Gauge) (H : Bed) (μ : ℝ) (z : Momentum) (t : Cover) : proxy G H μ (z+reciprocal t) = proxy G H μ z := by simp only [proxy,kineticSymbol,Vertex.mul,Vertex.transpose,root,Row.periods,neg_add,← reciprocal_neg,symbol_period,long_period,surfeit_base,factor_base,gauged_period,massive_base]



end YM.Push.Loops.Fine
