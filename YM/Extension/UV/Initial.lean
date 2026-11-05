import YM.Extension.UV.NativeBed
import YM.Extension.UV.ActualLimit
import YM.Extension.UV.Build
import YM.Extension.UV.Bare

/-! Actual partial extension: keeps the shared construction, true-program nearby feasibility,
finite-law analyticity separately in bare coupling for frozen insertions, not a bound comparing
cutoffs. The UV and uniform analytic tuning criteria require more.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extension.UV
open PhysicalNext.Repeat.Legato Extraction Function Filter Topology Set Wilson
variable {G : Gauge}

structure Partial (X : UVBuild G) : Prop where
  shared : X.Shared
  coupling_budgets : Secure X
  final : ∃ f:Extraction.Order, ∃ S:Table X.C.book, Nonempty (YM.Spec.Final X.C f S)
  native_symbol (m : ℕ) : ∃ σ C, 0<σ ∧ 0<C ∧ ∃ V, (∀ a b x, ‖V a b x‖ ≤ C*Linear.weight (-σ) x) ∧ ∀ τ:ℝ, τ<σ → Linear.Weighted (Linear.Kseries X.prices.B.M m) τ V
  leading_symbol (m p : ℕ) : ∃ k, Tendsto (fun n=>Linear.Kactual X.prices.B.M n m p) atTop (nhds k)
  used : neighboring X.tower X.tower.a.clock.bar X.C.path
  nearby (b:ℝ) : NearTarget X.tower.a b → ∃ H : RG.History G, neighboring X.tower b H ∧ SelectedAt b H
  finite_correlations N p : ∃ r>0, ∀ k : ℕ, ∀ d : Fin k→ℕ, ∀ x:(i:Fin k)→X.C.label (d i),∀ o:Fin k→Lattice.Site (X.C.side N p),let f (U:Wilson.Config G (X.C.side N p)):= ∏ i, X.C.O N p (x i) (o i) U; AnalyticOnNhd ℂ (Bare.expectation f) (Metric.ball (X.C.beta N p:ℂ) r) ∧ (∀ s:ℝ, Bare.expectation f (s:ℂ)=moment s f) ∧ Bare.expectation f (X.C.beta N p)=X.C.omega N p f

theorem start_and_feasibility (g:G.Simple) (b:ℝ) (hb:0<b) : ∃ X:UVBuild G, X.prices.B.a.clock.kernel.penalty=b ∧ Partial X:= by
   obtain ⟨X,hx,hX,hy,hz⟩:=uv_delivery_secure g hb
   rw [← hx] at hy
   exact ⟨X,hx,hX,hz,X.final_at g hX,Linear.nativeK _ X.prices.B.plan hy,Linear.K_tendsto _ X.prices.B.plan hy,X.current.1,X.histories g,Bare.physical X.C⟩
end YM.Extension.UV
