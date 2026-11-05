import YM.RG08.Forms.PontChange
import YM.RG08.Steam.Routing

/-!
Entire nonlinear connected formal kernel propagation after quadratic extraction & conversion to
joint cell positions and ordering, including deterministic shift. These are strict event
coefficients in subsequent UV recurrences. Keep V itself out of this bound for unchanged rank:
needs the earlier all-curvature repeated Ψ estimates at pre-length powers. Typically for a bulk
vacuum use, V here is the aggregated positive-order input potential tensors (a decomposition
for powers), with Caps supplied by analytic canonical-path expansions, fine age, and
previously billed packets in higher rank/earlier degree. Post-block costs in these uses
must be paid by age powers in such consumer; no stage choices here.
-/
noncomputable section
namespace YM.RG08.Steam
open Forms Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false

variable {I J:Type}
def skip (e n a r:ℕ) := 0<r ∧ 0<a ∧ r≤a+2 ∧ (a<e ∨ (a=e ∧ n≤r))
def repeatLine (K:I→J→ℝ) (n:ℕ) : Cables n I J:=fun _=>K

/-- use t=1 on mass-one Gaussian. -/
def strict (Γ:Forms.Line I)(V:Grain I)(μ:I→J→ℝ):Grain J:= fun e n=>raft (repeatLine μ n) (cinder Γ V 1 e n)
def allG (Γ:Forms.Line I)(V:Grain I)(μ:I→J→ℝ):Grain J:= fun e n=>raft (repeatLine μ n) (V e n)+strict Γ V μ e n

lemma wagepow (n:ℕ) : Wage fun x=> x^n:=⟨1,n,by simp,fun x hx=>by simpa using (pow_nonneg (zero_le_one.trans hx) n)⟩

/-- Solve connected conditional graph bills through any fixed (positive coupling order, output
rank) pair. At arity 0 this only asserts a vacuous predicate and `strict` itself should not
be used on cover (volume divergence in the extensive scalar); statement specialized with arity
for clarity. -/
theorem paving (e n:ℕ)(_hn:0<n): ∃ P,Wage P ∧
 ∀ {I J:Type}(d:Ground I)(D:Ground J)(σ τ δ W:ℝ)(V V':Grain I)(Γ Γ':Forms.Line I)(μ μ':I→J→ℝ)(E:Cables n I J),
 Eligible V→Eligible V'→ WireCot d σ δ W Γ Γ'→ Alley d D σ τ δ W E (repeatLine μ n) (repeatLine μ' n)→0≤δ → 1≤W →
 (∀ a r,Residual e n a r→Cot d σ δ W (V a r) (V' a r))→
 Cot D τ δ (P W) (strict Γ V μ e n) (strict Γ' V' μ' e n) ∧
 (Cot d σ δ W (V e n) (V' e n) → Cot D τ δ (P W) (allG Γ V μ e n) (allG Γ' V' μ' e n)) := by
 obtain ⟨P,hP,H⟩:=postage e n
 let Q(x:ℝ):=(n+1:ℝ)*P x*x^n
 let A(x:ℝ):=(n+1:ℝ)*x*x^n
 have hQ : Wage Q:=((Wage.constant _ (by positivity)).mul hP).mul (wagepow n)
 have hA : Wage A:=((Wage.constant _ (by positivity)).mul Wage.input).mul (wagepow n)
 refine ⟨_,hA.add hQ,?_⟩
 intro I J d D σ τ δ W V V' Γ Γ' μ μ' E hV hV' hΓ hμ hd hW h
 have he:Cot D τ δ (Q W) (strict Γ V μ e n) (strict Γ' V' μ' e n):=(H d σ δ W 1 V V' Γ Γ' hV hV' hΓ hd hW (by simpa using hW) h).raft hμ hd
 exact ⟨he.mono le_rfl (le_add_of_nonneg_left (hA.nn hW)) hd,fun ht=>(ht.raft hμ hd).add he hd⟩
end YM.RG08.Steam
