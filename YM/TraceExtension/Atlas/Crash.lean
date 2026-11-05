import YM.TraceExtension.Atlas.Move
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pilot
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Over Terrace StressFlux TraceExtension MergeProof.East Next.Rank
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge}{C:Family G}{X:Extraction.Order}{S:Table C.book}(F:Final C X S){H:(Bel C.book).Hierarchy}(h:G.Simple){𝓛:Ultrafilter (ℕ×ℕ)}{Z:Arch C} (hq:Bliss F 𝓛 Z H)
local notation "F₀"=> Bel C.book
lemma parity (h:G.Simple)(F:Labels.Frame G 4)(x): F.scaled (-1) x=x:=by
    funext j;rw [Labels.Frame.scaled_apply]; by_cases hx:j=0
    · subst j; simp [F.zero_degree]
    rw [(nbase F (by decide) _ hx h).2.2]; norm_num

/-- Formal coefficient through first invariant coupling degree. X convention:
 work over g² on this parity sector, truncate modulo next degree (g⁴).
 Odd entries shown in readouts when interpreted as g coefficients. -/
abbrev Jet := Fin 2→ ℝ

def Jet.toSigned (x : Jet) : Fin 4→ℝ:= ![x 0,0,x 1,0]
def Jet.atSq (x:Jet)(g:ℝ):= x 0+g^2*x 1
lemma Jet.oddless (x:Jet)(t:ℝ): Jet.atSq x (-t)=Jet.atSq x t:=by unfold Jet.atSq;ring
lemma Jet.sample (x:Jet)(t:ℝ): ∑ k:Fin 4,(Jet.toSigned x k)*t^(k.val:ℕ)=Jet.atSq x t:=by simp [Fin.sum_univ_four, Jet.toSigned,Jet.atSq];ring
/-- Coupled verification of graded leading coefficients *asymptotically through
 that degree*. In particular we can calculate these without going via a statement
 about all-order existence or differentiating a pointwise asymptotic. This is an
 even formal jet at this accuracy; `Through` is verification to that order in the
 ring variable g², not a real bound by or asymptotics through the next *even* power.
 Sign reversal t→−t on these tests leaves charges exactly fixed. -/
def Through (g f:ℝ→ℝ)(J:Jet):= Tendsto (fun i=> (f i-J 0)/g i^2) trail (𝓝 (J 1))

-- matched results for EVERY permitted normalization of coupling at relevant order (canonical via `wilson`). No triangular change to the coefficient. No assertion that calibration by the three photon-stencil triangle matches beyond investigated cuts.
theorem odd_limit {P:ℝ→change S 4} (d:ℝ→ℝ)(hx:TendC F P d)(g:ℝ→ℝ)(hy:Coupling G g): ∃ j:Jet, Through g d j ∧ (4:ℝ) • Jet.toSigned j= ![0,0,-2*b0 G,0]:=by
    let J:Jet:=![0,-b0 G/2]; refine ⟨J,?_,?_⟩
    · unfold Through; rw [show J 0=0 from rfl,show J 1= -b0 G/2 from rfl]; simp only[sub_zero]; exact hx.measures g hy
    ext1 i; fin_cases i<;> first | rfl | (simp[J,Jet.toSigned] <;> ring)

include h in
lemma through_unique (d:ℝ→ℝ)(g:ℝ→ℝ)(h₁:Coupling G g)(i j:Jet)(ht:Through g d i)(he:Through g d j): i=j:=by
    have hv:=h₁.conforms h; have hp:=hv.pow (2:ℕ); have hh: Tendsto (fun x:ℝ=>g x^2) trail (𝓝 0):=by simpa using! hp
    have hs(j)(hp:Through g d j):Tendsto d trail (𝓝 (j 0)):=by
       have hx:= ((show Tendsto (fun x=> (d x-j 0)/g x^2) trail (𝓝 (j 1)) from hp).mul hh).add_const (j 0); rw[mul_zero,zero_add] at hx; apply hx.congr'; filter_upwards[h₁.positive] with s hs; rw[div_mul_cancel₀ _ (by positivity),sub_add_cancel]
    have hx:i 0=j 0:= tendsto_nhds_unique (hs _ ht) (hs _ he); have hz:i 1=j 1:=by unfold Through at ht he; rw[hx] at ht; exact tendsto_nhds_unique ht he
    exact funext (Fin.forall_fin_two.mpr ⟨hx,hz⟩)

-- Invariance of these even coefficients under real framing changes H assumed aligned to start.
end YM.Trace.Pilot
