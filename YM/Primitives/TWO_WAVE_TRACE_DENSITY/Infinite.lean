import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Papers
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Unique
import YM.Push.FREE_RESOLVENT.Test


/-!
# Infinite Brillouin expression DOES use the symbol inverse.

Identities on actual periodic precisions, so harmonic terms in that expression
are also the literal inverse, no interpolation ambiguity. Even identify the
base on published slots with Bed.metric Hess and `fullRow`. Not saying to
invert *fullRow*, which is not the free positive object here; use tree
compression! -/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave.RealSlice
open Lattice Laurent RG Bloch FreeResolvent Function Matrix Tree Precision Bid Exterior
open Work.F08 Push.Uniform Progress.ClassicalKin Progress.ClassicalKin.Tent SceneLedger
open scoped Classical BigOperators Topology
variable {G:Gauge}{P:Patch}{K:KernelChoices}{O:ChartRatio G}{p:Clip}{R:PathData G}
variable {L:SceneLedger (Coarse G) (Vertical G P K)} {s C:ℝ} (hc:Credits L s C)(h:∀ n:Side,Ad G P K n→L.Published (estates P K p O R n)) (hG:P.Branches K G)
    {z D Λ:ℝ}(hb:R.Bounds p z D Λ)

def mattress (L:SceneLedger (Coarse G) (Vertical G P K)):Row (Vertical G P K) (Vertical G P K):=fun i j=> row L.scale (Sum.inr i) (Sum.inr j)

lemma mattress_acts (n:Side): (mattress L).acts n=(headMatrix (pieces L.scale n)).submatrix (TwoWave.peg (Coarse G)) (TwoWave.peg (Coarse G)):=by rw [← head_periods]; rfl

include h hb
theorem original_link (n:Side)(hn:Ad G P K n):
    let e:= insider P K G (enough P K hn); let T:=trees P K n
    (mattress L).acts n=(hessian T (label (dock P K n)) p R 0 0).submatrix e e:=by
  intro e T; rw [mattress_acts, ← (h n hn).full]; exact outline_frame P K p R hn Λ hb
include hc hG


-- Series uniqueness even when borrowing other Purchase widths on some H
omit hb in
lemma only {M:SceneLedger (Coarse G) (Vertical G P K)} {s' C':ℝ}(hm:Credits M s' C') (hv:∀ n:Side,Ad G P K n→M.Published (estates P K p O R n)):L=M:=by
  -- can omit hb. specialized union all six
  obtain ⟨d,hd⟩:=dock_larger P K hG
  have hw {α:Type}{k:ℕ}{C D}{F T:Fan α α k}(he:Cap F s C)(ht:Cap T s' D)(hp:∀ n,Ad G P K n→pieces F n=pieces T n): F=T:=
    fan_frozen he hc.level.le ht hm.level.le ((Filter.eventually_ge_atTop d).mono fun l hl n h=>hp n (hd n (hl.trans h)))
  have hq: L.scale=M.scale:=hw hc.scale hm.scale fun n hn=>by rw [← (h n hn).full, ← (hv n hn).full]
  have hh: L.spur=M.spur:=hw hc.spur hm.spur fun n hn=>by rw [← (h n hn).marks,← (hv n hn).marks]
  have hH:L.cross=M.cross:=hw hc.cross hm.cross fun n hn=>by rw [← (h n hn).marks₂,← (hv n hn).marks₂]
  have h₁:L.tail₁=M.tail₁:=hw hc.tail₁.choose_spec hm.tail₁.choose_spec fun n hn=>by rw [← (h n hn).other₁, ← (hv n hn).other₁]
  have h₂:L.tail₂=M.tail₂:=hw hc.tail₂.choose_spec hm.tail₂.choose_spec fun n hn=>by rw [← (h n hn).other₂, ← (hv n hn).other₂]
  have hg:L.cov=M.cov:=hw hc.green hm.green fun n hn=>by
    ext i j; have he:=congr_fun (congr_fun (((h n hn).green).symm.trans (hv n hn).green) i) (j 0); rw [headMatrix_at,headMatrix_at] at he
    rwa [show j= ![j 0] from by ext1 k; fin_cases k; rfl]
  cases L; cases M; congr

omit hc hG in
lemma bed_link (n:Side)(hn:Ad G P K n){B:Bed}{a U:ℝ}
    (he:Attached B R)(hf:Floor B p (below P n) a U)(hsw:Sworn B (below P n) G)
    {η B₁:ℝ}(hp:B.metric.strip η B₁)(hη:0≤η):
    let e:=insider P K G (enough P K hn)
    let T:=trees P K n; let S:=dock P K n
    let X:=Lifted.grid S T (G:=G) ∘ e
    (mattress L).acts n=((fullRow G P K.penalty B.metric).acts n).submatrix X X := by
  intro e T S X
  have hu:= Work.F03.answer G _ _ S hn T B _ _ _ _ _ _ _ hf hb he hsw (Work.F02.answer G p R z D Λ hb)
  have hh := FreeResolvent.Tests.checked_loop T B (label S) p R hu.1 hu.2
  rw [original_link h hb n hn,hh,Lifted.tree_read hη hp]
  rfl
end YM.Primitives.TwoWave.RealSlice
