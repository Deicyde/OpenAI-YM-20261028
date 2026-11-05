import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Unmasked
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymBooks
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Gongs
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Optics
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Citrus
/-!
 # Set up cap parameters ordered before Stage.Orders from pledge later. Predictor built on Scratch T.B (the SAME Flight). Withdrawal from A0, credit for nonlinear height sails.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG RG.Supply Wilson Pressure Pressure.Tube Tree Next Next.Foundations Precision
open Push Push.PriceCompiler AnalyticBridge LocalGaussianLaws JointLoad JointLoad.Heir JointLoad.Heir.Suite
open Input Org Extra.Histories Planned.PrimaryIntegral295 WaterLevels Bloch Bid Planned.AtomRegular Planned.AtomRegular.Foliage
open AnalyticBridge.VerifiedReset.Time Next.Scheduling Peak
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
-- BEFORE P: stages determined by order & exponent, only, buy Heir.fee.R through Az.
variable {G:Gauge} {c f:Side}{S:StepData c f}
open Next.Free Carrier PPX Exterior
open Source Labels
-- Prepaid for arbitrary early order expression inputs. Crew.Step j i true.P(f,j) i
structure Cliff (G:Gauge) (n b b' d j i:ℕ)(r:ℕ)(A F:ℝ) (K:KernelChoices) where -- data rather than projections? kernel positivity
    lens:ℝ
    big:1≤lens
    early(c f:Side) (S:StepData c f)(T:Tube G S) (P:Flight j i) (C:Libretto G n): C.Z=Az G n→ (h:S.patch.L=P.L) → HEq T.R.A0 (linesOf P K.penalty) → Peak.glider G T d b' (2*C.C) lens -- HEq okay
    charge:ℝ
    large:1≤charge
    accepts:Mercury.priceA b d r F (A+2) lens charge (store G n)
-- use rec.S.patch
private lemma held {T:Tube G S} {i j:ℕ} {P:Flight j i}(k:ℝ)(h:S.patch.L=P.L) (H: HEq T.R.A0 (linesOf P k)) (C α:ℝ) (l:List Axis)(hp:(advanceC P.L (linesOf P k) l).strip α (C/(P.L.val:ℝ)^(1+l.length))): (advanceC S.patch.L T.R.A0 l).strip α (C/(S.patch.L.val:ℝ)^(1+l.length)):=by
    have he (i:Side)(Z : Carrier.Lines i)(hh:i=P.L)(hE:HEq Z (linesOf P k)): (advanceC i Z l).strip α (C/(i.val:ℝ)^(1+l.length)):=by subst i; rwa [eq_of_heq hE]
    exact he _ _ h H
lemma palladium (G:Gauge)(n b b' d j i r:ℕ) (K:KernelChoices) {A F:ℝ}(hA: 0≤A)(hF:0<F)(hd: d≤b')(hj:4≤j)(hi:4≤ i)(he:d+2 ≤ j) : Nonempty (Cliff G n b b' d j i r A F K):=by
  have hh := Cube.fee_one (Az G n)
  let M:= 2*Cube.fee (Az G n); have hv : 0<M:=by unfold M; positivity
  obtain ⟨s,c,hs,hc,H⟩:= Carrier.priced _ K.penalty_pos hj hi
  obtain ⟨C,hC,hx⟩:= Peak.cradle G d b' M c hv hd hs
  obtain ⟨W,hW,h⟩:= gestureA (store G n) d b r C (zero_le_one.trans hC) hF (show 0≤A+2 by linarith)
  exact ⟨C,hC,fun i j S T P Z hZ ha h' => (by change Peak.glider _ _ _ _ (2*Cube.fee Z.Z) _; rw [hZ]; exact hx S T (fun l hl=> held _ ha h' _ _ _ (H P l (by omega)))), W,hW,fun i j=>h⟩
end YM.PhysicalNext.Repeat.Circlet
