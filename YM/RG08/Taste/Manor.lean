import YM.RG08.Taste.Swallow
/-!
# Exact compensation certificate, zero-order remainder. Full temperature still polynomial.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Drift Pivot
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J W:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}{U V:J→ BoardU D R G} {p q:J→ℝ}
variable (he:Tights T S ν D' u)(hx:Heirs T' u)(hp:Mirth X U V w p q E k τ){s:Quilt X.kernel.penalty g.w}(hQ:Plays (X:=X) u s)
local notation "[↓]" => offerD w
local notation "[↑]" => offerF w
local notation "◈" => wallY X
local notation "▿" => topY X w
local notation "[ℝ]" => strideP X w p
local notation "▽" => wallQ (w:=w) q
local notation "Ⓐ" => remnant ν D' T [↓] U
local notation "Ⓑ" => remnant ν D' T [↑] V
abbrev portal (w:J→ ShoreP u)(i:J) : Wall w 0:= foothold (Wall.tip w i)
include he hx hp hQ
set_option maxHeartbeats 300000 in
lemma vCook_pay (a:Letter F) : Tonic ◈ [ℝ] ▽ (fun i:Wall w 0=> vCook [↓] T i (Ⓐ i) a) (fun i:Wall w 0=> vCook [↑] T i (Ⓑ i) a) := by
    let P i:= fires X G ([↓].N (Wall.a (b:=w) (n:=0) i)) i.i; let Q i:=fires X G ([↑].N (Wall.a (b:=w) (n:=0) i)) i.i
    have hU i:=vol_p he [↓] hp.has hp.does i; have hV i:=vol_p he [↑] hp.owes hp.lives i
    obtain ⟨c,hc,G⟩:= ponderous he hQ
    have hx'(i:Wall w 0): Plaque (P i-Q i) (c i.world *(▽ i)):= ⟨mul_nonneg (hc.positive _) (cWiz hp _),fun a b z=> (G i.world|>.2.2|>.2 a b z).trans (mul_le_mul_of_nonneg_left ((Wall.loan X i).trans (hp.peak _)) (hc.positive _))⟩
    have hc' : Weighed (wallY X (b:=w) (n:=0)) (fun i=>c i.world) := (Wall.invested X).sway (Wall.plusOne X) (hc.transfer Wall.world)
    let r i:= frisk (P i) (Ⓐ i 0) τ (slot a); let s i:=frisk (Q i) (Ⓑ i 0) τ (slot a)
    have hH j n : Drum k ◈ ▽ [ℝ] (fun i=> fig (P i) (Ⓐ i 0) j n) (fun i=> fig (Q i) (Ⓑ i 0) j n) 1:= by
       induction j generalizing n with
       | zero=> exact v_rails he hx hp (Nat.zero_le E) n
       | succ j ih=> simp_rw [fig]; have ht:=twix (A:=P) (B:=Q) (fun i=> G i.world|>.1) (fun i=> G i.world|>.2.1) hx' hc' (Wall.plusOne X) (ih (n+2)); exact Drum.weight ht (↑(j+1:ℕ):ℝ)⁻¹
    have hD : Drum k ◈ ▽ [ℝ] r s 1:= Drum.group _ (Wall.plusOne X) zero_le_one (fun j _=> hH j (slot a))
    have hm:d*slot a*slot a ≤ k:= (Nat.mul_le_mul (Nat.mul_le_mul_left _ (slot_le a)) ((slot_le a).trans (le_trans he.hh (Nat.le_add_right ..)))).trans T'.budget
    refine ⟨cardDig H a hD.first hm,cardDig H a hD.second hm,?_⟩
    have hg i:Gold (r i):= gold_sum (fun j _=>golden_terraces X.kernel.penalty_pos (X.adm i.i) (W:=Ⓐ i 0) (fun _=> sober_vetted (hU i).1) ..)
    have hg' i:Gold (s i):= gold_sum (fun j _=>golden_terraces X.kernel.penalty_pos (X.adm i.i) (W:=Ⓑ i 0) (fun _=>sober_vetted (hV i).1) ..)
    rw [show _-_= (fun i: Wall w 0=> invest H ((r-s) i) a) from funext fun i=>?_]; · exact cardDig H a hD.funds hm
    exact (Pivot.invest_less H a (polished_sum (fun j _=>pol_front (G i.world|>.1) (hU i|>.2 0) j _): Polished (r i)) (polished_sum (fun j _=>pol_front (G i.world|>.2.1) (hV i|>.2 0) j _):Polished (s i)) (hg i).toToute (hg' i).toToute).symm
lemma vCook_return (a: Letter F):
    Tonic ▿ (fun i=> [ℝ] (portal w i)) q (fun i=> vCook [↓] T (Wall.tip w i) (Ⓐ (Wall.tip w i)) a) (fun i=>vCook [↑] T (Wall.tip w i) (Ⓑ (Wall.tip w i)) a):= by
    let L i:= V i; let Y i:=vCook [↓] T i (Ⓐ i); let Z i:= vCook [↑] T i (Ⓑ i)
    have hA i : Y i= breathP ν D' T [↓] i *ᵥ Y (foothold i):= v_pot he _ hp.has hp.does i
    have hB i : Z i= breathP ν D' T [↑] i *ᵥ Z (foothold i):= v_pot he _ hp.owes hp.lives i
    change Tonic _ _ _ (fun i=>Y _ a) (fun i=>Z _ a); rw [show (fun i=> Y (Wall.tip w i) a)=_ from funext fun i=> congr_fun (hA (Wall.tip w i)) a, show (fun i=>Z (Wall.tip w i) a)= _ from funext fun i=> congr_fun (hB (Wall.tip w i)) a]
    have hz: Lying ▿ q (fun i=> breathP ν D' T [↓] (Wall.tip w i)) (fun i=> breathP ν D' T [↑] (Wall.tip w i)):= by
       let y:= topY X w; have ht:Audience y:=fun i=>Wall.plusOne X _
       intro a b; have he := leaseT (Summit.Lease.whirls (trump_pay he (Nat.zero_le E) a b) w) ht (show Weighed y y from by simpa only [pow_one] using Weighed.power y ht 1) hp.peak
       unfold breathP diagonalSl; simp_rw [Matrix.of_apply]; split; exact he; exact Lease.const ..
    apply draw hz (fun a=> Tonic.viaD (vCook_pay he hx hp hQ a) (fun i=> portal w i)) (fun i=> Wall.plusOne X _) (cWiz hp) (fun i=> mul_nonneg (hp.price i) (gain_pos ..).le) a -- ambiguous .. syntax
-- exact zero-order registration
variable (ν D' T) in
def smoke (b:Offer w)(U:J→ BoardU D R G)(i:J) := vCook b T (Wall.tip w i) (U i) - (oven X ν D' H Ω (d.le_succ.trans hD) h (b.N i) (w i|>.next.i))*ᵥ (fun j=> coeff 0 (vMatch ν D' T b U i j))
lemma kwmt (a:Letter F): Tonic ▿ (fun i=> [ℝ] (portal w i)) q (fun i=> smoke ν D' T [↓] U i a) (fun i=>smoke ν D' T [↑] V i a) := by
   have hv b (U:J→ BoardU D R G)(hU:∀ i,Marvel τ (U i))(hp:∀ i,Lank (U i)) (i:J): smoke ν D' T b U i=vCook b T (Wall.tip w i) (remnant ν D' T b U (Wall.tip w i)):= by
      let f:=phase0 ν D' T b (Wall.tip w i); let Y i:=vMatch ν D' T b U i; obtain ⟨hz,hV⟩:= edge_crew f (Y i) (he.firs _|>.toBoards) he.hh; rw [v_opens ν D' T b U i]; unfold vCook; rw [vCook_cut _ _ _ _ (hU i) hz (hp i) hV]; unfold smoke; exact congr_arg (vCook b T (Wall.tip w i) (U i) -·) ((vCook_basis he b (Wall.tip w i) (Y i)).symm)
   rw [show (fun i=>smoke ν D' T [↓] U i a)= _ from funext fun i=> congr_fun (hv _ _ hp.has hp.does i) a, show (fun i=>smoke ν D' T [↑] V i a)= _ from funext fun i=> congr_fun (hv _ _ hp.owes hp.lives i) a]; exact vCook_return he hx hp hQ a
end YM.RG08.Taste
