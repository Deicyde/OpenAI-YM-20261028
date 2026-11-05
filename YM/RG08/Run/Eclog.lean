import YM.RG08.Run.Choir
/-!
# Apply exact prescription of stable powers and their marked generators. Cost relative to initialized stride and perturbative overlap. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J : Type}{u : I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}{p q:J→ℝ}
variable {U V:J→ BoardU D R G}{W: Wall w 1→ Wings u 1}
section
variable (T ν D')
def dawnP (W:Wall w 1→ Wings u 1)(t:ℕ)(V:J→ BoardU D R G)(i:Wall w 0) := if h:i.i<(w i.a).next.i then
    let z:Wall w 1:= ⟨i.a,i.i,i.first,h⟩
    eject H (Ye X ν D' T (W z).low) (Needle.push (heights X ν D' (W z)) t d (dawnP W t V z.roof)) else V i.a
termination_by ((w i.a).next.i - i.i)
decreasing_by
    unfold Wall.roof; dsimp only; omega
-- param validation
end
lemma openingP (i:J): dawnP ν D' T W t U (Wall.tip w i)= U i:= by rw [dawnP, dif_neg (show ¬ (Wall.tip w i).i < (w (Wall.tip w i).a).next.i from Nat.lt_irrefl _)]; rfl
lemma darkens (i:Wall w 1): dawnP ν D' T W t U i.low=eject H (Ye X ν D' T (W i).low) (route (dawnP ν D' T W t U) X ν D' W t d i) := by rw [dawnP, dif_pos (show i.low.i< (w i.low.a).next.i from i.last)]; rfl
lemma dawning (he:Tights T S ν D' u)(hp:t≤τ) (hz:∀ i,(W i).toLaunch=i.world.toLaunch)(hv:∀ i,Crop t (U i) H F): Keeps (dawnP ν D' T W t U) T ν D' W t:= by
  refine ⟨hz,hp,fun i=>?_,darkens⟩
  generalize ht: (w i.a).next.i-i.i=k; induction k using Nat.strong_induction_on generalizing i with
  | h k ih=>
    rw [dawnP]; split_ifs with hk; swap; exact hv _
    let p: Wall w 1:= ⟨i.a,i.i,i.first,hk⟩; have hh: (w p.a).next.i - p.roof.i < k := by change _- (i.i+1)< k; unfold p; dsimp only; omega
    have ht:= ih _ hh p.roof rfl
    exact pin H (crest_u (he.fair _) h ht.hU) (crest_l (he.fair (W p)) h ht.hU ht.paid) (he.firs (W p).low)

-- program relative to finite upper cutoff, canonical calling shape. Root top input as formal normalized profile. Clock spend at earlier or newer report scale verified.
theorem balances (he:Tights T S ν D' u)(hE:Heirs T' u)(hp:t≤τ)(hx : ∀ i,Crop t (U i) H F)(hv:∀ i,Crop t (V i) H F)(hw:0 ≤ p)(hy:0 ≤ q)(hq:∀ i:Wall w 1, tiltP X i≤q i.a)
    (hh:∀ i≤E,∀ j,Drum k (fun i=>wallY X (Wall.tip w i)) q p (fun t=> U t i j) (fun t=>V t i j) 1)(hk:e≤E)(r):
    let A:=dawnP ν D' T (wallL (w:=w)) t U; let B:=dawnP ν D' T wallR t V; let ℓ:=route A X ν D' wallL t d; let ℓ':=route B X ν D' wallR t d
    Tribe T' H F (q*p) (A-B) (ℓ-ℓ') e r ∧ Tribe T' H F p A ℓ e r ∧ Tribe T' H F p B ℓ' e r := by
   dsimp only
   refine dip_all he hE (dawning he hp (fun i=> rfl) hx) (dawning he hp (fun i=>rfl) hv) hw hq hy hk (fun i hi r=>?_); simp_rw [openingP]; exact hh _ hi _
-- Relative-power may also include capture-scale weights. emit after difference. 
end YM.RG08.Run
