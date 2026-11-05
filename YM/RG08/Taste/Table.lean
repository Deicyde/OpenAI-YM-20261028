import YM.RG08.Taste.Soups
/-!
# Powers and payment of exact compensated top test stencil vector. Full solved residual bounds NOT using forward-product exponential costs.
-/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J W:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}
variable {U V:J→ BoardU D R G} {p q:J→ℝ}{δ ρ y:W→ℝ}
-- spend canonicals before inverse-product accumulation
section
variable {A B: W→Native (Letter F)}{b:W→ Roam u}(he:Tights T S ν D' u)
local notation "F₁" => forward X ν D'
include he
lemma forward_d (h: Weighed y (fun i=> (b i).measure X))(hk:∀ i,(b i).cost X ≤ δ i)(h1:0 ≤ ρ)(hx:Audience y)(ht:∀ i≤e,∀ a,Tonic y ρ δ (fun j=>coeff i (A j a)) (fun j=>coeff i (B j a)))(hE:e≤E)(a:Letter F): Tonic y ρ δ (fun i=> coeff e (F₁ (b i).N (b i).i (b i).main (A i) a)) (fun i=>coeff e (F₁ (b i).M (b i).i (b i).main (B i) a)):= Tonic.ferry (fun i hi=> ht i hi a) (fun i hi=> leaseT (Summit.Lease.whirls (carriers he (hi.trans hE)) b) hx h hk) hx h1 (fun i=>((gain_pos ..).le).trans (hk i))
lemma forward_p (h: Weighed y (fun i=> (b i).measure X))(hk:∀ i,(b i).cost X ≤ δ i)(h1:0≤ρ)(hx:Audience y)(ht:∀ i≤e,∀ a,Tonic y ρ δ (fun j=>coeff i (A j a)) (fun j=>coeff i (B j a)))(hE:e≤E)(a:Letter F): Tonic y ρ δ (fun i=> coeff e (F₁ (b i).N (b i).main (b i).i (A i) a)) (fun i=>coeff e (F₁ (b i).M (b i).main (b i).i (B i) a)):= Tonic.ferry (fun i hi=> ht i hi a) (fun i hi=> leaseT (Summit.Lease.whirls (prices_come he.hc he.hv he.hz he.hs (hi.trans hE)) b) hx h hk) hx h1 (fun i=>((gain_pos ..).le).trans (hk i))
lemma trump_d (b:W→ ShoreP u)(h:Weighed y (fun i=> (b i).y X))(hk:∀ i,(b i).rate X ≤ δ i)(h1:0 ≤ ρ)(hx:Audience y)(ht:∀ i≤e,∀ a,Tonic y ρ δ (fun j=>coeff i (A j a)) (fun j=>coeff i (B j a)))(hE:e≤E)(a:Letter F):
   Tonic y ρ δ (fun i=> let v:=b i; coeff e (((trump T ν D' v.next.N v.low v.next.main v.city)*ᵥ A i) a)) (fun i=>let v:=b i; coeff e (((trump T ν D' v.next.M v.low v.next.main v.city) *ᵥ B i) a)):= by
     apply Tonic.thrum _ ht hx h1 (fun i=> ((gain_pos ..).le).trans (hk i))
     exact fun i hi j k=> leaseT (Summit.Lease.whirls (trump_pay he (hi.trans hE) j k) b) hx h hk
end
section
variable (he:Tights T S ν D' u)(hx:Heirs T' u)(hp:Mirth X U V w p q E k τ)
local notation "[↓]" => offerD w
local notation "[↑]" => offerF w
local notation "◈" => wallY X
local notation "▴" => strideP X w p
local notation "▽" => wallQ (w:=w) q
include he hx hp
lemma pays_s (hE:e≤E)(a:Letter F):
   Tonic (fun i:Stem w=>◈ i.i) (fun i=>▴ i.i) (fun i=>▽ i.i)
    (fun i=>coeff e (freightP ν D' T [↓] i (shiftV ν D' T [↓] U (inside i)) a)) (fun i=>coeff e (freightP ν D' T [↑] i (shiftV ν D' T [↑] V (inside i)) a)):= by
    let f (i:Stem w):= fragment i; let L i:=(f i).fromR; let y(i:Stem w):=◈ i.i
    have hz:Audience y:= fun i=> Wall.plusOne X _
    have hw:Weighed y y:= by simpa only [pow_one] using Weighed.power y hz 1
    have hh : Weighed y (fun i=>(f i).y X):= hw.mono (fun i=> zero_le_one.trans (city_one (f i) X)) (race_a X)
    have hP (i:Stem w): (f i).rate X ≤ ▽ i.i:= (race_b X i).trans (hp.peak _)
    have h1 (i:Stem w): 0≤▴ i.i:=mul_nonneg (hp.price _) (gain_pos ..).le
    have hV(i): (L i).cost X ≤ (f i).rate X := by
        apply Real.exp_monotone; have ht := age_scale_mono X.S (max_le_max (f i).init (le_refl (f i).next.main)); change -(1/4:ℝ)*(X.S.scale (f i).next.N-X.S.scale (max (f i).low (f i).next.main))≤ -(1/4:ℝ)*(X.S.scale (f i).next.N- X.S.scale (max (f i).next.i (f i).next.main)); linarith
    -- pay debts from i to here. amplitude monotone
    have hv i:▴ (inside i) ≤ ▴ i.i:= by
      refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (hp.price _)
      change -(1/4:ℝ)*(X.S.scale (w i.i.a).next.i-X.S.scale (inside i).i) ≤ -(1/4:ℝ)*(X.S.scale (w i.i.a).next.i-X.S.scale i.i.i); have ht: (inside i).i ≤ i.i.i:= along_roof i; linarith [age_scale_mono X.S ht]
    have hL : Weighed y (fun i=>(L i).measure X):= hw.mono (fun i=> zero_le_one.trans (sh X _)) (fun i=> (le_max_left (L i|>.measure X) ((f i).next.measure X)).trans (race_a X i))
    exact trump_d he f hh hP h1 hz (fun j hj a=> forward_p he hL (fun i=> (hV i).trans (hP _)) h1 hz (fun n hn a=> Tonic.rises (Tonic.viaD (shift_k he hx hp ((hn.trans hj).trans hE) a) inside) hv (fun i:Stem w=> cWiz hp _)) (hj.trans hE) a) hE a
lemma payable (hE:e≤ E)(a:Letter F): Tonic ◈ ▴ ▽ (fun i=>coeff e (heap ν D' T [↓] U i a)) (fun i=>coeff e (heap ν D' T [↑] V i a)) := by
   let A (i:Stem w):= freightP ν D' T [↓] i (shiftV ν D' T [↓] U (inside i))
   let B (i:Stem w):= freightP ν D' T [↑] i (shiftV ν D' T [↑] V (inside i))
   unfold heap spreads; simp_rw [Finset.sum_apply, _root_.map_sum]; apply Tonic.swing (raceL (w:=w)) _ (race_c X) (fun i=>mul_nonneg (hp.price _) (gain_pos ..).le) (fun i:Wall w 0=>cWiz hp _) (Wall.plusOne X); convert pays_s he hx hp hE a using 1 <;> first|rfl|funext i <;> rw [dif_pos (show i.k < raceL i.i from i.hw)]
lemma offer_r (hE:e≤E)(a:Letter F) : Tonic ◈ ▴ ▽ (fun i=>coeff e (offerUp ν D' T [↓] U i a)) (fun i=>coeff e (offerUp ν D' T [↑] V i a)) := by
   let A (i:Wall w 0): Roam u:= ⟨i.world,(w i.a).next.fromK,(w i.a).next.ends⟩
   have hp'(i:Wall w 0): (A i).cost X ≤ tiltP X i:= by apply Real.exp_monotone; let B:=w i.a; change -(1/4:ℝ)*(X.S.scale B.next.N-X.S.scale (max i.i B.next.main)) ≤ -(1/4:ℝ)*(X.S.scale B.next.N-X.S.scale (max B.next.i B.next.main)); have h : i.i ≤ B.next.i:= i.last; linarith [age_scale_mono X.S (max_le_max h (le_refl B.next.main))]
   exact forward_d (b:=A) he (Wall.invested X) (fun i=> (hp' i).trans (hp.peak _)) (fun i=>mul_nonneg (hp.price _) (gain_pos ..).le) (Wall.plusOne X) (fun j hj a=> payable he hx hp (hj.trans hE) a) hE a
lemma v_year (hE:e≤E)(b:Letter F) : Tonic (topY X w) p q (fun i=>coeff e (vMatch ν D' T [↓] U i b)) (fun i=>coeff e (vMatch ν D' T [↑] V i b)) := by
    have hh : Audience (topY X w):= fun i=> Wall.plusOne X _
    unfold vMatch; simp_rw [Pi.add_apply,_root_.map_add]
    have ht:= Tonic.viaD (offer_r he hx hp hE b) (Wall.tip w)
    simp_rw [strideP,Wall.tip,gain_zero,mul_one] at ht
    exact Tonic.more (call_pair T' H hh hE hp.has hp.does hp.owes hp.lives (fun i hi r=> hp.drums i (hi.trans hE) r) b) ht hh
lemma v_rails (hE:e≤E)(r): Drum k ◈ ▽ ▴ (fun i=>remnant ν D' T [↓] U i e r) (fun i=>remnant ν D' T [↑] V i e r) 1:= by
    have h1 i:=he.firs ((offerD w).part (i:Wall w 0)); have h2 i:=he.firs ((offerF w).part (i:Wall w 0)); exact drumCut (rise_k he hx hp hE r) (heads_up (fun i=>(h1 i).toBoards) (fun i=>(h2 i).toBoards) (Wall.plusOne X) (fun i=> cWiz hp _) (fun i hi b r=> south he hp.peak (hi.trans hE) b k r) (fun i hi b=> offer_r he hx hp (hi.trans hE) b)) (Wall.plusOne X) zero_le_one
end
end YM.RG08.Taste
