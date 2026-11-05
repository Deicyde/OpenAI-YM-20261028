import YM.RG08.Sideshow.Morn
/-! # Graph iteration covers any admitted corridor (quantitative layer follows).
- No reconstruction on report sequence used (only schedule). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Sideshow
open Forms Function Finset Jetty Lattice Isles Pert.Bulk Stationary Spar Camera Glyph Filter Room Laurent RG Precision Exterior Skiff Trickle Weald Hatch Carrel Quarry Steam
open Planned.PrimaryIntegral295 Place Film Labels Source Source.Drops WardBin Parts Flint Lagoon Yurt Next.Free Atrium Trill Necks
open scoped Classical ContDiff BigOperators Topology ENNReal PowerSeries Matrix
variable {G:Gauge}{n D d p l e k c j t:ℕ}{σ τ μ V Q B C δ η a b W:ℝ}{P:Patch}{K:KernelChoices}
variable (X:Labels.Frame G d)
local notation "I₀"=>Accent X
local notation "M₀"=>Playbook X
local notation "S₀"=>Bouquet X
structure Silo (D k:ℕ)(h:0<σ)(S:S₀):Prop where
 unbound : Threads D S
 seats :Deck X D k h S
 merit :Clean X S
lemma Silo.root {H:Hol G}{T:SectionData X}(hT:T.Sound H)(ht:Bid.pop T)(hp:0<σ)(hd:d≤D):Silo X D k hp (Fete.encore T):=by
 obtain ⟨H1,H2⟩:=Atrium.standardized H T hT ht hd; exact ⟨H1,fun i e _ n=>Fete.encore_price T i hd _ hp e n,H2⟩
-- Store all orders
structure Branch (L:Side)(Q:Crew G P K)(S:S₀)(D k:ℕ)(σ B:ℝ)(hs:0<σ):Prop where
 rises : Silo X D k hs (sing X Q S)
 unique0: play Q S=Atrium.shuffle (deposit X Q S) (sing X Q S)
 wins : Wins (deposit X Q S) (adj X Q S)
 tasked: Monogram X L B (deposit X Q S)

lemma oneWing (D e j t:ℕ)(K:KernelChoices)(σ τ η μ V:ℝ)(H:Hol G)(h:Font d D e j t σ τ η μ V):∃ C:ℝ,1≤C∧∀{P:Patch}{Q R:Crew G P K}{W δ:ℝ}{S S':Bouquet X},Race σ τ η μ V W δ D d e (d+e) j t Q R → 0<δ → Silo X D e h.fine S→Silo X D e h.fine S' →
 Branch X P.L Q S D e η C h.coarse∧Branch X P.L R S' D e η C h.coarse:=by
 obtain ⟨C,hC,H'⟩:= awake X D e j t H K σ η τ μ V h
 refine ⟨C,hC,fun {P Q R W δ S S'} hr hd hs hs'=>?_⟩
 have hT:=hs.unbound;have hT':=hs'.unbound; have hD:=hs.seats;have hD':=hs'.seats
 obtain ⟨hf,hf'⟩:= H' hr hd hT hT' hD hD' hs.merit hs'.merit
 obtain ⟨hy,hz⟩:=sleeved X h Q R hr hd hT hT' hD hD'
 have hw(Q:Crew G P K)(S:S₀)(he:Silo X D e h.fine S)(hR:Monogram X P.L C (deposit X Q S))(hB:Deck X D e h.coarse (play Q S)):Branch X P.L Q S D e η C h.coarse:=by
    obtain ⟨hl,hx⟩:=overjoy X Q S he.unbound
    have hw : Wins (deposit X Q S) (adj X Q S):=evacuation hx hR.funded
    obtain ⟨hU,hV,hW⟩:=normalized (play Q) S (adj X Q S) hl hw.leading0Cloth hw.right hw.left
    exact ⟨⟨hU,deckFusion X hB _,hV⟩,hW,hw,hR⟩
 exact ⟨hw _ _ hs hf hy,hw _ _ hs' hf' hz⟩
end YM.RG08.Sideshow
