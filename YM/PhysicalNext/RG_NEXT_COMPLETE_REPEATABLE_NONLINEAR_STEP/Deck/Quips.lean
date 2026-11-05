import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Detrain
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Sully
/-! # Illuminate actual Coin(irres). Cross-cover orientations via Crop and calendars. No coercion on propagated Inputs/Ledgers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Mint
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "Y" => stepped Q H
local notation "Y'" => stepped Q h
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
include hC he
variable {U : Finset (Music C F)} {a v W q K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta)
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (verse_down (Lace.project (h:=h) (H:=H) hC he)) U)
    (hS:C'.unionP (hatch (stepped Q H) U)⊆neighbors n Z) (hw:∀ i∈U,verse R'.path i ≤ radiusB p)
    (V:Config G c) (χ:Chi) (hv : RG.flags (Pressure.temp p) V=∅)
include C' c' hq ht hx hb hv hZ hd hS hw

lemma meetups (hp:Ac.Spark C'.supportP (hatch Y U)) (hP: Ac.Spark c'.supportP (hatch Y' (wrappers (L) U))):
    C'.spawn χ ((L).low.links V) (hatch Y U)= c'.spawn χ V (hatch Y' (wrappers (L) U)):= by
  letI:Nonempty (Forest (Y).ratio):= Tree.select (decreed H) P.odd_side; letI:Nonempty (Forest (Y').ratio):= Tree.select (decreed h) P.odd_side
  let V':= (L).low.links V; let q:= hatch Y U; let p':= hatch Y' (wrappers (L) U)
  have hx' : RG.flags (Pressure.temp p) V'=∅:= by
    ext i; rw [show i∈ RG.flags (Pressure.temp p) V' ↔ _ from flagged hC V i (by have h:= c'.laws.data.room.buys; omega) (Pressure.temp p),hv]; simp
  have hh E (F:Forest (Y).ratio) (he:(L).Fitted E F) : proceedsA R' (prism T' p χ o.K V' F) W o.a J.halo J.table q = proceedsA R (prism T p χ o.K V E) W o.a J.halo J.table p':= by
    have ha : standsIn (prism T' p χ o.K V' F) R' J.halo q:=⟨hp,hatchT ..,by change RG.flags (Pressure.temp p) V' ∩ _ = _; rw [hx',show roster q=_ from unrostered ..,Finset.empty_inter]⟩
    have hw':standsIn (prism T p χ o.K V E) R J.halo p':=⟨hP,hatchT ..,by change RG.flags (Pressure.temp p) V ∩ _ = _; rw [hv,show roster p'=_ from unrostered ..,Finset.empty_inter]⟩
    unfold proceedsA; rw [if_pos ha,if_pos hw']; exact trimmed hC _ C' c' hq ht hx hb Z n hZ hd hS hw V χ hv he
  let p₁:=(L).low.cut; let w:= Deck.reverts hC Z
  let f' (i:Reserve Y):= proceedsA R' (prism T' p χ o.K V' (Greenbelt.allot i)) W o.a J.halo J.table q
  let f (i:Reserve Y'):= proceedsA R (prism T p χ o.K V (Greenbelt.allot i)) W o.a J.halo J.table p'
  let P (i:Reserve Y) (j:Site c):= Deck.dismount (h:=h) hC he Z (i (w j))
  change likely f' = likely f
  have heq k:f' k=f (P k):= by
    let F':= Greenbelt.allot (S:=(Y')) (P k); let E':=(L).repeater F'
    rw [show f (P k)= _ from (hh F' E' ⟨fun i=>rfl⟩).symm]; refine Horticulture.Travels.sails _ _ _ rfl rfl rfl rfl rfl rfl C' ?_; intro i hi
    have hc := (hS (show _∈ C'.unionP (hatch Y U) from hi)); let x:= (Y).ratio.parent i; have hx':x∈ Set.range w:= ⟨p₁ x,(same_site hC Z _ (by omega) hS x hi)⟩
    change (k x).up i = F'.up ((L).high.cut i); unfold F' Greenbelt.allot P; dsimp only; unfold dismount; dsimp only
    rw [show (Y').ratio.parent _= _ from Lace.position (L) i,show w ((L).low.cut ((L).R.parent i))=x from same_site hC Z _ (by omega) hS x hi, Deck.hereagain (h:=h) (H:=H) hC he Z hx' i rfl]
  rw [funext heq]; have hk : Matchup (P: Reserve Y→ Reserve Y'):= ((Deck.countingF (Q:=Q) (h:=h) (H:=H) hC he Z).expands w (irrevocable ..)); exact hk.cashout f
end YM.PhysicalNext.Repeat.Deck.Mint
