import YM.RemainderComparison.Harmonics.Bramble
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Harmonics
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Deck.Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
variable {hC he I I' V U}
variable (D : Youth (p:=p) hC he I I' V U)
variable (hZ:2*(2*n+3)<c.val) (hS:C'.unionP V⊆neighbors n Z)(V₀:Config G c)(χ:Chi) (hv : RG.flags (Pressure.temp p) V₀=∅)
namespace Youth
include D hZ hS ht hx hb hv C' c' hq
lemma cultivates (hf : (L).Fitted E E') :
    let Y':=(L).low.links V₀
    let X:=planted (prism T p χ o.K V₀ E) U
    let X':=planted (prism T' p χ o.K Y' E') V
    I'.steep X' (Matter.own V) W o.a J.table J.halo V=I.steep X (Matter.own U) W o.a J.table J.halo U:=by
  intro Y' X X'
  have hk := c'.laws.data.room; have hM:= C'.laws.data.room
  have hE: X.manifest:=planted_valid ..; have he':X'.manifest:=planted_valid ..
  have hb':bleached X:= by
    change { (roster U) with flags:= RG.flags (Pressure.temp p) V₀}= _; rw [D.candida.2.whiteG,hv]
  have hQx : RG.flags (Pressure.temp p) Y'=∅ := by
    ext i; rw [show i∈RG.flags (Pressure.temp p) Y' ↔ _ from flagged hC V₀ i (show _ from (by have h:= hk.buys; omega)) (Pressure.temp p),hv]; simp
  have hB': bleached X':= by
    change { (roster V) with flags:= RG.flags (Pressure.temp p) Y'}= _; rw [D.candida.1.whiteG,hQx]
  let p' := weftK (h:=h) (Q:=Q) (H:=H) hC Z
  let f' k:=I'.tithe (X'.taggedL k) (Matter.own V) W o.a J.table J.halo V; let f k:=I.tithe (X.taggedL k) (Matter.own U) W o.a J.table J.halo U
  have hh k : f' ((L).pullTag Q k)=f k:= by
    let Z:= X.taggedL k; let Y'':=X'.taggedL ((L).pullTag Q k); have hr:Deck.Stellar hC he K p Z Y'':= ⟨hb',hB',rfl,rfl,rfl,rfl,rfl,hf,rfl,hk,hM,hq,by have hp:=hk.buys; omega⟩
    exact taxation hr C' c' ht hx hb D hZ hS _ _ he' hE rfl
  have hg k : f' k=f (p' k):= by
    rw [← hh]
    let w:= X'.taggedL ((L).pullTag Q (p' k)); have hx i (hi:i∈C'.unionP V):Deck.reverts hC Z ((L).low.cut i)=i:= same_site hC Z _ (by omega) hS i hi
    apply I'.coni (X'.taggedL k) _ w C' rfl he' he' _ (fun _ _=>Iff.rfl)
    refine ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun i hi=>?_,fun i hi=> ?_,fun _ _ _=> rfl⟩
    · exact (congr_arg k.1 (hx _ hi)).symm
    exact (congr_arg k.2 (show (Deck.reverts hC Z ((L).low.cut i.1),i.2)=i from Prod.ext (hx i.1 hi) rfl)).symm
  change likely f'=likely f; rw [funext hg]; exact (makeup (hC:=hC) Z).cashout f

set_option maxHeartbeats 600000 in
lemma farm : I'.lotus T' p χ o.K W o.a J.table J.halo ((L).low.links V₀) V= I.lotus T p χ o.K W o.a J.table J.halo V₀ U:=by
  letI:Nonempty (Forest (Y).ratio):= Tree.select (decreed H) P.odd_side; letI:Nonempty (Forest (S).ratio):= Tree.select (decreed h) P.odd_side
  let V':= (L).low.links V₀; have hx' : RG.flags (Pressure.temp p) V'=∅:= by
    ext i; rw [show i∈ RG.flags (Pressure.temp p) V' ↔ _ from flagged hC V₀ i (by have h:= c'.laws.data.room.buys; omega) (Pressure.temp p),hv]; simp
  have hh E (F:Forest (Y).ratio) (he:(L).Fitted E F) : I'.bloom (prism T' p χ o.K V' F) W o.a J.table J.halo V= I.bloom (prism T p χ o.K V₀ E) W o.a J.table J.halo U:= by
    have hp : Ac.Spark C'.supportP V ↔ Ac.Spark c'.supportP U := mantle C' c' ht D (by omega) hS
    have hW : standsIn (prism T p χ o.K V₀ E) R J.halo U ↔ Ac.Spark c'.supportP U:=
        ⟨And.left,fun h=>⟨h,D.candida.2.untraced ..,by change RG.flags (Pressure.temp p) V₀ ∩ _ = _; rw [hv,D.candida.2.whiteG,Finset.empty_inter]⟩⟩
    have hK : standsIn (prism T' p χ o.K V' F) R' J.halo V↔Ac.Spark C'.supportP V:=
        ⟨And.left,fun h=>⟨h,D.candida.1.untraced ..,by change RG.flags (Pressure.temp p) V' ∩ _ = _; rw [hx',D.candida.1.whiteG,Finset.empty_inter]⟩⟩
    unfold Team.bloom; exact if_congr ((hK.trans hp).trans hW.symm) (cultivates C' c' hq ht hx hb D hZ hS V₀ χ hv he) rfl
  let p₁:=(L).low.cut; let w:= Deck.reverts hC Z
  let f' (i:Greenbelt.Reserve Y):= I'.bloom (prism T' p χ o.K V' (Greenbelt.allot i)) W o.a J.table J.halo V
  let f (i:Greenbelt.Reserve S):= I.bloom (prism T p χ o.K V₀ (Greenbelt.allot i)) W o.a J.table J.halo U
  let P (i:Greenbelt.Reserve Y) (j:Site c):= Deck.dismount (h:=h) hC he Z (i (w j))
  change likely f' = likely f
  have heq k:f' k=f (P k):= by
    let F':= Greenbelt.allot («S»:=(S)) (P k); let E':=(L).repeater F'
    rw [show f (P k)= _ from (hh F' E' ⟨fun i=>rfl⟩).symm]; refine I'.sailV (prism T' p χ o.K V' (Greenbelt.allot k)) (prism T' p χ o.K V' E') V rfl rfl rfl rfl rfl C' ?_
    intro i hi; let x:= (Y).ratio.parent i; have hx':x∈ Set.range w:= ⟨p₁ x,(same_site hC Z _ (by omega) hS x hi)⟩
    change (k x).up i = F'.up ((L).high.cut i); unfold F' Greenbelt.allot P; dsimp only; unfold dismount; dsimp only
    rw [show (S).ratio.parent _= _ from Lace.position (L) i,show w ((L).low.cut ((L).R.parent i))=x from same_site hC Z _ (by omega) hS x hi, Deck.hereagain (h:=h) (H:=H) hC he Z hx' i rfl]
  rw [funext heq]; have hh' : Matchup (P : Greenbelt.Reserve Y → Greenbelt.Reserve S):= ((Deck.countingF (Q:=Q) (h:=h) (H:=H) hC he Z).expands w (irrevocable ..)); exact hh'.cashout f
end Youth
end YM.RemainderComparison.Harmonics
