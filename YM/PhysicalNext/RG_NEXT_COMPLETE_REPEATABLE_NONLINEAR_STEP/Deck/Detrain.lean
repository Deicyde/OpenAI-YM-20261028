import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Purloin
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Turbine
/-!
 # No tie to fresh k/F. Move molecule account across covers.
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
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
-- no S field
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

abbrev hatch (S: StepData c f) (u:Finset (Music c f)):= u.map (disc S)
lemma not_used (S:StepData c f) (u:Finset (Music c f)): (hatch S u).toLeft=∅ ∧ Matter.own (hatch S u)=∅ := by
  have hh i (hi:i∈u) : (disc S) i=album S i:=rfl
  constructor <;> ext p
  · simp only [mem_toLeft,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:= mem_map.mp h; unfold disc at hx; injection hx
  simp only [own,mem_toLeft,mem_toRight,notMem_empty,iff_false]; intro h; obtain ⟨i,hi,hx⟩:=mem_map.mp h; unfold disc at hx; injection hx with he; injection he
lemma unrostered (S:StepData c f) (u:Finset (Music c f)): roster (hatch S u)= ⟨∅,∅,∅⟩:= by unfold roster; rw [(not_used S u).1]; simp [Packets.store]; exact ⟨by ext; simp,by ext; simp,by ext; simp⟩
lemma hatchT {G : Gauge} (S:StepData c f) (T:Tube G S) (u:Finset (Music c f)) (R: RG.Rep G f) (i j:ℕ) : troupe T R i j (hatch S u):= by
  unfold troupe; rw [unrostered,(not_used S u).1,(not_used S u).2]
  constructor
  · constructor
    · simp
    · simp
    simp [Packets.seeds]
  constructor
  · intro _ h; exact False.elim (notMem_empty _ h)
  intro _ h; exact False.elim (notMem_empty _ h)

-- pick all in ball. no need surject.
def weftK (hC : C.val=c.val*M) (x : Site C) (k : (stepped Q H).Choices): (stepped Q h).Choices :=
    (fun i=> k.1 (reverts hC x i),fun i=> k.2 (curr (reverts hC x) i))
def makeup (x:Site C) : Matchup (weftK (Q:=Q) (h:=h) (H:=H) hC x):= by
  let p:=reverts hC x; let q:=curr p (X:=Axis); have hp:=irrevocable hC x; have hq:Injective q:= by rintro ⟨i,j⟩ ⟨l,k⟩ h; exact Prod.ext (hp (congr_arg Prod.fst h)) (congr_arg (fun p : Bond C=>p.snd) h)
  exact ((Deck.reads P.FrameTag).expands p hp).times ((Deck.reads P.Points).expands q hq)

variable (hC he)
variable {U : Finset (Music C F)} {a v W q K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta)
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (verse_down (Lace.project (h:=h) (H:=H) hC he)) U)
    (hS:C'.unionP (hatch (stepped Q H) U)⊆neighbors n Z) (hw:∀ i∈U,verse R'.path i ≤ radiusB p)
    (V:Config G c) (χ:Chi) (hv : RG.flags (Pressure.temp p) V=∅)
include he C' c' hq ht hx hb hv hZ hd hS hw
lemma trimmed (hf : (L).Fitted E E') :
    let q:=hatch (Y) U; let r:=(wrappers (L) U).map (disc (stepped Q h)); let Y':=(L).low.links V
    amountP R' (prism T' p χ o.K Y' E') W o.a J.halo J.table q=amountP R (prism T p χ o.K V E) W o.a J.halo J.table r := by
  intro q r Y'
  let X:= planted (prism T p χ o.K V E) r; let X':= planted (prism T' p χ o.K Y' E') q
  have hk := c'.laws.data.room; have hM:= C'.laws.data.room
  have he: X.manifest:=planted_valid ..; have he':X'.manifest:=planted_valid ..
  have hB:bleached X:= by
    change { (roster (hatch (stepped Q h) _)) with flags:= RG.flags (Pressure.temp p) V}= _; rw [unrostered,hv]
  have hQx : RG.flags (Pressure.temp p) Y'=∅ := by
    ext i; rw [show i∈RG.flags (Pressure.temp p) Y' ↔ _ from flagged hC V i (show _ from (by have h:= hk.buys; omega)) (Pressure.temp p),hv]; simp
  have hB': bleached X':= by
    change { (roster (hatch (stepped Q H) _)) with flags:= RG.flags (Pressure.temp p) Y'}= _; rw [unrostered,hQx]
  let p' := weftK (h:=h) (Q:=Q) (H:=H) hC Z -- shadowed h
  let f' k:=(X'.taggedL k).attains R' J.table W o.a (own q) J.halo q; let f k:=(X.taggedL k).attains R J.table W o.a (own r) J.halo r
  have hh k : f' ((L).pullTag Q k)=f k:= by
    let Z:= X.taggedL k; let Y'':=X'.taggedL ((L).pullTag Q k); have hr:Stellar hC (by assumption) K p Z Y'':= ⟨hB,hB',rfl,rfl,rfl,rfl,rfl,hf,rfl,hk,hM,hq,by have hp:=hk.buys; omega⟩
    exact hr.blankets C' c' ht (by assumption) hb he' he rfl (own q) (own r) _ _ hZ hd hS hw
  have hg k : f' k=f (p' k):= by
    rw [← hh]
    let w:= X'.taggedL ((L).pullTag Q (p' k)); have ht i (hi:i∈C'.unionP q):Deck.reverts hC Z ((L).low.cut i)=i:= same_site hC Z _ (by omega) hS i hi
    apply C'.vista q (X'.taggedL k) w rfl rfl he' he' _ (fun _ _=>Iff.rfl); refine ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun i hi=>?_,fun i hi=> ?_,fun _ _ _=> rfl⟩
    · exact (congr_arg k.1 (ht _ hi)).symm
    exact (congr_arg k.2 (show (Deck.reverts hC Z ((L).low.cut i.1),i.2)=i from Prod.ext (ht i.1 hi) rfl)).symm
  change likely f'=likely f; rw [funext hg]; exact (makeup (hC:=hC) Z).cashout f
end YM.PhysicalNext.Repeat.Deck.Mint
