import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Blue
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Bridge

/-!
 # CoreFlow. Compare ANY two physical stencil tags, same levels/time only.
 No Cargo between incompatible flag sectors asserted; here healthy all. Common
 Choir on bigger virtual period -> both. Allow pert and pure interactions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Slide
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {c f C' F:Side} {i j m n N:ℕ}
variable {C : Targets X.p X.K} {Z : Expenses C} {p : Return.Wages} {v : ℕ→ℝ} (R : Register D Z p v) (A : Alloy X D)
local notation "α" => A.B.a
local notation "J" => A.B.a.clock.J (m+1)
local notation "I" => A.B.a.clock.J m
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "x" => A.B.a.clock.hatBeta m
local notation "θ" => Pressure.temp (A.B.a.clock.hatBeta m)
local notation "𝒯" => Pane.orchestra A N
local notation "U" => (X.p.profile I)
local notation "B" => (A.B.a.budget m)
local notation "e" => (Z J I)
local notation "P'" => (C J I)
local notation "β" => (A.B.a.budget (m+1))
local notation "D'" => (band α (m+1))
local notation "γ" => (A.B.kin.alpha N m)
local notation "O" => Chi.canonical
set_option quotPrecheck false
local notation "D₀" => Meadow.studio (C J I).halo (radiusB x)
local notation "ℒ" => ((α).S.block m)
section switch
variable (H : f.val=c.val*(A.B.a.S.block m).val) (hc:4*Meadow.studio (C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo (radiusB (A.B.a.clock.hatBeta m))+16≤c.val)
local notation "T" => Pane.orchestra A N H
variable {M:ℕ} (H' : F.val=C'.val*(A.B.a.S.block m).val) (hC:C'.val=c.val*M)
  {u : RG.Rep G f} {w : RG.Rep G F}
   {Y : Chartlet R A N m H u} {K: Chartlet R A N m H' w}
    (h : w.path=u.path) (hb:w.p=u.p) (hβ:w.beta=u.beta) (hm: m < N) (hT:Tenement R A.delay) (hr : ∀ N m n,m≤N→ Bid.Sworn (A.B.M.H N m) n G)
include h hm hT hr hC hβ hb Y K hc
-- notation hC val arguments avoiding aligns every H externally
lemma span (Q:Site C') (V: Config G c) (ht : flags θ V=∅):
    Meadow.barony K O n γ Q ((normal (Deck.divides hC) hC).links V)= Meadow.barony Y O n γ (splitter (Deck.divides hC) Q) V := by
  let hH:= hT J x (A.B.valid.pays m) I (step_paid A.B.a m); obtain ⟨C,d,r,g,b,t,z,Y'',q,l,i,⟨N',hv⟩,hK,hp'⟩:= hH.2 _ _ _ (Pane.orchestra A N H) Y.laws.data.funds (Pane.ovation A N H hm hr) u Y
  obtain ⟨w₀,d',r',g',b',t',z',Y''',q',l',i',⟨M',hv'⟩,hK,hp'⟩:= hH.2 _ _ _ (Pane.orchestra A N H') K.laws.data.funds (Pane.ovation A N H' hm hr) w K
  exact Meadow.replay («I»:= Y) (I':=K) («T»:=T) (T':=𝒯 H') hC (show 2 ≤ c.val from (by omega)) rfl h hb hβ Q (by dsimp only [Meadow.studio] at hc; omega) N' M' V ht γ n
omit hm hT hr hβ h H' hC K hc hb
lemma stroll (z:Site c) (V:Config G c): Meadow.barony Y O n γ 0 (translate z V)=Meadow.barony Y O n γ z V:= by rw [← pull_one,← Meadow.rotates]; simp [Lattice.affine]
end switch
section associate
variable (H : f.val=c.val*(A.B.a.S.block m).val) (H' : F.val=C'.val*(A.B.a.S.block m).val)
    {u : RG.Rep G f} {w : RG.Rep G F}
   (Y : Chartlet R A N m H u) (K: Chartlet R A N m H' w)
    (h : w.path=u.path) (hb:w.p=u.p) (hw: w.path=A.B.kin.path N (m+1)) (hu:w.p=A.B.a.budget (m+1))
   (het : u.beta∈ RG.Shoot.band A.B.a (m+1)) (hβ:w.beta=u.beta) 
    (ht : Pollened D R A.delay) (hq : v≤ A.delay.betaEntry)
    (hm: m < N) (hT:Tenement R A.delay) (hr : ∀ N m n,m≤N→ Bid.Sworn (A.B.M.H N m) n G)
   (hG : (X.p.profile (A.B.a.clock.J m)).supportExponent+3≤ (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).earn)
    (hp: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
include h hb hw hu het hβ ht hq hm hT hr hG hp
lemma parses (hc : 4*D₀+16≤ c.val) (hC : 4*D₀+16≤ C'.val) (z:Site c) (z':Site C') (W:Config G C') (V:Config G c) (hk : flags θ V=∅) (hV: flags θ W=∅) (hA:Agrees (Lattice.box D₀) (expandAt z' W) (expandAt z V)) : Meadow.barony K O n γ z' W=Meadow.barony Y O n γ z V:= by
  let Cb := c*C'; let Fb:= Cb * ((α).S.block m)
  have hM:Fb.val=Cb.val*(A.B.a.S.block m).val:=rfl; have hN: Cb.val=c.val*C'.val:=rfl; have hN': Cb.val=C'.val*c.val:= mul_comm ..
  have he' : c.val ≤ Cb.val:=Nat.le_mul_of_pos_right _ C'.pos
  let u₀ := Pane.virgin (𝒯 hM) β u.beta
  obtain ⟨k,hl⟩:= Pane.affords A N hM hm (show 100*(1+radiusB x) ≤ Cb.val from Y.laws.data.room.buys.trans he') R hq hr het
  let A₀:=Lattice.translate z V; let B₀:= Lattice.translate z' W; let u1 := normal (divides hN) hN; let v2:=normal (divides hN') hN'
  have hV1: flags θ A₀=∅:= by unfold A₀; rw [← pull_one]; exact Pane.tranquility V hk ..
  have hV2: flags θ B₀=∅:= by unfold B₀; rw [← pull_one]; exact Pane.tranquility W hV ..
  obtain ⟨F₀⟩:= Tree.select (panel A m hM).ratio (panel A m hM).patch.odd_side
  let P:= Match.staple (R:=u₀) (H:=k) («J»:=k) rfl rfl rfl
  have hp' := lays R A hM P ht hm hT hr hG hp hl F₀
  have hK:= Meadow.regularY P n (0:Site Cb) hp'.1 rfl rfl rfl rfl
  have hK' := Slide.span R A (n:=n) H hc hM hN (Y:=Y) (K:=k) (h:= (hw.symm.trans h)) (hu.symm.trans hb) rfl hm hT hr 0 A₀ hV1
  have hY:= Slide.span R A (n:=n) H' hC hM hN' (Y:=K) (K:=k) hw.symm hu.symm hβ.symm hm hT hr 0 B₀ hV2
  rw [map_zero] at hK' hY
  rw [← stroll R A H' (Y:=K) z' W,← stroll R A H (Y:=Y) z V,← hK',← hY]
  apply hK.sites _ _ (readNear (Z:=D₀) 0 (by omega) ?_); rw [Slide.rolls,Slide.rolls,map_zero,map_zero]; unfold A₀ B₀; rw [increases,increases]; exact hA
end associate
end YM.PhysicalNext.Repeat.Slide
