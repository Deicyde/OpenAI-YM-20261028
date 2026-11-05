import YM.RG08.Calendar.Vocals
import YM.RG08.Dart.Seams
import YM.RG08.Extra.Grail
/-!
 # Optional path lifts with the same window. Expenditure at ANY root in the
 stated paid usage; choices may be by mark set & kept root, finite scope. Does
 not include cost of living in real mask budgets. Vacuum-path Frame extras from
 ANY stage view assigned before choosing L. (Used only if relating to Kin tapes.)
 Thus even reciprocal widths for Track curvature can be imposed on the same
 schedule. `loopCap` no stronger than the construction gives it.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Admission
open Function Filter Lattice Wilson Exterior Precision Laurent Finset RG Next.Free RG.Supply Bloch Input Conductor Wings Stationary Staffer Drift Virtue
open Town Run Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Creek Dart Wax Canon
open scoped BigOperators Topology Real ContDiff Classical
variable {I Y:Type} {G:Gauge}{K:KernelChoices} {a:Ask}{N:Names G K}{P:Hol G}{F:Frames G}{Ω:∀ i, SectionData (F.level i)}{b:Dialect P Ω N a} {p:Finset (Fin a.n)}
section Frames
variable (G N b)
-- explicit framing rate, Money independent of actual Kin choices/levels.
def oilZ (G:Gauge)(d:ℕ)(X:RG.Stage)(s:ℝ)(hp:0<s):= (Spills.quote G d X s hp).choose
def oilY (G:Gauge)(d:ℕ)(X:RG.Stage)(s:ℝ)(hp:0<s):= (Spills.quote G d X s hp).choose_spec.choose
-- canonical in the exact alpha palette
variable {G}
abbrev oilW (N:Names G K)(d e i:ℕ)(X:RG.Stage):= oilZ G d X ((N.act e).η i) ((N.act e).positive i)
abbrev oilM (N:Names G K)(d e i:ℕ)(X:RG.Stage):= oilY G d X ((N.act e).η i) ((N.act e).positive i)
def paintsP (N:Names G K)(a:Ask):Need:=⟨fun _=>0,fun _ i _ Z=>max (oilM N a.vac a.E i Z) (oilW N a.vac a.E i Z)⁻¹⟩
end Frames
-- style relief Fin sum. request sectors for Mark set T,k in 0..τ, q≤ k+E.
structure Coin (a:Ask) where
    T:Finset (Fin a.n)
    p:↥T
    k:Fin (a.τ+1)
    q:Fin (k.val+a.E+1)
-- construct Fintype, private proof-independent cost
instance (a:Ask) : Fintype (Coin a) := by
    let T:=Σ t:Finset (Fin a.n), (Σ k:Fin (a.τ+1),Fin (k.val+a.E+1)) ×↥t
    let e:T≃ Coin a:= ⟨fun t=>⟨t.1,t.2.2,t.2.1.1,t.2.1.2⟩,fun v=>⟨v.T,⟨v.k,v.q⟩,v.p⟩,fun _=>rfl,fun _=>rfl⟩
    exact Fintype.ofEquiv T e

namespace Coin
variable (b)(p:Coin a)
def heightP (i:ℕ) := (Dart.coin_pre p.T p.p p.k a.E p.q (Nat.le_of_lt_succ p.q.isLt) (b.w i) (b.rain i) G a.R a.D).choose
def priceP (i:ℕ) := (Dart.coin_pre p.T p.p p.k a.E p.q (Nat.le_of_lt_succ p.q.isLt) (b.w i) (b.rain i) G a.R a.D).choose_spec.choose
lemma pins (i:ℕ): 0<heightP b p i ∧ heightP b p i ≤ b.w i ∧ 0≤priceP b p i ∧ ∀ (U:Layouts (Fin a.n) G a.D a.R)(w:Fin a.n→ℕ)(B:ℝ), Sense w U → p.k.val=vanes w p.T → (∀ j≤ a.E,∀ k, Owns (b.w i) p.T (fun x=> U x p.T j k) B) → ∃ S:Dart.Ample p.T G a.D a.R,Armor (Dart.moneyP U w p.p p.q.val) (p.k.val-p.q.val) (p.k.val+a.E-p.q.val+1-(p.k.val-p.q.val)) S (heightP b p i) (B*priceP b p i) := (Dart.coin_pre p.T p.p p.k a.E p.q (Nat.le_of_lt_succ p.q.isLt) (b.w i) (b.rain i) G a.R a.D).choose_spec.choose_spec
end Coin
def marshP (b:Dialect P Ω N a)(p:Coin a):Need:=⟨fun _=>0,fun _ i _ _=>max (p.priceP b i) (p.heightP b i)⁻¹⟩
def skinT (b:Dialect P Ω N a): Need:= (paintsP N a).brings (Need.basket (marshP b))

variable {X:Levels G}{N:Names G X.clock.kernel}{b:Dialect P Ω N a}{D:ChartRatio G}{ν:G.ColorIndex}
local notation "Y" => Chain.actual X
variable {u:I→Windows}
local notation "ξ"=> Launch.farY (u:=u) Y

structure Tincture (b:Dialect P Ω N a)(u:I→Windows): Prop where
    wash : Weighed (Launch.farY (u:=u) (Chain.actual X)) fun i=> (oilW N a.vac a.E (X.clock.J i.i) (X.clock.params i.i))⁻¹
    earns : Weighed (Launch.farY (u:=u) (Chain.actual X)) fun i=> oilM N a.vac a.E (X.clock.J i.i) (X.clock.params i.i)
    fits (p:Coin a): Weighed (Launch.farY (u:=u) (Chain.actual X)) fun i=> (p.heightP b (X.clock.J i.i))⁻¹
    rate (p:Coin a): Weighed (Launch.farY (u:=u) (Chain.actual X)) fun i=> p.priceP b (X.clock.J i.i)

lemma paths_in (hp:G.Simple)(hV:NearZ X u)(hv:∀ k, Affords (skinT b) X (u k).start): Tincture b u:= by
    have hb k:= (hv k).of_sub (Need.Higher.front ..)
    have hh k p:= Need.basket_affords _ ((hv k).of_sub (Need.Higher.back ..)) p
    refine ⟨Affords.cash_w hp hV hb (fun i=>?_) (fun i=>?_), Affords.cash_w hp hV hb (fun i=>?_) (fun i=>?_), fun p=> Affords.cash_w hp hV (fun k=> hh k p) (fun i=>inv_nonneg.mpr (p.pins ..|>.1.le)) (fun i=>le_max_right ..),fun p=> Affords.cash_w hp hV (fun k=>hh k p) (fun i=> p.pins ..|>.2.2.1) (fun i=>le_max_left ..)⟩
    · exact inv_nonneg.mpr ((Spills.quote _ _ _ _ ((N.act a.E).positive _)).choose_spec.choose_spec.1.le)
    · exact le_max_right ..
    · exact (Spills.quote _ _ _ _ ((N.act a.E).positive _)).choose_spec.choose_spec.2.1
    exact le_max_left ..
-- analogue of reserves using these widths
lemma oilS (Z:Names G X.clock.kernel){H:Horizon X}{S:Supply.Sheet G}{M:Rolls S}{Q:Kin H D}{A:PostCost M}(hD:Q.Planned A)(ν:G.ColorIndex)(a:Ask) : ∃ V:Spills.Reserves ν hD (Z.act a.E).η a.vac, V.tariff=(fun i=> oilM Z a.vac a.E i (X.clock.stage i)) ∧ V.venue=(fun i=> oilW Z a.vac a.E i (X.clock.stage i)):= by
   refine ⟨⟨_,_,fun i=>(Spills.quote G a.vac (X.clock.stage i) _ ((Z.act a.E).positive i)).choose_spec.choose_spec.2.1,fun i=>(Spills.quote G a.vac (X.clock.stage i) _ ((Z.act a.E).positive i)).choose_spec.choose_spec.1,fun N i hp he hz =>?_⟩,rfl,rfl⟩
   intro a' R Ω Z' V B H hA HZ
   let Z'':= Chain.actual X
   have hx:= Chain.wake_actual X
   obtain ⟨hv,hP,hX⟩:= Z''.high_stocks ν N i
   have HV:= Z''.packing ν D hx hz hp
   apply (Spills.quote G a.vac Ω _ ((Z.act a.E).positive (X.clock.J i))).choose_spec.choose_spec.2.2 _ _ _ _ H ?_ hA _ HV.gets hv (hD.cap _ _ hp) HZ HV.opens
   swap
   · exact fun m=> Canon.rides (hD.cap N i hp) (planned_pay hD ν he hz N i hp) (Chain.side_infinite X.S i) hv hP HV.gets m
   unfold Calendar.loopCap Calendar.monitor; positivity
end YM.RG08.Admission
