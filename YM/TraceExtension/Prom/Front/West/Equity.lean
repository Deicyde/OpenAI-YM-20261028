import YM.MergeProof.West.Equity
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.Mallow
import YM.TraceExtension.Prom.Front.West.Mooncake
import YM.TraceExtension.Prom.Front.West.Residual
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.LedgerGate
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Pilgrim
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Stepped
import YM.TraceExtension.Prom.Hill.TableGate
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Soft.Coupons
import YM.TraceExtension.Prom.Port.Soft.Denarii
import YM.TraceExtension.Prom.Port.Soft.Diana
import YM.TraceExtension.Prom.Port.Soft.Supra
/-!
  Variant of YM.MergeProof.West.Equity for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter Paint Vac.Numbers Prayer Glimmer Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{N n p k m u D:ℕ}{ξ:Purse}{R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s z:ℝ}{Ψ:AtlasData G C.S p}
section
variable {x:Points n} {d0:Fin n → ℕ}(h:∀ i,d0 i ≤ D) (w v:(i:Fin n)→ C.label (d0 i))

local notation "D'"=> C.path.levels
local notation "γ"=>clim C.path.levels k
local notation "b"=> ξ.band
set_option quotPrecheck false
structure BalconSky (s : ℝ)(h:∀ i,d0 i ≤ D)(w:(i:Fin n)→ C.label (d0 i))(x:Points n)(k d:ℕ):Prop where
  passes : passingX h w k d s
  route : sufficientlySky C (jointX w) s x k
  pends (g:FitSky C.path.levels s k x):
    let t:=clim C.path.levels k
    Prayer.Meridian D (Ship.fittingSky g) (G:=G) (fraction n d t) (fraction n d t) (bill (-3) t) (bill (fuel d n) t)
        (bill (-2) t) (Station.mag D' s k) (lengthW t)
  mind : let t:=clim C.path.levels k; ∀ q P F, Expands P q → Expands F (Read.maxProfile C (Station.tested D' s k x) (jointX w)) →
          (∀ z, ‖q.part z-(Read.maxProfile C (Station.tested D' s k x) (jointX w)).part z‖ ≤ bill (-3/2) t) →
            ‖P-F‖+bill (-3/2) t ≤ bill (-31/32) t
lemma x_crushedSky (Z:BalconSky b h w x k ξ.taylor) (g:FitSky D' b k x) (hB:BellSky D' Ψ D ξ.taylor g)
   (Xg:CeremonySky ξ c P R Ψ) (F:(i:Fin n)→ StampDuty C k N p (d0 i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
   (he:∀ i,Price.Solves C (mag D' b k) (d0 i) k N p (F i).T (w i) (v i))
   (hp:ChastSky P c Ψ x (fun i=>prefaced (F i) (v i) (Station.choose D' b k x i)) ξ u (IssuedXSky C b x c.allow p v)):
      ArrangementsSky c.allow c P (jointX w) (q_asked (C:=C) v) g ξ.era.coast u := by
  let A0:= C.path.levels; let T:= Ship.yardSky C b c.allow p; let S := clim A0 k
  let s:= Station.choose D' b k x
  let f:= Ship.targetsSky C (jointX w) g
  intro hv hs; obtain ⟨α,β,bα,bβ,H,K,W,h1,hbg,h2,h3,h4⟩ := hp hv hs
  refine ⟨α,β,bα,bβ,H,K,W,h1,hbg,h2,fun i => ⟨(h3 i).1,(h3 i).2,fun U HH => ?_⟩⟩
  obtain ⟨y,hy,hh⟩ := h4 i.1 U HH
  let V(i):=prefaced (F i) (v i) (s i); let l:=beforeSky D' b k
  let C0:= t_cum (track Ψ) V l y
  have he' : Expands C0 (Answer Ψ s l (fun j=> (F j).heater (v j)) (fun i=>(y i:ℂ))):=by
      have hr: spunW (track Ψ) V l y= Answer Ψ s l (fun j=> (F j).heater (v j)) (fun i=>(y i:ℂ)):= by
         ext i; apply Eq.symm; change _=text y (shelve (track Ψ) l (∏ j ∈ i.val, V j)); rw [forecast]; unfold V; simp_rw [genesis _ _ Xg.invariant]; rfl
      exact hr ▸ expanders (track Ψ) V l y
  have hz : ‖C0-f‖+bill (-3/2) S ≤ bill (-31/32) S:= Z.mind _ _ _ he'
    (Read.cumulative C (Station.tested D' b k x) (jointX w) (Ship.fittingSky g))
    (sizesXSky w g ξ.taylor h c.allow (Z:=fun i=> (F i).heater) (T:=fun i=>(F i).T) (fun i=> (F i).lights) hB _ hy Z.passes v he (Z.pends g))
  let v:= (W i).value U; let z:= Peak.view T f i; let a:= (Array.reorient T i.1 C0).part i.2.val
  change ‖v+z‖ ≤ _
  rw [show v+z=(a+z)+(v-a) by ring]; exact (norm_add_le ..).trans ((add_le_add (honor (C:=C) i.1 _ _ i.2) (hh _)).trans hz)

lemma turns_XSky (hX:AllowedSky D' b k)(H:Tally (wheelSky D' k) γ ξ.era u)(hC:PlesseySky ξ x c P R u) (T:Config G (C.side N p)→ veil (Fin n)) : ExhibitsSky c P b x u c.allow T ξ.era:=by
  intro j hj hp; dsimp only; intro M
  let l:= middleSky D' b k;let y:= γ; let z:=spouse y ξ.era (l-(j+1));
  have hk:z≤ Perch.bill (-1/2) y:= (partner ξ.era (show (l-(j+1)) ≤ more (wheelSky D' k) y from (Nat.sub_le_sub_left (hj.trans (Nat.le_succ _)) l).trans hX.shift)).trans H.growth
  obtain ⟨α,β,hα,hβ,H,K,h,hg,hL⟩:= M; rw [h]; exact (hC.dark j hj hp).rent _ _ _ hα hβ H K z (spouse_pos ..|>.le) hk hL hg
open PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Market Ship
lemma tenderlySky {O:HaarBudget G}(hc:ChargeSky D' b k u O ξ.era)(hZ:bank O D' (widthSky D' b k))(ht:n ≤ u)(V:NylonSky c P Ψ R ξ)(g:FitSky D' b k x)
    (Z:BalconSky b h w x k ξ.taylor)(hX:CeremonySky ξ c P R Ψ)(hB:BellSky D' Ψ D ξ.taylor g)(hC:PlesseySky ξ x c P R u)
   (F:(i:Fin n)→ StampDuty C k N p (d0 i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
   (he:∀ i,Price.Solves C (mag D' b k) (d0 i) k N p (F i).T (w i) (v i))
   (hp:ChastSky P c Ψ x (fun i=>prefaced (F i) (v i) (Station.choose D' b k x i)) ξ u (IssuedXSky C b x c.allow p v))
   (s : modes (Fin n)) (sh : s.val.Nonempty):
    let X:=jointX w; let Y:=q_asked (C:=C) v
    (yardSky C b c.allow p).rootTest (C.beta N p) (fun U=> (invoiceSky X Y g N p U).part s) ≤ Ship.budget D' u k:=by
   intro X Y
   have hM:Peak.InstanceSky c.allow c P ξ.era X Y g u:=⟨x_crushedSky h w v Z g hB hX F he hp,turns_XSky hc.allot.permitted hc.tally hC _⟩
   have hv:Path_Sky c P c.allow b:= fun i h hx=>V.use_ i h (hx.trans (beforeSky ..))
   have he:= v_conditionedSky c.allow c P ξ.era X Y g hc.allot.permitted hv hc.tally hc.assured hM ht Z.route
   exact Soft.couponSky O hc.allot hZ (hv _ le_rfl (widerSky ..)|>.chand) Y X g ht ξ.era.coast.base le_rfl le_rfl he s sh
end
end YM.Next.Rank.Tapes.West
