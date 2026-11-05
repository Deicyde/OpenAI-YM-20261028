import YM.MergeProof.West.Esme
import YM.TraceExtension.Prom.Sway.Dol
import YM.TraceExtension.Prom.Sway.Sushi
import YM.TraceExtension.Prom.Front.West.Brite
import YM.TraceExtension.Prom.Front.West.Coke
import YM.TraceExtension.Prom.Front.West.Cream
import YM.TraceExtension.Prom.Front.West.Equity
import YM.TraceExtension.Prom.Front.West.Jolly
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Pilgrim
import YM.TraceExtension.Prom.Hill.Promises
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.TableGate
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.MergeProof.West.Esme for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter Paint Vac.Numbers Prayer Glimmer Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{N n p k m u D:ℕ}{ξ:Purse}{R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s z:ℝ}{Ψ:AtlasData G C.S p}
section
variable (A:Levels G){x : Points n} {K:Set (Points n)}
set_option linter.unusedVariables false

end
variable {K:Set (Points n)} {d:ℕ}{d0:Fin n→ℕ}(h:∀ i,d0 i≤ d)(w:(i:Fin n)→ C.label (d0 i))
set_option quotPrecheck false
local notation "AΩ" => C.path.levels
structure WallsSky (b:ℝ)(h:∀ i,d0 i ≤ d)(w:(i:Fin n)→ C.label (d0 i))(K:Set (Points n))(D k:ℕ):Prop where
   merry (x:Points n)(hx:tested C.path.levels b k x ∈ K): BalconSky b h w x k D
   replies x : tested C.path.levels b k x∈K →∀ hk:FitSky C.path.levels b k x, AllowedSky C.path.levels b k →
       (∀ p N (hN:k≤N),Spaced (scouts C k) (seatsSky C b x hN p)) ∧
       ∀ p Ψ,Wall.VantageSky C.path.levels d k p n D b Ψ → BellSky C.path.levels Ψ d D hk
lemma mural_castSky (hK:IsCompact K)(hx:K ⊆ conf _)(H:C.Makes)(he:G.Simple) (b:ℝ)(hb:6 ≤ b)(hs:∀ i,saves C (d0 i)+3 ≤ b) (D:ℕ) (I:ℕ→ℝ)(hL:∀ i,b ≤ I i)(β:ℝ)(hU:∀ i,I i ≤ β) : ∀ᶠ k in atTop,WallsSky (I k) h w K D k:=by
   let Y (k:ℕ) x:= tested AΩ (I k) k (x:Points n); have hr:0 < b:=by linarith
   have hp:∀ᶠ k in atTop, ∀ x:Points n, Y k x∈K→ BalconSky (I k) h w x k D:=by
      apply maxim hK; intro x hg ζ hz v hV; let W:=jointX w
      have he' := hx hg
      filter_upwards [hz.eventually (passingX_allSky he H D h w),clockwiseXSky D AΩ he hr x he' ζ hz v (I ∘ ζ) (fun i=> hL (ζ i)) hV d,coughXSky (C:=C) he x he' W ζ v (I ∘ ζ) hz hV,
         Glimmer.accumulate ℕ atTop (fun i=> Read.maxProfile C (Y (ζ i) (v i)) W) (Read.maxProfile C x W) (profile_tends _ _ (Maxwell.table_smooth C.labels) he' hV) _ ((hat_rate AΩ he).comp hz)] with k H1 H2 H3 H4
      exact ⟨H1 (I (ζ k)) (hr.le.trans (hL _)) (fun i=> (hs i).trans (hL _)),H3,H2,H4⟩
   let V k (x:Points n) (h:FitSky C.path.levels (I k) k x) : Prop := AllowedSky C.path.levels (I k) k →
       (∀ p N (hN:k≤N),Spaced (scouts C k) (seatsSky C (I k) x hN p)) ∧
       ∀ p Ψ,Wall.VantageSky C.path.levels d k p n D (I k) Ψ → BellSky C.path.levels Ψ d D h
   have hz:∀ᶠ k in atTop,∀ x:Points n, Y k x∈K→ ∀ h, V k x h:=by
      apply maxim hK; intro x hg ζ hz v hV; filter_upwards [Wall.on_holdSky AΩ b D d he (hx hg) hb ζ hz v (I ∘ ζ) (fun i=> hL (ζ i)) β (fun i=> hU (ζ i)) hV,Edition.riseXSky C x he (hx hg) hr ζ v (I ∘ ζ) (fun i=> hL (ζ i)) hz hV] with k hC HH h1 h2
      exact ⟨HH h1 h2,hC h1 h2⟩
   filter_upwards [hp,hz] with k hP hV
   exact ⟨hP,hV⟩
end YM.Next.Rank.Tapes.West
