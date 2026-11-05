import YM.UVExtension.Gale.Shard
import YM.UVExtension.Gale.Eddy
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{s:Levels G}{n N r k:ℕ}
variable (L:∀ i:ℕ,ℂ→ Lacing.Banner s F A n i)
local notation "O'"=> s.clock
local notation "D"=> F.Coeff
local notation "H"=> Lacing.Card s F A n
local notation "X₀"=> s.params
local notation "l'"=> s.S.block
local notation "κ"=> s.clock.forcedAllowance
local notation "S"=> s.S
local notation "g₀"=> fun i=> Lacing.glaring s i n
variable (i N:ℕ)
noncomputable def route (z:ℂ)(μ:Motion):= L i (Eyelet.gazeH μ z)
local notation "X1"=> RestA -- abbrev check
noncomputable def beam (Z:ℂ→ Lacing.Card s F A n (i+1))(z:ℂ): H i:= Lacing.crown (route L i z) (fun m=> Z (gazeH m z)) (Lacing.glaring s i n)
noncomputable def fire (U:ℂ→ Lacing.Card s F A n N)(i:ℕ)(z:ℂ):H i:= if h:i≤ N then (Nat.decreasingInduction (motive:=fun i _=> ℂ→ H i) (fun k hk X=> beam L k X) U h) z else 0
variable (U:ℂ→ Lacing.Card s F A n N)
lemma up : fire L N U N=U:=funext fun z=> by rw [fire,dif_pos le_rfl,Nat.decreasingInduction_self]
lemma sail (h:i < N): fire L N U i = beam L i (fire L N U (i+1)) := by
   ext1 z; unfold fire; simp_rw [dif_pos (show i+1≤ N from h),dif_pos h.le,Nat.decreasingInduction_succ_left _ _ h h.le]
noncomputable def turn (i:ℕ)(z:ℂ):= steer (route L i z) (fun m=> fire L N U (i+1) (gazeH m z)) (Lacing.glaring s i n)
variable (u v c w:ℕ→ℝ)
-- w both. 'forms Bond currently use constant s schedule maps' includes <N.
structure Rotor (s:Levels G)(F:Frame G d)(A:Hol G)(n N r:ℕ)(a:ℝ)(L:∀ i:ℕ,ℂ→ Lacing.Banner s F A n i)(u v c w : ℕ→ℝ) : Prop where
   opens : 0<a
   quiet (i:ℕ)(hi:r ≤ i): Tollgate F (u i) (v i) (c i) (w i) (w (i+1))
   tiny i (hi:r ≤ i): 256*c i*u i*w (i+1) ≤ 1 -- ℓ1 seed y estimate.
   busy (i:ℕ)(hi:r ≤ i)(hv:i<N): ∃ T: Heading F, (∀ z∈Metric.ball (0:ℂ) a,Tips (L i z) (s.S.block i) T (u i) (v i))∧ ∀ x,F.coeffSize (T.map x) ≤ c i*F.coeffSize x∧ F.coeffSize (T.map.symm x)≤ c i*F.coeffSize x
   wheels i(hi:r ≤ i)(hv:i<N): Rains (ball 0 a) (L i)
variable {i N u v c w L}{a:ℝ}
local notation "Z"=> ball (0:ℂ) a
variable (R:Rotor s F A n N r a L u v c w)
variable (hW:∀ t∈Metric.ball (0:ℂ) a, Length F (U t) (w N))(hU:∀ x, DifferentiableOn ℂ (fun z=> U z x) (Metric.ball 0 a))
include R hW hU
set_option maxRecDepth 8192
set_option maxHeartbeats 640000
lemma framed (i:ℕ)(hi:r≤ i)(h:i≤ N): (∀ t∈Z, Length F (fire L N U i t) (w i))∧ ∀ x:ℂ→F.Coeff,DifferentiableOn ℂ x Z→ DifferentiableOn ℂ (fun z=> fire L N U i z (x z)) Z:=by
   induction h using Nat.decreasingInduction with
   | self=> rw [up]; exact ⟨hW,fun x he=> (curtains (fun z=> (U z).toContinuousLinearMap) hU).clm_apply he⟩
   | of_succ i hk ih=>
      obtain ⟨T,hT,hV⟩:= R.busy i hi hk; have hs:=hi.trans i.le_succ; obtain ⟨hy,hb⟩:= ih hs; rw [sail L i N U hk]; constructor
      · intro t ht; exact Lacing.brunt (R.quiet _ hi) (fun m=>hT _ (Gale.rises m t ht)) hV (fun m=> hy _ (Gale.rises m t ht)) (glaring s i n)
      intro x hv; exact (clippers R.opens (R.wheels i hi hk) hT (P':=fire L N U (i+1)) (glaring s i n) (R.quiet _ hi) hV hy (fun x=> hb _ (differentiableOn_const _)) x hv).2.2
lemma arcs (i:ℕ)(hi:r≤ i)(h:i<N)(x:ℂ→ F.Coeff)(hv:DifferentiableOn ℂ x (ball 0 a)): DifferentiableOn ℂ (fun z=> turn L N U i z (x z)) (ball 0 a) ∧ DifferentiableOn ℂ (fun z=> (turn L N U i z).symm (x z)) (ball 0 a):= by
   obtain ⟨T,hT,hP⟩:= R.busy i hi h; obtain ⟨hy,hb⟩:= framed U R hW hU (i+1) (hi.trans i.le_succ) h; obtain ⟨ht,hq,_⟩:= clippers R.opens (R.wheels i hi h) hT (P':=fire L N U (i+1)) (glaring s i n) (R.quiet _ hi) hP hy (fun x=> hb _ (differentiableOn_const _)) x hv; exact ⟨ht,hq⟩
lemma funds (i:ℕ)(hi:r≤ i)(h:i<N) {z:ℂ}(hz:z∈Metric.ball 0 a)(x):(F).coeffSize ((turn L N U i z).symm x) ≤ 2*c i*F.coeffSize x:=by
   obtain ⟨T,hT,hP⟩:= R.busy i hi h; obtain ⟨hy,hb⟩:= framed U R hW hU (i+1) (hi.trans i.le_succ) h
   let P' m:=fire L N U (i+1) (gazeH m z); let w' i:= L i; let U_:=turn L N U i z; let t':= glaring s i n
   have hp:= R.quiet i hi; have h0 m := hT _ (Gale.rises m z hz); have hs m:= hy _ (Gale.rises m z hz)
   have hg : major (route L i z) P' t' (U_.symm x)= x:= by rw [← focal (L:=route L i z) (Y:=P') hp h0 hP hs]; exact U_.apply_symm_apply _
   have he:= Lacing.Gate (L:=route L i z) (Y:=P') hp h0 hP (fun m=> hs m) t' (U_.symm x)|>.1; rwa [hg] at he
end YM.UVExtension.Gale
