import YM.FullVolume.Tess.BarsP
/- Acquire tariff & eventual canopy budgets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "X"=> R.kit
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
local notation "S"=> R.alloy.B.a.S
open MergeProof.Ribbons Next.Rank Next.Rank.Spindle
namespace Face
open Metric
open Ray
variable {W:Pillars R T}{p:ℕ}
local notation "P!"=>R.alloy.B.a
namespace Fan
variable (F:Fan T W p){n:ℕ}(V₀:Fin n→ R.family.book.Token)
local notation "δ"=> intervalClock R
local notation "a"=> R.family.S.a
variable (l:List (MotionIndex n))
-- kFilm along F.Real; goal slope Astronomy.
abbrev kFilm (N:ℕ)(s:sun): Positions n→ℂ:= gKernel ((F.film s).V T W) V₀ l N p
structure Pledge (w:sun)(K:Set (Points n))(L v:ℝ):Prop where
   rates : 0≤ L
   quiet : 0 < v
   paths : ∀ᶠ N in atTop,∀ x y:Positions n,tag (R.family.S.a N) x∈K → dist (tag (R.family.S.a N) y) (tag (R.family.S.a N) x) ≤ v→ ∀ s:sun, dist (kFilm F V₀ l N (scaleSun w s) y) (kFilm F V₀ l N (scaleSun w s) x)≤ L*dist (tag (R.family.S.a N) y) (tag (R.family.S.a N) x)
variable {K:Set (Points n)} (hV:IsCompact K) (h: K⊆ NoHit R.alloy.B.a.S p n)
variable (H:T.Winter) (h':Jams.Wild R.kit.shape R.alloy.delay)
include H h' h hV
lemma pledged :∃ (w:sun)(L r:ℝ),0<w.val ∧ Pledge F V₀ l w K L r:=by
     obtain ⟨c,hc,t,B,ht,hB,hL⟩:= ((show ∀ᶠ c:ℝ in 𝓝[>] 0,0<c from self_mem_nhdsWithin).and (Face.living T W H h' p K V₀ l hV h)).exists -- order
     obtain ⟨w,hΩ,hφ⟩:= F.amenable c hc
     exact ⟨w,B,t,hΩ,hB,ht,hL.mono fun N hL x y hz hv s=> hL (F.film (scaleSun w s)) (hφ N s) x y hz hv⟩
omit H h' h hV
namespace Pledge
variable {L r:ℝ}{w:sun}(h₁:Pledge F V₀ l w K L r)
include h₁
lemma restrict (u:sun) : Pledge F V₀ l (scaleSun u w) K L r:=by
    refine ⟨h₁.rates,h₁.quiet,h₁.paths.mono fun N hc x y hz ht s=>?_⟩; rw [← px]; exact hc x y hz ht _
lemma lived : ∀ᶠ j:ℕ in atTop,∀ N,∀ (hm:j ≤ N)(x:Positions n),tag (R.family.S.a j) x∈K → ∀ s:sun,
     dist (swellK F V₀ w j N hm l s x) (kFilm F V₀ l N (scaleSun w s) (ascending (S) p hm x)) ≤ L*(l.length * R.family.S.a j):=by
    obtain ⟨m,hV'⟩:=eventually_atTop.mp h₁.paths
    have hv: Tendsto (fun j=> (l.length:ℝ)*(a j)) atTop (𝓝 0):=by simpa using (R.family.S.shrinks.const_mul (l.length:ℝ)) -- S=C.F defeq
    filter_upwards [eventually_ge_atTop m, hv.eventually (ge_mem_nhds h₁.quiet)] with j hj hf₁ N hm x hz s
    apply fareWarp (S) hm _ _ x _; intro y ht
    have hp:=(hV' _ (hj.trans hm)); let X':= ascending (S) p hm x; have hX:tag (a N) X'=tag (a j) x:= arrivesP (S) p hm x
    have hu: tag (a N) X' ∈ K:= hX.symm ▸ hz
    have h_:dist (tag (a N) y) (tag (a N) X') ≤ l.length*(a j):= by rw [hX]; exact ht
    exact (hp X' y hu (h_.trans hf₁) s).trans (mul_le_mul_of_nonneg_left h_ h₁.rates)
lemma payCost (t:ℝ)(ht:0≤t):∃ M:ℝ,0≤M∧ ∀ᶠ j in atTop,∀ N:ℕ,∀ (h₁:j<N)(x y:Positions n),tag (a j) x∈K→tag (a (j+1)) y∈K→dist (tag (a (j+1)) y) (tag (a j) x) ≤ t*(a j)→∀ s:sun,
     dist (swellK F V₀ w (j+1) N h₁ l s y) (swellK F V₀ w j N h₁.le l s x) ≤ M/(δ j) :=by
     let M:= L * (t+2*(l.length:ℝ))
     refine ⟨M,(by unfold M; have hv:=h₁.rates; positivity),?_⟩
     obtain ⟨k,hk⟩:= eventually_atTop.mp ((h₁.lived F V₀ l).and h₁.paths) -- ordering
     have hp:Tendsto (fun j=> t*(a j)) atTop (𝓝 0):=by simpa using! (R.family.S.shrinks.const_mul t)
     filter_upwards [eventually_ge_atTop k, hp.eventually (ge_mem_nhds h₁.quiet)] with j hj hT N hN x y hx hy hv s
     let u:= ascending (S) p (j:=j) hN.le x; let z:= ascending (S) p (j:=j+1) hN y; let Q:=kFilm F V₀ l N (scaleSun w s)
     have hu:tag (a N) u= tag (a j) x:= arrivesP (S) p (j:=j) hN.le x
     have hZ:tag (a N) z= tag (a (j+1)) y:= arrivesP (S) p (j:=j+1) hN y
     have hq:= (hk N (hj.trans hN.le)).2 u z (hu.symm ▸ hx) ((hZ.symm ▸ hu.symm ▸ hv).trans hT) s -- inference
     apply (dist_triangle4 _ (Q z) (Q u) _).trans
     rw [hZ,hu] at hq; rw [dist_comm (Q u)]; apply le_trans (add_le_add (add_le_add ((hk (j+1) (hj.trans j.le_succ)).1 _ _ _ hy s) (hq.trans (mul_le_mul_of_nonneg_left hv h₁.rates))) ((hk j hj).1 _ _ _ hx s))
     unfold M; rw [div_eq_mul_inv,show (δ j)⁻¹=a j from rfl]; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((R.family.S.strictAnti j.lt_succ_self).le) (Nat.cast_nonneg l.length (α:=ℝ))) h₁.rates]
end Pledge
variable {v:ℕ→ℕ→ℝ}{Θ:Luna.Tableau T.width 300}(hk:Sky R T Θ v)
include hk H hV h h'
local notation "P₀"=> Beam ℂ
/-- existence with total field of power series. -/
lemma traceS : ∃ (C L r:ℝ) (w:sun) (b:ℕ)(U:ℕ→ℕ→Positions n→ Beam ℂ),0≤C∧0<w.val∧ Pledge F V₀ l w K L r ∧ ∀ᶠ j:ℕ in atTop,∀ N:ℕ,∀ (hn:j ≤ N)(x:Positions n),tag (a j) x∈K → ‖U j N x‖≤ C*δ j^b ∧∀ s:sun, read ℂ s (U j N x)= swellK F V₀ w j N hn l s x:=by
     obtain ⟨b,B,w,hw,hB,hL⟩:=pricedB F V₀ hV h hk l
     obtain ⟨u,L,r,hx,hφ⟩:= pledged F V₀ l hV h H h'
     let v₁:=scaleSun u w; have hz:v₁=scaleSun w u:=Subtype.ext (mul_comm w.val u.val)
     have hq:=hφ.restrict F V₀ l w
     obtain ⟨m,hm⟩:=eventually_atTop.mp hL
     choose! U hU hZ using fun (j:ℕ)(h:m≤ j)(N:ℕ)(hn:j ≤ N)(x:Positions n)(hv:tag (a j) x∈ K)=> (hm j h N hn x hv).arrives
     refine ⟨B,L,r,v₁,b,fun j N x=> Amp.Beam.fit u (U j N x),hB,mul_pos hw hx,hz.symm ▸ hq,(eventually_ge_atTop m).mono fun j hh N hN x hp=>⟨(fitN ..).trans (hU j hh N hN _ hp),fun s=>?_⟩⟩
     rw [fitL,(hZ j hh N hN _ hp _).symm]; unfold swellK; rw [show slash u.val u.property s=scaleSun u s from rfl, px]
end Fan
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.Pledge.payCost
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.Fan.traceS
