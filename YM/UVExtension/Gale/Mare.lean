import YM.UVExtension.Gale.Sheets
import YM.UVExtension.Gale.Tambour
import YM.UVExtension.Gale.Pole
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
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Roost.Factor A}
    (S:Uses X hG) (d N n:ℕ)
variable {a:ℝ}(ha:0 < a)(hp: Metric.ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
set_option quotPrecheck false
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "n0"=> A.B.a.S.side N n
local notation "D"=> Row a
local notation "T"=> desk a ha
local notation "Z"=>Metric.ball (0:ℂ) a
local notation "W₀"=> A.B.a.clock.forcedAllowance N
local notation "p"=> A.B.a.budget N
local notation "O"=> hol G
local notation "V"=> S.cart N n
local notation "H"=> S.fits N n
open Mast Fitted Tabernacle Dales Rafter
open Mast Cellar
variable {t:ℕ→ℕ}{C:ℕ→ℝ}{w:Bid.Worth}(R:Legato.Bandage X C w)
    (U:Cellar S t R)
local notation "s!"=> A.B.a
local notation "r"=> t d
local notation "Φ"=> Cow G (A.B.a.S.side N n) (A.B.a.budget N) d (hol G)
set_option quotPrecheck false
local notation "Q"=> (s!).params
variable (hN:t d ≤ N)
include hp ha R hN U
private lemma charted (v:Keys S): IsLinearMap ℂ (rise S d N n (v N n)):=by
    let T_:= U.cantors v d n; have h:=T_.lyr N hN
    have hx:= h.incomeX N hN le_rfl; rw [h.head] at hx
    exact hx
local notation "Z!"=>Metric.ball (0:ℂ) a
set_option maxHeartbeats 440000 in
lemma cloudy : ∃ g:ℂ→ Card (s!) (F) O n N, (∀ (b:Row a) x, g (b.val:ℂ) x =rise S d N n (realK S ha hp b) x) ∧ (∀ z∈ ball (0:ℂ) a, Length (F) (g z) (A.B.a.params N).columns)∧∀ x,DifferentiableOn ℂ (fun z=> g z x) Z!:=by
   let f(x:Row a):= rise S d N n (realK S ha hp x)
   have hs(x): IsLinearMap ℂ (f x):= charted S d N n ha hp R U hN (fun _ _=> realK S ha hp x); have he:d ≤ A.B.a.clock.J N:= (le_trans (Nat.le_add_right d _) ((U.posts d).trans (A.B.a.fits.mono hN)))
   choose g hg hL hV using leaves S d N n ha hp R he
   have h(z:ℂ)(hz:z∈Z!): IsLinearMap ℂ (fun i=> g i z):= by
       constructor
       · intro x y; exact Rafter.pair T (g (x+y)) (g x+g y) (hg _) (Lamppost.bends_add (hg _) (hg _)) (fun d=>by rw [hL,Pi.add_apply,hL,hL]; exact (hs d).map_add ..) _ hz
       intro x y; exact Rafter.pair T (g (x • y)) (x • g y) (hg _) (fun _ _ w h v=> (hg y _ _ w h v).const_smul _) (fun d=> by rw [hL,Pi.smul_apply,hL]; exact (hs d).map_smul ..) _ hz
   let Gp(z:ℂ):= if hz:z∈Z! then IsLinearMap.mk' _ (h z hz) else 0
   have hp0 z(hz:z∈Z!) x:Gp z x=g x z:= by unfold Gp;rw [dif_pos hz];rfl
   have hV':2≤ (A.B.a.params N).columns:=by
       have h := R.clock.room N; have hp' := w.prices ((A.B.a.clock.J N)+1); nlinarith
   refine ⟨Gp,fun b x=> (hp0 ((desk a ha|>.call b)) ((desk a ha).within b) x).trans (hL x _),fun z hz i=>?_ ,fun v=>?_⟩
   · rw [hp0 z hz]; exact (hV i z hz).trans (mul_le_mul_of_nonneg_right hV' (size_nonneg ..))
   exact (show DifferentiableOn ℂ (g v) Z! from (hg v Z! id Metric.isOpen_ball (Set.mapsTo_id _) differentiableOn_id)).congr (fun z hz=> hp0 z hz v)
omit hp ha
open Pans
variable (u:ℝ)(v:Keys S)(hu:(v N n).val=u) (Z₀:ℂ→ Card A.B.a ((frames G).level d) (hol G) n N) (Z1:∀ i:ℕ,ℂ→ Banner A.B.a ((frames G).level d) (hol G) n i)
    (hx:∀ i,t d ≤ i→i<N→Z1 i (u:ℂ)= U.line d n i N (v N n))(he:∀ x,Z₀ (↑u:ℂ) x=rise S d N n (v N n) x)
local notation "K"=> U.cantors v d n
local notation "V0"=> ((K).song N)
local notation "A!"=> ((K).lyr N hN)
include R hx he hN
set_option maxHeartbeats 550000 in
lemma makes (i:ℕ)(h:t d ≤ i)(hi:i≤ N): fire Z1 N Z₀ i (u:ℂ)= Lyrics.Vista (A!) i :=by
   induction hi using Nat.decreasingInduction with
   | self=>
     rw [up]; apply LinearMap.ext; intro x; rw [he, Lyrics.takes (A!) N hN le_rfl]; change _=terrain (Orchard.Path S v) N n O N (V0|>.tone N) x; rw [show (V0).tone N= TopHat S v d n N from (A!).head]; exact (impart S d N n v x).symm
   | of_succ i hi IH=>
     obtain ⟨ha,hb⟩:= Lyrics.eqst R (U.pay v d n) (A!) i h hi; rw [sail Z1 i N Z₀ hi]; refine Eq.trans ?_ (Eq.symm hb); unfold Gale.beam route; simp_rw [Gale.genes,IH (h.trans i.le_succ),hx i h hi]; rfl
lemma ties (i:ℕ)(h:t d ≤ i)(hi:i<N): turn Z1 N Z₀ i (u:ℂ)= Pans.stalls S v d n K i N:=by
   unfold turn route stalls; simp_rw [Gale.genes,hx i h hi,Pans.base,dif_pos hN,makes S d N n R U hN u v Z₀ Z1 hx he _ (h.trans i.le_succ) hi]; rfl
lemma tendrils (i:ℕ)(h:t d≤ i)(hi:i≤N): tether Z1 N Z₀ r i h u=Pans.feeds S v d n K i N:=by
   induction h with
   | refl=> rw [flipI]; ext x; simp [feeds]
   | step H_ ih =>
      rename_i i; rw [Gale.mirror Z1 N Z₀ r i H_,ties S d N n R U hN u v Z₀ Z1 hx he i (show t d≤ i from H_) hi,ih (le_trans (Nat.le_succ i) hi)]
      apply LinearEquiv.ext; intro x; unfold feeds; exact (LinearMap.congr_fun (Pans.sym S v R d n (U.pay v d n) K i N (by assumption) hi) _).symm
-- actual .terminal. t d references.Beta fields.
lemma height (x: (F).Coeff): (U.gate v d N n|>.terminal).symm x= tether Z1 N Z₀ (t d) N hN u x:=by
    rw [tendrils S d N n R U hN u v Z₀ Z1 hx he N hN le_rfl]
    change _= ((U.cantors v d n).song N|>.tone N).index (((U.cantors v d n).song N|>.tone (t d)).index.symm x)
    rw [show (V0).tone N= TopHat S v d n N from (A!).head,Mast.peak (v:=v) d N n U hN]; try rfl
end YM.UVExtension.Gale
