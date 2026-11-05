import YM.MergeProof.Cloudlet


/-!
 # At ATOM REQUEST, withdraw root forecasts AFTER getting λ required.Schedules. Architecture.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Graces
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}(g:G.Simple) {X : Metals G} {D:Rolls X.p} {A:Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n d:ℕ} (hm:m<N) {Z:Bolt A} (h:Nest R Z) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
set_option quotPrecheck false
local notation "O" => (H).rep N n m
local notation "S" => (H).rep N n (m+1)
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "Q'" => R.target j₀ i₀
local notation "P" => X.p.profile i₀
local notation "o" => (0:Site (A.B.a.S.side m n))
local notation "L₀" => D.L j₀
local notation "f₀"=>A.B.a.clock.hatBeta m
local notation "δ" => A.B.a.clock.forcedAllowance m
local notation "ξ" => (R.shape.μ j₀ i₀)
local notation "T₀" => YM.Labels.frames G
local notation "F" => ((YM.Labels.frames G).level d)
local notation "S'" => A.B.a.clock.op m n
variable (hC:Mallow.Arrives R.shape A.delay)(U: Spring R N m n l v Q)(x:Icc l v)
    (he: (Issue.trail Z).rep N n m = U.result x.val) (ht: (Issue.trail Z).rep N n (m+1) = Q x.val) -- careful Hull.L
variable {a:ℝ}{K: ℕ→ℝ} {W:Bid.Worth} (hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
    (hd : d ≤ A.B.a.clock.J m) (T:Cloud (Q x)) (hω: (0:Site (A.B.a.S.side m n))∈T.live.crest.image (A.B.a.clock.op m n).ratio.parent)
local notation "T!" => houseS U x
local notation "V₁" => pupil U x T.live
local notation "V₂" => pupil U x T.pale
set_option quotPrecheck false
local notation "v'" => ((D.L (A.B.a.clock.J (m+1))).val:ℂ)^d
local notation "X!" => Blush.scope (T!) T o
local notation "M" => Blush.screen (T!) T V₁ V₂ v' F
local notation "w" => authors A.B.a m
local notation "κ" => Real.sqrt δ
local notation "fi" => coinFee G P d L₀ -- ambig
local notation "vh" => vigors G P d
include hd hp
include hC h hm g he ht hω hh
-- Main budgets may also consumed for predictive case.
local notation "m0" => (Q x).p.mass T.live.crest T.live.weight
local notation "m1" => Blush.marvel (L:=L₀) (x:=f₀) (Q:=Q') T
local notation "T2" => (T!)
local notation "d'" => (κ)⁻¹*(‖v'‖*(jewelDebt T.live Q' L₀ f₀+jewelDebt T.live Q' L₀ f₀)*straw ξ L₀ G f₀)
lemma suppliesLeaf (e:ℝ)(ha:fi*m0 ≤ e) (hs:∃ s:(houseS U x).fragrances→ℝ, SumBudget (fun i=>Push.Local.reservedMass B (locus T.live (T!) o i) (s i)) e ∧ ∀ i,prince T.live (T!) i → (B).supBounds o (locus T.live (T!) o i) (pane (T!) T v' i) (s i)) {r : ℝ} (hy: e*host G P d ≤ r) : YM.MergeProof.Fancy (localSection G d) H N n m (hol G) T.milk (X!) M 0 (authors A.B.a m) r r:=by
  obtain ⟨hx,hF,hs',hU₁,hR,hv⟩:= attestCard g hm h hC U x he ht hp hh hd T hω hs
  have hB:=ha; have hS:e * host G P d ≤ r:=hy
  have hie : 0 ≤ fi *m0 := mul_nonneg (coin_pos ..|>.le) (T.live.profit.trans ((Q x).p.loMass _ _ T.live.profit))
  have hR:= hR.trans ha; have hv:= hv.trans ha
  have hf:e≥0:= hie.trans ha
  let p:= vh*((‖v'‖*(m1+m1))+e); let t:= P; have hv':0≤p:= (hs'.costs_nonneg (Real.sqrt_pos.mpr (Extra.Histories.forcedPos A.B.a m))).1
  have hu:= hp; have hV:= A.B.a.params m; have hu: (O).p=B:=by rw [he]; rfl
  let a:= vigors G (P) d; let s:= faded (P); let D₁:= Motion.orbitCost ((YM.Labels.frames G).level d)
  have hq : Push.Local.turnCost (O).p.order (O).p.power=s :=by rw [hu,Rain.jersey (A:=A) (m:=m)|>.1,Rain.jersey (A:=A) (m:=m)|>.2.1]; rfl
  have hp : p≤2*|a| * e:=by
     let t1:= ‖v'‖*(m1+m1); have hHp : 0≤a:=by
       have hQ:= (livelyCard hp hd (n:=n)).nonneg; unfold a vigors; unfold authors at hQ; rw [params_eq A.B.valid m] at hQ; unfold Local.factor; exact mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Push.Local.atomPrice_ge_one _ _ hQ))
     change a*(t1+e) ≤ _; rw [abs_of_nonneg hHp]
     have hX : t1+e≤e+e:=by linarith only [show t1≤e from hR]
     refine (mul_le_mul_of_nonneg_left hX hHp).trans ?_; apply le_of_eq; ring
  have hZ:1≤ D₁:=Motion.orbitCost_one_le _; have hd': 0<s:= turnFee_pos (Time.probe t); change e * (1+2*|a| *(1+D₁+|s|)) ≤ r at hS; rw [abs_of_pos hd'] at hS
  refine ⟨p,d',p,hx,hF,hs',hU₁,?_,Or.inr ?_⟩
  · rw [hq]; nlinarith [mul_le_mul_of_nonneg_left hp hd'.le, mul_nonneg (show 0≤ D₁ from by linarith) (abs_nonneg a)]
  change D₁*((F).coeffSize (0-0)+p)≤r; simp only [sub_zero,Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero,zero_add]; nlinarith [mul_le_mul_of_nonneg_left hp (show 0≤ D₁ by linarith)]
end YM.PhysicalNext.Repeat.Graces
