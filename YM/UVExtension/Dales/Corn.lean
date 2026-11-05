import YM.UVExtension.Dales.Pry
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Eagles
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Dales
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Whirl PhysicalNext.Repeat.Graces
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ}{ε : ℝ}
local notation "R₁" => A.B.a.budget (m+1)
local notation "B" => A.B.a
local notation "Y" => A.B.a.clock.hatBeta (m+1)
local notation "Pv" => mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
abbrev Reality (T:Levels G) (m n:ℕ)(d:Cham T m n)(x:Valve m n T d)(β : ℝ): Prop:= β∈RG.Shoot.band T m∧‖place T m n d x‖ ≤1
lemma epoch (T:Levels G) (m n:ℕ)(d:Cham T m n): Reality T m n d 0 (T.clock.hatBeta m):=by have ht:= zero_lt_one.trans (T.fits.delayed m); refine ⟨⟨by linarith,by linarith⟩,by simp⟩
variable (hG:G.Simple) (t:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)
    {x x':Valve (m+1) n A.B.a d} {β β':ℝ} (hx: Reality A.B.a (m+1) n d x β) (hh:Reality A.B.a (m+1) n d x' β')

namespace Tour
def oracle (s:ℝ): Item R (P:= mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0) (N:=N) (mount R N (m+1) n x.val β s):=
    let V:= outset R x.val β s ((tapT (m+1) n B d x).1 hx.2) hx.1 H.hm; ⟨V.choose,V.choose_spec,⟨rfl,rfl,rfl,rfl,rfl⟩,hx.1⟩
def cu := Item.song R H.atTopH H.W H.k (H.oracle R d hx 0)
def bonus := Item.coupon R H.atTopH H.W H.k (H.oracle R d hx 0)
abbrev newB := β+A.B.kin.alpha N m+ H.bonus R d hx
def speck (s:ℝ):= Item.issue R H.atTopH H.W H.k (H.oracle R d hx s)
abbrev cores : Sheath A.B.a m n:= ((H.speck R d hx 0).activities.E,(H.speck R d hx 0).activities.K)
lemma forecast (s:ℝ): Item.song R H.atTopH H.W H.k (H.oracle R d hx s)=cu R H d hx:= sameArts _ _ (A.B.kin.alpha N m) (show KinBase Pv Pv from ⟨rfl,rfl,rfl,rfl,rfl⟩) _ _ rfl rfl _ _ ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
lemma around (s:ℝ): H.speck R d hx s= mount R N m n (H.cores R d hx) (H.newB R d hx) (flatRate A.B.a m n (mount R N (m+1) n x.val β s)):= by
    change Item.issue ..=_; unfold Item.issue Item.first Item.coupon; rw [forecast]; rfl

def rolls (s:Signed)(u:Site (A.B.a.S.side m n)): (Tabernacle.floor (A.B.a.budget m) (cores R H d hx)).Moves s u:= Item.perFinal R H.hm hG t H.atTopH H.W H.k H.hr rfl (H.oracle R d hx 0) (d.maps _ x s _)
include hG t
lemma banking : Tabernacle.rake (A.B.a.budget m) (H.cores R d hx):= by
    exact ⟨_,_,Item.honor R H.hm hG t H.atTopH H.W H.k H.hr rfl (H.oracle R d hx 0)⟩
include hh in
lemma kindred (σ:Signed) (v:Site (A.B.a.S.side m n)): Twins (H.rolls R hG t d hx σ v) (H.rolls R hG t d hh σ v):= by
    let u:= (A.B.a.clock.op m n).ratio.embed v; have he:= d.choice _ x σ u; have hz:=d.choice _ x' σ u
    exact Item.perfect R H.hm hG t _ _ _ H.hr rfl (H.oracle R d hx 0) (H.oracle R d hh 0) _ _ ⟨he.1.trans hz.1.symm,he.2.trans hz.2.symm⟩

def back : Cham A.B.a m n where
    root:= H.cores R d (epoch _ _ n d)
    checks:= H.banking R hG t d (epoch _ _ n d)
    run:= H.rolls R hG t d (epoch _ _ n d)
structure Hind (R:Factor A) (hG:G.Simple) (t:Crest R ε) (H: Tour R N m n ε) (d:Cham A.B.a (m+1) n)(d':Cham A.B.a m n):Prop where
    appointed : d'=H.back R hG t d
lemma admiral {V:Cham A.B.a m n}(he:Hind R hG t H d V): Tabernacle.copied (A.B.a.budget m) V (H.cores R d hx):=by
    rw [he.appointed]; exact ⟨H.banking R hG t d hx,fun s b=> ⟨H.rolls R hG t d hx s b,H.kindred R hG t d hx (epoch _ _ n d) s b⟩⟩
variable {V:Cham A.B.a m n}(he:Hind R hG t H d V)
abbrev royals :Valve m n A.B.a V:=⟨H.cores R d hx, admiral R hG t H d hx he⟩
def choiceV (x:Valve (m+1) n A.B.a d) (β:ℝ): Valve m n A.B.a V:= if hx:Reality B (m+1) n d x β then H.royals R hG t d hx he else 0
def claim (x:Valve (m+1) n A.B.a d) (β:ℝ): ℝ:= if hx:Reality B (m+1) n d x β then H.bonus R d hx else 0
lemma new_mem : ‖place A.B.a m n V (H.royals R hG t d hx he)‖ ≤ 1:= (tapT m n A.B.a V _).mpr (Item.honor R H.hm hG t _ _ _ H.hr rfl (H.oracle R d hx 0))
open Set UVNext.CouplingReset
lemma voy (s:ℝ) (hL : Lives A.B.bake N (m+1) n (mount R N (m+1) n x.val β s)): let Q:= mount R N (m+1) n x.val β s; let u := H.speck R d hx s
    A.B.Move N m n u Q ∧ Accurate A.B R.post N m n u Q∧ Protected R N m n u Q:= by
  intro Q u
  let T:=fun _ : ℝ=> Q; let f:= H.oracle R d hx s; let i:=Icc (0:ℝ) 1
  have h0 : (0:ℝ)∈ i:= left_mem_Icc.mpr zero_le_one; let w:i:= ⟨0,h0⟩
  have hc : Curve (A.B.a.budget (m+1)) T i := by
     refine ⟨continuousOn_const,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,fun ε h x hx=>?_⟩
     filter_upwards with v
     exact ⟨fun _=>0,fun _=>0,fun j=>⟨le_refl _,fun _ _ _ _ _=> by simp [T]⟩, fun i=>⟨le_rfl,by simp [T]⟩,show SumBudget (fun i=> (A.B.a.budget (m+1)).mass (Q.activities.reg i).support 0) ε from (by simp [BudgetPoint.mass, SumBudget,h.le]),by simp [BudgetPoint.mass,SumBudget,h.le]⟩
  obtain ⟨U⟩:= Guild.voyaging R H.hm hG t H.atTopH H.k H.W H.hr (l:=0) (t:=1) zero_le_one T (fun _=>f) hc (fun i hi=> ⟨hL,hx.1⟩) -- t ambiguous
  have hP:u= U.body.result 0:= (U.pay w).symm
  rw [hP]; have hL:= (U.body.moves hG H.hm).2 0 h0; refine ⟨hL.1,?_,0,1,T,U.body,0,h0,rfl,rfl⟩
  rw [show Accurate A.B R.post N m n (U.body.result 0) Q= (|(U.body.result 0).beta - UVNext.CouplingReset.predictor A.B N T 0| ≤ UVNext.CouplingReset.width A.B.a m R.post) from (by unfold Accurate UVNext.CouplingReset.predictor; rw [sub_add_eq_sub_sub])]; exact hL.2.1
end Tour
end YM.UVExtension.Dales
