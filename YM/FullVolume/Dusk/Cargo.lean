import YM.FullVolume.Shroud.Pool
import YM.FullVolume.Dusk.Graff
import YM.FullVolume.Dusk.Albion
import YM.FullVolume.Dusk.Rain
import YM.FullVolume.Dusk.Jaws
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
open YM.MergeProof MergeProof.Accent
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Urns
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} {T:Campaign R} (W:Pillars R T)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
open Spirit Branch
variable {F:∀ p N,Contest N p T.L}(C:Cantata T F)
local notation "H"=> R.alloy.B.bake.make C.q
local notation "R₀"=> R.alloy
local notation "t"=> R.t
local notation "b₀"=> R.b
local notation "φ"=> far L!
local notation "w"=> near L!
local notation "ζ"=> fly L!
local notation "π"=> renal L!
local notation "M"=> mutt L! R.Q
variable (S:Album T W C) (p N i:ℕ)
include W S
open Matric Next.Extract
local notation "Z!" => Album.family T W C S
theorem ridgeT : Mauve (Album.family T W C S) R.w φ (waybill L!) w π ζ M (doorT C)∧ Fridge Z! φ ζ ∧ (∃ (V:∀ d:ℕ,SectionData ((Labels.frames G).level d)) (Y:Push.Mark.Weave G), ∃ P b,(∀ d:ℕ,Push.Mark.Portfolio (hol G) (V d) (Y d)) ∧ Hearthside Z! V Y P b ζ) ∧ Extraction.Wcmain Z!:=by
    have hx:= R.again T.gains.SimpleR|>.1; let hG:=T.gains.SimpleR; have hm:= S.makes T W C
    obtain ⟨hp,hP,hα,hβ,hγ,hΨ,⟨cost,D,V,Y,hc,hv,hY,hD⟩,hF⟩:= R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
    let J:=R.alloy.B.a.clock.J
    have hW(i:ℕ)(d:ℕ)(he:R.t d ≤ i):d+3  ≤  J i:= (R.accepts d).trans ((L!|>.fits.mono) he)
    have hu (i:ℕ)(d:ℕ)(he:d  ≤  J (i+1)):= hY d (J (i+1)) he _ ((hD _).trans (R.rolls.large (J (i+1))).need)
    have hw(i):= hc _ _ (step_paid _ i) _ ((K!|>.valid.pays) i)
    have hs:Mauve Z! R.w φ (waybill L!) w π ζ M (doorT C):=by
      refine ⟨fun p k n h=> ponds W C S p n k h,W.late,hx.scrim.back,hx.scrim.grows,hx.scrim.jump,fun d N p m h he=>?_⟩
      let U:= (C.mat N p).steps m ((W.late d).trans h) he; obtain ⟨G',V,hV⟩:= (Boutique.tickets hG R.b U (C.mat N p).choice (hW m d h) R.tuning.receipts).chamber
      rw [doorT,dif_pos ((W.late d).trans h)]
      refine ⟨_, Matric.Tool.tuneR _ _ _ _ _ _ _ hV ?_⟩
      change (1+2*(R.alloy.B.a.params m).columns)*Doors.rate (R.alloy.B.a.S.block m) ≤ Bid.barunit (R.alloy.B.a.S.block m); rw [params_eq R.alloy.B.valid, Extra.Iteration.block_eq R.alloy.B.valid]; exact (hu m 0 (Nat.zero_le _)).2.2.2 _ (L!|>.fits.mono m.le_succ)
    have hfr : Fridge Z! φ ζ:=by
       refine ⟨fun n p=> ?_,hx.fridge.candle,hx.fridge.path,hx.fridge.smoke,hx.fridge.shifts⟩
       rcases n with _ | n
       · have ht:= hx.fridge.full 0 p; change Nonempty (Guard.Keeper (C.q 0 p 0).p (C.q 0 p 0).activities); rw [C.zero]; exact ht
       exact ⟨Guard.Keeper.sufficient ((C.mat (n+1) p).slots (n+1) (by omega) le_rfl)⟩
    refine ⟨hs,hfr,?_,?_⟩
    · obtain ⟨P,b,hb⟩:= fireguard hm (C:=Album.family T W C S) hx.tabs hs hfr V Y hv hG (by
         intro d; let b:= fun i=> cost d (J i)
         have h₀ : ∀ᶠ i:ℕ in atTop, ∃ j,i=j+1∧ d ≤ J (j+1) := by
            filter_upwards [eventually_gt_atTop (R.t d)] with i hi; obtain ⟨j,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0); exact ⟨j,rfl,(Nat.le_add_right d 3).trans (hW (j+1) d hi.le)⟩
         refine ⟨b,⟨?_,?_,?_⟩⟩
         · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; change Bid.Credit _ (R.alloy.B.a.params _|>.order) (R.alloy.B.a.params _|>.power) _; rw [params_eq R.alloy.B.valid]; exact (hu j d h).2.1
         · filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi; exact ⟨(hu j d h).2.2.1, (hw (j+1)).2 d h |>.1⟩
         filter_upwards [h₀] with i hi; obtain ⟨j,rfl,h⟩:=hi
         change 2*(1+(R.alloy.B.a.params _|>.columns))*sphere (R.alloy.B.a.params _) ((V _).stencil∪(localSection G _).stencil).card (b _) ≤ Bid.puffs (R.alloy.B.a.S.block _)*sliver (Labels.frames G|>.level d)
         rw [params_eq R.alloy.B.valid,show j+1-1=j from rfl, Extra.Iteration.block_eq R.alloy.B.valid]; exact (hu j d h).1)
      exact ⟨V,Y,P,b,hv,hb⟩
    exact oboes _ hx.tabs hm hs hs.back hG hp.reception.2.2.1
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.ridgeT
