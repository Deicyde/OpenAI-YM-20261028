import YM.RemainderComparison.Cadenza.Finale
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
import YM.RemainderComparison.Profile.Synod

/-!
# Pre-stage launches for all-order AP proof

* C0 of Quotation(L-independent). Choose caps at program per PRE profiles
 to be consumed after derivative & scalar registration. Only those L with gates
 authorized e.g. inherited nearly-linear assembler. Doesn't assert enough to
 iterate a not-yet-specified reclosure.
* economics Quay in sync AFTER L. No before-L assumption on additional
 analytic envelopes except that compilation does not require *one* field sensor
 priced independently across changing L; that is part of Assembly.LA hypothesis
 to RG02/03 at policy formation. For example Rays standard mark price in memory,
 occupancy & ℓ horizon paid before lifting Scout.
* Program request uniformly for all sufficient cutoffs & periods on literal
 construction use (meeting clock gates). Can compose all previous accepted
 Layer P.Epoch cost claims, not choosing S.M.C again. Needs Pole supplies.
* Reserve standard B+2 refund and high budgets with MARK hulls charged
 stronger. Producer requiring higher support at same stage must check available
 spare and make new demands; doesn't just change prices. Endpoint-Level.N not
 quoted after reclosure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Chron
open Function Filter Set Lattice RG Tree Wilson Supply Input Org Shoot
open Push PriceCompiler Push.AbsoluteSums Gauge Pressure Testing SectorMeasure Precision
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Psalm Next.Scheduling AnalyticBridge VerifiedReset
open Extra.Iteration
open Height Roost
open ConnectedActivityE6
open Cadenza
open JointLoad.Heir.Suite
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {s:Sheet G} {K:MapPrices} {D : Rolls s} {R : Targets s K} {X : Expenses R}
variable {P: Protection D} {p : ℕ →ℝ}{w: Return.Wages}

-- edit Legato import
/-- Any post-L aperture-specific purchases proved successful eventually (need depend on
 pre resource choices and policy), threaded through Chronicle so not
 assuming power-loss at selected coupling. -/
structure Boost (G : Gauge)(L:Side) where
   extra : Cadenza.Quarry→ℝ→Prop
   actually (D:Cadenza.Quarry) (q:ℝ) : Quarry.Financed D G L q→ ∀ᶠ x :ℝ in atTop, extra D x
def Boost.trivial (G:Gauge)(L:Side): Boost G L := ⟨fun _ _=>True,fun _ _ _=>Eventually.of_forall (fun _=>True.intro)⟩
structure Glint (G:Gauge) (L : Side) where
    scope : Cadenza.Scrollwork G L
    propAim : Cadenza.Songbook G L
    grade : ℕ
    order : ℕ -- maximum marks
    reserveK : ℕ
    rank : ℕ
    meter : ℕ
    limit : ℝ
    ξ : ℝ -- expectation/E-crop.S scheduler
    η_goal : ℝ→ℝ
    grant : Reserve G L η_goal
    positive : 0<limit
    border : 0<ξ
    books : Boost G L
structure Firmament (D:Rolls s) where
    count : ℕ →ℕ→ℕ
    slots (j i:ℕ) (s:Fin (count j i)) : Glint G (D.L j)

structure Contemple (G : Gauge) where
    hearth : ℕ→ℕ→RG.Stage→RG.Stage→ℝ -- turnFee grants PRE L
    tolerance (i j : ℕ) (P Q: RG.Stage) : 0 < hearth i j P Q
    epics {s : Sheet G}{D:Rolls s}{K:MapPrices}{R:Targets s K}{X:Expenses R}{p:ℕ→ℝ}{w:Return.Wages}(H: PhysicalNext.Repeat.Register D X w p)(Y:PostCost D)(C:Programs s)(r:ℕ→ℕ→ℕ)(d:ℕ→ℕ→JointLoad.Heir.Record) (h:Protection D): Firmament D
-- edit P param useless
variable (T:Contemple G) (R)
variable (C:Programs s)(r:ℕ→ℕ→ℕ)
local notation "E'" j:max=> (s.profile j)

def squash (P:RG.Stage):=P.supportExponent+2
namespace Glint
variable {P:Teller G}{R:ConnectedActivityE6.Target G P}{ε:ℝ} {F:G.Color} {L:Side}
variable (G':Glint G L) (X:RG.Stage)

def award (ε:ℝ):Rays:=⟨G'.grade,G'.order,G'.meter,G'.reserveK,(max G'.grade G'.reserveK)+1,G'.rank,X.order+(G'.grade+1)+G'.grade+2,X.order,squash X,squash X+1,ε⟩
def partition (a:ℝ):ℝ:= (a-(squash X+1))/4
lemma song (hf:X.supportExponent+3 < ε): (G'.award X (Glint.partition X ε)).Heart X ε:=by
   have hx : X.supportExponent+3=squash X+1:=by unfold squash; ring
   have h : 0 < Glint.partition X ε:=by unfold Glint.partition; linarith
   refine ⟨add_nonneg X.price_pos.le zero_le_two,le_add_of_nonneg_right zero_le_two,le_rfl,h, show squash X+1+3*Glint.partition X ε≤ _ from ?_,le_rfl,Nat.le_refl _,?_ ,?_⟩
   · unfold Glint.partition; linarith only [hx,hf]
   · exact Nat.add_le_add_right (le_max_left ..) _
   exact Nat.add_le_add_right (le_max_right ..) _
end Glint
open JointLoad.Heir.Suite

def Pledge (f:ℕ→ℕ)(C':ℕ→ℕ→ℝ):Prop:=∀ j i, Release.Quotation (C j i) (s.profile i).power (r j i) (s.profile j).supportExponent (squash (s.profile i)) (C' j i) ∧
      (StepStages j i → ∀ L:Side, f j ≤ L.val → Cadenza.Quay (R j i) s.kernel L ∧ Lyric.radiusCost (R j i) L (s.profile j).supportExponent ∧ Release.accepts (r j i) (s.profile j).supportExponent (squash (s.profile i)) L ∧ C' j i / L.val ≤ T.hearth j i (s.profile j) (s.profile i))
private abbrev QuotationStub {Q : RG.Stage} (C : Libretto G Q.order) (r:ℕ)(P' Q' : RG.Stage)(v:ℝ)(k:ℕ)(T:Contemple G)(i j:ℕ):Prop := Release.Quotation C Q'.power r P'.supportExponent (squash Q') v∧ ∀ L:Side,k ≤ L.val → Release.accepts r P'.supportExponent (squash Q') L ∧ v / L.val ≤ T.hearth i j P' Q'

lemma sails (hG:G.Simple)(hr: ∀ i j, 3/8+(R i j).rate<0):∃ f c,Pledge R T C r f c:=by
    have hu (i j:ℕ) (t u : RG.Stage) (C: Libretto G u.order) (r':ℕ):∃ E k,QuotationStub C r' t u E k T i j:=by
      obtain ⟨E,H⟩:= Release.quoting C u.power r' t.price_pos (add_nonneg u.price_pos.le zero_le_two)
      have hN : Tendsto (fun x:ℕ=>E / (x:ℝ)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      obtain ⟨k,h⟩:= eventually_atTop.mp ((hN.eventually_le_const (T.tolerance i j t u)).and ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.atTop_mul_const t.price_pos).eventually_ge_atTop (20*Release.base (squash u) r')))
      exact ⟨E,k,H,fun L he=>⟨(h L.val he).2,(h L.val he).1⟩⟩
    choose f k h using fun j i=> hu j i (s.profile j) (s.profile i) (C j i) (r j i)
    choose g h₁ using fun j i=> Cadenza.buoys (R j i) s.kernel hG (hr j i)
    have he (j i:ℕ): ∃ n:ℕ,∀ L:Side,n≤L.val→ Lyric.radiusCost (R j i) L (s.profile j).supportExponent := by
       have hh:= (R j i).usable; apply Lyric.bidLift (b:=(R j i).ε) _ hh
       have hp: 4*(R j i).ε<(s.profile j).supportExponent:= (R j i).grants.1; linarith only [hh,hp]
    choose n he using he
    let K j:= fromMax g j + (fromMax k j+fromMax n j)
    exact ⟨K,f,fun j i=> ⟨(h j i).1,fun hi L hx=> ⟨h₁ j i _ ((le_fromMax g hi).trans ((Nat.le_add_right ..).trans hx)), he j i _ ((le_fromMax n hi).trans (( (Nat.le_add_left ..).trans (Nat.le_add_left ..) ).trans hx)),(h j i).2 _ ((le_fromMax k hi).trans (((Nat.le_add_right ..).trans (Nat.le_add_left ..)).trans hx))⟩⟩⟩

end YM.RemainderComparison.Chron
