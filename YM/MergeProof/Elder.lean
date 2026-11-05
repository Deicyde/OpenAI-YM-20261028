import YM.MergeProof.Cloudlet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Fort
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Momentum
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Graces.Upswing


/-!
 # One FULL raw promise issued on regular operand. True supports, PV/Eq. Unit even empties. 
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
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}{B:BudgetPoint}{X:Support c}{f:Config G c→ℂ} {o:Site c}
variable (g:G.Simple) {M : Metals G} {D:Rolls M.p} {A:Alloy M D}
    {R: Factor A} {l v:ℝ} {N m n k d:ℕ} (hm:m<N) {Z:Bolt A} (h:Nest R Z) {Q: In A.B.a m n}
local notation "H" => Issue.trail Z
local notation "i₀" => A.B.a.clock.J m
local notation "j₀" => A.B.a.clock.J (m+1)
local notation "B" => A.B.a.budget m
local notation "ΔB" => A.B.a.budget (m+1)
local notation "L₀" => D.L j₀
local notation "f₀"=> A.B.a.clock.hatBeta m
local notation "P" => M.p.profile i₀
local notation "pT" => R.prices j₀ i₀
local notation "S0" => ships A.B N m n
local notation "N'" => A.B.a.clock.op m n
local notation "O" => Chi.canonical
local notation "V" => A.B.a.S.side m n
set_option quotPrecheck false
local notation "U!" => ((H).rep N n (m+1))
local notation "O'" => ((H).rep N n m)
local notation "ip"=> A.B.a.params m
variable (hC:Mallow.Arrives R.shape A.delay) (hM : Moms R.prices M.K R.span M.p.floorL)(hV: Cruise R.prices D R.recordP R.span R.shape A.delay) (hd:d+3 ≤ A.B.a.clock.J m) {K:ℕ → ℝ}{W:Bid.Worth}(hp : Doors.Budget A.B.a K W)(hh : Comply R.shape A.delay)
include hp hd g hC hM hV hh h hm
variable (ht' : Spring R N m n l v Q)(x':Set.Icc l v)
    (hr : (Issue.trail Z).rep N n (m+1)= Q x'.val) (hℓ: (Issue.trail Z).rep N n m=ht'.result x'.val) (hΘ:HasSlots (Q x'|>.p) (Q x'|>.activities))
include hr hℓ
lemma regularCard (b : Support (A.B.a.S.side (m+1) n)) (c:ℝ)(f:Config G (A.B.a.S.side (m+1) n)→ℂ) (hf: RegFit (Q x') 0 d (hol G) b f)(hB:(Q x').p.supBounds 0 b f c):
    let y:= Doors.rate L₀ *((Q x').p.mass b c)
    let F:= (YM.Labels.frames G).level d
    let T:= float (Q x') 0 b hf.anchor f c hf.smooth hB hΘ
    let U:=houseS ht' x'
    let Pix:= Blush.screen U T (pupil ht' x' T.live) (pupil ht' x' T.pale) (((L₀).val:ℂ)^d) F
    YM.MergeProof.Fancy (localSection G d) H N n m (hol G) (Extra.Histories.salary (Q x') b f) (Blush.scope U T 0) Pix 0 (authors A.B.a m) y y:=by
  intro y FF Tq Uq Pq
  let x:= x'.val; have hx:= x'.property
  let hT:= ht';have hv: O'=hT.result x:= hℓ
  let Y:= Q x
  obtain ⟨hf₀,hb,hZ,ht⟩:= hf
  have he: Y.p.supBounds 0 b f c:= hB
  have hY:Y.p=ΔB:= (hT.knows x hx).1.point
  let T:=float Y 0 b hb f c hf₀ he hΘ
  let U:=houseS hT x'; let k:=found 0 b hb
  have hk:T.live.turn = .logKey k:=rfl; have hi:T.pale.turn=.logKey k:=T.together.symm.trans hk
  have hκ:T.live.weight=c:=rfl
  have hK: Y.activities.reg k=reg 0 b hb:= Blush.latch Y 0 b hb hΘ
  have hc : T.live.crest=b:=by change (Y.activities.reg k).support=b; rw [hK]
  have hy: (plate U k).site=0:=by
     change (N').ratio.parent (Y.activities.reg k).site=0; rw [hK]; let Zp:=(N').ratio; change Zp.parent 0=0; rw [← Zp.root.map_zero]; exact Zp.embed_parent _
  let L:= winG G P d L₀
  let W' := (L*Y.p.mass b c); let F i:= pane U T (((L₀).val:ℂ)^d) i -- fix
  have aim(S: Lotus.Leaf Y)(j:ℂ→L[ℝ] ℝ)(h₁:∀ i, ‖j i‖ ≤ ‖i‖)(hv:S= cove Y 0 b hb f c hf₀ he j h₁ hΘ) :∃ C, (B).supBounds 0 (plate U k).support (matin S U (icon U k) O) C ∧ Push.Local.reservedMass B (plate U k).support C ≤ W':=by -- hh in binding instead
     subst S; let S:=cove Y 0 b hb f c hf₀ he j h₁ hΘ; have hs:S.turn=.logKey k:=rfl
     have hp': S.crest=b:=by change (Y.activities.reg k).support=b; rw [hK]
     let e: ℂ→L[ℝ]ℝ:=j; let f':=e ∘ f
     have htC : S.ingredient = masked Y.p.threshold (Y.activities.reg k).support f':=by
       funext i; change j (masked Y.p.threshold b f i) = _; rw [hK]; by_cases h:Healthy Y.p.threshold b i; exact congr_arg j (masked_eq _ _ _ _ h)|>.trans (masked_eq _ _ f' _ h).symm; change _=masked Y.p.threshold b f' i; rw [masked_ne _ _ _ _ h]; rw [masked_ne _ _ _ _ h,map_zero]
     have hw : Nonwrapping (Y.activities.reg k).support (Y.activities.reg k).site → Peak.lit (Y.activities.reg k).site (Y.activities.reg k).support f' d:=by
       rw [hK]; intro hv
       apply Peak.spoke f e (hol G) b hf₀ (show Nonwrapping b 0 from hv) ((by have := Return.enough_room A.B (m+1) n; omega)) (by
          rw [hY]; have hz:= (hp.stage (m+1)).1; have ht:=step_paid A.B.a m|>.1; exact (by omega : d≤ j₀).trans hz
         ) (le_refl d) (fun j=> (ht hv j).2)
     have hyR : Y.p.Regular (Y.activities.reg k).support f':=by rw [hK]; exact readings e hf₀
     have hyS : Y.p.supBounds (Y.activities.reg k).site (Y.activities.reg k).support f' S.weight:=by rw [hK]; exact pricesL e hf₀ h₁ c he
     obtain ⟨C,hv,hx⟩:= crowning hm hC hM hV (feet hd hp) hT x' S f' k hs hyR htC hyS hw
     exact ⟨C, hy ▸ hv, hx.trans_eq (congr_arg (fun b'=> L * Y.p.mass b' c) hp')⟩
  obtain ⟨Cp,h₁,Hm⟩:= aim T.live Complex.reCLM juror rfl
  obtain ⟨D',h₂,Hn⟩:= aim T.pale Complex.imCLM jurorI rfl
  suffices hy : YM.MergeProof.Fancy (localSection G d) H N n m (hol G) T.milk (Blush.scope Uq Tq 0) Pq 0 (authors A.B.a m) y y from (congr_arg (fun f:Config G (A.B.a.S.side (m+1) n)→ℂ =>YM.MergeProof.Fancy (localSection G d) H N n m (hol G) f (Blush.scope Uq Tq 0) Pq 0 (authors A.B.a m) y y) (Blush.balm Y 0 b hb f c hf₀ he hΘ)).mpr hy
  apply sendsCard g hm h hC hT x' hv hr hp hh (d:=d) (by omega) T (support_zero _ _ (hc.symm ▸ hb)) ?_ (by change _ * Y.p.mass T.live.crest T.live.weight≤ Doors.rate L₀ * Y.p.mass b c; rw [hκ,hc])
  let y':=(‖((L₀).val:ℂ)^d‖*(Cp+D')); have ha:0 ≤ y':=mul_nonneg (norm_nonneg _) (add_nonneg h₁.1 h₂.1)
  refine ⟨fun i=>if i=icon U k then y' else 0,?_,fun p hf=>?_⟩
  · change SumBudget (fun i:U.fragrances=> Push.Local.reservedMass B (locus T.live U 0 i) _) (_*(Q x'|>.p).mass ..)
    let f(p:U.fragrances):= Push.Local.reservedMass B (locus T.live U 0 p) (if p=icon U k then y' else 0)
    have he p (hp:p≠ icon U k):f p=0:=by unfold f; rw [if_neg hp,Push.Local.reservedMass,mul_zero]
    have ht : Summable f:=summable_of_ne_finset_zero (s:={icon U k}) (fun i hi=> he i (by simpa using hi))
    refine ⟨fun i=>?_,ht,(show ∑' i,f i≤ _ from ?_)⟩  
    · change 0 ≤ f i; unfold f; split; exact mul_nonneg (Real.exp_pos _).le ha; rw [Local.reservedMass,mul_zero]
    rw [tsum_eq_single (icon U k) he]; unfold f; rw [if_pos rfl, grinchY U T.live k hk]; unfold Push.Local.reservedMass y'; rw [hκ,hc]
    calc
      _ = (((L₀).val:ℝ)^d)*(Push.Local.reservedMass (B) (plate U k).support Cp+Push.Local.reservedMass (B) (plate U k).support D'):=by unfold Local.reservedMass; simp;ring
      _ ≤ (((L₀).val:ℝ)^d)*(W'+W'):=by gcongr
      _ = _:=by unfold W' L winG; field_simp; ring -- maybe no ring
  have hV : p=icon U k:= (grinch U T.live k hk).2 _ hf; subst p; rw [grinchY U T.live k hk]; simp only [if_true]
  have hp (S: Lotus.Leaf Y)(hk:S.turn= .logKey k): (B).Regular (plate U k).support (matin S U (icon U k) O):=by
     -- retrieve Captain & require Plays or scops
     let v:= step_paid A.B.a m; let N'':=(N'); let p:= hT.knows x hx
     have ih:= hC _ _ (A.B.valid.pays m) _ v|>.1.2; let j:= R.pledging.conducts
     obtain ⟨a,b,y₀,gP,v₀,Y',p',B',g',e,i,hX,hY,N'',hη⟩:=ih _ _ _ _ (Opera.protocol A.B hm j.full (n:=n)) _ _ (houseS hT x')
     have hf:= (Psalm.Stage.directed j.hearing A.B hm p.2 p.1 (fun m' h'=>j.full _ _ _ (by simp at h'; omega))).1.enabled.make
     have hY:Y.p=ΔB:= p.1.point
     exact Mercury.cornice (houseS hT x') S k hk (R.recordP j₀ i₀) O N'' (hY.symm ▸ hf : Heir.Plays _ _ (B) Y.p _ _ _) hη (Rain.jersey (A:=A) (m:=m)|>.1.le) -- p:/hma
  have heB:=hp T.live hk; have ht:=hp T.pale hi; have he :=bound_smul Complex.I (pricingG ht h₂); rw [Complex.norm_I,one_mul] at he
  exact bound_smul _ (bound_add (ornate heB) (regular_smul _ (ornate ht)) (pricingG heB h₁) he)
end YM.PhysicalNext.Repeat.Graces
