import YM.FullVolume.Rank.Bones
import YM.FullVolume.Rank.Wind
import YM.FullVolume.Rank.Setup

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
open Pressure ConnectedActivityE6 Blaze March Lim Umbra FullVolume.Paint
open Matric Guard
namespace Boutique
set_option quotPrecheck false
variable {q:ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {f:ℕ→ℕ} {p m:ℕ}
local notation "Z₀"=> (A.B.a.S.oneStep m p).exact_size
local notation "z"=> A.B.a.S.side m p
local notation "Z"=> A.B.a.S.side (m+1) p
local notation "W!"=> A.B.a.clock.op m p
local notation "Q"=> A.B.a.budget m
local notation "t'"=> A.B.a.budget (m+1)
open RG.Shoot Lark Rain Blush
local notation "W₁"=> FullVolume.Urns.layout G Z t'
variable {q':ℕ→ ℕ→∀ p, Shoot.Trail A.B.a p} {g:ℕ→ℕ} (U:Stack X m p q f) (V:Stack X m p q' g)
variable {D:Desk G (A.B.a.S.side m p)}{d:ℕ}{L:ℕ→ℝ} {K':Bid.Worth}
variable (hU:∀ i, (A.B.bake.make (q i)).Selected) (hV:∀ i,(A.B.bake.make (q' i)).Selected) (hd:d+3 ≤ A.B.a.clock.J m)
variable (he:Stationary.Artes.Cadre A.post A.B.kin)(hv:Next.Free.Amplify A.B.M)(hX: Jams.Wild X.shape A.delay)(hh:Lark.Near A m f)(hG':Lark.Near A m g)(ht:Tendsto f atTop atTop)(hl:Tendsto g atTop atTop)
open FullVolume.Shadow
local notation "φ"=> fun n=> (A.B.bake.make (q n)).rep (f n) p m
local notation "φ'"=> fun n=> (A.B.bake.make (q' n)).rep (g n) p m
variable (hc:Echo U V)
variable (hW:∀ n, Well ((A.B.bake.make (q n)).rep (f n) p m) D (Real.sqrt (A.B.a.clock.forcedAllowance m)))(hW':∀ n, Well ((A.B.bake.make (q' n)).rep (g n) p m) D (Real.sqrt (A.B.a.clock.forcedAllowance m)))
open FullVolume.Paint.Rank
local notation "Q₁"=> A.B.a.clock.J (m+1)
local notation "Fa"=> (Labels.frames G).level d
include b hU hV hd hW hW' hG he hv hX hh hG' ht hl hc U V
variable {E:Desk G (A.B.a.S.side (m+1) p)} (ha:∀ i,Well ((A.B.bake.make (q i)).rep (f i) p (m+1)) E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))) (ha':∀ i,Well ((A.B.bake.make (q' i)).rep (g i) p (m+1)) E (Real.sqrt (A.B.a.clock.forcedAllowance (m+1))))
variable (x: Coin ((Labels.frames G).level d) (hol G) E)
local notation "r"=> E.orient
-- Merchant any selected stack.Buy equal κ.Accords not assumed.S Component.Data. Create ropes.F.M.Read.per.
local notation "κ₀"=> (Real.sqrt (A.B.a.clock.forcedAllowance m))
local notation "κ₁"=> (Real.sqrt (A.B.a.clock.forcedAllowance (m+1)))
open Extra.Histories.InputColumn Finset
local notation "A₀"=> (A.B.a.params (m+1)).columns
local notation "w"=> C Q₁
local notation "L'"=> A.B.a.S.block m
local notation "ψ"=> Doors.rate L'
local notation "T₀"=> fun n=> (U n|>.castT b (hU n) hd)
variable (hz:Nest X Y)
include hz
omit hV he hv hX hh hG' ht hl hc hW' V
include ha
lemma dolls (i: (Fa).Index): let f(n:ℕ)(j:Extra.Histories.InputColumn.Listing):= gas (T₀ n) i (Coin.uses x) j
     ∃ a:Extra.Histories.InputColumn.Listing→ℝ,Summable a ∧ ∀ j, Doll (fun n=>Matric.tell (f n j)) (hol G) D (a j):=by
    intro F; let Q':=Matric.book (Size.axis Fa i) (Coin.uses x)
    choose T A' hT using fun n=>(tickets hG b (Y:=Y) (U n) (hU n) hd hz).chamber
    let B:= E.orient; have hv (n):= granted (ha n) (hol G) (Size.axis Fa i) x
    let u n:= (U n).player; let K n:=(T₀ n).up; have hx n:(rack (K n) Q').Format 0 (hol G) (u n):= rack_format _ Q' (hv n).1
    let S:= rack (K 0) Q'; have hS(n):rack (K n) Q'= S:=by
       have hp : (u n).activities.forced=(u 0).activities.forced := ((ha n).alongside.force.symm).trans ((ha 0).alongside.force); have he' : profile (u n|>.activities) Q'.forced= profile (u 0|>.activities) Q'.forced:=by unfold profile barcode; rw [hp]
       have hx : stowK (K n) Q'= stowK (K 0) Q':= congr_arg (fun f:Box (Z)→ Config G Z→ℂ => Function.extend (cart (K 0)) (f ∘ Subtype.val) 0) he'
       unfold S rack; rw [hx];rfl
    have hp : S.remBound 0 (u 0) κ₁ ‖x‖:= (keeps (K 0) Q' (hv 0).2) -- if rw issue
    obtain ⟨pC,qN,hx',hy'⟩:= rem_tabs.mp hp; obtain ⟨v,hV,HX⟩:= hx'.regular; obtain ⟨c,hC,hP⟩:= hx'.forced
    let W n:= (φ n); let a j:=(u 0).p.mass (S.support j) (v j); let r' j:=(u 0).p.mass ((u 0).activities.forced j).support (c j)/κ₁; have hQ:E.k=κ₁:= (ha 0).paid; have hs: 0<κ₁:= hQ ▸ E.sane; let s:= Size.axis Fa i; let V' := w * (Fa).coeffSize (Bid.vowel Fa L' s)+ ψ *(Fa).coeffSize ((Fa).core s); let Z':= w * (Fa).coeffSize (Bid.vowel Fa L' ((Fa).core s)); let f' := max Z' V'; let V:= consist f' (fun j=> ψ*a j) (fun j=> ψ *r' j)
    have hv : HasSum V (f'+((∑' i, ψ*a i)+∑' j, ψ*r' j)):= added (((show Summable a from hV.2.1).mul_left _).hasSum) (((hC.2.1.div_const κ₁).mul_left _).hasSum)
    refine ⟨V,hv.summable,fun j n=> ?_⟩
    have hQ:=hT n; have hK₀ : (A.B.bake.make (q n)).S.block m=L':= rfl; have hx''(P : Coefficient Fa z) (q:ℝ)(hx: P.Format 0 (hol G) (φ n))(hp:P.remBound 0 (φ n) κ₀ q)(hf:(Fa).coeffSize P.x ≤ q): P.Format 0 (hol G) D.orient ∧ P.remBound 0 D.orient D.k q ∧ (Fa).coeffSize P.x ≤ q:= ⟨along_format _ ((hW n).alongside.sym) hx,along_bound _ (hW n).alongside.sym ((hW n).paid.symm ▸ hp),hf⟩
    have hO {v:ℕ}(hv:True): True:=trivial
    rcases j with j|j|j
    · have he:= (hQ.copies.main i).earns; let P:= Matric.tell (F n (.inl j))
      apply hx'' P f' he.format (rem_mono he.bound (le_max_left Z' V')); apply le_trans _ (le_max_right ..)
      let A:= T n; have hh: (Fa).coeffSize (A.leads L' s)≤ w * (Fa).coeffSize (Bid.vowel Fa L' s):=(hQ.copies.heading _).1
      apply (Work.G08.size_triangle Fa P.x (A.leads L' s)).trans; exact add_le_add hh ((le_mul_of_one_le_left (Work.G08.size_nonneg ..) (Motion.orbitCost_one_le Fa)).trans he.leadP)
    · have he:S.Format 0 (hol G) (u n):= hS n ▸ hx n; have h : (u n).p=(u 0).p:= (ha n).alongside.price.symm.trans (ha 0).alongside.price; have hz:=(hQ.copies.regular j (Q'.regular j) (v j) ⟨he.smooth j,he.origin j,he.identity_null j,he.projects j⟩ (h.symm ▸ HX j : (u n).p.supBounds 0 _ _ _)).earns
      let Z_:=ψ*a j; let X:= Matric.tell (F n (.inr (.inl j)))
      have hh : Z_= ψ*(u n).p.mass (mapSeat (n:=A.B.a.S.side (m+1) p) j) (v j):=by rw [h];rfl
      change X.Format .. ∧ X.remBound _ _ _ Z_∧ (Fa).coeffSize X.x≤ Z_
      rw [hh]; apply hx'' X _ hz.format hz.bound; have hp:=hz.leadP; rw [sub_zero] at hp; exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (Motion.orbitCost_one_le Fa)).trans hp
    let P':= rack (K n) Q'; have he: P'.Format 0 (hol G) (u n):=hx n; let b:=P'.forced j; let X:=Matric.tell (F n (.inr (.inr j))); let d:= ψ*r' j
    have hv:0≤d:= mul_nonneg (hQ.budget.epsilon) (div_nonneg (hC.1 j) hs.le); have hm : F n (.inr (.inr j))=(T₀ n).plate.ink j b:=rfl
    change X.Format 0 _ _ ∧X.remBound 0 D.orient D.k d∧ (Fa).coeffSize X.x ≤ d
    by_cases hh:b=0
    · have hx': X=Matric.tell 0:= by unfold X; rw [hm,hh,hQ.copies.blank]
      rw [hx']; let p:= (0:Coin Fa (hol G) D); have hM:=Coin.wealth p; refine ⟨hM.1,rem_mono (P:= Matric.tell 0) hM.2 (by simp [p,hv]),?_⟩; simpa only [Matric.tell, Matric.book_x, Prod.fst_zero,Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero] using hv
    have hy: A' n (.gasKey j):=by have hp:j∈Set.range (cart (K n)):= not_not.mp (fun h=>hh (pit _ _ h)); obtain ⟨i,rfl⟩:=hp; exact hQ.cart _
    have hu: b=S.forced j:= congr_arg (fun p: Coefficient Fa (A.B.a.S.side (m+1) p) => p.forced j) (hS n)
    have hf:= (hQ.copies.forced j b (c j) hh hy ⟨he.invariant _,he.borel j,he.supported j,he.carried j,he.forcing j⟩ (hP j).1 (fun U=>by rw [hu]; exact (hP j).2 U)).earns
    have hh: d=ψ*((u n).p.mass ((u n).activities.forced j).support (c j)/κ₁):=by rw [(ha n).alongside.price.symm.trans (ha 0).alongside.price,(ha n).alongside.force.symm.trans (ha 0).alongside.force]
    rw [hh]; apply hx'' X _ hf.format hf.bound; have hk:=hf.leadP; rw [sub_zero] at hk; exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (Motion.orbitCost_one_le Fa)).trans hk
include V hV hW' he hv hX hh hG' ht hl hc ha'
-- i=0 Pin Shift even `tags` main; capture of Unit with force zero and layout static.
local notation "U'"=>fun n=> V n|>.castT b (hV n) hd
lemma linters (i:(Fa).Index): Hue (fun n=> (T₀ n).shot i (Coin.uses x)) (fun n=>(U' n).shot i (Coin.uses x)) (hol G) D:=by
    let f (n:ℕ)(k:Extra.Histories.InputColumn.Listing):Pin Fa z := Matric.gas (T₀ n) i (Coin.uses x) k; let g (n:ℕ)(k:Extra.Histories.InputColumn.Listing):Pin Fa z :=Matric.gas (U' n) i (Coin.uses x) k
    have hf k: Shift D (fun n=>f n k) (fun n=>g n k) :=by
        rcases k with k|k|k
        · by_cases hy:i=0
          swap;· exact graces hG b Y U V hU hV hd he hv hX hh hG' ht hl hc hW hW' hz i hy
          subst i; let A:= f 0 (Sum.inl k); -- unit.In across N via stowK zero
          let x':= Extra.Histories.primary (0:Site z) (((P.L Q₁).val:ℂ)^d • (Fa).e0)
          suffices hh : (fun n=> f n (Sum.inl k))=(fun _=>A) ∧ (fun n=> g n (Sum.inl k))=(fun _=>A) by
             rw [hh.1,hh.2]; obtain ⟨c,hc,hf⟩:=dolls hG b Y U hU hd hW ha x hz (0:(Fa).Index) -- x shadow
             have hp:=hf (Sum.inl k) 0; exact same _ _ ⟨_,hp.2.1⟩ hp.1
          have hx_{n:Side}{G:Gauge}{d:ℕ}{F:Labels.Frame G d}{R R':Rep G n}(A:Keeper R.p R.activities)(A':Keeper R'.p R'.activities)(v:F.Coeff): closeK A (Extra.Histories.primary 0 v)=closeK A' (Extra.Histories.primary 0 v):=by
              refine Prod.ext rfl (Prod.ext rfl ?_); funext i U
              have h {R:Rep G n}(A:Keeper R.p R.activities): stowK A (Extra.Histories.primary (0:Site n) v) i U=0:=by by_cases hi:i∈Set.range (cart A); obtain ⟨i',ht⟩:= hi; rw [← ht,stowed]; simp [profile,cram,Extra.Histories.primary]; rw [pit _ _ hi];rfl
              exact (h A).trans (h A').symm
          have hb₀ (n): f n (.inl k)= closeK (Keeper.sufficient (U n).down) x':=by change Cub.border (U n).stock center (U n).down (U n).up ((U n).okC b (hU n) hd) 0= _; unfold Cub.border; rw [if_pos rfl]; rfl
          have hb₁ (n): g n (.inl k)= closeK (Keeper.sufficient (V n).down) x':=by change Cub.border (V n).stock center (V n).down (V n).up ((V n).okC b (hV n) hd) 0= _; unfold Cub.border; rw [if_pos rfl]; rfl
          exact ⟨funext (fun n=> (hb₀ n).trans ((hx_ _ _ _).trans (hb₀ 0).symm)),funext fun n=>(hb₁ n).trans ((hx_ _ _ _).trans (hb₀ 0).symm)⟩
        · exact perfume hG b U V hU hV hd he hv hX hh hG' ht hl hc hW hW' ha ha' x k
        exact verdun hG b U V hU hV hd he hv hX hh hG' ht hl hc hW hW' ha ha' x i k
    obtain ⟨wQ,hw,hG'⟩:= dolls hG b Y U hU hd hW ha x hz i
    obtain ⟨v,hv,hV'⟩:= dolls hG b Y V hV hd hW' ha' x hz i
    have hh {n:Side}{G:Gauge}{d:ℕ}{F:Labels.Frame G d}{p:ℕ→ Coefficient F n}{t y:ℝ}{S:Desk G n}{A:Hol G}(h:Doll p A S y)(h':y≤t): Doll p A S t:=fun n=>⟨(h n).1,rem_mono (h n).2.1 h',(h n).2.2.trans h'⟩
    -- code ambiguity.Open Bok
    have hx(j):Doll (fun n=> Matric.tell (f n j)) (hol G) D (wQ j + v j):= hh (hG' j) (le_add_of_nonneg_right (rem_nonneg (hV' j 0).2.1))
    have hy(j):Doll (fun n=> Matric.tell (g n j)) (hol G) D (wQ j+v j):= hh (hV' j) (le_add_of_nonneg_left (rem_nonneg (hG' j 0).2.1))
    exact uplift (Extra.Histories.code _) (p:=f) (t:=g) (hw.add hv) hx hy hf
end Boutique
end Bandage
end YM.PhysicalNext.Repeat.Legato
