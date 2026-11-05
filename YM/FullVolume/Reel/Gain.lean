import YM.FullVolume.Reel.Page
import YM.FullVolume.Reel.Treasure
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse.Veil
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable {v q s t' t t₂:ℝ}{N n m d:ℕ}{L:Lyrics R t t}
open UniformSpace
open Luna Graces Mallow Extra.Histories Planned.GuardedAtom Guard
open MergeProof MergeProof.Matric Next.Foundations
set_option maxHeartbeats 420000
set_option synthInstance.maxHeartbeats 130000
set_option quotPrecheck false
variable (H:Chord R N m n t t) (g:G.Simple)(Z:Ticket A N m n)
local notation "s₀"=> A.B.a.S.side m n
local notation "s₁"=> A.B.a.S.side (m+1) n
variable {W:Bid.Worth}{c₁:ℕ→ℝ}(b:Legato.Bandage R c₁ W) (hd:d+3 ≤ A.B.a.clock.J m)(U0:Heading ((Labels.frames G).level d))(hU:EntryP H b hd U0)
local notation "k₀"=> A.B.a.clock.J m
local notation "k₁"=> A.B.a.clock.J (m+1)
local notation "L_"=> D.L k₁
local notation "ℓ"=> ((L_).val:ℂ)^d
local notation "F_"=> (Labels.frames G).level d
local notation "p_"=>localSection G d
local notation "o_"=>Next.Foundations.hol G
local notation "R_"=> Z.val.val
local notation "O_"=> H.moment Z.val
local notation "κ"=> A.B.a.clock.forcedAllowance m
local notation "va"=> authors A.B.a m
local notation "D_"=> Orchard.portal H Z.val
-- inspect portal namespace
namespace Splint
open Graces Mallow MergeProof.Menu Circlet Blush Lotus Orchard
variable {S: Set Wing}
variable (hx:Orchard.Visit H Z.val)
local notation "D0s"=>portal H Z.val
local notation "u'"=> Real.sqrt κ
local notation "p0"=> A.B.a.budget m
local notation "p1"=> A.B.a.budget (m+1)
local notation "ST"=> (Labels.frames G).level d
local notation "n'"=> A.B.a.S.side (m+1) n
local notation "ρ"=> Doors.rate L_
set_option quotPrecheck false
open YM.Source Labels
open Matric.Stamp
open Legato.Bandage.Boutique Extra.Histories.InputColumn
variable (T: Desk G (A.B.a.S.side (m+1) n))(ht:Feeling A (m+1) n T) (K:Keeper T.orient.p T.orient.activities)(hk:K=Keeper.sufficient ht.aboard)
variable (i:((Labels.frames G).level d).Index)(x:Coin ((Labels.frames G).level d) (Next.Foundations.hol G) T)
local notation "A!"=>T.orient
local notation "W_"=>Keeper.sufficient ht.aboard
local notation "x_"=> pollen ST o_ T i x
local notation "X_"=>packY ST o_ T K i x
-- zero tag primary contribution. actual orientation Stats W.Seat.Pupil and Teller.Real.
open YM.FullVolume.Nectar FullVolume.Ray Luna.Aank FullVolume FullVolume.Paint.Tower
-- item.Parent currency. value ℓ1 anchored. Countable cocktail exactly sums into Finite Glacial.B.
local notation "A_"=> (A.B.a.budget (m+1))
local notation "P"=> inkSet (A:=A) (m:=m) (n:=n) T K
variable [FX:Fintype ↑(inkSet (A:=A) (m:=m) (n:=n) T K)]
local notation "U₀"=> framePay (A:=A) (m:=m)
include hU hx
local notation "V_"=> fun i:↥P=> Real.exp ((Z.val.val.p.supportExponent:ℝ)*coverNumber Z.val.val.p.B (i.val.support Z.val.val))
local notation "z_"=> pointEx (A:=A) (m:=m) (n:=n) i
-- estimate nonconstant premise.C.exact budget along axes uses stored Static components TRUE once at tip (or any Z). No β-powers per-L. NK κ.
include g
lemma fareP : Treasure V_ (fun _=> pointEx (A:=A) (m:=m) (n:=n) i ∘ Subtype.val) (2*U₀):=by
   obtain ⟨h,-⟩:= boots H g Z b hd U0 hU hx i (S:=P) (Exists.intro ⟨(p_).footprint (0:Site s₁),Circlet.ankle⟩ rfl)
   obtain ⟨I,hx,M,s,h,he⟩:= h.buys
   let e:↥P→Wing:= Subtype.val; let t:= Finset.univ.image e
   obtain ⟨p,hp,hP,hE⟩:= Net.flush s M he h.purchase t
   refine Treasure.subdued (a:=p∘ e) (fun i=>hp _) ?_ (fun i=> hE i.val)
   unfold t at hP; rw [Finset.sum_image (show _ from Subtype.val_injective.injOn)] at hP; exact hP
omit g hU hx
local notation "F0"=> Config G (A.B.a.S.side (m+1) n)→ℂ
local notation "e"=> Essence G (A.B.a.S.side (m+1) n)
def trib (w:Wing) (U:Config G (A.B.a.S.side (m+1) n)) := (∑' j, regMask (A.B.a.budget (m+1)) j ((X_).regular j) w U)+(∑' j,gasMask j ((X_).forced j) w U)
local notation "X0"=> packY ST o_ T K i x
section
variable {c p:ℕ→ℝ}(hp: Matric.Stamp.Relief ((Labels.frames G).level d) (Next.Foundations.hol G) T (packY ((Labels.frames G).level d) (Next.Foundations.hol G) T K i x) ‖x‖ c p)
local notation "G_"=> sigil (A:=A) (m:=m) (n:=n) T K i x
-- weights c,p at same T only; E sup at ANY Fields. flagsK including away from E health all.
omit FX
include ht hp
local notation "u₀"=> T.orient
local notation "w_"=> T.orient.p
lemma pricesEntry : ∀ j U, ‖masked (A.B.a.budget (m+1)).threshold (mapSeat j) ((X0).regular j) U‖≤c j:=by
    intro j U; by_cases h:Healthy (A.B.a.budget (m+1)).threshold (mapSeat j) U
    · rw [masked_eq _ _ _ _ h]; exact (hp.sharp j).2 U (by change Healthy T.orient.p.threshold (mapSeat j) U;rw [ht.healthy]; exact h) [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ h,norm_zero]; exact (hp.sharp j).1
lemma finitePay : Summable c∧ Summable p:=by
   have h: Summable (fun i=>T.orient.p.mass ((X0).support i) (c i)):= hp.totalsE
   have hx:Summable (fun i=>T.orient.p.mass (Local.patch T.orient.activities i) (p i)):=by
      have ht:= hp.totalsK.mul_right T.k; simp_rw [div_mul_cancel₀ _ T.sane.ne'] at ht; exact ht
   exact ⟨h.of_nonneg_of_le (fun i=> (hp.sharp i).1) (fun i=> T.orient.p.loMass _ _ (hp.sharp i|>.1)), hx.of_nonneg_of_le (fun i=> (hp.stock i).1) (fun i=>T.orient.p.loMass _ _ (hp.stock i|>.1))⟩
lemma emin (w:Wing)(U:Config G s₁) :HasSum (fun j=> G_ j w U) ((pointEx (A:=A) (m:=m) (n:=n) i) w U + trib (A:=A) (m:=m) (n:=n) T K i x w U) ∧ Summable (fun j=> regMask (A.B.a.budget (m+1)) j ((X_).regular j) w U) ∧ Summable (fun j=> gasMask j ((X_).forced j) w U):=by
    let H:= (x_); have hc :Summable c:=(finitePay T ht K i x hp).1; have hq: Summable p:=(finitePay T ht K i x hp).2
    have hh(j):‖regMask (A_) j ((X0).regular j) w U‖ ≤ c j:=by unfold regMask noteS; split_ifs; exact pricesEntry T ht K i x hp j U; exact (show _ = (0:ℝ) from norm_zero).trans_le (hp.sharp j).1
    have hf(j):‖gasMask j ((X0).forced j) w U‖ ≤ p j:=by unfold gasMask noteS;split_ifs; exact (hp.stock j).2 U; exact (show _ = (0:ℝ) from norm_zero).trans_le (hp.stock j).1
    have hA:= hc.of_norm_bounded hh; have hH:=hq.of_norm_bounded hf
    exact ⟨added hA.hasSum hH.hasSum, hA,hH⟩
end
include ht
lemma tribSub (y:Coin ((Labels.frames G|>.level d)) o_ T): trib T K i (x-y)=trib (A:=A) (m:=m) (n:=n) T K i x - trib (A:=A) (m:=m) (n:=n) T K i y:=by
    obtain ⟨a,p,hp⟩:=minted ST o_ T K i x; obtain ⟨b,q,hq⟩:=minted ST o_ T K i y; let V:=X0; let u:=packY ST o_ T K i y; funext j U
    have hx:= emin T ht K i x hp j U; have hu:=emin T ht K i y hq j U; have he:=solvent ST o_ T K i x y
    let p(i:ℕ)(F:F0):= regMask (A_) i F j U; let k(i:ℕ)(F:F0):= gasMask i F j U
    change (∑' j,p j _) + (∑' j,k j _) = ((∑' j,p j (V.regular j))+(∑' j,k j (V.forced j)))-((∑' j,p j (u.regular j))+(∑' j,k j (u.forced j)))
    have h(i)(f g:F0): p i (f-g)=p i f-p i g:=by unfold p regMask noteS; split_ifs; exact congr_fun (map_sub (Local.maskLinear (A_).threshold (mapSeat i)) f g) _ ; exact (sub_self _).symm
    have hh(i)(f g:F0): k i (f-g)=k i f-k i g:=by unfold k gasMask noteS;split_ifs; rfl; exact (sub_self _).symm
    rw [he.1,he.2]; simp_rw [Pi.sub_apply,h,hh]; rw [show (∑' j, (p j ((X0).regular j)-p j (u.regular j)))= _ from (hx.2.1|>.tsum_sub hu.2.1), show (∑' j,(k j ((X0).forced j)-k j (u.forced j)))= _ from (hx.2.2|>.tsum_sub hu.2.2)]; unfold V; abel -- syntactic adjust
-- reg+gas Asset ℓ weighted ANY. c rearr.T.P.Transform via PRINT. need cost at TRUE z but no Visit here.
section costs
local notation "W₁"=> trib T K i x
include FX
lemma stamps : Treasure (V_) (fun _:sun=> trib (A:=A) (m:=m) (n:=n) T K i x ∘ Subtype.val) ‖x‖:=by
    obtain ⟨p,q,hq⟩:=minted ST o_ T K i x; let F:=X0; have hs:=ware ST o_ T K i x rfl
    let U:=inkSet (A:=A) (m:=m) (n:=n) T K
    let d(j:ℕ):=T.orient.p.mass (F.support j) (p j); let k(j:ℕ):=T.orient.p.mass (Local.patch T.orient.activities j) (q j)/T.k
    have hv:= ht.carts Z.val.property.1.point Z.property
    let t(j:↥U):=Real.exp ((Z.val.val.p.supportExponent:ℝ)*coverNumber Z.val.val.p.B (j.val.support Z.val.val)); have ha j:0<t j:= Real.exp_pos _
    let r k:=regWing s₁ k; let F0_ (j:↥U):= cram r p j.val; let K0_ (j:↥U):= cram Wing.gasKey q j.val
    have he(i:↥U)(j:ℕ) (he:r j=i.val): t i*p j=d j:=by
        let Q0:=T.orient; unfold t d; rw [hv.alongside.price, ← he, show (r j|>.support Z.val.val)= _ from ?_];
        · exact (rfl: _ = Z.val.val.p.mass (mapSeat (n:=s₁) j) _)
        change ((R_).activities.reg (found (0:Site s₁) (mapSeat j) (spot s₁ j))).support=(mapSeat (n:=s₁) j); rw [Blush.latch _ _ _ _ Z.property]
    have hb(i:↥U)(j:ℕ)(he:Wing.gasKey j=i.val): t i*q j=T.k*k j:=by
        have ht:T.k≠ 0:=T.sane.ne'; unfold t k BudgetPoint.mass; rw [←he,hv.alongside.price,show Local.patch T.orient.activities j= _ from congr_arg (fun p:ℕ→ ForcedAddress G s₁=> (p j).support) hv.alongside.force]; rw [mul_comm T.k,div_mul_cancel₀ _ ht]; rfl
    have hF :=(finitePay T ht K i x hq); have hxP :=(heavy r hq.totalsE); have hxQ:= heavy Wing.gasKey (show Summable k from hq.totalsK)
    have Hc(i:↥U): t i*(F0_ i+K0_ i)= cram r d i.val + T.k*cram Wing.gasKey k i.val:=by
       rw [mul_add]; refine congr_arg₂ (·+·) ?_ ?_; unfold F0_ cram; rw [← tsum_mul_left]; exact tsum_congr (fun j=> he i j.val j.property)
       unfold K0_ cram; rw [← tsum_mul_left,← tsum_mul_left]; exact tsum_congr fun j=> hb i j.val j.property
    have HK i:F0_ i+K0_ i≥0:=add_nonneg (tsum_nonneg fun j=> (hq.sharp _).1) (tsum_nonneg fun j=>(hq.stock _).1)
    refine Treasure.subdued HK (a:=fun i=> F0_ i+ K0_ i) ?_ (fun j U=>?_)
    · change ∑ i:↥U,t i* (F0_ i+K0_ i) ≤ _; simp_rw [Hc]; rw [Finset.sum_add_distrib, ← Finset.mul_sum]; apply le_trans _ hq.price
      let J: Finset Wing:= Finset.univ.image (fun i:↥U=>i.val); have heg i:0≤k i:=div_nonneg (mul_nonneg (Real.exp_pos _).le (hq.stock _).1) T.sane.le
      have hg {f:Wing→ℝ}{t:ℝ}(h:HasSum f t)(hv:∀ i,0≤f i): ∑ i:↥U,f i.val≤t:=by
          refine le_trans (b:=∑ i∈J,f i) ?_ ((h.summable.sum_le_tsum _ (fun i _=> hv i)).trans_eq h.tsum_eq); unfold J; rw [Finset.sum_image Subtype.val_injective.injOn]
      apply add_le_add (hg hxP (fun i=> tsum_nonneg (fun j=>mul_nonneg (Real.exp_pos _).le (hq.sharp _).1)))
      exact (mul_le_mul_of_nonneg_left (hg hxQ (fun i=> tsum_nonneg fun j=> heg _)) T.sane.le).trans (mul_le_of_le_one_left (tsum_nonneg (g:=k) heg) ((hv.paid).trans_le (glyphBound A.B.a (m+1)).2))
    let W:=Z; have hx(i':ℕ):‖masked (A_).threshold (mapSeat i') (F.regular i') U‖ ≤ p i':= pricesEntry T ht K i x hq _ _
    have heQ : trib T K i x j.val U=cram r (fun k=> masked (A_).threshold (mapSeat k) (F.regular k) U) j.val + cram Wing.gasKey (fun k=>F.forced k U) j.val:=by
        unfold trib; rw [expand_eq,expand_eq]; apply congr_arg₂ (·+·)
        · apply tsum_congr; intro z; unfold regMask noteS r; split_ifs<;> rfl
        apply tsum_congr; intro z; unfold gasMask noteS; split_ifs<;> rfl
    rw [Function.comp_apply,heQ]; exact (norm_add_le ..).trans (add_le_add (metric_cram r hF.1 hx j.val) (metric_cram _ hF.2 (fun i=> (hq.stock i).2 U) j.val))
end costs
end Splint
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Splint.stamps
