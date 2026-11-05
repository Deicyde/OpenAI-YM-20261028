import YM.FullVolume.Reel.Range
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
abbrev inkSet (Q:Desk G (A.B.a.S.side (m+1) n))(K:Keeper Q.orient.p Q.orient.activities): Set Wing:=fun i => match i with
  | .logKey j=>j∈ Set.range (fun i: {s: Support (A.B.a.S.side (m+1) n) // (0:Site _)∈ s}=> Blush.found 0 i.val i.property)
  | .gasKey j=> j∈ Set.range (cart (R:=Q.orient) K) ∧ 0∈(Q.orient.activities.forced j).support
local notation "IP"=>inkSet (A:=A) (m:=m) (n:=n) T K
lemma inkFinite : (inkSet (A:=A) (m:=m) (n:=n) T K).Finite:=by
   let s:=A.B.a.S.side (m+1) n; let V:= {p:Support s// (0:Site s)∈p};let f:V→ Wing:=fun i=>.logKey (Blush.found (0:Site s) i.val i.property);let g (i:StockTag s): Wing:=.gasKey (cart (R:=T.orient) K i)
   apply ((Set.finite_range f).union (Set.finite_range g)).subset; rintro (j|j) h
   · obtain ⟨u,hy⟩:= (show j∈range (fun i:V=> found (0:Site s) i.val i.property) from h); exact Or.inl ⟨u, congr_arg Wing.logKey hy⟩
   obtain ⟨u,hy⟩:= (h: (j∈Set.range (cart K) ∧ _)).1; exact Or.inr ⟨u, congr_arg _ hy⟩
include ht
lemma informed (w:IP): w.val.blank Z.val.val ∧ 0∈ w.val.support Z.val.val:=by
   let v:=ht.carts Z.val.property.1.point Z.property
   obtain ⟨i,h⟩:=w; cases i
   next i=>
       let V:= {p:Support s₁// (0:Site s₁)∈p}; obtain ⟨p,rfl⟩:= (show i∈range (fun i:V=> found (0:Site s₁) i.val i.property) from h)
       refine ⟨Z.property.regular _,?_⟩
       change 0∈ ((R_).activities.reg (found (0:Site s₁) p.val p.property)).support; rw [Blush.latch _ _ _ _ Z.property]; exact p.property
   next i=>
       change (True) ∧ 0∈ ((R_).activities.forced i).support; rw [← v.alongside.force]; exact ⟨trivial,h.2⟩
-- x captain price. Printed plant & rem only.C.Full cost basis.Under hZ.Visit.
local notation "aG"=> stageP A.B.a (m+1) n
local notation "Q"=> (A.B.a.budget m)
local notation "Q1"=> (A.B.a.budget (m+1))
local notation "Zs"=> scoreTag g H b hd Z
local notation "I"=> Extra.Histories.InputColumn.Listing
local notation "K0"=> Keeper.sufficient Z.property
abbrev sigil:=consist (pointEx (A:=A) (m:=m) (n:=n) i) (fun j=> regMask (A.B.a.budget (m+1)) j ((X_).regular j)) (fun j=> gasMask j ((X_).forced j))
abbrev waist:= consist (headsMoney H b hd Z.val Z.property i) (fun j=> regMoney H Z.val Z.property j ((X_).regular j) d) (fun j=> inkMoney H Z.val j ((X_).forced j) d)
include g b hd
abbrev trunk:= gather (Zs) (K0) (x_) i
abbrev richesP :=2*(framePay (A:=A) (m:=m)) -- K ignored in frame pay
include hk
lemma trays :
   let g:=pollen ST o_ T i x;
   rack (R:=Z.val.val) (Keeper.sufficient Z.property) g= X_:=by
    intro p; let P:= T.orient; have hz:=ware ST o_ T K i x rfl
    have hc : cart (R:=T.orient) K= cart (R:=R_) K0:= by rw [hk];rfl
    have ht':=Matric.Stamp.bank ST T K (ht.carts Z.val.property.1.point Z.property|>.alongside) p hz.2.1 (K0) hc
    unfold packY rack; rw [← ht']
include hx hU
variable {a c:ℕ→ℝ}(hZ: Matric.Stamp.Relief ((Labels.frames G).level d) (Next.Foundations.hol G) T (packY ((Labels.frames G).level d) (Next.Foundations.hol G) T K i x) ‖x‖ a c)
local notation "g_"=> x_
local notation "X0"=> X_
local notation "x0"=> T.orient
omit hU hx
-- Specs context sharing across labels Ty.R
section
include hZ
lemma ReadyE (j:ℕ) : RegFit Z.val.val 0 d o_ (mapSeat j) ((X0).regular j) ∧ Z.val.val.p.supBounds 0 (mapSeat j) ((X0).regular j) (a j):=by
    have hx:= (ht.carts Z.val.property.1.point Z.property).alongside; have hc:= along_format (X0) hx hZ.suit
    exact ⟨⟨hc.smooth _,hc.origin _,hc.identity_null _,hc.projects _⟩,hx.price ▸ (show T.orient.p.supBounds 0 (mapSeat j) ((X0).regular j) (a j) from hZ.sharp j)⟩
lemma ReadyK (j:ℕ) : SlotFit Z.val.val 0 j ((X0).forced j):=by
    have hx:= along_format (X0) (ht.carts Z.val.property.1.point Z.property).alongside hZ.suit; exact ⟨hx.invariant _,hx.borel _,hx.supported _,hx.carried _,hx.forcing _⟩
lemma opMarks (j:ℕ): (X0).forced j≠0→ .gasKey j∈ inkSet (A:=A) (m:=m) (n:=n) T K:=by
    intro he
    change (j∈Set.range (cart (R:=T.orient) K))∧_
    exact ⟨by by_contra h; exact he (pit K (x_) h), hZ.suit.carried j he⟩
end
-- index block before coins lens.Carrier Booster.pivot Key event.
local notation "h_"=>framePay (A:=A) (m:=m)
local notation "Ω"=> sigil (A:=A) (m:=m) (n:=n) T K i x
local notation "t_"=> trunk H g Z b hd T K i x -- verify order macro quickly
local notation "S_"=> waist H Z b hd T K i x
include hx hU
lemma scoreP : let p:= pollen ST o_ T i x; let f:Essence G s₁:= fun j V=> ∑' k,(sigil (A:=A) (m:=m) (n:=n) T K i x k j V)
    Fleet R_ O_ D0s (inkSet (A:=A) (m:=m) (n:=n) T K) 0 0 ℓ (p.x 0) (p.exponentialEntry 0 p_ R_) (profile Z.val.val.activities p.forced) (profile (H.moment Z.val).activities ((trunk H g Z b hd T i x)).forced) (2*h_+2*‖x‖) (ledgers (A:=A) (m:=m) (c₁:=c₁) i + ρ*‖x‖) f (MergeProof.band (waist H Z b hd T K i x)):=by
    intro A' f; let p:= (x_); let Xp:= X0; have Hs := trays g Z b hd T ht K hk i x; -- H accidental binder
    obtain ⟨a,c,hE⟩:= minted ST o_ T K i x; let u(j):= T.orient.p.mass (Xp.support j) (a j); let k(j):= T.orient.p.mass (Local.patch T.orient.activities j) (c j)/T.k
    let W: Listing→ Pin ST s₀:= tags Zs (Keeper.sufficient Z.property) p i
    let P0s:= Extra.Histories.primary (0:Site s₁) (p.x)
    let E_:Listing→ Config G s₁→ℂ:=consist (P0s.exponentialEntry 0 p_ R_) (Xp.maskedTerm R_) 0; let K_:Listing→Res G s₁:= consist 0 0 (fun j=> exactGas (R_).activities j (Xp.forced j)); let p':=consist (p.x 0) 0 0; let x':Listing→ℝ:= consist (2*h_) (fun j=> 2*u j) (fun j=>2*k j); let y':=consist (ledgers (A:=A) (m:=m) (c₁:=c₁) i) (fun j=>ρ*u j) (fun j=>ρ*k j)
    let Xg(j):= Matric.tell (W j); let O(j):=profile (O_).activities (Xg j).forced
    let Fsk:= Ω; let Fw:= S_
    have hv:=ht.carts Z.val.property.1.point Z.property; have h0 : Xp=rack (K0) p:= Hs.symm
    have h(i'): Fleet R_ O_ D0s IP 0 0 ℓ (p' i') (E_ i') (K_ i') (O i') (x' i') (y' i') (Fsk i') (Fw i') ∧ (Xg i').remBound 0 O_ (Real.sqrt κ) (y' i'):=by
       rcases i' with _|j|j
       · exact boots H g Z b hd U0 hU hx i (S:=IP) (Exists.intro ⟨(p_).footprint (0:Site s₁), Circlet.ankle⟩ rfl) -- with unit.Tag witness ordering A.
       · obtain ⟨hp,hq⟩:= ReadyE g Z b hd T ht K hk i x hE j
         have he:= clocks H g Z b hd hx j ((Xp).regular j) (a j) (S:=IP) (Exists.intro ⟨mapSeat (n:=s₁) j, spot _ _⟩ rfl) hp hq
         let t : I:= Sum.inr (Sum.inl j)
         have ht : T.orient.p.mass (Xp.support j) (a j)=Z.val.val.p.mass (mapSeat (n:=s₁) j) (a j):=hv.alongside.price ▸ rfl
         have hx : E_ t= masked (A.B.a.budget (m+1)).threshold (mapSeat (n:=s₁) j) ((Xp).regular j):=by rw [← Z.val.property.1.point];rfl
         rw [show E_ _= _ from hx, show x' t=2*(u j) from rfl, show y' t=ρ*u j from rfl]; unfold u; rw [ht]; exact he
       let t:= (Sum.inr (Sum.inr j):I)
       have hh := cabinet H g Z b hd hx j (Xp.forced j) (c j) (opMarks g b hd T ht K hk i x hE j) (ReadyK g Z b hd T ht K hk i x hE j) (hE.stock j).1 (hE.stock j).2 -- macro H
       change Fleet R_ O_ D0s IP 0 0 ℓ 0 0 (exactGas _ _ _) (profile (O_).activities (Matric.tell ((Zs).ink j _)).forced) (2*k j) (ρ*k j) (Fsk t) (Fw t) ∧ (Matric.tell ((Zs).ink j _)).remBound 0 O_ _ (ρ*k j)
       rw [show stowK (R:=R_) (K0) p j=Xp.forced j from (h0.symm ▸ (show stowK (K0) p j= _ from rfl)), show k j= (R_).p.mass ((R_).activities.forced j).support (c j)/Real.sqrt (A.B.a.clock.forcedAllowance (m+1)) from ?_]; exact hh
       unfold k; rw [hv.alongside.price,hv.paid]; unfold Local.patch; rw [hv.alongside.force]
    let a':= (∑' j,u j)+(∑' j,k j); have hp : a'≤‖x‖:=hE.price
    have hA : HasSum x' (2*h_+ 2*a'):=by unfold a'; rw [mul_add]; exact added (hE.totalsE.hasSum.mul_left _) (hE.totalsK.hasSum.mul_left _)
    have hB : HasSum y' (ledgers (A:=A) (m:=m) (c₁:=c₁) i +ρ*a'):=by unfold a'; rw [mul_add]; exact added (hE.totalsE.hasSum.mul_left _) (hE.totalsK.hasSum.mul_left _)
    have he' :HasSum p' (A'.x 0):=by simpa only [p',consist,Sum.elim_inl, add_zero] using added (f:=p') hasSum_zero hasSum_zero
    refine (Fleet.amassed (Orchard.soundVisit H g _ hx b.r |>.1) (fun i=> (h i).1) (α:=A'.exponentialEntry 0 p_ R_) (ζ:=profile Z.val.val.activities A'.forced) ?_ ?_ (fun i U=>profile_merge (code Listing) Xg (Real.sqrt_pos.2 (forcedPos ..)) (fun i=> (h i).2) hB.summable i U) he' hA.summable hB.summable).loosen le_rfl (hA.tsum_eq.trans_le (add_le_add_right ?_ _)) (hB.tsum_eq.trans_le (add_le_add_right ?_ _))
    · intro U; have h: A'.exponentialEntry 0 p_ R_ U=P0s.exponentialEntry 0 p_ R_ U+((∑' j,Xp.maskedTerm R_ j U)+0):=by
         have h₁:= congr_fun (peaL Z (p.x)) U; rw [show P0s.exponentialEntry 0 p_ R_ U= _ from h₁]; rw [add_zero]; exact rfl
      rw [h]; exact added (f:=fun i=> E_ i U) ((Xp.regular_series (along_bound Xp hv.alongside (ware ST o_ T K i x rfl).2.2.2)).summable U|>.hasSum) hasSum_zero
    · intro j U; rw [← show profile Z.val.val.activities Xp.forced=profile Z.val.val.activities (A').forced from (by rw [h0]; exact stows (K0) p)]
      have he := profiled (R_).activities (Xp.forced) (rem_dominated (along_bound Xp hv.alongside (ware ST o_ T K i x rfl).2.2.2)) U j; convert added (f:=fun i=> K_ i j U) hasSum_zero he using 1; change _ = (0:ℂ)+(0+_); rw [zero_add,zero_add]
    · exact mul_le_mul_of_nonneg_left hp zero_le_two
    exact mul_le_mul_of_nonneg_left hp (Doors.rate_pos _).le
end Splint
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Splint.scoreP
