import YM.FullVolume.Reel.Arch
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
include g b hd
local notation "D0s"=>portal H Z.val
local notation "p0"=> A.B.a.budget m
local notation "p1"=> A.B.a.budget (m+1)
local notation "ST"=> (Labels.frames G).level d
local notation "n'"=> A.B.a.S.side (m+1) n
local notation "ρ"=> Doors.rate L_
set_option quotPrecheck false
open YM.Source Labels
-- actual Origin offers. E response.B real. Slot fit for zeros. independent of η scale at projection.
abbrev regWing (n:Side)(i:ℕ):= Wing.logKey (found (0:Site n) (mapSeat i) (spot n i))
abbrev regMask (B:BudgetPoint){G':Gauge}{n:Side} (i:ℕ)(f:Config G' n→ℂ): Essence G' n:= noteS (regWing n i) (masked B.threshold (mapSeat i) f)
abbrev gasMask {G':Gauge}{n:Side} (i:ℕ)(f: Config G' n→ℂ): Essence G' n:= noteS (.gasKey i) f
local notation "xD"=> scoreTag g H b hd Z
variable (i:ℕ)(f:Config G (A.B.a.S.side (m+1) n)→ℂ)(w:ℝ)
local notation "W₁" => (mapSeat (n:= A.B.a.S.side (m+1) n) i)
include hx g b hd
lemma clocks (hM:regWing s₁ i∈S)(hC: RegFit Z.val.val 0 d o_ (mapSeat i) f)(he:Z.val.val.p.supBounds 0 (mapSeat i) f w) : let a:= Z.val.val.p.mass (mapSeat (n:=s₁) i) w; let v':= ρ*a
   let k:= (xD).tint i f; let v:= Matric.tell k;
   Fleet (R_) (O_) D0s S 0 0 ℓ 0 (masked (A.B.a.budget (m+1)).threshold (mapSeat i) f) 0 (profile (O_).activities v.forced) (2*a) v' (regMask (A.B.a.budget (m+1)) i f) (regMoney H Z.val Z.property i f d)∧ v.remBound 0 O_ (Real.sqrt κ) v':=by
    intro a v' k v
    obtain ⟨C,hU,hV,hW⟩:=fitting H g Z.val Z.property i f d hC he;
    let s:=sInf {y| (R_).p.supBounds 0 W₁ f y}; let P:= Blush.float (R_) 0 W₁ (spot _ _) f s hC.smooth C Z.property; let a':=(R_).p.mass W₁ s; let t':=ρ * a'
    have hz:P.live.crest=W₁:=paneX Z (spot _ _) f s hC.smooth C |>.2.1; have he':P.live.turn∈ S:= hM
    have hS : k=mei H g Z.val P d:= hU;
    have hp:Z.val.val.p= A.B.a.budget (m+1):=Z.val.property.1.point
    have hF : a' ≤ a := mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
    have ht' : t' ≤ v':= mul_le_mul_of_nonneg_left hF (Doors.rate_pos _).le
    have ht:=RegX H g b hd Z.val f s hp.symm W₁ (spot _ _) C hC Z.property
    have h':= moonDeck H g Z b hd hx b.r P (hz.symm ▸ spot _ _) he' ht; have hG:=paneX Z (spot _ _) f s hC.smooth C; unfold v; rw [hS,hV,← hp]; unfold regMask
    have htU := h'.loosen (Y:=S) le_rfl (t':=2*a) (mul_le_mul_of_nonneg_left (show load P.live ≤ _ from (by unfold load; rw [hz]; exact hF)) zero_le_two) ht'
    let P0s:=masked ((R_).p.threshold) W₁ f; rw [show prose P.live + Complex.I • prose P.pale=P0s from hG.2.2.1, show MergeProof.entry P.live+Complex.I • MergeProof.entry P.pale=0 from hG.2.2.2.1, show dig Z P.live + Complex.I • dig Z P.pale=P0s from hG.2.2.2.2.1] at htU
    exact ⟨htU,rem_mono (EffortMint H g Z b hd P _ ht|>.2.1) ht'⟩
local notation "G₁"=> (R_).activities
omit hx
private lemma noneQ (w:ℝ)(h:0≤w) : let p:= Matric.tell (F:= ST) (n:=s₀) 0
    p.remBound 0 O_ (Real.sqrt κ) w∧ profile (O_).activities p.forced=0:=by
    intro u; have hz:0<Real.sqrt κ:=Real.sqrt_pos.mpr (forcedPos ..)
    refine ⟨⟨0,0,le_rfl,le_rfl,?_,hz,⟨fun i=>0,budget0 ..,fun i=>(regular0 ..).2⟩,fun i=>0,?_,fun i=>⟨le_rfl,fun V=>?_⟩⟩,?_⟩
    · simpa using h
    · rw [mul_zero]; exact budget0 ..
    · exact norm_zero.le
    funext i U; unfold profile cram; change (∑' j:{j // _},(0:ℂ))= _; rw [tsum_zero]; rfl
local notation "μ"=> Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
include hx
lemma cabinet (hM:f≠0→ .gasKey i∈ S) (h:SlotFit Z.val.val 0 i f)(hp:0≤w)(he:∀ U,‖f U‖≤w): let a:= Z.val.val.p.mass (Z.val.val.activities.forced i).support w; let ur:= a/Real.sqrt (A.B.a.clock.forcedAllowance (m+1)); let v':= Doors.rate L_ * ur; let p:=Matric.tell ((xD).ink i f)
   Fleet (R_) (O_) D0s S 0 0 ℓ 0 0 (exactGas (G₁) i f) (profile (O_).activities p.forced) (2*ur) v' (gasMask i f) (inkMoney H Z.val i f d) ∧ p.remBound 0 O_ (Real.sqrt κ) v':=by
     intro a ur v' k
     have hz:=glyphBound A.B.a (m+1);have hu: 0≤a:= mul_nonneg (Real.exp_pos _).le hp; have htA: a≤ur:= le_div_self hu hz.1 hz.2
     by_cases hf:f=0
     · have hK : k=Matric.tell (n:=s₀) (0:Pin ST s₀):=by unfold k; rw [hf]; refine congr_arg Matric.tell (show spicy H g Z.val i 0 d=_ from dif_neg ?_); exact fun ⟨_,h,_⟩=> h rfl
       rw [hK,hf] -- hf attempts rewrite `a` etc
       have he:= noneQ H g Z b hd v' (mul_nonneg (Doors.rate_pos _).le (hu.trans htA)); have hD: inkMoney H Z.val i 0 d=0:=dif_neg (fun ⟨_,h,_⟩=> h rfl)
       refine ⟨?_,he.1⟩; rw [show profile (H.moment Z.val).activities (Matric.tell (n:=s₀) (0:Pin ST s₀)).forced=_ from he.2, hD, show exactGas (G₁) i 0=0 from (by simp [exactGas]),show gasMask (G':=G) (n:=s₁) i 0=0 from (by funext j; simp [gasMask,noteS])]
       exact Fleet.waters.loosen le_rfl (mul_nonneg zero_le_two (hu.trans htA)) (mul_nonneg (Doors.rate_pos _).le (hu.trans htA))
     obtain ⟨H₀,hU,hV,hW⟩:= fitted H g Z.val i f d h hf he
     let u_:= sInf { y| ∀ U,‖f U‖≤y}; let P:= fan Z.val.val 0 i f u_ H₀ h
     have hV': k=Matric.tell (mei H g Z.val P d):= congr_arg Matric.tell hU; rw [hV',hV];
     let a':= Z.val.val.p.mass (Z.val.val.activities.forced i).support u_; have hh : a'≤a:=mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
     have hx' : Doors.rate L_*(a'/μ) ≤ v':= mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hh hz.1.le) (Doors.rate_pos _).le
     have ht:= heavyX H g b hd Z.val i f u_ h hf H₀ Z.val.property.1.point.symm
     have hG:= paneK Z i f u_ h hf H₀
     have hY:= moonDeck H g Z b hd hx b.r P (hG.2.1) (show P.live.turn∈ S from hM hf) ht
     let fp:= noteS P.live.turn (dig Z P.live + Complex.I • dig Z P.pale)
     have hF: fp= gasMask i f:=by unfold fp; rw [show dig Z P.live+Complex.I • dig Z P.pale=f from hG.2.2.2.2.1]; rfl
     have hxP: Fleet R_ O_ (Orchard.portal H Z.val) S 0 0 ℓ 0 (prose P.live +Complex.I • prose P.pale) (MergeProof.entry P.live+Complex.I • MergeProof.entry P.pale) (profile (O_).activities (Matric.tell (mei H g Z.val P d)).forced) (2*ur) v' (gasMask i f) (moi H Z.val P d):=hF ▸ hY.loosen le_rfl (mul_le_mul_of_nonneg_left (hh.trans htA) zero_le_two) hx' -- hF rewrite motivate
     rw [show prose P.live+Complex.I • prose P.pale=0 from hG.2.2.1, show MergeProof.entry P.live+Complex.I • MergeProof.entry P.pale=exactGas _ _ _ from hG.2.2.2.1] at hxP; exact ⟨hxP,rem_mono (EffortMint H g Z b hd P _ ht|>.2.1) hx'⟩
end Splint
end YM.PhysicalNext.Repeat.Muse.Veil
#print axioms YM.PhysicalNext.Repeat.Muse.Veil.Splint.cabinet
