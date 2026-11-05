import YM.UVExtension.Cloud.Papa
import YM.UVExtension.Rafter.Flight
/-!
 # REAL spigot on the short-upper interval. No full-sequence assumptions.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Cloud
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open Fitted
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ)(b:Shade)
set_option quotPrecheck false
local notation "H"=> S.fits N n
local notation "V"=> S.cart N n
local notation "τ"=> S.grove.coins
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
local notation "J₀"=> A.B.a.clock.J m
local notation "J"=> A.B.a.clock.J (m+1)
local notation "Δ"=> P.L J
set_option quotPrecheck false
variable (hm:m<N)(hd:d+3≤A.B.a.clock.J m)
local notation "Hut"=> (S.fits N n).Hut
open UVExtension.Flake Dales Guild Lamppost Rafter Tabernacle Camp Oriel Oriel.Charted
include hm
local notation "F0"=> A.B.a.clock.forcedAllowance m
open Bud Linden Copse Mallow Lotus Daisy Charity
open Pressure Pressure.Testing ConnectedActivityE6 Push.SectorMeasure
-- receipts passport ANY common root cloud + corresponding turns. true traveller.s.Ensure healthy supports MRT.
variable (K : ∀ b:Shade,duetB S N m n b hm)
local notation "c"=> A.B.a.S.side m n
local notation "q!"=> mount X N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0
local notation "W!"=> Cash.fragrances (((S.fits N n).charts m hm).atTopH)
local notation "k"=> (((S.fits N n).charts m hm).atTopH)
local notation "o"=> (0:Site c)
set_option quotPrecheck false
local notation "q₁"=> A.B.a.S.side (m+1) n
local notation "s1"=> A.B.a.budget (m+1)
local notation "Hb"=> readB R d m n hd
local notation "Υ"=> fun b=>pins1 S N m n b hm
local notation "K0"=> fun b=> Keeper.sufficient (pinsQ S N m n b hm (K b))
local notation "Φ"=> facing (X:=X) d m
local notation "k!"=> Real.sqrt (A.B.a.clock.forcedAllowance (m+1))
local notation "N!"=> Bucket (F) (A.B.a.budget m) (hol G) c
variable (L:Shade→Banner A.B.a ((frames G).level d) (hol G) n m)
    (he:∀ b:Shade,Waged ((K b).body) beam0 (readB R d m n hd) (pins1 S N m n b hm) (Keeper.sufficient (pinsQ S N m n b hm (K b))) (L b)) (hz:Guild.PriceS X m)
omit hm
lemma faces : 0≤ facing (X:=X) d m:=by
    have hA:= zero_lt_one.trans (A.B.a.fits.delayed (m+1)); have hr:= Push.Local.readPrice_pos (hol G) ((frames G).level d)
    unfold facing reflux; exact le_max_of_le_left (by positivity)
private lemma base : HasSlots (A.B.a.budget (m+1)) (mount X N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0).activities:=by exact ⟨rfl,rfl,fun _=> rfl,fun _=>rfl⟩ -- has unused he hz. remove
private lemma fares {B:Type}[NormedAddCommGroup B][NormedSpace ℂ B]{A:Type}[AddCommGroup A][Module ℂ A] (v:A→ₗ[ℂ] B)(u:ℂ)(h:DenseRange v)(he:u≠0): DenseRange ⇑(u • v) := Dense.mono (by rintro x ⟨y,rfl⟩; exact ⟨u⁻¹ • y, by simp [smul_smul,he]⟩) h
include hm he hz
set_option synthInstance.maxHeartbeats 250000 in
set_option maxHeartbeats 700000 in
lemma sleeping (i: Eyelet.Slot (A.B.a.S.side (m+1) n)) : ∃ g:ℂ→ (Gondola d O! i.1 s1)→L[ℂ] N!,Bumps spreadK.span g∧ (∀ b,g (spreadK.call b)=(L b).glass i)∧∀ z∈spreadK.span,‖g z‖≤ Φ:=by
    let R0:=q!; let U:= tin d (hol G) i.1 (s1); let v:= Eyelet.toll_pos (s1) i.1.val; let a:ℂ:=↑(Eyelet.fee (s1) i.1.val); let p:=a • twig U; have hvp: a≠0:=by unfold a; exact_mod_cast v.ne'
    refine Rafter.flick spreadK _ p (fares _ _ (steams U) hvp) (faces ..) (fun j=>?_)
    let z:= ‖U j‖; have hz:(s1).supBounds 0 i.1.val j.val z:= (pays d (hol G) _ _ j).mpr le_rfl; let Vb b:= tonne (Q:=fun _=>cumulus S N m n b (m+1)) beam0 (Υ b) i j z hz
    have heP:= recognizes d (hol G) i.1 (s1) j
    let V' := Blush.float R0 0 i.1.val i.1.property j.val z heP.pose hz (base (X:=X) N m n)
    have hG:V'.live.crest=i.1.val:=by change (R0.activities.reg (Blush.found 0 i.1.val i.1.property)).support=i.1.val; rw [Blush.latch R0 _ _ _ (base ..)]
    obtain ⟨g,hg,hL,hV⟩:= hats S R d N m n hm hd K V' Vb (fun _=> rfl) (nativity X V'.live _ _ _ rfl) (fun _=> rfl) (fun _=> rfl) (hG.symm ▸ i.1.property) (show PriceS X m from by assumption) (fun b=> (he b|>.sack i).spark j z hz)
    have hp: Linden.prices V'.live 0= ‖p j‖:=by
       unfold Linden.prices; rw [Copse.worth,Copse.one,hG]; change z*_=‖a • twig U j‖; rw [norm_smul]; unfold a; rw [Complex.norm_real,Real.norm_of_nonneg v.le]; exact mul_comm ..
    exact ⟨g,hg,fun b=> (hL b).trans ((he b|>.sack i).linke j z hz),fun z hz=>(hV z hz).trans_eq (congr_arg (Φ *·) hp)⟩
set_option synthInstance.maxHeartbeats 250000 in
set_option maxHeartbeats 700000 in
lemma thrums (i:StockTag (A.B.a.S.side (m+1) n)) : ∃ g:ℂ→ (Eyelet.Stream G s1 i)→L[ℂ] N!,Bumps spreadK.span g∧ (∀ b,g (spreadK.call b)=(L b).wing i)∧∀ z∈spreadK.span,‖g z‖≤ Φ:=by
    by_cases hv:(0:Site q₁)∈i.val.1; swap; · exact ⟨fun _=>0,bumps _ _ (differentiableOn_const _),fun b=> (he b |>.blank i hv).symm,fun _ _=> by change ‖(0:Eyelet.Stream G s1 i →L[ℂ] N!)‖ ≤ Φ; exact le_trans (show ‖(0:Eyelet.Stream G s1 i →L[ℂ] N!)‖≤0 from le_of_eq (@norm_zero (Eyelet.Stream G s1 i →L[ℂ] N!) _)) (faces d m)⟩
    let R0:=q!; let U:= sink (G:=G) (s1) i; let v:= Eyelet.toll_pos (s1) i.val.1; let P₀:= base (X:=X) N m n; have hκ := glyphBound A.B.a (m+1)
    have hh₀:0< Eyelet.fee (s1) i.val.1/k!:= div_pos v hκ.1
    let a:ℂ:= ↑(Eyelet.fee (s1) i.val.1/k!); let p:= a • twig U; have ha:a≠0:=by unfold a; exact_mod_cast hh₀.ne'
    refine Rafter.flick spreadK _ p (fares _ _ (steams U) ha) (faces ..) (fun j=>?_)
    let z:= ‖U j‖; have hu:∀ V', ‖j.val V'‖≤ z := (debts (s1) i j).2 le_rfl
    let Vb b:= vaneT (Q:=fun _=>cumulus S N m n b (m+1)) beam0 (Υ b) i j z hu
    let i₀:= MergeProof.cart (R:=R0) (Keeper.sufficient P₀) i
    let V':= Blush.fan R0 0 i₀ j.val z hu (((tailor _ _ _).mp j.property).1)
    have hQ : V'.live.crest=i.val.1:=congr_arg Prod.fst (cardK (R:=R0) (Keeper.sufficient P₀) i)
    obtain ⟨g,hg,hL,hV⟩:= hats S R d N m n hm hd K V' Vb (fun _=> rfl) ⟨fun _ _ _=> trivial⟩ (fun _=> rfl) (fun _=> rfl) (hQ.symm ▸ hv) hz (fun b=> ((he b).limb i hv).spark j z hu)
    have hy: Linden.prices V'.live 0≤ ‖p j‖:=by
       unfold Linden.prices; rw [Copse.worth,Copse.one,hQ]; change z*_≤‖a • twig U j‖ -- Le!
       rw [norm_smul]; unfold a; rw [Complex.norm_real,Real.norm_of_nonneg hh₀.le]; change z*Eyelet.fee (s1) i.val.1 ≤ Eyelet.fee (s1) i.val.1/k!*z; rw [mul_comm z]; exact mul_le_mul_of_nonneg_right (le_div_self v.le hκ.1 hκ.2) (norm_nonneg _)
    exact ⟨g,hg,fun b=> (hL b).trans (((he b).limb i hv).linke j z hu),fun z hz=> (hV z hz).trans (mul_le_mul_of_nonneg_left hy (faces ..))⟩

set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 680000 in
lemma pointE (i: Eyelet.Slot (A.B.a.S.side (m+1) n)) : ∃ g:ℂ→ (Gondola d O! i.1 s1)→L[ℂ] N!, (∀ v,Bumps spreadK.span (fun z=> g z v))∧ (∀ b,g (spreadK.call b)=(L b).glass i)∧∀ z∈spreadK.span,∀ v, ‖g z v‖≤ Φ*‖v‖:=by
    obtain ⟨g,hg,hE,h⟩:= sleeping S R d N m n hm hd K L he hz i; exact ⟨g,fun v s f hs hv ht=>DifferentiableOn.clm_apply (hg s f hs hv ht) (differentiableOn_const _),hE, fun z hz v=> ((g z).le_opNorm v).trans (mul_le_mul_of_nonneg_right (h z hz) (norm_nonneg _))⟩
set_option maxHeartbeats 680000 in
lemma pointK (i:StockTag (A.B.a.S.side (m+1) n)) : ∃ g:ℂ→ (Eyelet.Stream G s1 i)→L[ℂ] N!, (∀ v,Bumps spreadK.span (fun z=>g z v))∧ (∀ b,g (spreadK.call b)=(L b).wing i)∧∀ z∈spreadK.span,∀ v,‖g z v‖≤ Φ*‖v‖:=by
    obtain ⟨g,hg,hE,h⟩:= thrums S R d N m n hm hd K L he hz i; exact ⟨g,fun v s f hs hv ht=>DifferentiableOn.clm_apply (hg s f hs hv ht) (differentiableOn_const _),hE, fun z hz v=> ((g z).le_opNorm v).trans (mul_le_mul_of_nonneg_right (h z hz) (norm_nonneg _))⟩
end YM.UVExtension.Cloud
