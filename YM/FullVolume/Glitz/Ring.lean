import YM.FullVolume.Glitz.Stem
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Circlet.Rebel
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus Blush Mallow
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels Peak Mercury Graces
open Planned.PrimaryIntegral295 WaterLevels
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}{M : Metals G}{D:Rolls M.p}{A:Alloy M D}{Q:ℕ→ℕ→ Teller G}{C: Programs M.p}
   {r p:ℕ→ℕ} {R:ℕ→ℕ→Record}{B:Factor A}{V:Bolt A}
local notation "cc"=> A.B.a
variable {m N n d:ℕ} (hm:m<N)
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T"=> A.B.a.clock.J m
local notation "B₁"=> A.B.a.budget m
local notation "B₂"=> A.B.a.budget (m+1)
local notation "X"=> A.B.a.clock.op m n
local notation "V0"=> ships A.B N m n
local notation "V1"=> forecast V m N n
local notation "L"=> D.L J
local notation "y"=> A.B.a.clock.hatBeta m
local notation "v"=> R J T
local notation "u"=> C J T
local notation "vT"=> M.p.profile J
local notation "vB"=> M.p.profile T
local notation "r'"=> B.span J T
set_option quotPrecheck false
variable (hP:Circlet.Pitch M.p M.K Q C r) (hp: Pads D R Q M.K C A.delay) (hc: Decked C D R B.span B.shape A.delay) (hb:goodD M.p (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) d)(hV:Nest B V) (hC:Mallow.Arrives B.shape A.delay)
local notation "F"=> (Labels.frames G).level d
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
variable {K:In A.B.a m n} {x t:ℝ} (H: Chord B N m n x x)(z: Chord.Flight A N m n)
open Jams Jams.Cryst
local notation "Z"=> H.sight z
local notation "K!"=> z.val
variable {τ:ℝ} (hz:Push.Local.Readable (hol G) (localSection G d) (z.val).p (A.B.a.S.side (m+1) n) τ) (h!:HasSlots (z.val|>.p) (z.val|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (z.val).beta
local notation "Ω"=> badge G n₁ d
local notation "w"=> B.span J T
local notation "Xp"=> (localSection G d).footprint (0:Site n₁)
local notation "Yp"=> (plate Z Ω).support
include h!
lemma minesG: Walled X ((localSection G d).footprint (0:Site n₁)) (plate Z Ω).support y w:=by
   have he:=billboard Z (B.pledging.agenda J T (step_paid A.B.a m)|>.2.2) Ω
   convert he using 1; rw [signboard (z.val) h!] -- may no goal
lemma zeroOG : (plate Z Ω).site=0:=by
   change (X).ratio.parent ((z.val).activities.reg Ω).site=_; rw [signboard (z.val) h!]; let s:= (X).ratio; change s.parent 0=0; rw [← s.root.map_zero]; exact s.embed_parent _
include hP hp hc hb hm hV
lemma shellsG : Nonwrapping (plate Z Ω).support 0 ∧ coverNumber (B₁).B Yp ≤ (B₁).B:=by
   have hs:=shifting (A:=A) (m:=m); have he:=united (n:=n) hm hP hp hV; have hf: d≤ J:=Nat.le_trans (Nat.le_add_right d 2) hb.2.2.2
   obtain ⟨hy,hk⟩:= hc.buys _ _ (step_paid A.B.a m) (first_le A.B.valid m) _ (A.B.valid.pays m) d hf |>.geometry
   apply setting (minesG H z h!) rfl (show (B₂).B ≤2*(B₁).B from he.1.rehearsed.weft.cover) (by rw [hs.2]; exact hk) hy
   exact vastly (m:=m) hc

variable (i:((Labels.frames G).level d).Index)(hi:i≠0)
local notation "Mi"=> ((F).grades i).1
-- conductor boost
variable (U:Cliff G (M.p.profile (A.B.a.clock.J m)).order (M.p.profile (A.B.a.clock.J m)).power (M.p.profile (A.B.a.clock.J (m+1))).power ((((Labels.frames G).level d).grades i).1-1) (A.B.a.clock.J (m+1)) (A.B.a.clock.J m) (B.span (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (M.p.profile (A.B.a.clock.J m)).supportExponent (M.p.profile (A.B.a.clock.J (m+1))).supportExponent M.p.kernel) (a:ℂ→L[ℝ]ℝ)(h₁:∀ t,‖a t‖ ≤ ‖t‖)
local notation "leaf₀"=> cove (z.val) 0 Xp ankle _ _ (lofty (z.val) i hz).1 (lofty (z.val) i hz).2 a h₁ h!
local notation "f'"=> a ∘ (hills (z.val) i)
local notation "p"=> (z.val).p -- conflict ℕ→ℕ
include hC hi
-- Graces.Moms only used for Phase.Scale q length requirement. introduce explicit.L
set_option maxHeartbeats 700000 in
lemma tallySG (hv: Heir.Release.accepts (B.span J T) (vT).supportExponent ((vB).supportExponent+2) L) : let H' :=cove (z.val) 0 Xp ankle _ _ (lofty (z.val) i hz).1 (lofty (z.val) i hz).2 a h₁ h!
    ∃ t:ℝ,(B₁).supBounds 0 Yp (matin H' Z (icon Z Ω) Chi.canonical) t ∧ Push.Local.reservedMass B₁ Yp t ≤ (U.charge+1)*((L).val:ℝ)⁻¹^(Mi)*((z.val).p.mass Xp τ):=by -- ambiguous Let.L.val
  intro H'; obtain ⟨hT,hA,hκ,hK,hr⟩:= inks (z.val) i hz h! a h₁
  let i':= Mi; have hI:1≤ i':= GridRenewal.Speed.grade_grows i hi; let n':=i'-1; have h':n'+1=i':=by omega
  let j:= J; let t:= T; let c₀:=(K!).p; let u0:=H
  have hJ := step_paid A.B.a m; have hO: n'+1≤ (vB).order:= h' ▸ ((show i' ≤ d from (F).bound i).trans ((Nat.le_add_right _ _).trans hb.2.1)) -- edit
  have hd:d≤ J:=Nat.le_trans (Nat.le_add_right d 2) hb.2.2.2
  have hn: n'≤d:= (Nat.sub_le ..).trans ((F).bound i)
  have hX:=B.pledging.conducts; have hU:= A.B.valid.pays m
  have hT':=z.property
  have he:c₀=B₂:= hT'.1.point
  have hΨ:=hc.buys _ _ (step_paid A.B.a m) (first_le A.B.valid m) _ hU d hd
  obtain ⟨q,hq,hZ,hξ⟩:= hΨ.optional
  obtain ⟨hL,hL'⟩:=united (n:=n) hm hP hp hV
  let F':= WaterLevels.forecast V m N n
  have hw':= Rain.jersey (A:=A) (m:=m); have hu:= shifting (A:=A) (m:=m)
  have hS:= hΨ.owed _ _ hw'.2.1 hu.1 n' hn ((z.val).beta) (show betaF G y L/2 ≤ _ from (by rw [← PriceCompiler.beta_eq A.B.valid]; exact hT'.2.1))
  have hC':= hC _ _ hU _ hJ|>.1; obtain ⟨aF,b,y',g,v₀,Y',p',B',g',e,ν,ht',hy,N'',hη⟩:= hC'.2 _ _ _ _ (Opera.protocol A.B hm hX.full (n:=n)) _ _ Z
  have he': (B₂).supportExponent=(vT).supportExponent:= Rain.jersey (A:=A) (m:=m+1)|>.2.2.1
  have hg:0<gStep β:= inv_pos.mpr (Real.sqrt_pos.mpr (Z).laws.intake.positive)
  have hu':H'.crest=Xp:=by change ((z.val).activities.reg Ω).support=Xp; rw [signboard (z.val) h!]
  let L':= Warehouse.flight (Issue.trail V) N m
  have hΩ: Peak.glider G F' n' (B₂).power (2*(u).C) U.lens := by
     rw [Rain.jersey (A:=A) (m:=m+1)|>.2.1]; apply U.early _ _ _ _ L' _ (hP.gift j t|>.1) rfl
     change HEq (Carrier.linesOf L' A.B.a.clock.kernel.penalty) (Carrier.linesOf L' M.p.kernel.penalty); rw [A.B.valid.kernel]
  have hτ:= shellsG hm hP hp hc hb hV H z h!; have hx :=zeroOG (d:=d) H z h!
  let V' := Peak.sale n' (store G _) u U.lens v B₁ c₀ (X).patch.L Xp w y (gStep β) -- missing.SOrder let.Gamma
  have hh:0≤ V':=by unfold V'; unfold Peak.sale; have hk:0≤ poleSum n' (store G (vB).order) U.lens:=polepos n' _ (zero_le_one.trans U.big); have hW:=Peak.wage_pos n' u v B₁ c₀ (X).patch.L Xp w y _ hg.le; unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; have hp:= (R J T).peak; positivity
  rw [← he] at hL hL' hΩ hS hu -- no!
  have hStu:Heir.Short X c₀ Xp:= by
     have heX: minSide G d ≤ c₀.B:=by rw [hu.2]; exact hΨ.geometry.2
     unfold Heir.Short; have hk:= close_stencil G d c₀.B _ heX (0:Site n₁); have hs:= (X).patch.coarse -- name
     exact lt_of_le_of_lt (Nat.pow_le_pow_left hk _) (by norm_num; omega)
  have hw0:=minesG (d:=d) H z h!
  have ha:∀ V:Config G n₀, Healthy (B₁).threshold Yp V→ ∀ (F0:Tree.Forest (X).ratio) (k:(X).Choices) (l:List (Directions G n₀)), l.length≤ (vB).order→ (∀ t∈l,(B₁).dirBound (plate Z Ω).site t)→‖leftDerivs (hore Z Ω v Chi.canonical Chi.canonical 1 (f') F0 k) l V‖ ≤ τ * V':= by -- can't infer l
    intro q' hV F0 k l hl hb
    unfold Mercury.hore; rw [YM.PhysicalNext.Repeat.Circlet.muse V (mapcase Z Ω F0) _ _ _ _ _ _ _]
    let g':=mapcase Z Ω F0
    have ht : ((z.val).activities.reg Ω).support= Xp:=by rw [signboard (z.val) h!]
    have hs: ((z.val).activities.reg Ω).site=0:=by rw [signboard (z.val) h!]
    let x₀:= ((z.val).activities.reg Ω).support
    have hh: c₀.supBounds ((z.val).activities.reg Ω).site x₀ (f') τ:=by rw [hs]; unfold x₀; rw [ht]; exact hr
    have hg':Walled X x₀ Yp y w:= (by unfold x₀; rw [ht]; exact hw0)
    have hT':= shines (z.val) i hi hz a (by have := Return.enough_room A.B (m+1) n; omega)
    unfold V'; rw [← ht]
    apply Peak.tinyBill Chi.canonical 1 k g' 1 hL' hK ((z.val).activities.reg Ω).anchor hg' hg.le (guard_silent Chi.canonical hg (mul_pos (R j t).guards c₀.threshold_pos)) hV hh (ht.symm ▸ hStu) hO hΩ U.big (by rw [hs,ht]; exact hT') _ l hl hb
    -- exact
  have hb:= show (B₁).supBounds 0 Yp (matin H' Z (icon Z Ω) Chi.canonical) (τ*V'+τ*q) from hx ▸ Mercury.around Z H' Ω hT v Chi.canonical Chi.canonical 1 N'' hη _ hK hκ hL (hw'.2.1.symm ▸ hξ) rfl hw'.1.le hτ.2 hq (mul_nonneg hz.nonneg hh) ha
  refine ⟨_,hb,?_⟩
  have h0:= hw'.2.2.1; have hA':c₀.supportExponent=(vT).supportExponent:= he ▸ he'
  let k:= (B.span j t)
  have hL'' : (X).patch.L=L:= PriceCompiler.block_eq A.B.valid m
  have hp:= U.accepts _ _ X u v B₁ c₀ Xp Yp _ _ hw'.2.1 hA' (hL''.symm ▸ hv) hw0 rfl hL'.rehearsed.weft.cover hL'.rehearsed.tensions.coarse hg.le (hL''.symm ▸ hS) _ hz.nonneg
  have hvv := (F).bound i
  let H!:=c₀.mass Xp τ
  unfold Push.Local.reservedMass; rw [h0,mul_add]; let M0 := U.charge*((X).patch.L.val:ℝ)⁻¹^i' * H!
  have hA:0<( (L).val:ℝ):=by positivity
  let Z0:= ((L).val:ℝ)⁻¹^i' * H!
  have hh: Real.exp (((B₁).supportExponent+2)*coverNumber (B₁).B Yp)*(τ*q) ≤ Z0:=by
    have hk': Heir.Release.accepts w c₀.supportExponent ((B₁).supportExponent+2) (X).patch.L:=by rw [hA',h0,hL'']; exact hv
    have hf:= Mercury.fades Z H' Ω rfl (B.pledging.agenda _ _ hJ|>.2.2) hk' hL'.rehearsed.weft.cover q hq
    have ht : ((z.val).activities.reg Ω).support= Xp:=by rw [signboard (z.val) h!]
    change Real.exp (((B₁).supportExponent+2)*coverNumber (B₁).B Yp)*(q*τ) ≤ _*q*c₀.mass ((z.val).activities.reg Ω).support τ at hf
    rw [ht,mul_comm q τ,h0] at hf; rw [h0]; apply hf.trans; apply mul_le_mul_of_nonneg_right _ (hz.nonneg.trans (c₀.loMass _ _ hz.nonneg)); rw [mul_comm _ q]
    exact hZ.trans (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (L).property)) hvv)
  rw [h0] at hh; refine (add_le_add (le_trans hp ?_ : _ ≤ M0) hh).trans_eq ?_
  · exact le_of_eq (by change U.charge*_ ^ (n'+1)*H! =_; rw [h'])
  change U.charge*_ *H! + Z0= (U.charge+1)*_ * H! -- prefer specify
  unfold Z0; rw [hL'']; ring
end YM.PhysicalNext.Repeat.Circlet
