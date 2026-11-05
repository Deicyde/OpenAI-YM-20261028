import YM.FullVolume.Shroud.Plateau
/-! Epoch credit on every p. Compensation at real course only.Level zero altered only after full Wilson law certified. Base widths tiny for marks.Fixed p. -/
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
variable {G:Gauge}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:Bolt A}{C:ℕ→ℝ}{K:Bid.Worth}
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K'"=> R.alloy.B
local notation "B→"=> L!|>.budget -- remove lexer
local notation "o"=> R.alloy.B.a.clock.bar
section
-- more credit.E# actual α Error includes slack for level0 via forecastE ≤ th^2 /64. Use all.A.N curvature.H.Texture.
variable {N m p:ℕ} (Q:Contest N p T.L)
lemma shaped (h:m≤N): let A:= Q.trail m; let P':= L!
   A.Lawful (P'.params m).width (P'.params m).paths (P'.clock.loopCap m) (FullVolume.Amp.glint*P'.clock.allowance m) (FullVolume.Amp.glint*P'.clock.forcedAllowance m):=by
    intro v P'
    let p':= T.halls p N; let X':= p'.plan m h; have hp:=Contest.framed T.gains p' Q m h
    let y:=Q.homeP T.gains p' m h; let a:= Q.sparkCost T.gains p' (show Fin (N+1) from ⟨m,Nat.lt_succ_of_le h⟩)
    have hh: ‖(y.val:FullVolume.Urns.Show (stageP P' m p))‖ ≤ FullVolume.Amp.glint:= a
    have hb:=Q.home_observe T.gains p' m h; have hr:= (Q.rises.prices m (Nat.zero_le _) h).1
    have hi:v.p=(P').budget m:= hr.point; refine ⟨hr.valid.paths,?_⟩; rw [show v.p=P'.budget m from hr.point,show v.activities= FullVolume.Urns.observe _ y from hb.symm]; exact FullVolume.Urns.qualifies _ hh -- check f param
lemma headroom (h:m<N): let P':= L!; |(Q.trail (m+1)).beta - (Q.trail m).beta-G.slopeConstant*Real.log (P'.S.block m).val| ≤ (P'.params (m+1)).drift-1/2:=by
    let P':= R.alloy.B.a; let Ψ:= P'.clock; dsimp only; let M0:= R.kit; let H:= (Q.rises.persists m (Nat.zero_le _) h).continues; obtain ⟨l,t,F,hT,x,hx,hF,hK⟩:= (H.1.2).1
    have hx:= (hT.moves T.gains.SimpleR h).2 x hx
    let a:=hK; rw [hK,hF]; let e:= (hT.result x).beta - predictor K' N F x; have he: (P'.budget m).threshold^2 * |e| ≤ forecastE P' m:= hx.2.2.1
    have ht:0<(P'.budget m).threshold:= (P'.budget m).threshold_pos
    have hp:(P'.clock.allowance m)≤(P'.budget m).threshold^2:=by
       let v:= Ψ.hatCoupling m; have hv:0 < v:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (P'.fits.delayed m)))
       have ha:v ≤ (P'.budget m).threshold:= le_mul_of_one_le_right hv.le (Real.one_le_exp (sq_nonneg _)); have hb:v≤1:= ha.trans (P'.budget m).threshold_le
       exact le_trans (b:=v^2) (by change v^((11:ℝ)/5)≤ v^(2:ℕ); rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_ge hv hb (by norm_num)) (pow_le_pow_left₀ hv.le ha 2)
    let z:= Time.credit G (P'.params m)
    have hf : z ≤ 1/2:= by have he:= Time.base_nonneg G (P'.params m); unfold z Time.credit; have hb : (1+Time.base G (P'.params m))⁻¹≤ 1:= inv_le_one_of_one_le₀ (le_add_of_nonneg_right he.1); linarith
    have hh: |e| ≤ 1/2:= by
       refine le_of_mul_le_mul_left  (?_ : (P'.budget m).threshold^2 * |e| ≤ _ ) (pow_pos ht _); exact he.trans (mul_le_mul hf hp (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (by norm_num : (0:ℝ)≤1/2)|>.trans_eq (mul_comm ..)) -- forecastE unfolding
    have hV:= R.alloy.B.support.kinetic N m h; let U:= P'.params (m+1); have he': (F x).beta-(hT.result x).beta-G.slopeConstant*Real.log (P'.S.block m).val= -(e+(R.alloy.B.kin.alpha N m+ G.slopeConstant*Real.log (P'.S.block m).val)):=by unfold e predictor; ring
    change |_ -_ - G.slopeConstant * Real.log (P'.S.block m).val| ≤ _; rw [he',abs_neg]; apply (abs_add_le ..).trans; linarith only [hh,hV] -- defeq P'
end
local notation "B'"=> L!|>.params 0
local notation "ν"=> L!|>.clock.allowance 0
local notation "θ"=> L!|>.clock.forcedAllowance 0
local notation "Λ"=> L!|>.clock.loopCap 0
local notation "M'"=> L!|>.budget 0
lemma supply (p:ℕ): ∃ t, 0<t∧t ≤ 1/2∧ ∀ N, 1 ≤ N → ∀ Q:Contest N p T.L, |Q.bonusB-o| ≤ t → let R':= Muslin.adorn (Q.trail 0) (Q.bonusB-o)
      R'.Lawful (B').width (B').paths Λ ν θ ∧ R'.eval=(Q.trail 0).eval:=by
   -- prices from any used hm=0
   let P':= L!; let C:=P'.params 0; let v:= T.center 1 p; let Y:= fun _:ℝ=> v.trail 1; have hL:∀ x:ℝ,x∈ Set.Icc 0 1 → Lives (R.alloy.B.bake) 1 1 p (Y x) ∧ (Y x).beta∈band P' 1:=fun x _=> let hx:= (v.rises.prices 1 (by decide) le_rfl); ⟨T.L.altitude.1 hx.1,hx.2⟩
   have ht:= (R.kit.machine.passes (Q:=Y) (m:=0) zero_lt_one hL).1
   have hn:0<ν:=Real.rpow_pos_of_pos (inv_pos.mpr <| Real.sqrt_pos.mpr <| zero_lt_one.trans (R.alloy.B.a.fits.delayed _)) _
   have hp:0<θ:=Real.exp_pos _
   have hw:=Real.exp_le_one_iff.mpr (show -( ((P'.clock.monitor 0)^((1:ℝ)/5))) ≤ 0 from neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_nonneg _) _))
   have hd: FullVolume.Amp.glint * ν < ν:=mul_lt_of_lt_one_left hn (by norm_num [FullVolume.Amp.glint]); have hv : glint* θ < θ:=mul_lt_of_lt_one_left hp (by norm_num [FullVolume.Amp.glint])
   obtain ⟨t,h,h'⟩:= Muslin.earned (G:=G) (n:=P'.S.side 0 p) (P'.budget 0) C.clip C.width C.paths (P'.clock.loopCap 0) _ _ _ _ hd hv (le_trans hv.le hw) (actual_side_ge ..) ht.decent ht.width
   refine ⟨min t (1/2),lt_min h (by norm_num),min_le_right ..,fun N hn Q ha=>?_⟩; have hg:= (Q.rises.prices 0 (Nat.zero_le _) (Nat.zero_le _)).1; exact h' _ (ha.trans (min_le_left ..)) _ hg.point hg.clip (shaped T Q (m:=0) (Nat.zero_le _))
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.supply
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.headroom
