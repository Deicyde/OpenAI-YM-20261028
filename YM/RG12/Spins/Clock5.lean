import YM.RG12.Spins.Ion
import YM.RG12.Spins.Tubal
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Circlet
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
local notation "w0"=> ((M.profile T).supportExponent+2) -- wrong
variable {K:In A.B.a m n} {x t:ℝ} (H: Spring B N m n x t K)(z: Icc x t)
local notation "Z"=> houseS H z
local notation "K!"=> K z.val
variable (hz:Push.Local.Readable (hol G) (localSection G d) (K z).p (A.B.a.S.side (m+1) n) (Cub.title G (M.p.profile (A.B.a.clock.J (m+1))))) (h!:HasSlots (K z|>.p) (K z|>.activities))
-- wrap etc. earn with fixed Glider.
local notation "β" => (K z.val).beta
local notation "Ω"=> badge G n₁ d
local notation "Xp"=> (localSection G d).footprint (0:Site n₁)
local notation "Yp"=> (plate Z Ω).support
open PPX Next.Free WardBin.Lies
-- expose Leg without footing.Help alignment
variable (i:((Labels.frames G).level d).Index)
local notation "θ!"=> Cub.title G vT
local notation "T!"=> lark (K z) i hz h!
local notation "c0"=> (K z).p
local notation "U!"=> (X)
local notation "f!"=> hills (K z) i
local notation "Z0"=> icon Z Ω
local notation "q'"=> Chi.canonical
set_option quotPrecheck false
-- removed
open Multi.Puff Source Bid
include hm hP hp hc hb hV h! hz
local notation "D!"=> Mercury.groves
local notation "S!"=> localSection G d
local notation "φ!" η=> Mercury.hore Z Ω v Chi.canonical Chi.canonical 1 (η ∘ f!)
local notation "g!" η => fun (W:Config G n₀)=> Mercury.groves Z Ω v Chi.canonical Chi.canonical 1 W (η ∘ f!)
-- calmer.Frost
set_option maxHeartbeats 480000 in
lemma chorus8 {ε:ℝ}(G':Legato.Pads8 (M:=M) D C Q R B.span ε A.delay)(hi: ((F).grades i).2=2)(η:ℂ→L[ℝ]ℝ)(he:‖η‖≤1):
   let ψ:=deem 0 y (V1) (η ∘ (f!))
   ∀ X' Y':Directions G n₀,(B₁).dirBound 0 X' → (B₁).dirBound 0 Y' → ‖leftDerivs (g! η) [X',Y'] 1-leftDerivs ψ [X',Y'] 1‖ ≤ y^ε/y :=by
   have hv:= (united (n:=n) hm hP hp hV).1; have hB:(K z).p=B₂:= (H.knows _ z.2).1.point; rw [← hB] at hv
   obtain ⟨hR,hT,hK,hW,hU⟩:= inks (K z) i hz h! η (fun x=> (η.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) he))
   have hp':=(vB).order_ge
   have hτ:=masts Z Ω v Chi.canonical Chi.canonical 1 (1:Config G n₀) hv _ hW (one_healthy _ _ (B₁).threshold_pos.le)
   intro ψ X' Y' hX hY
   letI:Nonempty (Forest (X).ratio):=Tree.select _ (X).patch.odd_side
   rw [hτ.2 _ (by simp only [List.length_cons,List.length_nil]; exact Nat.le_trans (by decide:2≤6) hp')]
   refine like_sub_tame _ (fun _=> like_sub_tame _ (fun _=> colorion hm hP hp hc hb hV H z hz h! i G' hi η he _ _ hX hY _ _))
-- compare fourth order probe on pane exactly.Inspection ledger.Optional supplement
open YM.RG12
set_option quotPrecheck false
local notation "f₀" => ocean (V1) (f!) y
local notation "v0"=> ((L).val:ℂ)^d
local notation "F0"=> (Blush.pane Z T! v0 Z0)
local notation "C?" η:max γ:max=>cove (K z) 0 Xp ankle _ _ (lofty (K z) i hz).1 (lofty (K z) i hz).2 η γ h!
protected def Ai (d:ℕ)(p:Labels.Jet G):=Classical.choose (Spins.energyProbe (hol G) d p)
omit hm hP hp hc hb hV h! hz in
lemma ai_pos (d:ℕ)(p:Labels.Jet G):0≤Cub.Ai d p:=Classical.choose_spec (Spins.energyProbe (hol G) d p)|>.1
-- NEED only DIAGONAL songs.Brush suppliers use comparison gemstone. W.engineering.P.den no post.
include hC in
set_option maxHeartbeats 880000 in
lemma quartz8 {ε W:ℝ} (hW:0≤W)(G':Legato.Pads8 (M:=M) D C Q R B.span ε A.delay)(hS:G.Simple) (hi: ((F).grades i).2=2)
    (hF:∀ (η:ℂ→L[ℝ]ℝ)(γ:∀ x:ℂ,‖η x‖ ≤ ‖x‖),‖η‖≤ 1 → ∀ Z':Directions G n₀,(B₁).dirBound 0 Z' →
      ‖leftDerivs (Charity.matin (C? η γ) Z (icon Z Ω) Chi.canonical) [Z',Z'] 1-leftDerivs (g! η) [Z',Z'] 1‖ ≤ W)
    (a:Labels.Jet G)(l:Fin (d+1))(hL:l.val=4):
    let Z':=W+(y^ε)/y
    ‖Local.sample (hol G) 0 Yp ((B₁).threshold) (F0) (a,l) - Local.sample (hol G) (0:Site n₀) Yp ((B₁).threshold) (v0 • f₀) (a,l)‖ ≤ Cub.Ai d a*((L).val:ℝ)^d*(Z'+Z'):=by
     intro v₀
     have hv:= (united (n:=n) hm hP hp hV); have hB:(K z).p=B₂:= (H.knows _ z.2).1.point; rw [← hB] at hv
     have hU:= A.B.valid.pays m
     obtain ⟨aF,b,y₀,g,vα,Y',p₁,B',g',e,ν,hX,hY,N'',hη⟩:= (hC _ _ hU _ hb.1).1.2 _ _ _ _ (Opera.protocol A.B hm B.pledging.conducts.full (n:=n)) _ _ Z
     have hn:= Rain.jersey (A:=A) (m:=m)|>.1
     have h₁' := Mercury.cornice Z (T!).live Ω rfl v Chi.canonical N'' hv.1 hη hn.le
     have h₂' := Mercury.cornice Z (T!).pale Ω rfl v Chi.canonical N'' hv.1 hη hn.le
     have h₁:= Blush.ornate h₁'; have h₂:=Blush.ornate h₂'; have hF': (B₁).Regular Yp (F0):= regular_smul (v0) (regular_add h₁ (regular_smul Complex.I h₂))
     have hk : 4 ≤ (B₁).order:= (le_trans (by norm_num) (B₁).order_ge)
     have hk':4 ≤ (vB).order:= hn ▸ hk
     have hy:= (show (0:ℝ) ≤ y from zero_le_one.trans (A.B.a.fits.delayed m).le) -- name
     have hZ:Germ 4 (F0) (1:Config G n₀):= (hF'.smooth 1 (one_healthy Yp _ (B₁).threshold_pos.le)).of_le (Nat.cast_le.mpr hk)
     let O:Config G n₀→ℂ:= f₀; let V(η:ℂ→L[ℝ]ℝ) := deem 0 y (WaterLevels.forecast V m N n) (η ∘ (f!)); let Y(η:ℂ→L[ℝ]ℝ):= Complex.ofRealCLM ∘ V η
     have h1: O=Y Complex.reCLM+ Complex.I • Y Complex.imCLM:=by funext W; change _= ↑(O W).re + Complex.I*↑(O W).im; rw [mul_comm Complex.I]; exact (Complex.re_add_im _).symm
     let q:= (K z).p.threshold
     let H'(w:Config G n₀):= (Heir.route (WaterLevels.forecast ‹Bolt A› m N n)) (Heir.crop ((X).ratio.parent (0:Site n₁)) (Heir.reach (y)) 1 w)
     have hN : (X).ratio.parent 0=0:= ((X).ratio.root.map_zero : (X).ratio.embed 0=0) ▸ (X).ratio.embed_parent 0
     have he (w:Config G n₀): O w= (q^2)⁻¹ • Spins.drawing (S!) 0 i (H' w):=by
        change (Local.presented S! 0 q (Place.copy _ i) (increment 1 (H' w)))=_ -- ocean uses parent zero?
        rw [Spins.draw S! (0:Site n₁) i,hi]
     obtain h':=Repeat.Cub.posed (u).Z hv.2.rehearsed.wire (o:=((X).ratio.parent (0:Site n₁)))
     let f:=Spins.drawing (S!) (0:Site n₁) i
     obtain ⟨M,hM,hT⟩:=Spins.uniform (n:=4) S! i
     have hQ:= (hT n₁ (0:Site n₁) 0 (by simp)).smooth; change ContDiffAt ℝ (↑(4:ℕ)) f 0 at hQ
     let t:=H'∘ increment 1; have he0:t 0=0:=by unfold t H'; rw [Function.comp_apply,Work.G07.at_zero_increment, Repeat.Cub.blankBirth,map_zero]
     have hc':ContDiffAt ℝ 4 t 0:=(Heir.route ..).contDiff.contDiffAt.comp _ (h'.germ.of_le le_top)
     let H!:Config G n₀→ℂ:= (v0) • O; let g:=H! ∘ increment 1
     have hb0 : g= (v0) • ((q^2)⁻¹ • (f ∘ t)):=funext fun x=>congr_arg (fun w=>(v0) • w) (he _)
     have hξ:= ((show ContDiffAt ℝ 4 f (t 0) from he0.symm ▸ hQ).comp _ hc')
     have hK:Germ 4 H! 1:=by change ContDiffAt ℝ 4 g 0; rw [hb0]; exact (hξ.const_smul ((q^2)⁻¹:ℝ)).const_smul (v0)
     have hD:fderiv ℝ ((F0) ∘ increment 1) 0=fderiv ℝ g 0:=by
        have he0':= Spins.no_low S! (0:Site n₁) i (Next.Foundations.valuation G d) (show 1<(F|>.grades i).2 from hi.symm ▸ Nat.one_lt_two)
        let z':Directions G n₀→ℂ:= (q^2)⁻¹ • (f ∘ t)
        have he':DifferentiableAt ℝ z' 0:=(hξ.const_smul ((q^2)⁻¹:ℝ)).differentiableAt (by norm_num)
        rw [Spins.bareHat hS hF'.symmetry hZ,show g=(v0) • z' from hb0,fderiv_const_smul he']; unfold z'; rw [fderiv_const_smul (hξ.differentiableAt (by norm_num)),fderiv_comp _ (by rw [he0]; exact hQ.differentiableAt (by norm_num)) (hc'.differentiableAt (by norm_num)),he0,show fderiv ℝ f 0=0 from ?_]; swap; · rw [← norm_eq_zero,← norm_iteratedFDeriv_one,he0',norm_zero]
        ext «v»; simp
     have hL': ‖v0‖= ((L).val:ℝ)^d:=by simp
     refine le_trans ((Classical.choose_spec (Spins.energyProbe (hol G) d a)|>.2) n₀ 0 Yp l hL B₁ (F0) H! (‖v0‖*(v₀+v₀)) hZ hK hD ?_ (by unfold v₀; positivity)) (by rw [←mul_assoc,hL']; rfl)
     intro D' hd
     have hr : ‖Complex.reCLM‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp only [one_mul]; exact juror)
     have ht' : ‖Complex.imCLM‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simp only [one_mul]; exact jurorI)
     have h3 (η:ℂ→L[ℝ]ℝ)(γ)(hs:‖η‖≤1): ‖leftDerivs (Charity.matin (C? η γ) Z (icon Z Ω) Chi.canonical) [D',D'] 1-leftDerivs (V η) [D',D'] 1‖ ≤ v₀:=by
         refine (norm_sub_le_norm_sub_add_norm_sub _ (leftDerivs (g! η) [D',D'] 1) _).trans (add_le_add (hF η γ hs D' hd) ( chorus8 hm hP hp hc hb hV H z hz h! i G' hi η hs D' D' hd hd))
     change ‖leftDerivs (F0) [D',D'] 1- leftDerivs H! [D',D'] 1‖≤ _; unfold H!; rw [h1]
     have hs1 := (Graces.readings Complex.reCLM (lofty (K z) i hz).1); have hs2 := (Graces.readings Complex.imCLM (lofty (K z) i hz).1)
     apply Cub.cleared (d:=4) ((h₁'.smooth 1 (one_healthy Yp _ (B₁).threshold_pos.le)).of_le (Nat.cast_le.mpr hk)) ((h₂'.smooth 1 (one_healthy Yp _ (B₁).threshold_pos.le)).of_le (Nat.cast_le.mpr hk)) (by exact (deem_focus (o:=(0:Site n₁)) hv.2 hs1).germ.of_le (Nat.cast_le.mpr hk')) (by exact (deem_focus (o:=(0:Site n₁)) hv.2 hs2).germ.of_le (Nat.cast_le.mpr hk')) v₀ v₀ [D',D'] (by simp) (v0) (h3 _ juror hr) (h3 _ jurorI ht')
end YM.PhysicalNext.Repeat.Cub
