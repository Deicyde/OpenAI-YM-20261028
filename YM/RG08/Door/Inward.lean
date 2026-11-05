import YM.RG08.Door.North
/-!
# Calibration persists and T⁻¹ coherence. Reads exact joint output in calibrated raw
marks. No analytic field-height series inference beyond horizon shown.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit
open PertExtension.Series.Tested PertExtension.Series.Radial Scores
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
lemma invest_less (H:Hol G)(v:Letter F){U V:EnvelopeU D R G r}(he:Toute U)(hk:Toute V)(hp:Polished U)(hv:Polished V) : invest H (U-V) v=invest H U v-invest H V v := by rw [sub_eq_add_neg,← neg_one_smul ℝ V, invest_more H v he (tot_weight hk _) hp (polished_scale hv _),invest_sm H v _ hk hv]; ring
lemma travel (H:Hol G)(v:Letter F){U:ℕ→EnvelopeU D R G r}{A:EnvelopeU D R G r}{δ:ℕ→ℝ}(h:Twill (fun _=> C) δ U (fun _=> A) (fun _=>w))(hw:0<w)(he:0 ≤ δ)(hh:Tendsto δ atTop (𝓝 0))(hp:∀ i,Toute (U i))(hk:Toute A) : Tendsto (fun i=> invest H (U i) v) atTop (𝓝 (invest H A v)) := by
  let w' := min 1 w; have hv:0<w':=lt_min one_pos hw; let p:= h.soften (v:=fun _=> w') (fun i=>min_le_right ..)
  have hz:= digs H p.goes (fun _=>hv) (fun i=>min_le_left ..) (Weighed.constant _ (inv_nonneg.mpr hv.le)) v
  obtain ⟨B,⟨K,e,hK,H⟩,hx⟩:=hz.asset
  apply tendsto_iff_norm_sub_tendsto_zero.mpr; refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun i=> K*C^e*δ i) (fun i=>?_) (by simpa using hh.const_mul (K*C^e))
  rw [← invest_less _ v (hp i) hk (scarlet (h.one.serves.choose_spec.2 i) hw) (scarlet (h.two.serves.choose_spec.2 i) hw)]
  exact (hx i).trans (mul_le_mul_of_nonneg_right (H i|>.2) (he i))
variable {I:Type}{u:I→Windows}
variable (he:Tights T S ν D' u)
include he
local notation "Ξ" => Xe (u:=u) T ν D'
local notation "♣" => Te (u:=u) T ν D'
local notation "Υ" => Ye (u:=u) X ν D' T
local notation "Ⓨ" => menu X
local notation "Δ" => chop X (1/4)
local notation "◆" => (zPlay X Ω ν D' H h hD)
local notation "◇" => (wPlay X Ω ν D' H h hD)
local notation "✤" => glowSig X Ω ν D' H h hD
local notation "Ψ" => puffSig X Ω ν D' H h hD

lemma hues (x:Launch u)(hk:e≤E)(b: Letter F)(r): Hurled (fun i=>Υ (low (escalates x i)) b e r) (◆ x.i b e r) := Twill.stint (w:=ώ T x.i) (C:=x.farY X) ((frozenY he hk b r).move fun i=>low (escalates x i)) (bye X x) (fun _=>(gain_pos ..).le) (T.pos _|>.le)
lemma irons (x:Launch u)(hk:e≤E)(b:Letter F)(r): Hurled (fun i=> Ξ (escalates x i) b e r) (◇ x.i b e r) := Twill.stint (w:=ώ T x.i) (C:=x.farY X) ((frozenX he hk b r).move (escalates x)) (bye X x) (fun _=>(gain_pos ..).le) (T.pos _|>.le)
lemma peakY (x:Launch u)(b:Letter F) : SnowFirm E (slot b) (◆ x.i b) := gazette (X:=fun i=> Υ (low (escalates x i)) b) (fun e he' r=> hues he x he' b r) (fun i=>(he.firs _).rank _) (fun e he' r=> scarlet ((frozenY he he' b r).two.serves.choose_spec.2 (low (escalates x 0))) (T.pos _))
lemma peakX (x:Launch u)(b:Letter F) : SnowFirm E (slot b) (◇ x.i b) := gazette (X:=fun i=> Ξ (escalates x i) b) (fun e he' r=> irons he x he' b r) (fun i=>(he.lived _).rank _) (fun e he' r=> scarlet ((frozenX he he' b r).two.serves.choose_spec.2 (escalates x 0)) (T.pos _))

lemma peaks (x:Launch u)(hk:e≤E)(a b: Letter F): Tendsto (fun i=> hot (♣ (escalates x i)) e a b) atTop (𝓝 (hot (✤ x.i) e a b)) := leasePass (y:= x.farY X) (δ:=fun i=>Δ (escalates x i)) (fun _=>(gain_pos ..).le) (bye X x) (Summit.Lease.whirls (frozenT he hk a b) (escalates x))
lemma peaksB (x:Launch u)(hk:e≤E)(a b:Letter F): Tendsto (fun i=> hot (♣ (escalates x i))⁻¹ e a b) atTop (𝓝 (hot (Ψ x.i) e a b)) := leasePass (y:=x.farY X) (δ:=fun i=>Δ (escalates x i)) (fun _=> (gain_pos ..).le) (bye X x) (Summit.Lease.whirls (frozenB he hk a b) (escalates x))
lemma anchorsY (x:Launch u)(hk:e≤E): hot (atlas H (◆ x.i)) e= hot (1:Session (Letter F)) e := by
   ext i j; have eh(v) := (he.firs (low (escalates x v))).cost
   suffices he : Tendsto (fun v=>hot (atlas H (Υ (low (escalates x v)))) e i j) atTop (𝓝 (hot (atlas H (◆ x.i)) e i j)) by
     simp_rw [eh] at he; exact tendsto_nhds_unique he tendsto_const_nhds
   simp_rw [atlas_fees,auditT]; apply tendsto_finsetSum _; intro v hv; split_ifs with hV
   swap; exact tendsto_const_nhds
   have hz:e+v-slot i ≤ E:= by have hh:= mem_range.mp hv; omega
   exact travel H i (δ:=fun i=> Δ (escalates x i)) (w:=ώ T x.i) (C:=Launch.farY X x) ((frozenY he hz j v).move (fun i=>low (escalates x i))) (T.pos _) (fun _=> (gain_pos ..).le) (bye X x) (fun i=>seat_made ((he.firs _).rank j)) ((peakY he x j).sector _ hz v|>.1)
lemma price_correct (x:Launch u)(hk:e≤E) : hot (✤ x.i) e= hot (atlas H (◇ x.i)) e:= by
    ext i j; refine tendsto_nhds_unique (peaks he x hk i j) ?_
    change Tendsto (fun v=> hot (atlas H (Ξ (escalates x v))) e i j) _ _
    simp_rw [atlas_fees,auditT]; apply tendsto_finsetSum _; intro v hv; split_ifs with hV
    swap; exact tendsto_const_nhds
    have hz:e+v-slot i≤E:= by have hh:=mem_range.mp hv; omega
    exact travel H i (δ:=fun i=> Δ (escalates x i)) (w:=ώ T x.i) (C:=x.farY X) ((frozenX he hz j v).move (escalates x)) (T.pos _) (fun _=>(gain_pos ..).le) (bye X x) (fun v=> seat_made ((he.lived _).rank j)) ((peakX he x j).sector _ hz _|>.1)
lemma coins_meet (x:Launch u)(hk:e≤E)(b:Letter F)(r): ◇ x.i b e r=bureau (◆ x.i) (✤ x.i) b e r := by
    have hv:= (hurled_t (irons he x hk b r))
    refine tendsto_nhds_unique hv ?_; simp_rw [fun i=>(he.reads i).2, expose]
    apply tendsto_finsetSum _; intro i _; apply tendsto_finsetSum _; intro j hj
    have hp:=peaks he x (e:=j) (by have hh:=mem_range_succ_iff.mp hj; omega) i b
    exact hp.smul (hurled_t (hues he x (e:=e-j) (by omega) i r))
omit he in
lemma melt {S T: ℕ→Session (Letter F)}{X Z:Session (Letter F)}(h:∀ i≤e,∀ a b,Tendsto (fun j=> hot (S j) i a b) atTop (𝓝 (hot X i a b)))(hk:∀ i≤e,∀ a b,Tendsto (fun j=>hot (T j) i a b) atTop (𝓝 (hot Z i a b)))(he:∀ j:ℕ,S j*T j=1): hot (X*Z) e=hot (1:Session (Letter F)) e := by
  ext a b; have hb : Tendsto (fun j=> hot (S j*T j) e a b) atTop (𝓝 (hot (X*Z) e a b)):= by
    simp_rw [hot_mul,Matrix.sum_apply,Matrix.mul_apply]; apply tendsto_finsetSum _; intro i hi; have hp:=mem_antidiagonal.mp hi; exact tendsto_finsetSum _ (fun j _=> (h i.1 (by omega) a j).mul (hk _ (by omega) j b))
  simp_rw [he] at hb; exact tendsto_nhds_unique hb tendsto_const_nhds
lemma sigInv (x:Launch u)(hk:e≤E): hot ((Ψ x.i) * (✤ x.i)) e= hot (1:Session (Letter F)) e ∧ hot ((✤ x.i)*(Ψ x.i)) e=hot (1:Session (Letter F)) e := by
    have hx i:= recoupC (he.reads (escalates x i)).1; exact ⟨melt (S:=fun i=> (♣ (escalates x i))⁻¹) (fun j hj=>peaksB he x (hj.trans hk)) (fun j hj=>peaks he x (hj.trans hk)) (fun i=>Matrix.nonsing_inv_mul _ (hx i)),melt (S:=fun i=> ♣ (escalates x i)) (fun j hj=> peaks he x (hj.trans hk)) (fun j hj=> peaksB he x (hj.trans hk)) (fun i=>Matrix.mul_nonsing_inv _ (hx i))⟩
end YM.RG08.Door
