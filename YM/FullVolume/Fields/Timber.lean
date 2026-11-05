import YM.FullVolume.Fields.Capital
/-! Rent-to-actual full fixed family point, including mixed weights, at ALL fixed fitted augurs of separated ancestry. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}(hG:G.Simple){M:Metals G}{P:Rolls M.p}{A:Alloy M P}{X:Factor A}{Y:Bolt A}{C:ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K)
open YM.MergeProof MergeProof.Matric Guard
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Sever
variable {q:ℕ→ℕ→∀ p,Shoot.Trail A.B.a p}{f:ℕ→ℕ}{p k r:ℕ}(J:Rising X q f p k) {ψ:ℕ→ℕ} (T:∀ n d N p,TransferData ((Labels.frames G).level d) (A.B.bake.make (q n)) N p)
variable (hx:Jams.Wild X.shape A.delay)(hz:Nest X Y)
namespace Rising
open Marker
open MergeProof.Accent Extra.Multi
set_option quotPrecheck false
local notation "P'"=> A.B.a
local notation "F'"=> (Labels.frames G).level
local notation "C'"=> fun i=> wen (A:=A) q ψ T i
section
-- Cargo tariff uniformly at fixed rung
lemma limitVault {V:Type}[Fintype V]{n:Side} {f:ℕ→V→ Config G n→ℂ}{g:ℕ→V→Box n→ Config G n→ℂ}(hp:∀ i,Confluence fun j=>f j i)(hf:∀ i k,Confluence fun j=>g j i k)(w:V→ℝ)(he:∀ i,0<w i):∃ x y:ℝ,∀ᶠ n in atTop,Vault w (f n) (g n) x y:=by
    choose a ha using fun i=> (hp i).stretch; choose b hb using fun i k=> (hf i k).stretch; let x:=∑ i,w i*|a i|; let y_i(i:V):=∑ k:Box n,w i*|b i k|; let y:=∑ i,y_i i
    refine ⟨x,y,?_⟩; filter_upwards [eventually_all.mpr ha, eventually_all.mpr (fun i=> eventually_all.mpr (hb i))] with n hn hT; refine ⟨fun i U=>?_ ,fun i U=>?_⟩
    · exact (mul_le_mul_of_nonneg_left ((hn i U).trans (le_abs_self _)) (he i).le).trans (Finset.single_le_sum (fun i _=>mul_nonneg (he i|>.le) (abs_nonneg (a i))) (Finset.mem_univ _))
    exact (Finset.sum_le_sum (fun k _=> mul_le_mul_of_nonneg_left ((hT i k U).trans (le_abs_self _)) (he i).le)).trans (Finset.single_le_sum (f:=y_i) (fun i _=> Finset.sum_nonneg fun k _=>mul_nonneg (he i).le (abs_nonneg _)) (Finset.mem_univ _))
lemma cauchy_copy {X:Type} [PseudoMetricSpace X] {s v:ℕ→X}(h:CauchySeq s)(he:s=ᶠ[atTop] v): CauchySeq v:=by
   obtain ⟨N,hN⟩:= eventually_atTop.mp he; refine Metric.cauchySeq_iff.mpr fun e hε=>?_; obtain ⟨K,hK⟩:= Metric.cauchySeq_iff.mp h e hε
   refine ⟨max N K,fun i hi j hj=>?_⟩; obtain ⟨ha,hb⟩:= max_le_iff.mp hi; obtain ⟨hr,hf⟩:= max_le_iff.mp hj; rw [← hN i ha,← hN j hr]; exact hK i hb j hf
end
variable {V:Type}[Fintype V][DecidableEq V] (v:V→ℕ)(z:∀ i:V,((Labels.frames G).level (v i)).Coeff) (U:Census V)
variable (hc:∀ i,Tenable b J T hz (v i) ψ)(o:∀ i,V→ Site (A.B.a.S.side i p))(s:V→Motion)
-- under constant tables.Repeated.Bond.Fitted.
local notation "F!"=>fun j n (i:V) => harp (C' n) v z p (f n) o s j i
local notation "g!"=>fun j n (i:V) => chill (C' n) v z p (f n) o s j i
include hG b hx hz J T hc z
variable {ι:ℕ} -- fitting k+ general
noncomputable def Kout (j n:ℕ)(i:V) : Box (A.B.a.S.side j p) → Config G (A.B.a.S.side j p)→ℂ:= g! j n i
noncomputable def Eout (j n:ℕ)(i:V): Config G (A.B.a.S.side j p)→ℂ:=F! j n i
local notation "X₀"=> Kout (q:=q) (ψ:=ψ) (f:=f) (p:=p) T v z o s
local notation "X₁"=> Eout (q:=q) (ψ:=ψ) (f:=f) (p:=p) T v z o s
variable (hr:∀ i,ψ (v i) ≤ r)
include hr
lemma ships (j:ℕ)(hw:r ≤ j) (w:V→ℝ)(he:∀ i,0<w i): ∃ x y:ℝ,∀ᶠ n in atTop,Vault w (X₁ j n) (X₀ j n) x y:=by
    have h(i):=J.hail hG b T hx hz (v i) (hc i) (z i) j ((hr i).trans hw) (s i) (fun m=> o m i)
    exact limitVault (f:= X₁ j) (g:=X₀ j) (fun i=> (h i).1) (fun i l=>(h i).2 l) w he
omit hG hx in
lemma winds (j:ℕ)(hw:r ≤ j): ∀ᶠ n in atTop,∀ i, Measurable (X₁ j n i)∧∀ l,Measurable (X₀ j n i l):=eventually_all.mpr fun i=> J.markets b T hz (v i) (hc i) (z i) j ((hr i).trans hw) (s i) (fun m=>o m i)
include U
set_option maxHeartbeats 480000 in
lemma latter (j:ℕ)(hj:k≤ j)(he:r ≤ j)(a:U.Mode): CauchySeq (fun n=> Cresting (C' n) v z p (f n) j o s a):=by
    let R i:= q i (f i) p j; have ht:PUnit.{1} := ⟨⟩
    have h(i):= J.hail hG b T hx hz (v i) (hc i) (z i) j ((hr i).trans he) (s i) (fun m=>o m i); have hQ := J.flooded hj
    let b':=till P' j p; have hx : 0<b':= tills (A.B.bake.make (q 0)) j p; have hp:= J.helmet.sails.eventually (eventually_ge_atTop j)
    have hs : ∀ᶠ i in atTop, b' ≤ lack (R i):= hp.mono fun i hi=>by let H:=A.B.bake.make (q i); let hm:= J.branch i|>.choice; change _ ≤ lack (H.rep (f i) p j); rw [taps H hm]; exact lingers H hm _ _ _ hi; exact hi
    have hc':= J.winds b T hz v z hc o s hr j he
    let F n:= mid (R n) (X₁ j n) (X₀ j n) a
    apply cauchy_copy (s:=F) (Confluence.laven R (X₁ j) (X₀ j) hQ (fun i=> (h i).1) (fun i k=>(h i).2 k) a hx hs hc')
    exact hp.mono fun i hi=> reply (A.B.bake.make (q i)) (J.branch i|>.choice) hi _ _ a -- universe N parameters implicit
-- grant possible books.D.Spec ℕ.unindexed.REVENUE.FITTER.motions.
variable {D:∀ n N p m:ℕ,m<N→GaugeDoor ((A.B.bake.make (q n)).rep N p (m+1)) ((A.B.bake.make (q n)).rep N p m)} {u π φ δ:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{p':ℕ→ℕ}
variable (hh:∀ᶠ n in atTop, Ponds (wen (A:=A) q ψ T n) K u π φ δ ζ p' (D n) p r (f n))(hp:∀ i,0<ζ (v i) r)
variable (hm : ∀ N, Migrating (A.B.bake.make (q N)) r p (f N) o)(hZ: Occupancy (o r) (p' r))(hO:∀ j ≥ r,Drake U (A.B.a.budget j).B (o j))
-- all not union derivative simultaneously. no reset reparameterizers.
include hh hp hm hZ hO
set_option maxHeartbeats 500000 in
lemma arrives (hk:k ≤ r)(a:U.Mode): CauchySeq fun n=> pilot (C' n) v z p (f n) o s a :=by
    choose w hw using fun i=> J.creditP hG b T hx hz (v i) (hc i) (z i) r (hr i)
    let x i:= ζ (v i) r/(|w i|+1); have hu i:0<x i:= div_pos (hp i) (by positivity)
    have hxc n i: x i*Next.Rank.Spindle.paid (C' n) (v i) r (f n) p (z i)≤ ζ (v i) r:= (mul_le_mul_of_nonneg_left ((hw i n).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one))) (hu i).le).trans_eq (by unfold x; field_simp)
    obtain ⟨H,y,hx'⟩:= Rising.ships hG b J T hx hz v z hc o s hr r le_rfl x hu
    let p₀ n:=pilot (C' n) v z p (f n) o s a
    let V':=fun j n=> Cresting (C' n) v z p (f n) j o s a
    let F₀:= refreeze A.B.a p r H y a x
    let g j:= Sever.brisk (A.B.a.budget j).B
    have hg:Tendsto g atTop atTop:=by
       have hb:Tendsto A.B.a.clock.hatBeta atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (A.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
       have hvb:= Work.E01.radiusB_tendsto.comp hb
       unfold g Sever.brisk; exact Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop.comp hvb).atTop_div_const (by norm_num))
    let hs:=J.helmet.sails
    have ht:Brine ((C' 0).path) r δ φ:=by
       obtain ⟨i,hv⟩:= hh.exists; have h:=hv.stay; refine ⟨h.water,h.mint,h.split,h.support⟩
    apply Metric.cauchySeq_iff.mpr; intro ε hε
    let t:=ε/4; have ht':0<t:=by unfold t; positivity
    obtain ⟨j,hj,h,hv⟩:= ((eventually_gt_atTop r).and ((hg.eventually (eventually_gt_atTop 2)).and (((tendsto_const_nhds (x:=F₀)).div_atTop (hg.atTop_div_const zero_lt_two)).eventually (ge_mem_nhds ht')))).exists
    let w':= march x φ r j; have hw': ∀ i,0<w' i:=fun i=> march_pos (C' 0|>.path) r δ φ x hu ht j hj.le i
    obtain ⟨s',t',hW⟩:= J.ships hG b T hx hz v z hc o s hr j hj.le _ hw'
    have hX : ∀ᶠ n in atTop, dist (p₀ n) (V' j n) ≤ t:=by
       filter_upwards [J.winds b T hz v z hc o s hr j hj.le,hx',hh,hW, hs.eventually (eventually_gt_atTop j)] with n hn ha hb hV hN
       obtain ⟨d,c,H,h⟩:= hb.night.days j hj.le hN
       rw [dist_eq_norm]; apply (Sever.echoes (C' n) v z p r (f n) j o s (J.branch n|>.choice) hb (fun i=>sound G _) hr (hxc n) hu hZ (hO _ le_rfl) (hm n) hN hj (hO _ hj.le) ?_ (show g j>2 by assumption) hV ha (fun i=> (hn i).1) (fun i=> (hn i).2) a).trans hv -- use H instead of h.S if order; hh Capture t ; hr wants `he:∀ psi.S.ref`; occult hM binder before
       linarith only [h.exp.1]
    obtain ⟨N,hN⟩:= eventually_atTop.mp hX; obtain ⟨u,hU⟩:= Metric.cauchySeq_iff.mp (J.latter hG b T hx hz v z U hc o s hr j (hk.trans hj.le) hj.le a) t ht'
    refine ⟨max u N,fun i hi n hn=> ?_⟩; obtain ⟨hs,hp⟩:=max_le_iff.mp hi; obtain ⟨he,hu⟩:=max_le_iff.mp hn; change dist (p₀ i) (p₀ n)< _
    have hv: dist (p₀ i) (p₀ n)≤ dist (p₀ i) (V' j i)+dist (V' j i) (V' j n) +dist (V' j n) (p₀ n):=(dist_triangle (p₀ i) (V' j n) (p₀ n)).trans (add_le_add (dist_triangle ..) le_rfl)
    have he':dist (V' j i) (V' j n)< t:= hU i hs n he; linarith only [hv,hN i hp,hN n hu,he',dist_comm (V' j n) (p₀ n),show ε=4*t from (by unfold t;ring),ht']
end Rising
end YM.PhysicalNext.Repeat.Legato.Bandage
#print axioms YM.PhysicalNext.Repeat.Legato.Bandage.Rising.arrives
