import YM.UVExtension.Hearth.Spices
import YM.MergeProof.South.FinalG
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Hearth
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open MeasureTheory Push GridApprox Mast Steady
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
open Relay Mast.Cellar Steady Push GridApprox Accent Cells

variable {t:ℕ→ℕ}{S v R} (U:Cellar S t R) (K:ℕ→ℕ)(h:Scrim (U.yard v) W (far A.B.a) (waybill A.B.a) (near A.B.a) (renal A.B.a) (Legato.Bandage.fly A.B.a) (mutt A.B.a K) (Orchard.roof S v))
    (hK: Stock.Tabs A.B.a) (J k:ℕ)(w:ℝ)(hw:0<w)(hz:Stock.Tabs.opens A.B.a 1 J m)
local notation "C0"=> yard v U
local notation "F"=> (C0|>.labels.level d)
local notation "K0"=> lensScope C0 d
local notation "o!"=> (0:Site ((C0).side k n))
local notation "T!"=> A.B.a.S

open Extraction OS RelayDifference
-- lift across registry J.Spectrum. retain rates eventually.M
lemma seatingM (P:Family G)(d m J:ℕ)(ε ζ:ℝ)(he:0<ε)(hh:0<ζ)(L:P.label d) : ∀ᶠ i in atTop,∃ w:ℝ, 0<w∧ w*‖alto P.path m d‖*(4*(1+(P.path.levels.params i).columns)/Bid.gainChart P.path i m) ≤ ζ/2 ∧ stockK P i d L * (stakes P J m/w) ≤ ε:=by
   let C:=P
   let T:=P.path
   let Y i:= (P.path.levels.params i).columns
   let b i:= ‖alto T m d‖*(4*(1+Y i)/Bid.gainChart T i m); let s:= stakes P J m; let w i:ℝ:= ζ/2/b i
   have hv i:0 < b i:=by unfold b; rw [alto_norm]; have hz:0 < C.S.a m:= C.S.a_pos m; have hh:1 ≤ Y i:= (C.path.levels.params i).columns_ge; have ht:0 < Y i:=zero_lt_one.trans_le hh; have ho:0<Bid.gainChart T i m:= Real.exp_pos _; exact mul_pos (inv_pos.mpr (pow_pos hz _)) (div_pos (by positivity) ho)
   have hw i : 0 < w i:= div_pos (by positivity) (hv i)
   have ht : ∀ᶠ i:ℕ in atTop, stockK C i d L * (s/w i) ≤ ε:=by
      let F':= Extraction.Order.full
      let a i:= stockK C i d L * s * (ζ/2)⁻¹
      let l i:= 4*(1+Y i)
      let v i:= ‖alto T m d‖* l i*Real.exp (Push.RelayDifference.gamma*C.S.scale m)
      have hD(i:ℕ): stockK C i d L*(s/w i)=a i*v i*RelayDifference.flight C (-RelayDifference.gamma) (i,0):=by
         unfold w; rw [div_div_eq_mul_div]; unfold b a v RelayDifference.gamma RelayDifference.flight l Bid.gainChart; rw [mul_sub,Real.exp_sub,div_div_eq_mul_div,neg_mul,Real.exp_neg]; unfold C T; dsimp only [Family.S]; ring_nf; simp only [inv_inv]; ring
      have hX : RelayDifference.Slow C F' (fun i=> Real.exp (Work.D01.columnLogs (T).levels i.1)):=by
         intro ε he; filter_upwards [(RelayDifference.cutoff_grows F').eventually (Work.D01.columnLogs_le (T).levels ε he)] with i hx; exact ((Real.norm_of_nonneg (Real.exp_pos _).le).le.trans (Real.exp_monotone hx): ‖Real.exp (Work.D01.columnLogs (T).levels i.1)‖ ≤ _)
      have hI: RelayDifference.Slow C F' (fun i=>a i.1):= ((((RelayDifference.Slow.const (C:=C) _).mul hX).mul (RelayDifference.Slow.const _)).mul (RelayDifference.Slow.const _)).mul (RelayDifference.Slow.const _)
      have hz₀: RelayDifference.Slow C F' (fun i=> l i.1):= (RelayDifference.Slow.const (C:=C) (4:ℝ)).mul ((RelayDifference.Slow.const (C:=C) 1).add (RelayDifference.columns_slow (C:=C) (f:=F')))
      have hz: RelayDifference.Slow C F' (fun i=>v i.1):=((RelayDifference.Slow.const (C:=C) _).mul hz₀).mul (RelayDifference.Slow.const (C:=C) _)
      have h₀: ∀ᶠ i in F'.fuse, stockK C i.1 d L * (s/w i.1) ≤ ε:=by
         filter_upwards [(hI.mul hz).sink (a:=1/16) (b:=RelayDifference.gamma) (by unfold RelayDifference.gamma; norm_num), (RelayDifference.flight_lands (ε:=1/16) (C:=C) (f:=F') (by norm_num)).eventually (ge_mem_nhds he)] with i h h'; rw [hD]; exact h.trans h'
      rw [Extraction.Order.fused] at h₀; exact h₀.exists.choose_spec
   filter_upwards [ht] with i hi; exact ⟨w i,hw i,(show _=_ from by rw [mul_assoc]; exact div_mul_cancel₀ _ (hv i).ne').le,hi⟩

include a hv
-- chart h.Calendar. Inputs represent touch.Cert. use covers only.K
lemma banquet (I:ℕ)(u:Fin I→ (C0|>.book.Token))(o:Fin I→ Cover)(hc:Injective (wrap ((yard v U).side J n) ∘ o))(hk:J ≤ k) (g:Fin I→ℕ→ Config G (A.B.a.S.side k n)→ℂ)(p:∀ i,Tune atTop (g i))(q:Fin I→ℝ)(t:Fin I→ℝ)(r:ℕ)(hh:GridApprox.room A.B.a J k r)
   (h:∀ᶠ N in atTop, ∃ hN:k ≤ N, let C':=yard v U; let T:= tilesAt A.B.a.S n (hk.trans hN); ∀ i, Interior (T.chamber 0) (C'.seen (u i) 0)∧ T.rootTest (C'.beta N n) (C'.seen (u i) 0) ≤ t i∧ Interior (GridApprox.window (0:Site (A.B.a.S.side k n)) r) (g i N) ∧ T.rootTest (C'.beta N n) (GridApprox.backTo C'.path N n hN (g i N)-C'.seen (u i) 0) ≤ q i) : ∃ F':ℕ→ℂ, UVExtension.Arrives F' ∧∀ᶠ N in atTop, ‖F' N-(yard v U).numeric N n u (fun i=> location A.B.a.S J N n (o i))‖ ≤ (∏ i,(q i+t i))-(∏ i,t i):=by
   let P:= C0; let o':= (wrap (P.side J n)) ∘ o; let L i:= lifting A.B.a.S n hk o' (fun j=> g j i); let t':=(P|>.path)
   have hp: Tune atTop L:= polysT _ (fun i _=> (p i).cues (translate (anchor A.B.a.S n hk (o' i))))
   have ht:∀ᶠ i in atTop, Envelope (L i):= h.mono (fun i hi=> lifts_env _ _ hk _ _ fun j=> cylinder_env (hi.choose_spec j|>.2.2.1))
   refine ⟨_, arrival S v k n a x hv L hp ht,?_⟩; filter_upwards [ht,h] with N ht h
   obtain ⟨hN,hn⟩:=h; let V:= t'.rep N n k
   let Q i:= GridApprox.backTo t' N n hN (g i N)
   let f (i:Fin I):= P.seen (u i) (0:Site (A.B.a.S.side N n))
   have hx:tasting V (L N)= moment (P.beta N n) (lifting A.B.a.S n (hk.trans hN) o' Q):=by rw [show lifting A.B.a.S n _ o' Q= backTo t' N n hN (L N) from (aggregation P.path hN hk r o' hc _ (fun i=> (hn i).2.2.1) hh).symm]; exact (scaledK _ (Orchard.selected S v) k N n hN ht).symm
   have hh:= GridApprox.tariff A.B.a.S (hk.trans hN) (P.beta N n) (Vintage.YM.Cells.seamless (intakeV v U) N n) o' hc f Q t q (fun i=> (hn i).1) (fun i=> whereBack P.path hN hk r (hn i|>.2.2.1) hh) (fun i=> (hn i).2.1) (fun i=>(hn i).2.2.2)
   let X i:= anchor A.B.a.S n (hk.trans hN) (o' i)
   have he i U : f i (translate (X i) U)=P.seen (u i) (X i) U:= (P.translation (d:=(u i).fst) (N:=N) (p:=n) 0 (X i) (u i).snd U).trans (congr_arg (fun x=>P.seen (u i) x U) (zero_add _))
   have hF : (fun U=> ∏ i,f i (translate (X i) U))=(fun U=>∏ i,P.seen (u i) (X i) U):= funext fun u=> Finset.prod_congr rfl fun i _=> he i u
   have hE: moment (P.beta N n) (fun U=> ∏ i,f i (translate (anchor A.B.a.S n (hk.trans hN) (o' i)) U))= P.numeric N n u X:=congr_arg (moment (P.beta N n)) hF
   -- avoid rewrites due defeq. match
   change ‖moment (P.beta N n) (lifting A.B.a.S n _ o' Q) - moment (P.beta N n) (fun U=> ∏ i,f i (translate (anchor A.B.a.S n (hk.trans hN) (o' i)) U))‖ ≤ _ at hh; rw [hE] at hh
   change ‖tasting V (L N)-_‖≤_; rw [hx]; simp_rw [Cells.location,dif_pos (hk.trans hN)]; exact hh

omit a hv in
lemma closet (P:Family G)(n J:ℕ)(w:P.book.Token)(h: Extraction.Wcmain P)(hj:P.ref w.1 ≤ J) : ∃ t:ℝ,∀ᶠ N in atTop, Extraction.centeredBudget P w t J N n:= by
    obtain ⟨r,hr,h⟩:=h w.1 (‖w.2‖+1) 1 (by positivity) (by norm_num); refine ⟨r*P.S.a J^(-(w.fst:ℝ)-1), (h J hj).mono fun i ht=> ?_⟩; exact ht n w.2 (by simp)

include hK h
lemma food (hw:Extraction.Wcmain (yard v U))(I:ℕ)(u:Fin I→ (C0|>.book.Token))(o:Fin I→ Cover)(hc:Injective (wrap ((yard v U).side J n) ∘ o))(hl : ∀ i,(C0).ref (u i).1 ≤ J) : UVExtension.Arrives fun N=>(yard v U).numeric N n u (fun i=> location A.B.a.S J N n (o i)):=by
   let m:= Stock.Tabs.chosen A.B.a 1 hK J; have hz: Stock.Tabs.opens A.B.a 1 J m:= Stock.Tabs.opened ..
   choose t' ht using fun i=> closet C0 n J (u i) hw (hl i)
   let P':= C0
   have hm i: P'.ref (u i).1 ≤ m := (hl i).trans hz.1
   let Ψ N:= P'.numeric N n u (fun i=> location A.B.a.S J N n (o i))
   let Φ (q:ℝ):= (∏ i,(q+t' i))-(∏ i,t' i); have hh: Continuous (fun q:ℝ=>Φ q):=by unfold Φ; fun_prop
   have hx (q:ℝ)(hq:0<q): ∃ F':ℕ→ℂ, UVExtension.Arrives F' ∧∀ᶠ N in atTop, ‖F' N-Ψ N‖ ≤ Φ q:=by
      have hp(i):=seatingM C0 (u i).1 m J q _ hq (h.grows (u i).fst m (hm i)) (u i).snd
      let r:= Finset.univ.sup (fun i=> lensScope C0 (u i).fst)
      have hr i: lensScope C0 (u i).fst≤r:= Finset.le_sup (s:=Finset.univ) (f:= fun i=> lensScope C0 (u i).fst) (Finset.mem_univ i)
      obtain ⟨k,hk,hZ,hM⟩:= ((eventually_ge_atTop m).and ((eventually_all.mpr hp).and (GridApprox.plenty A.B.a J r))).exists
      choose w hw hh hb using hZ; choose g hg H' using fun i=> peeling (v:=v) (u i).fst m n x hv U K h hK J k (w i) (hw i) hz (u i).snd (hm i) hk (room_small _ (hr i) hM) (hh i)
      refine banquet n a x hv U J k I u o hc (hz.1.trans hk) g hg (fun _=>q) t' r hM ?_
      filter_upwards [eventually_all.mpr H',eventually_all.mpr ht,eventually_ge_atTop k] with N hN H' hn; exact ⟨hn, fun i=>let ⟨w',h₁,h₂⟩:= H' i; ⟨(h₂ 0).1,(h₂ 0).2, ((hN i).choose_spec.1.enlarges (window_large (hr _))),((hN i).choose_spec.2.trans (hb i))⟩⟩
   apply cauchySeq_tendsto_of_complete; rw [Metric.cauchySeq_iff]
   intro ε he; obtain ⟨δ,hδ,hd⟩:= Metric.continuousAt_iff.mp (hh.continuousAt (x:=0)) (ε/4) (by positivity) -- at 0
   let q:= δ/2; have hq:0<q:=half_pos hδ
   have hD:Φ q<ε/4:=by
      have hc:=hd (show dist q 0<δ by rw [dist_zero_right,Real.norm_of_nonneg hq.le]; exact half_lt_self hδ); have hp:Φ 0=0:=by simp [Φ]
      rw [hp,dist_zero_right] at hc; exact (le_abs_self _).trans_lt hc
   obtain ⟨f,⟨b,hb⟩,hw⟩:= hx _ hq; obtain ⟨M,hM⟩:= eventually_atTop.mp hw; obtain ⟨N,hN⟩:= Metric.cauchySeq_iff.mp hb.cauchySeq (ε/4) (by positivity)
   refine ⟨max N M, fun i hi j hj=>?_⟩
   have hv(i)(hh:M ≤ i):dist (f i) (Ψ i)<ε/4:= by rw [dist_eq_norm]; exact (hM _ hh).trans_lt hD
   have hx:=dist_triangle4 (Ψ i) (f i) (f j) (Ψ j); have hy:= hN i (by omega) j (by omega); change dist _ _<_ -- inspect
   rw [dist_comm (Ψ i) (f i)] at hx; have hh':=dist_comm (Ψ j) (Ψ i); change dist (Ψ i) (Ψ j)< ε; linarith only [hx,hh', hv i (by omega),hv j (by omega),hy,he]
end YM.UVExtension.Hearth
