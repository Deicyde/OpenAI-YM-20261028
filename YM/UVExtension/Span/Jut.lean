import YM.UVExtension.Span.Horizon
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Span
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Score
open Oriented Vine Concerted
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Score v T H k l χ A b u B N r d f' V Z)
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} {M:κ→ Hat G F}
-- states use explicit
variable (he:∀ᶠ i in qq,Mode (Y i) (τ i) k u)(hK:∀ᶠ i in qq,(M i).legal s ∧ Y i (τ i)=(M i).bill)
-- K value inside sectors outside health. Don't collapse row truncation principal
include p h
variable (g:κ→ Config G c)(Z':κ→ S.Choices)(Ψ:κ→ Config G f)
-- Walt fare constant along x no p.W.proof needed
abbrev bracket : κ→ℝ:=fun _=>0
abbrev atR (g:κ→ Config G n): κ→ℝ→ Config G n:=fun i _=>g i
omit h p [FiniteDimensional ℝ E] in lemma atRlive (u:ℝ){V:κ→ Config G n}(hp:0≤ u)(k:ℕ) : ∀ᶠ i in qq, Mode (atR V i) (bracket i) k u:=Eventually.of_forall fun i=> ⟨hp,fun j=>a_oneB G _ hp⟩ -- omit ranked
lemma sternP (i:Twin c): Walt qq bracket 0 (fun n b (_:ℝ)=> (T (t n b)).vision (till s) (temp s) (g n) i):=by
    have hp:= p.views.xn h (atRlive (V:=g) 0 le_rfl 0) (till s); have hV:= hp i; obtain ⟨U,hu⟩:=p.views.low
    unfold Tube.vision
    unfold thinned; rcases hv:i.2 with _|_
    · simp_rw [Bool.false_eq_true,if_false]; let z n:= if toll (g n) i.1=0 then (1:ℝ) else min 1 (Pressure.temp s/toll (g n) i.1); have hx: Walt qq bracket 0 (fun i (_:Bool) (_:ℝ)=> z i):=by
        refine Walt.stamp ⟨⟨1,Eventually.of_forall (fun y b=>?_)⟩,(by simp [tendsto_const_nhds])⟩; dsimp only; unfold z; split; exact norm_one.le
        next he => exact abs_le.mpr ⟨le_trans (by norm_num : -(1:ℝ) ≤ 0) (le_min zero_le_one (div_nonneg (temp_nonneg _) (G.chord_nonneg _))), min_le_left ..⟩
      unfold Tube.Xn plotted at hV; simp_rw [hv,Bool.false_eq_true,if_false] at hV; exact hx.pay hV
    · simp_rw [if_true,hu]
      unfold Tube.Xn plotted at hV; simp_rw [hv,if_true] at hV
      exact Walt.choose _ (hV.excuse _) (Walt.ready _)
lemma usurped (i:Twin f): Walt qq bracket 0 (fun n b (_:ℝ)=> (T (t n b)).Mv (till s) (temp s) (g n) i):= Walt.schedule _ _ (fun j _=> p.views.reach h (atRlive (V:=g) 0 le_rfl 0) _ _ (till s) true (p.sternP h g j))
lemma usurper (i:Bond c): Walt qq bracket 0 (fun n b (_:ℝ)=> (T (t n b)).Mw (till s) (temp s) (g n) i):= Walt.schedule _ _ (fun j _=> extensionP h (atRlive (V:=g) 0 le_rfl 0) p.views.qui (pole i) _ _ _ S.patch.L.property true (p.sternP h g j))
lemma ustage (i: Co c Gain): Walt qq bracket 0 (fun n b (_:ℝ)=> zip ((T (t n b)).N (till s) (g n)) ((T (t n b)).vision (till s) (temp s) (g n)) i):= Walt.schedule _ _ (fun j _=> extensionP h (atRlive (V:=g) 0 le_rfl 0) p.views.ore i _ _ _ S.patch.L.property true (p.sternP h g j))
lemma pivot (i:Spot c f)(g':κ→Config G c): Together qq (fun n b=>Coat.principal (T (t n b)) s (Ψ n) (g n) (g' n) i) :=by
    suffices H: Walt qq bracket 0 (fun n b (_:ℝ)=> Coat.principal (T (t n b)) s (Ψ n) (g n) (g' n) i) from H.atProbe
    let D:=till s; let b:=temp s
    have hz i:=(p.usurped h g i)
    have hh i:=(p.usurper h g i)
    have hx i:=(p.sternP h g i)
    have he:= atRlive (qq:=qq) (V:=g) 0 le_rfl 0
    have hZ i:= zipperZ (S:=S) he g' i
    have hu i:= p.views.xf h (atRlive (V:=Ψ) 0 le_rfl 0) D i
    have ha i:= p.views.xn h he D i
    rcases i with z|z|z|z
    · exact (Walt.stamp (crownP (x:=Ψ) h D z _ _ _ p.views.cap p.views.high 1 (by norm_num))).sums (Walt.schedule _ _ (fun y _=> (selfP (hz (z,y))).minus (radars (hz _) (hu _))))
    · let u0:= S.kernel.penalty
      have hp: Together qq (fun i (_:Bool)=> monetary S (g' i) (g i) z):=by
         refine ⟨⟨|u0| *2^2/2,Eventually.of_forall fun i b=>?_⟩,(by simp [tendsto_const_nhds])⟩
         unfold monetary; rw [norm_div,norm_mul,norm_pow,Real.norm_of_nonneg (by norm_num : 0≤(2:ℝ))]; apply div_le_div_of_nonneg_right _ (by norm_num)
         apply mul_le_mul (show ‖S.kernel.penalty‖≤|u0| from le_rfl) (pow_le_pow_left₀ (norm_nonneg _) _ 2) (sq_nonneg _) (abs_nonneg _); rw [Real.norm_of_nonneg (show 0 ≤ wire (g' i) (g i) z from G.chord_nonneg _)]; exact G.chord_le_two _
      exact (Walt.stamp hp).sums ((selfP (hh z)).minus (radars (hh z) (hZ z)))
    · let N:= T; have hw : Walt qq bracket 0 (fun n v (_:ℝ)=> (N (t n v)).workC D (g n) b z):=(Walt.schedule _ _ (fun i _=> (radars (hx (z,i)) (ha (z,i))).minus (selfP (hx (z,i))))).minus (Walt.stamp (crownP h (x:=g) D z _ _ _ p.views.cap' p.views.low _ S.patch.L.property)) -- exact division
      have hp : Walt qq bracket 0 (fun n v (_:ℝ)=> (N (t n v)).workL D (Ψ n) (g' n) (g n) b z):= Walt.schedule _ _ (fun i _=> radars (hx (z,i)) (((Walt.schedule _ _ (fun j _=> p.views.reach h he _ _ D false (hu j))).sums (Walt.schedule _ _ (fun j _=> extensionP h he p.views.qui _ _ D _ S.patch.L.property false (hZ j)))).minus (ha _)))
      have hg : Walt qq bracket 0 (fun n v (_:ℝ)=>(N (t n v)).workD D (g n) b z):= Walt.schedule _ _ (fun i _=> ((radars (hx (z,i)) ((hx (z,i)).minus (((Walt.schedule _ _ (fun j _=> p.views.reach h he _ _ D false (hz j))).sums (Walt.schedule _ _ (fun j _=> extensionP h he p.views.qui _ _ D _ S.patch.L.property false (hh j)))).sums (Walt.schedule _ _ (fun j _=> extensionP h he p.views.ore _ _ D _ S.patch.L.property false (p.ustage h g j)))))).plant (Z:=fun i=> i/2) (contDiff_id.div_const _))) -- date
      exact hw.sums (hp.sums hg)
    exact selfP (p.ustage h g z)
lemma yieldsT (i:Spot c f): Together qq (fun n b=>Coat.yielding (T (t n b)) s (Ψ n) (g n) (Z' n) i):=by
    rcases i with i|i; swap; · exact pivot p h g Ψ (.inr i) (fun i=> S.prediction (Ψ i) (Z' i))
    unfold yielding soft; obtain ⟨K,hK⟩:=p.views.high; simp_rw [Sum.elim_inl,hK]
    have hx: Walt qq bracket 0 (fun n (_:Bool) (_:ℝ)=> flaw (faceValue (Ψ n) i)):=by
       refine Walt.twin (flawBill G) (0+0) ?_; filter_upwards with n; exact ⟨Blaze.cracked (f:= fun _ :ℝ=>faceValue (Ψ n) i) (a_oneB G _ le_rfl),rfl⟩
    apply Together.add ((Walt.ready K.direct).times hx).atProbe
    have hp k:= p.views.xf h (atRlive (V:=Ψ) 0 le_rfl 0) (till s) k; exact (Walt.schedule Finset.univ _ (fun j (_:j∈(Finset.univ (α:=Bool)))=> selfP ((hp (i,j)).minus (p.usurped h g _)))).atProbe -- schedule inference
open Raw Polar Silica
variable (qV:StableR v R)(M: κ→ Hat G F)(hu:0≤u)(hm:∀ n, (M n).legal s)(Y:κ→ Config G f)
    (Δ:κ→Directions G f)(hx : ∃ r: ℝ,∀ᶠ n in qq, ‖Δ n‖≤r)
-- uses real metrics only at fixed period
variable (J:κ→ Finset ℕ)
def echo (M: κ→Hat G F): κ→Config G c:= fun i=>(M i).bill
include h hu hm p
lemma stems : ∀ n b, let X:=Abide s χ U.K T M t n b; let K:= prize s χ U.K T R M t Δ n b
    course X A (R (t n b)).beta K X.V=K ∧ steer X A (Δ n) X.V=Δ n ∧ X.liftA (R (t n b)).beta K=Δ n ∧
      ∀ i j u,X.extracted u i j=Vine.costs X u i j :=by
  intro n b X K; have h:= (H (t n b)).laws.intake.positive; have hp: Room _ S _ X.x:=(H (t n b)).laws.data.room
  have hk : X.manifest:=hm _
  exact ⟨home X p.realm.bay K h,funext (fun i=>by unfold steer Silica.action; simp [Eider.nothing_f p.realm.bay]),(shine X hp hk _ _).trans (rent_bill _ _ h _), fun i j u=> cotton X hp hk u i j⟩
include hx
lemma glowed (i:Signed)(j:Spot c f):let Z:= Abide s χ U.K T M t
    Together qq (fun n b=> (Z n b).extracted (Δ n) i j) ∧ Together qq (fun n b=> (Z n b).extracted (Z n b).μ i j):=by
   intro X; have ht:=atRlive (qq:=qq) (V:=echo M) _ hu k; have hK:∀ᶠ n in qq, (M n).legal s ∧ atR (echo M) n (bracket n)=(M n).bill:= Eventually.of_forall fun n=> ⟨hm n,rfl⟩
   obtain ⟨r,hr⟩:=hx; have hh : Walt qq bracket k (fun n (_:Bool) (_:ℝ)=> Δ n):=by refine Walt.stamp ⟨⟨r,hr.mono fun _ hn _=>hn⟩,(by simp [tendsto_const_nhds])⟩
   constructor
   · refine (costsW p h ht hK i j hh).atProbe.shimmy (Eventually.of_forall fun n=> funext fun b=>?_); exact ((p.stems h M hu hm Δ _ _).2.2.2 i j _).symm
   refine (costsW p h ht hK i j (p.pulses h ht hK)).atProbe.shimmy (Eventually.of_forall fun n=>funext fun b=>?_)
   change Vine.costs _ _ _ _= _; rw [show Coat.extracted _ _ _ _=_ from ((p.stems h M hu hm Δ _ _).2.2.2 i j _),Vine.agrees_all (X n b) (P:=_) (H (t n b)|>.laws.data.room) (hm n)]; rfl
lemma tonesV (i: Signed) (j:Spot c f): let Z:= Abide s χ U.K T M t
    Together qq (fun n b=> (Z n b).light (Δ n) i j) ∧ Together qq (fun n b=> (Z n b).debit (Δ n) i j):=by
   intro Z
   have hp:= p.glowed h M hu hm Δ hx i j
   let U' n:= pull i 0 ((Z n false).input (Δ n)); let V n:=pull i 0 (M n).bill; let k n:=choice (S:=S) i (M n).tag
   have hX: Together qq (fun n b=> yielding (T (t n b)) s (U' n) (V n) (k n) j):= p.yieldsT h V k U' j
   have he: Together qq (fun n b=> Coat.principal (T (t n b)) s (U' n) (V n) (S.prediction (U' n) (k n)) j):= p.pivot h V U' _ _
   exact ⟨(hX.prod hp.1).continuous continuous_sub,(he.prod hp.1).continuous continuous_sub⟩
include qV
lemma strophe (P: LogLetter c f): Together qq (fun i b=> Raw.expo (T (t i b)) s (R (t i b)) (Y i) (echo M i) P):=by
   have ht:=atRlive (qq:=qq) (V:=echo M) _ hu k
   have hp:= (p.nesting h ht qV Y P).atProbe
   rcases P with P|P|P|P|P|P
   all_goals first|exact hp|skip
   obtain ⟨t',ht'⟩:=p.views.low; unfold Raw.expo pairValue pairTail; dsimp only
   let K i:= PathData.kept t' (temp s) P.2.2.1 (pull P.1 0 (echo M i))
   apply (Walt.choose K ((Walt.stamp (x:=bracket) (k:=0) hp).excuse _) (Walt.ready 0)).atProbe.shimmy
   filter_upwards with n; ext1 i
   unfold nest Polar.icicle Polar.twin; simp only [Sum.elim]; by_cases h:K n
   · rw [if_pos h]; dsimp only [atR]; simp only [ht',if_pos (show PathData.kept _ _ _ _ from h)]; unfold K at h; simp only [h,and_true]
   rw [if_neg h]; simp only [ht']; unfold K at h; simp [h]
lemma vaporsP (P:Stores S): Together qq (fun n b=>(Abide s χ U.K T M t n b).Pack (R (t n b)) Q.table (J n) w U.a P (Δ n)):=by
   let X i b:=Abide s χ U.K T M t i b; have hv :∀ n,(M n).legal s ∧ atR (echo M) n (bracket n)=(M n).bill:=fun n=> ⟨hm n,rfl⟩
   have he := atRlive (qq:=qq) (V:=echo M) _ hu k
   have hs i b : mobil A s U.K χ T t Δ M (atR (echo M)) i b (bracket i)=Δ i:= (p.stems h M hu hm Δ i b).2.1
   let K:= (visit P (200*radiusB s)); let X':κ→ Finset (Bond f):=fun i=> (X i false).plaza (P.dome (304*radiusB s)); let N:ℕ:=((visit P (10*radiusB s)).filter (fun i=> i∉F.trunks)).card; have hn i b:(X i b|>.pens P).card=N:=rfl
   have hp: Walt qq bracket 0 (fun i b (_:ℝ)=> steamLog (X i b) (R (t i b)) Q.table U.a P (Δ i)):=by
       have hh': Walt qq bracket 0 (fun i b (_:ℝ)=> (X i b).quoteNear P (Δ i)+(X i b).far_bills P):=
         ((Walt.ready _).pay (Walt.schedule _ _ (fun l _=> (Walt.schedule (posted (turnStore l P) (200*radiusB s)) _
           (fun j _=>Walt.stamp (p.tonesV h M hu hm Δ hx l j|>.2)))))).sums ((Walt.ready _).pay (Walt.schedule _ _ (fun l _=> Walt.schedule (posted (turnStore l P) (200*radiusB s)) _
           (fun j _=>Walt.stamp (p.glowed h M hu hm Δ hx l j|>.2)))))
       have hu i : Walt qq bracket 0 (fun n b (_:ℝ)=> (X n b).gentry Q.table U.a (Δ n) i):=by
          apply Walt.stamp; apply (cliffA p h he (Eventually.of_forall hv) Δ hx i).atProbe.shimmy; filter_upwards with n; ext1 b; rw [hs]; rfl
       have hq i b : (X i b).plaza (P.dome (304*(X i b).B))=X' i:=rfl
       unfold steamLog; simp_rw [hn,hq]; refine ((((Walt.stamp ((qV.pricesBet h).continuous continuous_neg)).times hh').sums (Walt.schedule K _ ?_)).sums (Walt.cut X' _ (fun j=> (Walt.schedule j _ (fun i _=> hu i)).excuse _))).minus ((Walt.ready _).times (Walt.stamp (p.moneyA h he (Eventually.of_forall hv) qV Δ hx |>.atProbe)))
       exact fun i _=> Walt.stamp ((p.logPins h he (Eventually.of_forall hv) i).atProbe)
   let Y' i:= (X i false).input (Δ i); let z:= 300*radiusB s
   let m i:= Contract.order (R (t i false)) (J i) (vias S P z) (Y' i)* Mask.tickets P z (Y' i) (M i).tag*Mask.profiles P χ z s w (Y' i) (M i).tag (M i).bill*(X i false).enforce U.a (Δ i) (X' i)
   have hg i : ‖m i‖≤ Real.exp (Mask.tollFee S.patch z * P.shares):=by
       have hs:=(X i false).conserve (X' i) U.a (Δ i); have hp:=Mask.profiles_range P χ z s w (Y' i) (M i).tag (M i).bill; have hc:= Contract.valid_pay (R (t i false)) (J i) (vias S P z) (Y' i); unfold m; have hx:0≤ Mask.tickets P z (Y' i) (M i).tag:=Mask.ticket_nonneg ..
       rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc.1 hx) hp.1) hs.1)]
       exact ((mul_le_of_le_one_right (mul_nonneg (mul_nonneg hc.1 hx) hp.1) hs.2).trans (mul_le_of_le_one_right (mul_nonneg hc.1 hx) hp.2)).trans ((mul_le_of_le_one_left hx hc.2).trans (Mask.tickets_le ..))
   have hm: Walt qq bracket 0 (fun i (_:Bool) (_:ℝ)=> m i):= Walt.stamp ⟨⟨_,Eventually.of_forall fun n b=> hg n⟩,(by simp [tendsto_const_nhds])⟩
   let f n:= (X n false).existSeeds P 300
   refine ((Walt.choose f ((hp.exponential.times hm).excuse _) (Walt.ready 0)).atProbe).shimmy ?_; filter_upwards with n; ext1 i; unfold Pack; by_cases h:f n
   · rw [if_pos h,if_pos (show (Abide s χ U.K T M t n i).existSeeds P 300 from h)]; unfold steam; dsimp only; unfold m; rw [qV.toKept.chores (t n false) (t n i)]; simp_rw [mul_assoc]; rfl
   rw [if_neg h,if_neg (show ¬(Abide s χ U.K T M t n i).existSeeds P 300 from h)]
lemma alight (P:Head S): Together qq (fun n b=>(Abide s χ U.K T M t n b).vertex (R (t n b)) Q.table w U.a (J n) Q.halo (prize s χ U.K T R M t Δ n b) P) :=by
   let X n b:= Abide s χ U.K T M t n b; let f n b:= R (t n b); let Z n b:=prize s χ U.K T R M t Δ n b
   let g:=atR (echo M); have hv : ∀ᶠ i in qq, Mode (g i) (bracket i) k u:=atRlive u hu _; have hV : ∀ n,(M n).legal s∧g n (bracket n)=(M n).bill:=fun n=>⟨hm n,rfl⟩
   have hp n b : liftA (X n b) (f n b).beta (Z n b) = Δ n:= (p.stems h M hu hm Δ n b).2.2.1
   have he n b: vary ((M n).order (T (t n b)) s χ U.K) (g n (bracket n))= X n b:= rfl
   have hs n b : course (X n b) A (f n b).beta (Z n b) (X n b).V=Z n b:=(p.stems h M hu hm Δ n b).1
   have hg n b : mobil A s U.K χ T t Δ M g n b (bracket n)=Δ n := (p.stems h M hu hm Δ n b).2.1
   let Y n:= (X n false).input (Δ n)
   change Together qq (fun _ _=>(X _ _).vertex (f _ _) _ _ _ _ _ (Z _ _) _)
   unfold vertex; simp_rw [hp]; rcases P with P|P|P|P
   · simp only [Sum.elim]; simp_rw [show ∀ i b,(X i b).B=radiusB s from fun _ _=>rfl]; split_ifs; exact p.vaporsP h qV M hu hm Δ hx J P; exact Together.steady _
   · refine (tokenK p h hv (Eventually.of_forall hV) qV Δ hx Y P).atProbe.shimmy ?_; filter_upwards with n; ext1 b; unfold sheath; rw [hg]; rfl
   · simp only [Sum.elim]; unfold raiseAir; apply (Together.continuous ?_ (T:=fun i:ℝ=> Real.exp i-1) (by fun_prop)); try assumption
     unfold farLog; simp_rw [hp]; rcases P with P|P|P
     · simp only [Sum.elim]; unfold inhale; let i n b:= (X n b).plaza (Raw.space (T (t n b)) 0 (radiusB s) (R (t n b)) P); have hi n b:i n b=i n false:=by unfold i; rw [(p.receipts qV.toKept (t n b) (t n false) (radiusB s) 0).1]; rfl
       refine ((Walt.stamp (p.strophe h qV M hu hm Y Δ hx P)).times (parka p h hv (Eventually.of_forall hV) Δ hx (2*U.a) (fun n=>i n false))).atProbe.shimmy ?_
       filter_upwards with n; ext1 b; rw [hg]; change _= _ * (X n b).enforce _ _ (i n b); rw [hi n b]; rfl
     · let F n b:= (X n b).Short (Δ n) Q.table (f n b).beta U.a P; simp only [Sum.elim]; change Together qq F
       have ht:= mini p h hv (Eventually.of_forall hV) qV Δ hx Y P|>.atProbe; cases P with
       | inr a=> refine ht.shimmy ?_; filter_upwards with i; ext1 b; rw [hg]; rw [show vary (Abide _ _ _ _ _ _ _ _) _= _ from he i b]; unfold F Short whelp; cases a <;> simp
       | inl a=>
         let W i:=(X i false).booth (rowSite S a); have hK: Together qq (fun n b=>(X n b).enforce (2*U.a) (Δ n) (W n)):=by
             apply (parka p h hv (Eventually.of_forall hV) Δ hx (2*U.a) W).atProbe.shimmy; filter_upwards with n; ext1 b; rw [hg]; rfl
         have hh:=(Walt.choose (x:=bracket) (k:=0) (fun i=> Shell.Inside (rowSite S a) (M i).seeds (200*radiusB s)) (Walt.ready (0:ℝ))
          ((((Walt.stamp ((qV.pricesBet h).continuous continuous_neg)).times (Walt.ready orientation)).times (((Walt.stamp hK).times (Walt.stamp (p.tonesV h M hu hm Δ hx a.1 a.2|>.1))).sums (Walt.stamp (p.glowed h M hu hm Δ hx a.1 a.2|>.2)))).excuse _))
         apply hh.atProbe.shimmy; filter_upwards with n; exact funext fun b=> by unfold F Short speck; simp only [W,X,Abide,Hat.order,Coat.B,booth,plaza,Coat.Hot, f,Sum.elim]
     have hh:= p.pledge h hv (Eventually.of_forall hV) qV Δ hx P|>.atProbe
     apply hh.shimmy; filter_upwards with n; ext1 b; rw [hg]; change spins (X n b) U.a (f n b) (Δ n) (course (X n b) A (f n b).beta (Z n b) (X n b).V) P=_; rw [hs]
     exact (Polar.margins (X n b) _ (f n b) _ (H (t n b)|>.laws.data.room) (hm n) (Δ n) (hp n b) P).symm
   simp only [Sum.elim]; refine (warning p h hv (Eventually.of_forall hV) qV Δ hx Y J P).atProbe.shimmy ?_
   filter_upwards with i; ext1 b; rw [hg]; cases P <;> rfl
end Score
end YM.UVExtension.Span
#print axioms YM.UVExtension.Span.Score.alight
