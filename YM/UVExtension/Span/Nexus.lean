import YM.UVExtension.Span.Roam
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
variable (qV:StableR v R)
variable (Δ:κ→Directions G f) -- actual held displacement at test. no norm when prices all Compass later
open Silica Flux WithLp MeasureTheory
open Raw Polar MeasureTheory
-- fixed-root old log terms. From incoming coefficient coupling + bounds.
section values
variable (Y' : κ→ Config G f)
include h qV p
-- value
lemma normsE (i:ℕ): Together qq (fun n b=> (R (t n b)).activities.regularOccurrence (R (t n b)).p i (Y' n)):= (qV.real_arrays h i Y').2
lemma normsK (i:ℕ): Together qq (fun n b=> (R (t n b)).activities.K i (Y' n)):= (qV.real_arrays h i Y').1
lemma atomsOld (i:Trans f) {a: κ→ Bool→ℝ}(ht:Together qq a): (let f d (F:PathData G→ ℕ→ Atom G d) := fun n b=> translateValue (R (t n b)).p (F (R (t n b)).path) (a n b) (Y' n) i; Together qq (f 2 PathData.loop) ∧ Together qq (f 3 PathData.cubic)∧Together qq (f 4 PathData.quartic)):=by
   rcases eq_or_ne qq ⊥ with hy|hy
   · have ht (f:κ→Bool→ℝ):Together qq f:=⟨⟨0,by simp [hy]⟩,by rw [hy]; exact tendsto_bot⟩; dsimp only; exact ⟨ht _,ht _,ht _⟩
   haveI : NeBot qq:=⟨hy⟩; haveI : NeBot v:=(h false).neBot
   obtain ⟨V₀,ht'⟩:= (ht.1.choose_spec).exists
   let z:=i.2.2; let u:= (R (t V₀ false)).p
   have hv n b:(R (t n b)).p=u:= qV.chan ..
   obtain ⟨σ,Z,hZ⟩:=p.views.cap
   let Y n:=pull i.1 0 (Y' n)
   have hf d (F:PathData G→ ℕ→ Atom G d)(hR:∀ i,(F ((T i).up) z).leg= (F Z z).leg)(hh: Revenues.bulk (σ:=σ) Z v (fun i=> (T i).up) d F): Together qq (fun n b=> translateValue (R (t n b)).p (F (R (t n b)).path) (a n b) (Y' n) i):=by -- replace j_
     simp_rw [show ∀ i,(R i).path=(T i).up from fun i=>(p.upR i).1,hv]
     let X n b:= F (T (t n b)).up z; let W:= F Z z; let p(v):Fin d → G.Color:=fun j=> (W.leg j).atSite (Y v) i.2.1
     have he : Walt qq (fun _ : κ=> (0:ℝ)) 0 (fun n b _=> translateValue u (F (T (t n b)).up) (a n b) (Y' n) i):=by
       change Walt qq (fun n:κ=>_) _ (fun n b y=> a n b*(X n b).placed u (Y n) i.2.1); apply (Walt.stamp ht).times
       let f n b:= (X n b).footprint (n:=f) i.2.1; have hx n b: f n b=W.footprint i.2.1:=by unfold f W Atom.footprint Atom.stencil X; rw [hR]
       let P: κ→Bool→ℝ:= fun n b=> (X n b).poly (p n); have hX n b : (X n b).placed u (Y n) i.2.1=if Healthy u.threshold (W.footprint i.2.1) (Y n) then P n b else 0:=by
          unfold Atom.placed; by_cases h : Healthy u.threshold (W.footprint i.2.1) (Y n)
          · rw [masked_eq _ _ _ _ (by rw [show (X n b).footprint _= _ from hx ..]; exact h), if_pos h]; exact congr_arg ((X n b).poly) (by unfold p X; rw [hR])
          rw [masked_ne _ _ _ _ (by rw [show (X n b).footprint _= _ from hx ..]; exact h), if_neg h]
       have hL : Walt qq (fun _ : κ=> (0:ℝ)) 0 (fun n b _=> P n b):=by
          unfold P Atom.poly; apply Walt.schedule _ _; intro j _; refine (Walt.stamp (pairsHere _ (W.coeff j) (fun b=> (hh.1 z j).comp (h b)))).times (Walt.stamp ⟨⟨(2:ℝ)^d,?_⟩,?_⟩)
          · filter_upwards with i b; rw [norm_prod]; apply (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun v hv=> (show ‖p i v (j v)‖ ≤ 2 from (stand_cap ..).trans (Slot.eval_norm ..)))).trans_eq; simp
          simp
       simp_rw [hX]; exact Walt.choose _ (hL.excuse _) (Walt.ready _)
     exact he.atProbe
   dsimp only; exact ⟨hf _ PathData.loop (fun v=> (hZ.layout v).1 _) hZ.parked₁,hf _ PathData.cubic (fun v=> (hZ.layout v).2.1 _) hZ.parked₂,hf _ PathData.quartic (fun v=> (hZ.layout v).2.2 _) hZ.parked₃⟩
omit qV p
lemma twinsP (u:ι→PathData G) (A:PathData G) (σ:ℝ) (hx: Revenues v σ u A)(Y:κ→ Config G n)(H:PlaqAxes)(p:Site n)(i:ℕ) : Together qq (fun n b=>(u (t n b)).ellTerms (p,H) i (Y n)):=by
   unfold PathData.ellTerms; simp_rw [hx.slots]; let f n:= (A.row H i).2.atSite (Y n) p
   have hP : Together qq (fun n (_:Bool)=> f n):= ⟨⟨2,by filter_upwards with n b; exact Slot.eval_norm ..⟩,by simp [tendsto_const_nhds]⟩
   exact (Walt.pay (x:=fun _:κ=> (0:ℝ)) (k:=0) (Walt.stamp (pairsHere _ _ (fun b=>(hx.starts H i).comp (h b)))) (Walt.stamp hP)).atProbe
include p qV
lemma paired (i: Pairs f) {a: κ→ Bool→ℝ} (ht:Together qq a): Together qq (fun n b=> pairValue (R (t n b)).path (R (t n b)).clip (R (t n b)).p.threshold (till s) 1 (a n b) (Y' n) i):=by
   unfold pairValue pairTail; simp_rw [(p.upR _).1,(p.upR _).2]
   obtain ⟨A,hA⟩:= p.views.high; obtain ⟨V,Z,hZ⟩:=p.views.cap; unfold long; simp_rw [hZ.slots,hA]
   let R(n b):=R (t n b); have hp n i: (R n i).p.threshold=(R n false).p.threshold:= by unfold R; rw [qV.chan (t n i) (t n false)]
   let L j := twinsP h (fun i=> (T i).up) Z V hZ (fun n=> pull i.1 0 (Y' n)) i.2.1 i.2.2.1 j
   let M n:= ¬((Z.row i.2.1 i.2.2.2.1).2.length*1 ≤ till s ∧ (Z.row i.2.1 i.2.2.2.2).2.length*1≤till s) ∧ PathData.kept A (R n false).p.threshold i.2.2.1 (pull i.1 0 (Y' n))
   have hg:= Walt.stamp (x:=fun _ : κ=> (0:ℝ)) (k:=0) ht
   have hh:= Walt.choose M (((radars (x:=fun _ : κ=> (0:ℝ)) (k:=0) (Walt.stamp (L i.2.2.2.1)) (Walt.stamp (L i.2.2.2.2))).plant (Z:=fun i=>i/2) (contDiff_id.div_const _)).excuse _) (Walt.ready 0)
   apply (hg.times hh).atProbe.shimmy; filter_upwards with n; ext1 b
   rw [show (R n b).p.threshold=(R n false).p.threshold from hp ..]; congr
end values
include p h he
lemma twinP (i:Pairs c) (τ':κ→ Bool→ ℝ)(hT: Together qq τ') : Walt qq τ k (fun n b y=> icicle (T (t n b)).down (Y n y) (till s) S.patch.L.val (τ' n b) i):=by
   obtain ⟨V,Z,hZ⟩:= p.views.cap'; let u' n y:= pull i.1 0 (Y n y); let g:Cell c:= (i.2.2.1,i.2.1); have hp : ∀ᶠ n in qq,Mode (u' n) (τ n) k u:=he.mono fun n hn=>Blaze.turn hn _
   have hx z: Walt qq τ k (fun n b y=> (T (t n b)).down.ellTerms g z (u' n y)):=by
       let S:=(Z.row g.2 z).2; have hP:= pairsHere (fun n b=> ((T (t n b)).down.row g.2 z).1) _ (fun b=>(hZ.starts g.2 z).comp (h b)); have ht:Walt qq τ k (fun n (_:Bool) y=> S.atSite (u' n y) g.1):= by
          refine Walt.twin (royalty G^2) (2*S.length*(u*royalty G)) (hp.mono ?_); intro i hx; exact ⟨slot_cost _ _ hx.pos hx.atLink,rfl⟩
       apply ((Walt.stamp hP).pay ht).same; filter_upwards with n b; filter_upwards with y; unfold PathData.ellTerms; rw [hZ.slots]
   unfold icicle Polar.twin Raw.long; simp_rw [hZ.slots]; split_ifs; swap; exact (Walt.stamp hT).times ((radars (hx _) (hx _)).plant (Z:=fun i=>i/2) (contDiff_id.div_const _)); exact (Walt.stamp hT).times (Walt.ready _)
include qV
lemma nesting (Y':κ→ Config G f) (i:Raw.LogLetter c f): Walt qq τ k (fun n b y=> Polar.nest (T (t n b)) s (Y n y) (Y' n) (R (t n b)) i):=by
   let v0 i b := - Raw.orientation*(R (t i b)).beta; have hp : Together qq v0:= ((qV.pricesBet h).continuous (T:=fun i=> -Raw.orientation*i) (by fun_prop))
   rcases i with i|i|i|i|i|i
   · exact Walt.stamp (((qV.real_arrays h i Y').2
       ).continuous continuous_neg)
   · exact Walt.stamp (atomsOld p h qV Y' i hp |>.2.1)
   · exact Walt.stamp (atomsOld p h qV Y' i hp |>.2.2)
   · exact Walt.stamp (atomsOld p h qV Y' i (Together.steady _) |>.1)
   · exact Walt.stamp (paired p h qV Y' i hp)
   exact twinP p h he i _ (hp.continuous continuous_neg)
end Score
end YM.UVExtension.Span
