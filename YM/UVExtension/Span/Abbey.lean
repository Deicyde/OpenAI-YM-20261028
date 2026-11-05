import YM.UVExtension.Span.Cask
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
include p h he hK
-- lenses itself
omit hK [FiniteDimensional ℝ E] in lemma orbits {W:κ→Bool→ E→ Directions G f}(hd:Walt qq τ k W)(g:Mention c f): Walt qq τ k (fun i b y=> orientedRow (T (t i b)) (till s) g.1 g.2 (Y i y) (W i b y)):=by
    let v i z:= pull g.1 0 (Y i z); let u0 i z:= replica S.ratio (Y i z)
    let fV:= W
    have hfV i : Walt qq τ k (fun j e z=> fV j e z i):=hd.leaf (ContinuousLinearMap.proj i)
    let c' i e z j:= displacement g.1 (fV i e z) (u0 i z) j
    have hp : ∀ᶠ i in qq,Mode (u0 i) (τ i) k u:= by filter_upwards [he] with i hi using ⟨hi.pos,recopy S hi.atLink⟩
    have hD i: Walt qq τ k (fun j e z=> c' j e z i):= by
       unfold c' displacement; split_ifs
       next =>
           let j:= Channel.edge g.1 i
           -- travel along edge j. then repel for inverse
           have ht:= ponder j.1 [⟨j.2,false⟩] hp _ (Together.steady 1) false _ (hfV j)
           have hh: Walt qq τ k (fun n b y=> G.adjoint (u0 n y j)⁻¹ (fV n b y j)):=ht.same (Eventually.of_forall fun n b=> Eventually.of_forall fun y=> by simp only [receive,Bool.false_eq_true,if_false,repel,one_smul,travel]; simp [Step.read,Step.used])
           exact hh.leaf (-(ContinuousLinearMap.id ℝ G.Color))
       exact hfV _
    let L' i e z:= spinRow S (carrier (focus S g.2) (v i z)) (c' i e z)
    have Hx j: Walt qq τ k (fun i e z=> L' i e z j):=by
       let x:= focus S g.2; have ht:= ponder x (SliceRows.carriage x (Shell.atEdge S j)) (he.mono fun i hi=>Blaze.turn hi g.1) _ (Together.steady 1) true _ (hD j)
       simpa only [receive,rated,one_smul,if_true] using! ht
    let G' i e z g:=barField (T (t i e)) (till s) (L' i e z) g
    have hz(m: Rod c f): Walt qq τ k (fun i e z=>G' i e z m):=by
       obtain ⟨σ,R,hσ⟩:= p.views.cap; rcases m with i|b; swap; · simp_rw [G',barField,Sum.elim_inr, zLin_eq]; exact (Walt.ready _).pay (Walt.schedule univ _ (fun i _=> (Walt.ready _).pay (Hx _)))
       unfold G' barField bareCut; simp only [Sum.elim_inl]; split_ifs
       · exact domino (fun i b=> (T (t i b)).up) (fun b=> hσ.incurs (h b)) Hx i.1 _
       obtain ⟨t',ht⟩:=p.views.high; simp_rw [ht]; apply (Walt.ready _).pay
       simp_rw [curl_eq]; exact ((Hx _).minus (Hx _)).minus ((Hx _).minus (Hx _))
    exact (hz g.2)
omit hK [FiniteDimensional ℝ E] in
lemma orbitW {W:κ→Bool→ E→ Directions G f}(hd:Walt qq τ k W)(g:Mention c f): Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).motion (W i b y) g):=by
    let X i b:=(M i).order (T (t i b)) s χ U.K; let f i e z:= (X i e).lens (W i e z); let r i:= (X i true).selected g.1 (spot S g.2)
    have hf:Walt qq τ k f:=by
       apply Walt.assemble; intro i
       have h : ∀ j e z,f j e z i= if (X j true).Hot i then (W j e z) i else 0:=fun _ _ _=> rfl
       simp_rw [h]; exact Walt.choose _ ((hd.leaf (ContinuousLinearMap.proj i)).excuse _) (Walt.ready _)
    exact Walt.choose r ((orbits p h he hf g).excuse _) (Walt.ready _)
omit hK [FiniteDimensional ℝ E] in
lemma formG : Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).form):=by
    apply Walt.rectangle; rintro ⟨i,j⟩ d; apply (Walt.ready (x:=τ) Coat.scale).times
    exact (p.orbitW h (M:=M) he (Walt.ready (sing d)) i).leaf ((LinearMap.comp (LinearMap.proj j) (WithLp.linearEquiv 2 ℝ _).toLinearMap : G.Color→ₗ[ℝ]ℝ).toContinuousLinearMap)
omit hK [FiniteDimensional ℝ E] in
lemma gram : Walt qq τ k (fun i b y=> (vary ((M i).order (T (t i b)) s χ U.K) (Y i y)).plate):=by
    let L : Matrix (Coat.Target c f G) (Tubular f G) ℝ →ₗ[ℝ] Matrix (Tubular f G) (Coat.Target c f G) ℝ :=
       { toFun:= Matrix.transpose
         map_add':= fun a b=>rfl
         map_smul':= fun a b=>rfl }
    let X i b y:= vary ((M i).order (T (t i b)) s χ U.K) (Y i y); let W n b y:= (X n b y).sleepy; have hV:= formG p h (M:=M) he
    have hp: Walt qq τ k (fun i b y=>(X i b y).form.transpose*(X i b y).form):=by
       apply Walt.rectangle; intro i j; simp_rw [Matrix.mul_apply,Matrix.transpose_apply]; refine Walt.schedule _ _ (fun k (_:k∈Finset.univ)=>?_)
       let F (z : Tubular f G) : Matrix (Coat.Target c f G) (Tubular f G) ℝ→ₗ[ℝ]ℝ:= { toFun:=fun Z=>Z k z, map_add':=fun a b=>rfl, map_smul':=fun a b=>rfl }
       exact (hV.leaf (F _|>.toContinuousLinearMap)).times (hV.leaf (F _|>.toContinuousLinearMap))
    have hw : Walt qq τ k W:=by
       apply Walt.rectangle; rintro ⟨i,j⟩ d
       unfold W sleepy; by_cases he:(i,j)=d; swap; · simp_rw [Matrix.diagonal_apply_ne _ he]; exact Walt.ready _ -- lemma order
       subst d; simp_rw [Matrix.diagonal_apply_eq]; exact Walt.choose (fun n=> ((M n).order (T (t n true)) s χ U.K).Hot i) (Walt.ready _) (Walt.ready _)
    exact hp.sums hw
lemma stocks (S':Signed)(i:Rod c f): Walt qq τ k (fun n b y=> bar (vary ((M n).order (T (t n b)) s χ U.K) (Y n y)) 0 (S',i)):=by
    let X i b y:= vary ((M i).order (T (t i b)) s χ U.K) (Y i y); let T' n b i:= bar (X n b i) 0
    have hx : ∀ᶠ n in qq,∀ b k', Brush k Z 1 (fun y=> stand (T' n b y) k') (τ n):= by
       filter_upwards [he,hK] with n hm hp b j; exact (p.tech E (Y n) F (t n b) ((M n).order _ s χ U.K) (τ n) rfl rfl rfl hp.1 hp.2 hm).2 j
    have ht' : Walt qq τ k (fun n b y=> (X n b y).signal 0):=by
       simp_rw [signal,Coat.lens_zero,add_zero]; apply Walt.assemble; intro i; apply Walt.twin V 1; filter_upwards [he,hK] with n hn hm; exact ⟨(p.tech E (Y n) F (t n true) ((M n).order _ s χ U.K) (τ n) rfl rfl rfl hm.1 hm.2 hn).1 _,rfl⟩
    let L i z:=pull S' 0 (Y i z); let t' n b y i:= bar (X n b y) 0 (S',i); have hl :∀ᶠ n in qq,Mode (L n) (τ n) k u:=he.mono fun n hn=> Blaze.turn hn S'
    let G' n b y i:= visual (T (t n b)) (till s) (L n y) i
    have hQ i: Walt qq τ k (fun n b y=> G' n b y i):=by
       rcases i with i|i; exact p.views.canopyP h _ hl _; exact p.views.canopyJ h _ hl _
    rcases i with i|j
    · let r i':=((M i').order (T (t i' true)) s χ U.K).selected S' (spot S (Sum.inl i))
      have hf : ∀ᶠ n in qq,Mode (fun y=> replica S.ratio (L n y)) (τ n) k u:= hl.mono fun n hn=> ⟨hn.pos,recopy S hn.atLink⟩
      let pZ: Mention c f:= (S', Sum.inl i)
      have ht: Walt qq τ k (fun n b y=> strain (X n b y) S' (Sum.inl i) 0):= ((p.views.xf h hf (till s) i).minus (hQ (.inl i))).sums (p.orbits h he ht' pZ)
      exact Walt.choose r (((Walt.ready _).pay ht).excuse _) (Walt.ready _)
    let r i':=((M i').order (T (t i' true)) s χ U.K).selected S' (spot S (Sum.inr j)); let E' i l n:= S.prediction (replica S.ratio (L i n)) (choice S' (X i l n).k)
    -- branch predictions may be discontinuous! dominant P service nevertheless at bar. difference cancels identically on each decision.
    let Y' n b y:= - G' n b y (.inr j) + orientedRow (T (t n b)) (till s) S' (.inr j) (Y n y) ((X n b y).signal 0)
    have hp: Walt qq τ k Y':= (((hQ (.inr j)).leaf (-(ContinuousLinearMap.id ℝ G.Color)))).sums (p.orbits h he ht' (S',.inr j)) -- parse
    let W' n b y:= if r n then Coat.scale • Y' n b y else 0
    have hw : Walt qq τ k W':= Walt.choose r (((Walt.ready _).pay hp).excuse _) (Walt.ready _)
    let F' n b y:= bar (X n b y) 0 (S',.inr j)
    have hu t: ∃ d : ℝ, ∀ᶠ n in qq,∀ b,Brush k d 1 (fun y=> (F' n b y) t) (τ n):= ⟨Z,hx.mono fun n h b=> h b ((S',.inr j),t)⟩
    let P : (G.ColorIndex→ℝ)→ₗ[ℝ] G.Color:=(WithLp.linearEquiv 2 ℝ _).symm.toLinearMap
    have hz: Walt qq τ k (fun n (_:Bool) y=> F' n false y):=by
       refine (Walt.assemble _ (fun i (_:Bool) y j=> (F' i false y) j) (fun j=>?_)).leaf P.toContinuousLinearMap
       obtain ⟨d,hH⟩:= hu j; exact Walt.twin d 1 (hH.mono fun n hn=>⟨hn false,rfl⟩)
    obtain ⟨B,_,hV⟩:=hw.cap; have hW:Walt qq τ k (fun n (_:Bool)=> W' n false) := Walt.twin B 1 (hV.mono fun n hn=> ⟨hn false,rfl⟩)
    refine (hz.sums (hw.minus hW)).same (Eventually.of_forall fun i b=> Eventually.of_forall fun y=>?_)
    change F' i b y=F' i false y+(W' i b y-W' i false y)
    suffices h:∀ b,F' i b y= W' i b y+ (if r i then Coat.scale • baseStroke (T (t i false)) s (choice S' (M i).tag) (L i y) (.inr j) else (0:G.Color)) from by rw [h,h]; abel -- underscore tube explicit
    intro b; by_cases hz:r i; swap; · unfold F' bar W'; simp only [if_neg hz]; rw [if_neg (show ¬(X i b y).selected S' (spot S _) from hz), add_zero] -- proof dep
    unfold F' bar W'; rw [if_pos (show (X i b y).selected S' (spot S _) from hz), if_pos hz, if_pos hz]; unfold strain freely
    rw [show baseStroke (T (t i b)) _ (choice S' (X i b y).k) _ _=baseStroke (T (t i false)) s (choice S' (M i).tag) (L i y) (.inr j) from rfl]; change Coat.scale • (_ -G' i b y (.inr j)+orientedRow (T (t i b)) (till s) S' (.inr j) (Y i y) ((X i b y).signal 0))= _; unfold Y'; simp only [sub_eq_add_neg,smul_add]; abel
lemma movesT (z:Mention c f) {u:κ→ Bool→E→Directions G f}(hf:Walt qq τ k u): Walt qq τ k (fun n b y=> bar (vary ((M n).order (T (t n b)) s χ U.K) (Y n y)) (u n b y) z):=by
    refine ((p.stocks h he hK z.1 z.2).sums ((Walt.ready Coat.scale).pay (p.orbitW h he hf (M:=M) z))).same ?_
    exact Eventually.of_forall fun i b=> Eventually.of_forall fun y=> Blaze.balances (X:= vary ((M i).order (T _) _ _ _) _) (H (t i b)|>.laws.data.room) z (u i b y)
lemma tentsW (z:Mention c f) {u:κ→ Bool→E→Directions G f}(hf: Walt qq τ k u) : Walt qq τ k (fun n b y=> pot (vary ((M n).order (T (t n b)) s χ U.K) (Y n y)) z.1 z.2 (u n b y)):=by
    have hp := selfP ((Walt.ready ((Coat.scale)⁻¹)).pay (movesT p h he hK z hf))
    refine hp.same ?_; filter_upwards with i b; filter_upwards with y; unfold pot bar; split_ifs; rw [inv_smul_smul₀ Coat.scale_pos.ne']; simp
lemma costsW (v:Signed)(z:Coat.Spot c f){u:κ→ Bool→E→Directions G f}(hf: Walt qq τ k u): Walt qq τ k (fun n b y=> Vine.costs (vary ((M n).order (T (t n b)) s χ U.K) (Y n y)) (u n b y) v z) := Walt.schedule _ _ (fun j _=> tentsW p h he hK (v,j) hf)
end Score
end YM.UVExtension.Span
#print axioms YM.UVExtension.Span.Score.gram
#print axioms YM.UVExtension.Span.Score.costsW
