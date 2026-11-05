import YM.UVExtension.Span.Palm
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
variable (hu:StableR v R) [NeBot v]
open Polar Raw Silica Eider
-- all joint primitives before Stock rollover. choose costs slim for supports.
-- real tight at unbounded Air; no comparison here
structure Toll (i : ι)(j:Head S)(a:ℝ):Prop where
    value (F:Forest S.ratio)(X:Coat (T i) F): X.x=s → X.width=U.K → X.χ=χ → X.manifest →∀ z n,|(X.vertex (R i) Q.table w U.a n Q.halo z j)|≤ a
    funded (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](F:Forest S.ratio)(X:Coat (T i) F)(Y:E→Config G c)(Z: E→ Directions G f)(τ:E)(P:E→Air f G)(r: Air f G): X.x=s → X.width=U.K → X.χ=χ → X.manifest →Mode Y τ k u→ Clutch X r U.a (R i).beta d τ k Y Z P → Healthy (temp X.x) ((H i).supportP j) X.V → ∀ n:Finset ℕ, Brush k a 1 (fun v=> Polar.ember (vary X (Y v)) U.a (R i) w Q.table (Z v) (X.input (worldZ X (R i).beta r)) (P v) n Q.halo j) τ
-- H: etc params p phantom not explicit? Toll signature in terms parameters referenced specify in later with abbreviation
abbrev Lodge (_:Score v T H k l χ A b u B N r d f' V Z) (i:ι) (j:Head S) (c:ℝ):= Toll (H:=H) (χ:=χ) (k:=k) (u:=u) (d:=d) i j c
def Lloyd (F: α→Head S):Prop:= ∃ f:ι→α→ℝ, Swift v f∧∀ᶠ i in v, ∀ j,Lodge p i (F j) (f i j)
include p
lemma lloyd_union (F:α→Head S)(Y: β→ Head S)(hp:Lloyd p F)(h:Lloyd p Y): Lloyd p (Sum.elim F Y):=by
   obtain ⟨f,hf,hp⟩:= hp; obtain ⟨g,hg,h⟩:= h; exact ⟨_,hf.onion hg,(hp.and h).mono (fun i hi x=>match x with| Sum.inl x=>hi.1 _|.inr x=> hi.2 _)⟩

-- cap `innerShare k*q.T` and Puts; works for all E.ρ primitive Germ *even when v huge* from Clutch.patch charge. old path IQ lift
lemma haj (Δ:ℝ) : ∃ (F: ℝ),0 ≤ F ∧ ∀ (n:ι) (P:Forest S.ratio) (Z:Coat (T n) P),Z.χ=χ → Z.x=s → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (X:E→ Config G c)(Y:E→ Directions G f) (v:E→ Air f G) (z:Air f G) (τ:E), Clutch Z z U.a (R n).beta d τ k X Y v → 0<Δ*Z.t → (∀ i,Brush k F 1 (fun y=> Z.cone Δ (Y y) i) τ) ∧ ∀ l:Finset (Bond f), Brush k F 1 (fun y=>Z.enforce Δ (Y y) l) τ :=by
   obtain ⟨w,hw,hp⟩ := Brush.compact (k:=k) (f:=χ.read) (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=>
       χ.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
   let t:= Δ*Pressure.fiery G s S.patch.L
   let K:= t⁻¹*(d+2*t); let R:= |(1+(k.factorial:ℝ)*w)*((1+K*K)*(1+1))|
   let c':ℝ:= (1+R)^k; let B:ℝ:=Fintype.card (Bond f); let V:=(1+B*R)^k; have hr: 0≤ R:=abs_nonneg _; have hc:0≤ c':=by unfold c'; positivity
   refine ⟨max c' V, hc.trans (le_max_left ..),?_⟩
   intro n F Z hZ hx E _ _ X Y v z τ p he
   have h(i):Brush k 1 R (fun y=>Z.cone Δ (Y y) i) τ:=by
     by_cases hv : (fun y=> Z.cone Δ (Y y) i)=ᶠ[𝓝 τ] (fun _=>0); · exact Brush.zi hv zero_le_one hr
     obtain ⟨hd,hA⟩:= Silica.Clutch.fostered p i he hv
     unfold cone; rw [hZ]; apply (plateauChi χ hA hp he (by rw [←mul_assoc]; exact hd)).climb le_rfl; unfold R K t; rw [← hx]; unfold Coat.t; rw [mul_assoc (2:ℝ) Δ]; exact le_abs_self _
   refine ⟨fun i=> ((h i).trim).climb ((one_mul _).trans_le (le_max_left c' V)) le_rfl,fun l=>?_⟩; have hf:=Brush.all_prod l _ _ _ (fun i (_:i∈l)=> h i); simp only [prod_const_one,sum_const,nsmul_eq_mul] at hf; refine hf.trim.climb ?_ le_rfl
   rw [one_mul]; apply (le_max_right c' V).trans'; unfold V; unfold B; gcongr; exact card_le_univ _

-- χ masks not handled by analytic atComplex. explicit.
section gr
omit p [NeBot v]
-- exp(f)-1 uniform linear bound along all real input curves analytic f ≤r in Brush (pointwise). exploit scales
lemma exam (k:ℕ)(R:ℝ)(hR:0≤R) : ∃ K:ℝ,0≤K∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f:E→ℝ)(τ:E) (a:ℝ), a≤R → Brush k a 1 f τ → Brush k (K*a) 1 (fun u=> Real.exp (f u)-1) τ:=by
   obtain ⟨v,hv,h⟩:= Brush.expands k
   obtain ⟨u,hU,hV⟩:= Brush.compact (k:=k) (f:=fun i:ℝ=> Real.exp i-1) (s:=Metric.closedBall 0 R) (isCompact_closedBall _ _) (fun i hi=> Real.contDiff_exp.contDiffAt.sub contDiffAt_const)
   let K:= k.factorial*u*(1+((1+R)*1))^k; have hx:0≤ K:=by unfold K; positivity
   refine ⟨max v K,hv.trans (le_max_left ..),fun E _ _ f τ a ht hp=>?_⟩
   by_cases he:a≤1; · exact (h E τ a 1 f hp he).climb (mul_le_mul_of_nonneg_right (le_max_left ..) hp.nonneg) le_rfl
   have hh:= (hp.climb ht le_rfl).pine (hV _ (mem_closedBall.mpr (by rw [dist_zero_right]; exact hp.bound.trans ht)))
   exact hh.trim.climb ((le_max_right v K).trans (le_mul_of_one_le_right (hx.trans (le_max_right ..)) (not_le.mp he|>.le))) le_rfl
end gr
include hu
lemma lumberT (hx:0≤u): Lloyd p (fun i:LogLetter c f=> Sum.inr (.inr (.inl (.inl i)))):=by
   obtain ⟨r,h₁,h⟩:= p.vouchers hu hx; obtain ⟨K,hK,hL⟩:= h₁.tills
   obtain ⟨F,hF,hv⟩:= haj p (2*U.a); let B:= 1+ F*(1+(1+1))^k; have hb:F*(1+(1+1))^k≤B:= le_add_of_nonneg_left zero_le_one; have hB:1≤B:= le_add_of_nonneg_right (by positivity); have hp :0 ≤ B:=zero_le_one.trans hB
   obtain ⟨C,hC,hY⟩:= exam k (B*K) (mul_nonneg hp hK.le)
   refine ⟨_, ((h₁.scales B hp).scales C hC),?_⟩
   filter_upwards [h,hL] with i hh hz j
   let P:=R i; let T':=T i; have ht : B*r i j≤B*K := mul_le_mul_of_nonneg_left (budget_single hz j) hp
   have hy : r i j≤B*r i j:= le_mul_of_one_le_left (hz.1 _) hB
   refine ⟨fun W X hX hu hχ hm z n=> ?_,fun E _ _ _ W X Y Q' τ P' r' hX hu hχ hm ht' hg hZ n=> ?_⟩
   · let f':= X.farLog (R i) U.a Q.table z (.inl j); have he:|f'|≤ B*r i j:= by
        let v:= X.liftA P.beta z; unfold f' farLog inhale; dsimp only [Sum.elim]; rw [abs_mul]
        have hS:= X.conserve (X.plaza (Raw.space T' 0 X.B P j)) (2*U.a) v; have hx: |expo (T i) X.x P (X.input v) X.V j|≤ B*r i j := (hX.symm ▸ (hh (X.input v) j).1 X.V).trans hy; exact (mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith only [hS.1],hS.2⟩)).trans hx
     exact (hY ℝ (fun _=>f') 0 (B*r i j) ht ((Brush.certified zero_le_one _).climb he le_rfl)).bound
   have hU := hh (X.input (worldZ X P.beta r')) j|>.2 E Y τ ht'; have hΘ:= hv i W X hχ hX E Y Q' P' r' τ hg (by rw [mul_assoc]; exact mul_pos zero_lt_two hg.pulse)
   have hw y : (vary X (Y y)).x=s:=hX
   apply hY _ _ _ (B*r i j) ht
   change Brush _ _ _ (fun u=> frost ..) _; unfold Polar.frost
   -- rewrite x only in nest
   conv => arg 4; intro y; arg 1; rw [hw]
   exact (hU.paints (hΘ.2 (X.plaza (Raw.space (T i) 0 X.B (R i) j)))).trim.climb ((le_of_eq (by ring : r i j *F*(1+(1+1))^k= F*(1+(1+1))^k *r i j)).trans (mul_le_mul_of_nonneg_right hb (hz.1 _))) le_rfl

lemma broadP : Lloyd p (fun i:ℕ=> Sum.inr (.inl i)) :=by
   obtain ⟨W,hw,h⟩:=hu.alongK; obtain ⟨A,hA⟩:=hw.books; obtain ⟨F,hF,hv⟩:= haj p (2*U.a); let B:=max 1 (F*(1+(0+1))^k); have hb:1≤B:=le_max_left ..; let b:= (R ·)
   refine ⟨_,hw.scales B (zero_le_one.trans hb),?_⟩; filter_upwards [h,hA] with i h hx j; refine ⟨fun V X _ _ _ _ Z d=>?_,fun E _ _ _ V X Y Q' τ U' K hX hu hχ hM hU hv' hK J=>?_⟩
   · change |_ * Coat.enforce _ _ _ _| ≤ _; rw [abs_mul]; apply (mul_le_of_le_one_right (abs_nonneg _) ?_).trans ((h j _).trans (le_mul_of_one_le_left (hx.1 _) hb)); apply abs_le.mpr; have hp:= X.conserve (X.plaza (forcedFoot S.ratio 0 X.B (R i) j)) (2*U.a) (X.liftA (R i).beta Z); exact ⟨(by linarith only [hp.1] : -(1:ℝ)≤X.enforce _ _ _),hp.2⟩
   let W':= W i j; let f:= (R i).activities.K j (X.input (worldZ X (R i).beta K)); have hK:|f| ≤ W':= h j _
   have hΘ:= hv i V X hχ hX E Y Q' U' K τ hv' (by rw [mul_assoc]; exact mul_pos zero_lt_two hv'.pulse)
   refine ((((Brush.certified (le_refl 0) f).climb hK le_rfl).paints (hΘ.2 (X.plaza (forcedFoot S.ratio 0 X.B (R i) j)))).trim).climb ?_ le_rfl
   exact (le_of_eq (by ring : W'*F*(1+(0+1))^k= (F*(1+(0+1))^k)*W')).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (hx.1 j))
end Score
end YM.UVExtension.Span
