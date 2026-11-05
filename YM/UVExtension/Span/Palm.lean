import YM.UVExtension.Span.Jut
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
open Polar Raw
section tags
variable {u':ι→α×β→ℝ}
lemma insulate [Fintype α] (p:∀ i:α,Swift v fun n j=> u' n (i,j)): Swift v u':=by
   choose r hr using fun i=> (p i).books; refine ⟨⟨∑ i,r i,?_⟩,fun ε h=>?_⟩
   · filter_upwards [eventually_all.mpr hr] with n hn; exact budget_rows (u' n) r hn (budget_finite (fun i=> budget_nonneg (hn i)) le_rfl)
   let C:ℝ:= Fintype.card α; have he : 0 ≤ C:= Nat.cast_nonneg _; let b:= ε/(1+C); have hb:0<b:=by unfold b; positivity
   choose s hs using fun i=>(p i).drops _ hb; refine ⟨univ.biUnion (fun i=> (s i).image (Prod.mk i)),?_⟩
   filter_upwards [eventually_all.mpr hs] with n hn
   refine budget_rows _ (fun _=>b) ?_ (budget_finite (fun _=>hb.le) ?_); intro i; simp; exact hn _ -- simp
   simp only [sum_const,nsmul_eq_mul,card_univ]; exact (mul_le_mul_of_nonneg_right (by linarith : C≤1+C) hb.le).trans_eq (by unfold b; field_simp)

-- exponent polynomial reserve lemma
lemma pays (c:ℝ)(he:0≤c)(u:ℝ)(hu:0<u)(k:ℕ): ∃ d:ℝ,0≤d∧∀ z:ℝ,0≤z→(1+z*c)^k≤ d*Real.exp (u*z):=by
    let h:=max u c
    let d:= ((1/u)+c/u+1+u)^k * k.factorial*Real.exp 1; -- comparison (L*(u*z+1))^k
    refine ⟨d, by unfold d; positivity, fun z hz=>?_⟩
    let D:=1/u+c/u+1+u; have hD:0≤D:=by unfold D; positivity
    have hv:1+z*c ≤ D*(u*z+1):=by
       unfold D; field_simp; nlinarith [mul_nonneg he hz,mul_nonneg hz (sq_nonneg u),show 0≤ u^3*z by positivity]
    calc
       _ ≤ (D*(u*z+1))^k:= pow_le_pow_left₀ (by positivity) hv _
       _ ≤ D^k*(Real.exp (u*z+1)*k.factorial):= by rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp _ (by positivity) _)) (pow_nonneg hD _)
       _ = _ := by unfold d D; rw [Real.exp_add]; ring
end tags

variable (Zc:StableR v R) [NeBot v]
include p
lemma steadyβ : ∃ r:ℝ, 0≤r∧∀ i, |-orientation*(R i).beta|≤ r ∧ |-orientation|≤ r:=by
   have hx:= orientation_range
   obtain ⟨i,hi⟩:= (Eventually.of_forall (p:=fun i:ι=>True) fun i=>True.intro : ∀ᶠ i in v, True).exists
   have hh:= H i|>.laws.intake.height
   let b:= betaF G s S.patch.L; change 1<b at hh
   use 2*b; refine ⟨by positivity,fun i=>?_⟩; have ht:= (H i).laws.intake
   rw [abs_mul,abs_neg,abs_of_pos hx.1,abs_of_pos ht.positive]; exact ⟨(mul_le_of_le_one_left ht.positive.le hx.2).trans ht.window.2,hx.2.trans (by linarith)⟩

-- Path (old/uv). atom & labels pricing
omit p in lemma atomPalm {σ:ℝ} (h:0<σ) {k:ℕ}(A:ι→ ℕ→ Atom G k) (Y:ℝ)(hy:0≤Y) (hp:Swift v fun n i=> (A n i).budget σ):
    ∃ F:ι→ Raw.Trans f→ℝ,Swift v F∧∀ i a, |a|≤Y → ∀ t U x, |Raw.translateValue t (A i) a U x|≤ F i x:=by
   let T i x:= (2:ℝ)^k*(A i x).budget σ; let f i (x:Raw.Trans f):= Y*T i x.2.2
   refine ⟨f, insulate fun i=> insulate fun j=> (hp.scales _ (by positivity : (0:ℝ)≤2^k)).scales _ hy, ?_⟩
   intro i a ha t U x; unfold Raw.translateValue; rw [abs_mul]; apply (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans; refine mul_le_mul_of_nonneg_left ?_ hy
   exact ((A i _).placed_bound _ _ _).trans (((mul_le_mul_of_nonneg_right ((A i _).lower_budget _ h) (by positivity : (0:ℝ) ≤2^k))).trans_eq (mul_comm ..))

omit p in lemma pairPalm (T:ι→PathData G) (σ:ℝ) (Z:PathData G)(h:Revenues v σ T Z)(Y:ℝ)(hy:0≤Y):
    ∃ F:ι→ Raw.Pairs n→ℝ,Swift v F∧∀ i t K R W a, |a|≤ Y→∀ U x,|pairValue (T i) t K R W a U x| ≤ F i x:=by
   let r i j k:= |((T i).row j k).1|; let f i (j: Raw.Pairs n):=Y*(2*(r i j.2.1 j.2.2.2.1*r i j.2.1 j.2.2.2.2))
   refine ⟨f,insulate (fun i=>insulate (fun j=>insulate fun k=> ((((h.fees' j).mixes (h.fees' j)).scales 2 (by norm_num)).scales _ hy))),?_⟩
   intro i t K R W a ha U x; unfold pairValue; rw [abs_mul]; apply mul_le_mul ha _ (abs_nonneg _) hy
   apply (pair_le ..).trans; unfold pairPrice; dsimp only; split; rfl; next=> unfold r; positivity

lemma iciclePalm {σ:ℝ}(Z: PathData G)(ht:Revenues v σ (fun i=> (T i).down) Z)(u':ℝ)(hu:0≤u')(Y:ℝ)(hy:0 ≤ Y): ∃ f:ι→Pairs c→ℝ,Swift v f∧∀ i,∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V:E→Config G c) (τ:E) (a:ℝ),|a|≤Y→ Mode V τ k u' →∀ t:Pairs c, Brush k (f i t) 1 (fun y=>icicle (T i).down (V y) (till s) S.patch.L.val a t) τ:=by
   let c':=royalty G^2; let h:=2*(u'*royalty G); have hh:=royalty_ge G; have he :0≤c':=by unfold c'; positivity
   have hg : 0≤h:= by unfold h; positivity
   let v0 i p z:= ((T i).down.row p z).2
   let f i p z:= |((T i).down.row p z).1| *c'*(1+(v0 i p z).length*h)^k; have hs i p z:0≤f i p z:=by unfold f; positivity
   have hf p: Swift v fun i z=> f i p z:= by
      obtain ⟨d,hd,hD⟩:= pays h hg σ ht.pos k; apply (((ht.fees p).2.scales _ hd).scales _ he).le
      exact Eventually.of_forall fun i z=> ⟨hs i _ _,(mul_le_mul_of_nonneg_left (hD ((v0 i p z).length:ℝ) (Nat.cast_nonneg _)) (mul_nonneg (abs_nonneg _) he)).trans_eq (by unfold v0; rw [ht.slots]; ring)⟩
   let A i (t:Pairs c):=Y*((f i t.2.1 t.2.2.2.1*f i t.2.1 t.2.2.2.2)*(1+(1+1))^k); refine ⟨A,?_,?_⟩
   · apply insulate; intro i; apply insulate; intro j; apply insulate; intro v; refine ((((hf j).mixes (hf j)).scales ((1+(1+1))^k) (by positivity)).scales _ hy).eq (Eventually.of_forall (fun d=> funext fun z=> congr_arg (Y*·) (mul_comm ..)))
   intro b E _ _ U w a ha M t; have H':= Blaze.turn M t.1; let i:Cell c:=(t.2.2.1,t.2.1); let V z:= pull t.1 0 (U z); have hX n : Brush k (f b t.2.1 n) 1 (fun z=> (T b).down.ellTerms i n (V z)) w:=by
       have hp := (slot_cost (v0 b t.2.1 n) i.1 hu H'.atLink).smul ((T b).down.row t.2.1 n).1 |>.trim
       refine hp.climb ?_ le_rfl; unfold f h c'; rw [Real.norm_eq_abs]; apply le_of_eq; ring
   unfold icicle Polar.twin; split_ifs
   · refine (((semi (stroke (hX _) (hX _))).trim).smul a).climb ?_ le_rfl
     exact mul_le_mul_of_nonneg_right ha ((mul_nonneg (mul_nonneg (hs b ..) (hs b ..)) (by positivity)))
   next ht=> simp only [mul_zero]; refine Brush.zi EventuallyEq.rfl ?_ zero_le_one; exact mul_nonneg hy (mul_nonneg (mul_nonneg (hs b ..) (hs b ..)) (by positivity))

include Zc
lemma vouchers (hu:0≤u) : ∃ coin:ι→ LogLetter c (f)→ℝ, Swift v coin∧∀ᶠ i in v,∀ (Y:Config G (f))(x:LogLetter c (f)), (∀ U, |expo (T i) s (R i) Y U x| ≤ coin i x) ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V:E→Config G c) (τ:E),Mode V τ k u → Brush k (coin i x) 1 (fun y=>Polar.nest (T i) s (V y) Y (R i) x) τ:=by
   obtain ⟨A,h,hA⟩:= p.steadyβ; obtain ⟨σ,g,hσ⟩:=p.views.cap; obtain ⟨t,hv0,ht⟩:=p.views.cap'; obtain ⟨F,hF,hr⟩:=Zc.alongE
   obtain ⟨G₁,h₁,k₁⟩:= atomPalm (f:=f) hσ.pos _ _ h hσ.parked₁.2; obtain ⟨G₂,h₂,k₂⟩:= atomPalm (f:=f) hσ.pos _ _ h hσ.parked₂.2; obtain ⟨G₃,h₃,k₃⟩:=atomPalm (f:=f) hσ.pos _ _ h hσ.parked₃.2
   obtain ⟨T₁,H,Ht⟩:=pairPalm (n:=f) _ σ g hσ _ h; obtain ⟨T₂,h₂',Ht'⟩:=pairPalm (n:=c) _ t hv0 ht _ h; obtain ⟨T₃,hv,ht'⟩:= p.iciclePalm hv0 ht u hu _ h
   obtain ⟨m,hm⟩:=hv.books; obtain ⟨r,hy⟩:=h₂'.books
   refine ⟨_,hF.onion (h₂.onion (h₃.onion (h₁.onion (H.onion (h₂'.plus hv))))),?_⟩
   filter_upwards [hr,hm,hy] with n hn hp hz Y i; have hx:=hA n
   have hb:|- (-orientation*(R n).beta)| ≤ A:= by rw [abs_neg]; exact hx.1
   rcases i with i|i|i|i|i|i; all_goals simp only [expo,nest,Sum.elim]
   · have h:|-(R n).activities.regularOccurrence (R n).p i Y|≤F n i:= (abs_neg _).trans_le (hn i Y); exact ⟨fun V=>h,fun _ _ _ _ _ _=> (Brush.certified zero_le_one _).climb h le_rfl⟩
   · rw [(p.upR n).1]; exact ⟨fun V=> k₂ n _ hx.1 _ _ _,fun _ _ _ _ _ _=> (Brush.certified zero_le_one _).climb (k₂ n _ hx.1 _ _ _) le_rfl⟩ -- `rw` changes
   · rw [(p.upR n).1]; exact ⟨fun V=> k₃ n _ hx.1 _ _ _,fun _ _ _ _ _ _=> (Brush.certified zero_le_one _).climb (k₃ n _ hx.1 _ _ _) le_rfl⟩
   · rw [(p.upR n).1]; exact ⟨fun V=> k₁ n _ hx.2 _ _ _,fun _ _ _ _ _ _=> (Brush.certified zero_le_one _).climb (k₁ n _ hx.2 _ _ _) le_rfl⟩
   · rw [(p.upR n).1]; exact ⟨fun V=> Ht n _ _ _ _ _ hx.1 _ _,fun _ _ _ _ _ _=> (Brush.certified zero_le_one _).climb (Ht n _ _ _ _ _ hx.1 _ _) le_rfl⟩
   exact ⟨fun V=> (Ht' n _ _ _ _ _ hb _ _).trans (le_add_of_nonneg_right (hp.1 _)),fun E _ _ V τ hτ=> (ht' n E V τ _ hb hτ _).climb (le_add_of_nonneg_left (hz.1 _)) le_rfl⟩
end Score
end YM.UVExtension.Span
