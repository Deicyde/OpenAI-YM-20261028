import YM.UVExtension.Wet.Aung
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady PhysicalNext.Repeat Lotus
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a ag u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Strata Strata.Polish Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
open Polar Silica Shield Score Flux Matter
open Wren Wren.Choir Gala Badge Next.Foundations Greenbelt Gas Multiple Ursell Trees Letter OmitClusters March Daisy Charity
variable [NeBot v][v.IsCountablyGenerated]{H:∀ i:ι,Cash w s q L Q U C (T i) (R i)}
variable {D:(i:ι)→ Lotus.Leaf (R i)}(p:Choir v T H k χ) (h:StableR v R)(g:Constant (v:=v) D)(j:ι)
local notation "P"=> H j
local notation "T!"=> p.sails j
local notation "X0"=> p.laws
local notation "q'"=> p.u
set_option quotPrecheck false
include p h g
lemma escortD {X:ι×ι→ Config G c} (m:(H j).ThinP)(hx:∀ n, Healthy (temp s) ((H j).unionP m.val) (X n)): Baton (v ×ˢ v) (fun n b V=> libs (D (wagtail n b)) (H (wagtail n b)) χ V (p.ice h j (wagtail n b) m)) X q' k:= by
    obtain ⟨V,Y,ht⟩:= cameo p.laws (p.sails j).position.le h g
    intro E _ _ _ W t hW he
    letI :=Tree.select S.ratio S.patch.odd_side
    let f (l:Greenbelt.Reserve S) n b y:= (D (wagtail n b)).picture (vary (prism (T (wagtail n b)) s χ U.K (X n) (Greenbelt.allot (S:=S) l)) (W n y)) m.val w U.a Q.table Q.halo
    have ht' n b : Healthy (temp s) ((H (wagtail n b)).unionP m.val) (W n (t n)):= p.laws.riders h.toKept j (wagtail n b) m.val ▸ (hW n ▸ hx n)
    have hD(l:Greenbelt.Reserve S): Walt (v×ˢv) t k (f l):= uplifts p.laws g (p.sails j).position.le h wig (pathD X l) he V Y ht m.val m.property.2 ht' hW
    apply ((Walt.ready (Fintype.card (Greenbelt.Reserve S):ℝ)⁻¹).times (Walt.schedule Finset.univ f (fun i _=>hD i))).same
    filter_upwards with n b; filter_upwards with r; change escort _ _ _ _ _ _ _ _ _ _ _ = _; rw [p.ice_all h j _ m]; rfl
omit g in
lemma batonD {X:ι×ι→ Config G c} (m:(H j).ThinP)(hx:∀ n,Healthy (temp s) ((H j).smallAt m) (X n)): Baton (v×ˢv) (fun n b=> p.tables h j (wagtail n b) m) X q' k:=by -- via vacuum fable over trivial shape? turns k singleton
    -- via direct
    obtain ⟨V,Y,ht⟩:= Polish.entrance p.laws (p.sails j).position.le h
    intro E _ _ _ W t hW he
    letI :=Tree.select S.ratio S.patch.odd_side
    let g (l:Greenbelt.Reserve S) n b y:= Stained.fringe (vary (prism (T (wagtail n b)) s χ U.K (X n) (Greenbelt.allot (S:=S) l)) (W n y)) w U.a m.val (R (wagtail n b)) Q.table Q.halo
    have ht' n b : Healthy (temp s) ((H (wagtail n b)).unionP m.val) (W n (t n)):= p.laws.riders h.toKept j (wagtail n b) m.val ▸ (hW n ▸ hx n)
    have hD (l : Greenbelt.Reserve S): Walt (v×ˢv) t k (g l):= Polish.tightR p.laws wig (pathD X l) he h (p.sails j).position.le V Y ht m.val m.prop.2 ht' hW
    apply ((Walt.ready (Fintype.card (Greenbelt.Reserve S):ℝ)⁻¹).times (Walt.schedule Finset.univ g (fun i _=>hD i))).same
    filter_upwards with n b; filter_upwards with r; exact p.coins h j _ (X n) (W n r) m
lemma melts (m:(H j).fragrances)(n:ι): speaks (D n) (H n) (p.casts h j n m)↔ speaks (D j) (H j) m:=by
    rcases m with ⟨m,x⟩; change (∃ i,(D n).turn.badge S∈(p.ice h j n (x i)).val∧troupe _ _ _ _ (p.ice h j n (x i)).val) ↔ (∃ i,(D j).turn.badge S∈ (x i).val ∧ troupe _ _ _ _ (x i).val); simp_rw [ice_all, g.turnC n j, h.toKept.phalanx T Q.halo (radiusB s) n j]
lemma heights (o:Site c)(m:(H j).fragrances) (n): locus (D n) (H n) o (p.casts h j n m)=locus (D j) (H j) o m:=by
    unfold locus; split; next ht=> rw [if_pos ((melts p h g j m n).1 ht)]; exact p.landscapes h j m n
    next he=> rw [if_neg (mt (melts p h g j m n).2 he)]
def froth (D:(i:ι)→ Lotus.Leaf (R i))(m:(H j).fragrances)(n:ι): Config G c→ℝ:= matin (D n) (H n) (p.casts h j n m) χ
omit g in
lemma fortune (n:ι) (m:(H j).fragrances) (x:Config G c): froth p h j D m n x=sailsW (H:=H) j m *∑ i,(∏ l ∈ univ.erase i,leaflet (H n) χ x (p.ice h j n (m.2 l))) * libs (D n) (H n) χ x (p.ice h j n (m.2 i)) := by rcases m with ⟨m,f⟩; unfold froth matin; rw [p.tariffs h j ⟨m,f⟩]; rfl
lemma fanfare {X:ι×ι→ Config G c} (m:(H j).fragrances)(o:Site c)(hx:∀ n,Healthy (temp s) (locus (D j) (H j) o m) (X n)): Baton (v×ˢv) (fun n b=> froth p h j D m (wagtail n b)) X q' k:=by
    by_cases hv:speaks (D j) (H j) m; swap; · intro E _ _ _ W t ht hh; apply (Walt.ready (0:ℝ)).same; filter_upwards with n b; filter_upwards with r; change froth .. = _; exact congr_fun (quiet _ _ _ _ (mt (melts p h g j m (wagtail n b)).1 hv)) _
    unfold locus at hx; rw [if_pos hv] at hx
    intro E _ _ _ W t ht hh
    have hx'(i)(n): Healthy (temp s) ((H j).smallAt (m.2 i)) (X n):= Finset.disjoint_of_subset_left (subset_biUnion_of_mem ((H j).smallAt ∘ m.2) (mem_univ i)) (hx _)
    have he(i):= batonD p h j _ (hx' i) E W t ht hh; have hC(i):= escortD p h g j _ (hx' i) E W t ht hh
    let f i n b y:= (p.tables h j (wagtail n b) (m.2 i)) (W n y)
    apply ((Walt.ready _).times (Walt.schedule univ _ (fun i _=> (caraffa (univ.erase i) f (fun i _=> he i)).times (hC i)))).same
    filter_upwards with n b; filter_upwards with y; exact fortune p h j (wagtail n b) _ _
-- Tunes lotus. all supports
set_option quotPrecheck false
abbrev yu n p V:= (D n).lotus (T n) s χ U.K w U.a Q.table Q.halo V p
include j
lemma honey : Transit v (fun n p V=> yu (T:=T) (D:=D) (Q:=Q) (U:=U) (χ:=χ) (s:=s) n p V):=by
    obtain ⟨f,hf⟩:= arrest p.laws g (p.sails j).position.le h
    let F n i V:= (D n).lotus (T n) s χ U.K w U.a Q.table Q.halo V i; obtain ⟨C,hC⟩:= hf.swift.books
    letI :=Tree.select S.ratio S.patch.odd_side
    let W:ℝ:= Fintype.card (Greenbelt.Reserve S); have hw: 0<W:= by unfold W; positivity
    have hp: ∀ᶠ n in v,∀ i V,‖F n i V‖≤ f n i:=by
       filter_upwards [hf.laws] with n hn i V; unfold F Leaf.lotus likely; rw [norm_mul, Real.norm_of_nonneg (inv_pos.mpr hw).le]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (g:=fun _=> f n i) fun j _=> (hn i _ _ rfl rfl rfl).1)) (inv_pos.mpr hw).le); rw [sum_const,card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hw.ne']
    refine ⟨⟨f,hf.swift,hp⟩,fun m=> Tune.spans ⟨C,(hp.and hC).mono fun i hh x=> (hh.1 _ x).trans (budget_single hh.2 _)⟩ (fun Y=>?_)⟩
    obtain ⟨V,X,ht⟩:= cameo p.laws (p.sails j).position.le h g
    let e (o:Greenbelt.Reserve S)(n:ι×ι)(b:Bool):= let i:=wagtail n b; (D i).bloom (prism (T i) s χ U.K (Y n) (Greenbelt.allot (S:=S) o)) w U.a Q.table Q.halo m
    have hz(i):Together (v×ˢv) (e i):= unfurled p.laws g (p.sails j).position.le h wig (pathD Y i) V X ht m
    apply ((Walt.ready ((Fintype.card (Greenbelt.Reserve S):ℝ)⁻¹)).times (Walt.schedule Finset.univ _ (fun i _=> Walt.stamp (x:=bracket) (k:=k) (hz i)))).atProbe.shimmy
    filter_upwards with n; ext1 b; cases b <;> rfl
end YM.UVExtension.Wet
