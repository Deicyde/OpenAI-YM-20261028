import YM.UVExtension.Span.Mug
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
variable [NeBot v]
-- Helpers.
open Mask Raw Matter Poll Pond Silica Eider Polar Reserves
include p
-- finite Head remainder
lemma larked [Fintype α](J: α→ Head S)(h:∀ i,∃ r,0≤r∧∀ᶠ k in v,p.Lodge k (J i) r): Lloyd p J:=by
   choose r hr hv using h; refine ⟨fun _=>r, Swift.sight fun i=>⟨_,Eventually.of_forall fun _=>⟨hr i,(le_refl (r i))⟩⟩,eventually_all.mpr hv⟩
lemma caging (P:Stores S)(c':ℝ): ∃ d:ℝ,0≤d∧∀ i, steamP S (Q.costs L q (R i).beta s c') P≤d:=by
   let K x:=steamP S (Q.costs L q x s c') P; have hk : Continuous K:=by unfold K steamP Target.costs Packets.income Buy.quote Grant.credit; fun_prop
   let M:=Set.Icc (betaF G s S.patch.L/2) (2*betaF G s S.patch.L); obtain ⟨r,hr⟩:=(isCompact_Icc (a:=betaF G s S.patch.L/2) (b:=2*betaF G s S.patch.L)).exists_bound_of_continuousOn hk.continuousOn
   exact ⟨_,abs_nonneg r,fun i=> (le_abs_self _).trans ((hr _ (H i).laws.intake.window).trans (le_abs_self _))⟩
lemma pitcher : Lloyd p (Sum.inl : Stores S → Head S):=by
    apply larked; intro i
    obtain ⟨T,hT,hv⟩:= caging p i C; obtain ⟨u,hu,hp⟩:= caging p i N
    let r':=(1+|r|)^k; have hr:0≤r':=by unfold r'; positivity
    let b:=max T (u*r'); have ht:b≥T:=le_max_left ..; have hb:0≤b:=hT.trans ht; refine ⟨b,hb,?_⟩
    filter_upwards with n; constructor; · intro F X hs hu hχ hm z b; refine ((H n).voice X hs hu hm b (Sum.inl i) z).trans ?_; unfold Cash.fair Mixed.costs; dsimp only [Sum.elim]; split; exact (hv n).trans ht; exact hb
    intro E _ _ _ F X Y W τ U' Z hs hz hχ hm hW he ht l
    have hx:=(p.pond n).stream E F X Y W U' τ Z hs hz hχ hm hW he l (.inl i) ht; dsimp only at hx
    refine hx.trim.climb ((le_max_right (α:=ℝ) T _).trans' ?_) le_rfl; unfold stout spanW Mixed.costs; simp only [Sum.elim]; split
    · have hr : 1 ≤ r:= (p.pond n).active; rw [mul_one]; unfold r'; rw [abs_of_nonneg (zero_le_one.trans hr)]; exact mul_le_mul_of_nonneg_right (hp _) (by positivity)
    rw [zero_mul]; exact mul_nonneg hu hr
-- uninsured M. warning hedge independent
open Mask Tags
section fog
attribute [local instance] Gauge.frobInner
lemma herald (χ : Chi) (u:ℝ)(hu:0≤u) (t W:ℝ): ∃ r:ℝ,0≤r∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](U:Stores S)(Y:Config G f)(K:S.Choices)(V:E→ Config G c)(τ:E), Mode V τ k u →∀ i: Bond c,Brush k r 1 (fun y=> Mask.noise U χ i t W Y K (V y)) τ:=by
    let f (a:G.Mat) := χ.read ((‖a-1‖/G.colorScale/(W*t))^2)
    have hh : ContDiff ℝ (↑k : WithTop ℕ∞) f := by
       unfold f; simp_rw [div_pow]; exact (χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp
        ((((contDiff_norm_sq ℝ).comp (f:=fun x:G.Mat=>x-1) (contDiff_id.sub contDiff_const)).div_const _).div_const _)
    obtain ⟨v,hv,hp⟩:= Brush.compact (k:=k) (f:=f) (s:=closedBall 0 (royalty G)) (isCompact_closedBall ..) (fun i _=> hh.contDiffAt)
    let r:= (k.factorial*v)*(1+(1+royalty G)*u)^k; have hr:0≤r:=by unfold r; have hx:=royalty_ge G; positivity
    refine ⟨1+r,by positivity,fun E _ _ U Y K V τ h i=> ?_⟩
    let g y:=V y i * (S.prediction Y K i)⁻¹; have hx: Brush k (royalty G) u (fun i=> G.mat (g i)) τ:=by simpa only [one_mul] using! offsetB (h.atLink i) 1 ((S.prediction Y K i)⁻¹)
    have he:=(hx.pine (hp _ (mem_closedBall_zero_iff.mpr hx.bound))).trim
    unfold Mask.noise; split_ifs
    · apply ((Brush.certified zero_le_one _).separating he).climb ; rw [norm_one]; exact le_rfl
    exact he.climb (le_add_of_nonneg_left zero_le_one) le_rfl
end fog
lemma munitions (hn:0≤u):∃ r:ℝ,0≤r∧∀ i,∀ (F:Forest S.ratio)(X:Coat (T i) F)(E:Type) [NormedAddCommGroup E][NormedSpace ℝ E] (V:E→Config G c)(τ:E), X.x=s → X.χ=χ → Mode V τ k u →∀ (U:Config G f)(l:Finset ℕ)(n:Panic c f),Brush k r 1 (fun y=> Polar.veil (vary X (V y)) (R i) w U l n) τ:=by
   obtain ⟨r,hr,hp⟩:= herald p χ u hn (Pressure.fiery G s S.patch.L) w
   let d:= r + topStorm S.patch; have hx: 1≤ topStorm S.patch:=topStorm_one _; refine ⟨d,by unfold d; linarith,fun i F X E _ _ Y τ ht hX he U l n=>?_⟩
   have hv (a : ℝ) (h : 0≤a) (hp : a≤topStorm S.patch) : Brush k d 1 (fun _ : E=> a) τ :=
    (Brush.certified zero_le_one a).climb (by rw [Real.norm_of_nonneg h]; exact hp.trans (le_add_of_nonneg_left hr)) le_rfl
   rcases n with j|j|j|j|j; swap
   · change Brush k _ _ (fun y=> Mask.noise X.seeds X.χ j X.t w U X.k (Y y)) τ; unfold Coat.t; rw [hX,ht]
     exact (hp E X.seeds U X.k Y τ he j).climb (le_add_of_nonneg_right (zero_le_one.trans hx)) le_rfl
   · exact hv (Mask.fine X.seeds X.χ j X.t U) (Mask.fine_range ..).1 ((Mask.fine_range ..).2.trans hx)
   · exact hv (Tags.pinMass U X.k j) (Tags.pin_nn ..) ((Tags.pin_cap ..).trans (le_add_of_nonneg_left (by positivity)))
   · exact hv (Tags.siteMass U X.k j) (Tags.site_nn ..) ((Tags.site_cap ..).trans ((le_add_of_nonneg_left zero_le_one).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))))
   rcases Contract.ordinary (R i) l U j with h|h; all_goals change Brush k _ _ (fun _=> Contract.charges (R i) l U j) τ; simp_rw [h]
   · exact hv _ le_rfl (zero_le_one.trans hx)
   exact hv _ zero_le_one hx
lemma warmly (hn:0≤u) : Lloyd p (fun i: WarningAt c f=> Sum.inr (Sum.inr (.inr i))):=by
   obtain ⟨A,hA,hp⟩:= haj p (2*U.a); obtain ⟨z,hz,h⟩:= p.munitions hn; obtain ⟨B,hB,hx⟩:= haj p U.a
   let b := A*(z+1)*(1+(1+1))^k
   let t:= max (max b (topStorm S.patch)) (B+1)
   have ht: topStorm S.patch ≤ t:= (le_max_right ..).trans (le_max_left ..); have he:1≤t:=(topStorm_one ..).trans ht
   apply larked; intro i; refine ⟨t,zero_le_one.trans he,?_⟩; filter_upwards with j; constructor
   · exact fun F X hs hu hχ hM v b=> ((H j).voice X hs hu hM b (.inr (.inr (.inr i))) v).trans ht
   intro E _ _ _ F X Y W τ Q' w' hs hu hχ hm hM hh ht' n
   have hp := hp j F X hχ hs E Y W Q' w' τ hh (by rw [mul_assoc]; exact mul_pos (by norm_num) hh.pulse)
   have hf := hx j F X hχ hs E Y W Q' w' τ hh hh.pulse
   rcases i with i|i
   · change Brush k _ _ (fun y=> Polar.flare ..) _; unfold Polar.flare
     change Brush k _ _ (fun y=> if mandatory X.seeds X.B i then 0 else _) _; split_ifs; · exact Brush.zi EventuallyEq.rfl (zero_le_one.trans he) zero_le_one
     refine ((hp.2 (X.plaza (halo X.B (districts S i)))).paints ((h j F X E Y τ hs hχ hM _ n i).separating (Brush.certified zero_le_one (1:ℝ)))).trim.climb ?_ le_rfl
     rw [norm_one]; exact (le_max_left b (topStorm S.patch)).trans (le_max_left ..)
   change Brush k _ _ (fun y=> if X.Hot i ∧ i∉ X.plaza (X.seeds.dome (304*X.B)) then X.cone U.a (W y) i -1 else 0) _; split_ifs
   · exact ((hf.1 i).separating (Brush.certified zero_le_one _)).climb (by rw [norm_one]; exact le_max_right ..) le_rfl
   exact Brush.zi EventuallyEq.rfl (zero_le_one.trans he) zero_le_one
lemma opening (Zc:StableR v R)(hp:0≤u): ∃ f:ι→ Head S→ℝ, Swift v f∧∀ᶠ i in v,∀ j,p.Lodge i j (f i j):=by
   have hs := lloyd_union p _ _ (p.pitcher) (lloyd_union p _ _ (p.broadP Zc) (lloyd_union p _ _ (lloyd_union p _ _ (p.lumberT Zc hp) (p.legsP)) (p.warmly hp)))
   obtain ⟨f,h,hf⟩:= hs; exact ⟨f,h,hf.mono fun i hi j=> (by rcases j with a|a|a|a; exact hi (.inl a); exact hi (.inr (.inl a)); rcases a with a|a; exact hi (.inr (.inr (.inl (.inl a)))); exact hi (.inr (.inr (.inl (.inr a)))); exact hi (.inr (.inr (.inr a))))⟩ -- parse repair
end Score
end YM.UVExtension.Span
#print axioms YM.UVExtension.Span.Score.opening
