import YM.UVExtension.Wren.Rhapsody
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration
open Song Strata Gala Concert
namespace Notes
open Choir
variable {P:BudgetPoint} {D:κ→ RegularAddress c} {F Q':ι→κ→ Config G c→ℝ}(h:Notes v P D F)
lemma rates : Notes v P D F ↔ (∀ i j,P.Regular (D j).support (F i j)) ∧ (∃ a,Swift v a ∧ ∀ᶠ n in v,∀ k,P.supBounds (D k).site (D k).support (F n k) (a n k)) ∧ ∀ k ε,0<ε→ ∀ᶠ n in v×ˢv,P.supBounds (D k).site (D k).support (F n.1 k-F n.2 k) ε :=by
   have hp (h:∀ i j,P.Regular (D j).support (F i j)) (n:ι×ι)(k:κ) (V:onstage P D k G) : V.read (F n.1 k-F n.2 k)=V.read (F n.1 k)-V.read (F n.2 k):= VerifiedReset.left_sub ((h n.1 k).smooth _ V.live) ((h n.2 k).smooth _ V.live) V.card
   constructor
   · intro h; obtain ⟨a,ha,hF⟩:= h.invests.rain; obtain ⟨u,hu⟩:= ha.books
     exact ⟨h.available, ⟨a,ha,(hu.and hF).mono fun i hi k=> tap_bound.mpr ⟨hi.1.1 _,hi.2 _⟩⟩,fun k ε he=> ((h.invests.meters k).uv ε he).mono fun n hn=> tap_bound.mpr ⟨he.le,fun x=> by rw [hp h.available n k x]; exact hn x⟩⟩
   rintro ⟨h,⟨a,ha,hF⟩,hh⟩; obtain ⟨u,hu⟩:= ha.books; refine ⟨h,⟨a,ha,hF.mono (fun n hn j=> tap_bound.mp (hn j)|>.2)⟩,fun k=> ⟨⟨u,?_⟩,fun ε hε=>?_⟩⟩
   · exact (hF.and hu).mono fun n hp i=> ((tap_bound.mp (hp.1 k)).2 i).trans (budget_single hp.2 k)
   exact (hh k ε hε).mono fun n hn V=> hp h n k V ▸ (tap_bound.mp hn).2 V

include h
lemma rotary : Notes v P (Song.revolve D) (fun n=> choir (F n)):=by
    obtain ⟨h,⟨a,ha,hA⟩,hh⟩:= rates.mp h
    let r:= turnFee P; let t:= (Fintype.card (Seat c):ℝ)⁻¹*r; have ht:r>0:=turnFee_pos _; have hb:t>0:=mul_pos (by positivity) ht
    let e (i:Seat c× κ)(f:Config G c→ ℝ): Config G c→ℝ:= Rim c • (f ∘ i.1.view)
    have he (i:Seat c× κ)(f:Config G c→ℝ)(k:ℝ)(hp:P.Regular (D i.2).support f)(hh:P.supBounds (D i.2).site (D i.2).support f k): P.supBounds (Song.revolve D i).site (Song.revolve D i).support (e i f) (t*k):=by
       have hh:= CouplingShape.sup_scale (Rim c) (Song.transSup i.1 hp hh); rw [abs_of_nonneg (rim_nn _)] at hh; unfold t; rw [mul_assoc]; exact hh
    have hs : Swift v (fun i (_:Seat c)=> t) :=Swift.sight fun i=> ⟨t,Eventually.of_forall fun _=>⟨hb.le,le_rfl⟩⟩
    apply rates.mpr
    refine ⟨fun i k=> CouplingShape.reg_scale _ (k.1.regular (h i k.2)),⟨_,hs.mixes ha,hA.mono fun i hi k=>he _ _ _ (h i k.2) (hi _)⟩,fun i ε hε=> ?_⟩
    filter_upwards [hh i.2 (ε/t) (by positivity)] with n hn
    have hv := he i _ _ (CouplingShape.reg_sub (h _ i.2) (h _ i.2)) hn
    rw [show choir (F n.1) i-choir (F n.2) i= e i (F n.1 i.2-F n.2 i.2) from (funext fun v:Config G c=> (mul_sub (Rim c) (F n.1 i.2 (i.1.view v)) (F n.2 i.2 (i.1.view v))).symm)]; exact (show t * (ε / t)=ε by field_simp) ▸ hv

lemma draws {σ:Type} (x:σ→κ) (hp:Injective x): Notes v P (D∘x) (fun i=> F i ∘ x):=
   ⟨fun i j=> h.available i _,h.invests.many x hp (fun i (U:onstage P (D∘x) i G)=> U)⟩

lemma plucks {X: α→ RegularAddress c} {f:ι→α→ Config G c→ℝ}(he:Notes v P X f): Notes v P (Sum.elim D X) (fun i=>Sum.elim (F i) (f i)):=by
   obtain ⟨h,⟨a,hb,ht⟩,hq⟩:=rates.mp h; obtain ⟨g,⟨b,hx,hf⟩,hh⟩:= rates.mp he
   apply rates.mpr; refine ⟨fun n i=> ?_, ⟨_,hb.onion hx,(ht.and hf).mono fun i he x=>?_⟩, fun i k hK=>?_⟩
   · cases i with | inl i=> exact h n i | inr i=> exact g n i
   · cases x with | inl x=> exact he.1 x| inr x=> exact he.2 x
   cases i with| inl x=> exact hq x k hK| inr x=> exact hh x k hK

lemma swells (d:ι→ℝ){t:ℝ}(he:Tendsto d v (𝓝 t)): Notes v P D (fun i k=> d i • F i k):=by
   have hv i k (x:onstage P D k G): x.read (d i • F i k) = d i * x.read (F i k) := WilsonStartup.Start.left_mult _ _ _
   obtain ⟨C,hC,hD⟩:=h.invests.rain; let t':=1+|t|
   have ht : ∀ᶠ i in v,|d i|≤ t':= he.abs.eventually_le_const (by unfold t'; linarith)
   have hR := (rates.1 h).2.2
   refine ⟨fun i k=> CouplingShape.reg_scale _ (h.available i k),⟨_,hC.scales t' (by unfold t'; positivity),(hD.and ht).mono fun n hn i V=>?_⟩,fun x=> ?_⟩
   · rw [hv,norm_mul]; exact mul_le_mul hn.2 (hn.1 i V) (norm_nonneg _) (by unfold t'; positivity)
   exact ((Tune.constant _ _ he).mul (h.invests.meters x)).switch (Eventually.of_forall (fun i=> funext (fun v=> (hv i x v).symm)))
lemma slides (f:ι→κ→ Prop)(g:κ→Prop)(hp:∀ i,∀ᶠ n in v,f n i=g i)[∀ i,DecidablePred (f i)]: Notes v P D (fun n i=> if f n i then F n i else 0) :=by
   refine ⟨fun i j=>?_,(h.invests.varying f g hp).fade (Eventually.of_forall ?_)⟩
   · split; exact h.available i j; exact CouplingShape.reg_const _
   intro i j; funext V; split
   next hx=> rfl
   next hx=> change 0= leftDerivs (fun _ : Config G c=> (0:ℝ)) V.poll V.view; rw [Work.G07.left_const,ite_self]
end Notes
end YM.UVExtension.Wren
