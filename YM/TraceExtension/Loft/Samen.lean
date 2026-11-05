import YM.TraceExtension.Loft.Fluent
set_option autoImplicit false
/-!
# Pole coefficient. Existence independent of regulator segment width (held
fixed during period limit). No path insertion over punctured tests implied.
-/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Audience Metric Lamp Det
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→Side}{L:Filter W}{G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n:ℕ}{σ τ A C D μ ε a r:ℝ}{V:Jar G}{S:Skuta W G}{R:W→PathData G}
structure Cred (g:W→Side)(p:Clip)(R:W→PathData G)(S:Skuta W G)(V:Jar G)(σ ε A C D:ℝ) : Prop where
   live: S.Live σ D ε C V
   grey: V.grey
   hat: V.fees σ A
   σp:0 < σ
   εp:0 < ε
   ac:0 ≤ A
   cb: 0 ≤ C
   leg: ∀ w, Ticket (S.useJar V w) (fineFlare p (R w) (m:=g w))
variable (q:G.ColorIndex)(Q:Tendsto (fun w=>(g w).val) L atTop) (h:Cred g p R S V σ ε A C D)(hF: Flare g R p a r)
include h Q hF
lemma slopeL (hG:G.Simple):∃ C':ℝ,0 ≤ C' ∧∀ μ:ℝ,0 < μ → μ ≤ 1 → ∀ᶠ w in L,
    |(ridge q p (R w) μ (g w)).re+ 12*(G.slopeConstant*Real.log μ⁻¹)|≤ C':=by
    obtain ⟨c,b,hc,hb,H⟩:=effect h.hat h.grey h.εp h.σp hG D C
    let C':= |cartWeight*costZone c b|
    have hp: 0 ≤ C':=abs_nonneg _; refine ⟨12*(C'+1),by positivity, fun μ hm hz=> ?_⟩
    let T (w):= quick μ G (S.useJar V w); let P(w:W):= marke p (R w) μ (f:=g w) ∘ input G (g w); let A w:= alphaPay q (profitable (T w)); let Y w:= yard 0 1 q (P w)
    obtain ⟨s,D',hs,hD',HT⟩:=banana h.live h.hat h.ac h.cb h.σp h.εp hm (μ:=fun _=>μ) (fun _=> ⟨le_rfl,hz⟩); choose B y x Z h' hl hu hw using hF.tanks
    have hr(w): (Det.stock p (R w) μ (1:Config G (g w))).det ≠ 0:= (hull_m (μ:=μ) hm le_rfl (h' w) (hl w) (hu w) (hw w)).1.det_pos.ne'
    have hx(w): Awards (T w) (P w):= quick_receipt (h.leg w) hm (hr w)
    have he:=payday q 0 1 Q T P hs hD' HT hx
    have ht: Rose L (fun i=>(Y i).re) A:=by
       apply Rose.chain (CohX Complex.reCLM he) (Rose.skip ?_)
       filter_upwards with w; change (neap 2 _ _ _:ℂ).re=_; rw[leapsL q 0 1 (h:=HT w) hs]; unfold A alphaPay; simp [Complex.mul_re,T]
    have hv(w): let X:=T w; |A w + G.slopeConstant*Real.log μ⁻¹| ≤ C':=by
       let Z(w):Orion V σ D ε C:=⟨_,S.μ w,q,_,_,S.light w,(h.live w).1,(h.live w).2.1,(h.live w).2.2⟩
       obtain ⟨hx,he⟩:=H (Z w) μ ⟨hm,hz⟩; intro X; exact le_trans (absoluteGeode q (F:=X) (HT w) hc hb hm hz hx he) (le_abs_self _)
    filter_upwards [ht.eventually (ball_mem_nhds 0 zero_lt_one)] with w hW; have hh: |(Y w).re-A w|≤1:=by simpa [Real.dist_eq, mem_ball] using (show _≤_ from (show dist (( (fun w=> (Y w).re)-A) w) 0<1 from hW).le)
    rw[ridge, jury q (contours_m hm (h' w) (hr w)), Complex.mul_re]
    have H1:= abs_add_le ((Y w).re-A w) (A w+G.slopeConstant*Real.log μ⁻¹); have H: |(Y w).re + G.slopeConstant*Real.log μ⁻¹|≤1+C':=by rw[← add_assoc,sub_add_cancel] at H1; exact H1.trans (add_le_add hh (hv w))
    change |(12:ℂ).re*(Y w).re-(12:ℂ).im*(Y w).im+_|≤ _; rw[show (12:ℂ).re=12 by norm_num,show (12:ℂ).im=0 by norm_num,zero_mul,sub_zero,← mul_add,abs_mul,abs_of_nonneg (by norm_num:0≤(12:ℝ))]; linarith only[H]
end YM.Trace.Loft
