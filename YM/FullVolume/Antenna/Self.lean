import YM.FullVolume.Antenna.Plane
/-! Algebra On Records. alpha gaze.Space.Second jet.Item law.Limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.ConeRay
open Lattice RG Precision Wilson Filter Function Laurent Bloch Exterior Finset
open Matrix (transpose mulVec of)
open scoped Matrix Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{n:Side}{m:ℕ→Side}{σ B:ℝ}
abbrev Section (m:ℕ→Side)(G:Gauge):=∀ i, Tensor.T (Link G (m i)) ℝ 2
variable {A X:Section m G}
lemma High.add (h:High m A)(he:High m X): High m (A+X):=by
    obtain ⟨b,hb,h₀,H⟩:= h.proceeds; obtain ⟨a,ha,h₁,L⟩:= he.proceeds; refine ⟨b+a,fun i=> add_nonneg (hb i) (ha i),(by rw [show (𝓝 (0:ℝ))=𝓝 (0+0:ℝ) by simp]; exact h₀.add h₁),fun i p q x y hw hv=>?_⟩
    simp only [Pi.add_apply,_root_.add_apply,mul_add]; exact (abs_add_le ..).trans (add_le_add (H _ _ _ x y hw hv) (L _ _ _ x y hw hv))
lemma High.sub (h:High m A)(he:High m X): High m (A-X):=by
    obtain ⟨b,hb,h₀,H⟩:= h.proceeds; obtain ⟨a,ha,h₁,L⟩:= he.proceeds; refine ⟨b+a,fun i=> add_nonneg (hb i) (ha i),(by rw [show (𝓝 (0:ℝ))=𝓝 (0+0:ℝ) by simp]; exact h₀.add h₁),fun i p q x y hw hv=>?_⟩
    simp only [Pi.add_apply,_root_.sub_apply,Pi.sub_apply,mul_add]; exact (abs_sub ..).trans (add_le_add (H _ _ _ x y hw hv) (L _ _ _ x y hw hv))
lemma High.coin (h:High m A)(s:ℝ) :High m (s • A):=by
    obtain ⟨b,hb,h₀,H⟩:=h.proceeds; refine ⟨fun i=> |s| * b i,fun i=> mul_nonneg (abs_nonneg _) (hb i),by simpa using h₀.const_mul |s|,fun i p q x y hw hv=> ?_⟩
    rw [Pi.smul_apply,_root_.smul_apply,smul_eq_mul,abs_mul,mul_left_comm]; exact mul_le_mul_of_nonneg_left (H _ _ _ x y hw hv) (abs_nonneg _)
-- Lease abstract
structure Tender (F:Words m G)(Q:Picture G 1):Prop where
    hear:∀ i,AnalyticAt ℝ (F i) 0
    wt:∃ w C,0<w ∧ ∀ i j,Firm w C (Q i j)
    jazz:∀ i, Recorded Q (F i) 0
variable {F K:Words m G}{P Q:Picture G 1}
lemma Tender.patch (h:Tender F P)(he:Tender K Q): Tender (F+K) (P+Q):=by
   obtain ⟨w,d,hx,H⟩:= h.wt; obtain ⟨w',B,hu,hΞ⟩:=he.wt; have hv:=lt_min hx hu
   refine ⟨fun i=>(h.hear i).add (he.hear i),⟨_,d+B,hv,fun i j=>?_⟩,fun i=> (h.jazz i).both (h.hear i) (he.hear i) (he.jazz i)⟩
   exact ((H i j).mono hv (min_le_left ..) le_rfl).add ((hΞ i j).mono hv (min_le_right ..) le_rfl)
lemma Tender.minus (h:Tender F P)(he:Tender K Q):Tender (F-K) (P-Q):=by
   obtain ⟨w,d,hx,H⟩:= h.wt; obtain ⟨w',B,hu,hΞ⟩:=he.wt; have hv:=lt_min hx hu
   refine ⟨fun i=>(h.hear i).sub (he.hear i),⟨_,d+B,hv,fun i j=>?_⟩,fun i=> (h.jazz i).less (h.hear i) (he.hear i) (he.jazz i)⟩
   exact ((H i j).mono hv (min_le_left ..) le_rfl).sub ((hΞ i j).mono hv (min_le_right ..) le_rfl)
lemma Tender.coin (h:Tender F P)(s:ℝ): Tender (s • F) ((s:ℂ) • P):=by
   obtain ⟨w,d,hx,H⟩:=h.wt
   refine ⟨fun i=> (show AnalyticAt ℝ (s • F i) 0 from ((h.hear i).contDiffAt.const_smul s : ContDiffAt ℝ ω (s • F i) 0).analyticAt),⟨w,_,hx,fun i j=> (Firm.const hx (s:ℂ)).mul (H i j)⟩,fun i=> (h.jazz i).weigh s (h.hear i)⟩

lemma tip_w (h:Tender F P)(x:G.ColorIndex): AnalyticAt ℝ (pressLens P ![x,x] 1 1) 0:=by obtain ⟨_,_,_,H⟩:=h.wt; exact priceL H ..
lemma Tender.curated (h:Tender F P)(s:ℝ)(x:G.ColorIndex): alphaPay x ((s:ℂ) • P)=s*alphaPay x P:=by
   unfold alphaPay leapTip
   let q := pressLens P ![x,x] 1 1
   have hv : pressLens ((s:ℂ) • P) ![x,x] 1 1=s • q := funext fun i=>rfl
   rw [hv]; unfold speedy Tensor.diagonal Tensor.coeff
   rw [iteratedFDeriv_const_smul_apply (show ContDiffAt ℝ 2 q 0 from (tip_w h x).contDiffAt)]
   unfold q; simp only [_root_.smul_apply, Complex.smul_re]; simp
lemma Tender.weave (h:Tender F P)(he:Tender K Q)(x:G.ColorIndex): alphaPay x (P+Q)=alphaPay x P+alphaPay x Q:=by
   let p := pressLens P ![x,x] 1 1; let q := pressLens Q ![x,x] 1 1
   have hv : pressLens (P+Q) ![x,x] 1 1=p+q:= funext fun _=>rfl
   unfold alphaPay leapTip; rw [hv]; unfold speedy Tensor.coeff Tensor.diagonal; rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ 2 p 0 from (tip_w h x).contDiffAt) (show ContDiffAt ℝ 2 q 0 from (tip_w he x).contDiffAt)]
   unfold p q; simp [smul_add]; ring
lemma Tender.void (h:Tender F P)(he:Tender K Q)(x:G.ColorIndex): alphaPay x (P-Q)=alphaPay x P-alphaPay x Q:=by
   rw [sub_eq_add_neg, ← neg_one_smul ℂ,← show (↑(-1:ℝ):ℂ)=-1 by simp]
   rw [Tender.weave h (Tender.coin he (-1)), he.curated]; ring
-- Cashier on all periods stamps
abbrev tick (m:ℕ→Side)(R: Words m G):Section m G:=fun i=> iteratedFDeriv ℝ 2 (R i) 0
lemma Tender.tickt (h:Tender F P)(x:ℝ): tick m (x • F)=x • tick m F:=by funext i; change iteratedFDeriv ℝ 2 (x • F i) 0=x • iteratedFDeriv ℝ 2 (F i) 0; rw [iteratedFDeriv_const_smul_apply (h.hear i|>.contDiffAt)]
lemma Tender.ticks (h:Tender F P)(he:Tender K Q): tick m (F+K)=tick m F+tick m K:=funext fun i=> iteratedFDeriv_add_apply (h.hear i|>.contDiffAt) (he.hear i|>.contDiffAt)
lemma Tender.ticked (h:Tender F P)(he:Tender K Q): tick m (F-K)=tick m F-tick m K:=funext fun i=> iteratedFDeriv_sub_apply (h.hear i|>.contDiffAt) (he.hear i|>.contDiffAt)
lemma Tender.marque (h:Tender F P)(hp:Tendsto (fun i=>(m i).val) atTop atTop)(he:High m (tick m F))(x:G.ColorIndex): tick m F=0 ∧ alphaPay x P=0:=by
    obtain ⟨w,c,_,H⟩:= h.wt; obtain ⟨hA,hB⟩:=roared he hp H h.jazz
    refine ⟨funext hB,?_⟩; unfold alphaPay leapTip; rw [show pressLens P ![x,x] 1 1=(fun _=>0) from funext fun i=> hA _ _ _]; unfold speedy Tensor.coeff Tensor.diagonal; rw [iteratedFDeriv_const_of_ne (by decide)]; simp
lemma opB (R:PathData G)(p:Clip){σ A L:ℝ}(h:R.Bounds p σ A L)(n:ℕ→Side): Tender (fun i=> turnSeries (m:=n i) R.loop) (filing R) ∧ ∀ x:G.ColorIndex,alphaPay x (filing R)=0:=by
    obtain ⟨hX,H⟩:=filing_ready R h
    have hp : Tender _ _ :=Tender.mk (F:=fun i=> turnSeries R.loop (m:=n i)) (fun i=>turns_analytic _ h.width h.two) ⟨_,_,h.width,fun i j=>(hX i j).1⟩ fun i => H _
    refine ⟨hp,fun x=>?_⟩; unfold alphaPay leapTip speedy
    let Q:=pressLens (filing R) ![x,x] 1 1
    have he:Rays 4 Q:=by intro v; unfold Q pressLens; simp only [map_smul]; exact (hX ![x,x] ![coord 1,coord 1]).2 (roads v)
    have hz:Tensor.coeff Q 2 0=0:=by unfold Tensor.coeff; rw [(rays_jet (tip_w hp x) 4).1 he 2 (by decide),smul_zero]
    change 2*(Tensor.diagonal (Tensor.coeff Q 2 0) _).re=_; rw [hz]; simp [Tensor.diagonal]
end YM.Stationary.ConeRay
