import YM.RG12.Spins.Noise
/-! Paired concert estimate. S demands for V9 ratio must be purchased at a NONthreshold price
 on the scaled directions D (through order 2 only needs proportionality to a^k at k).
 A `Band` whose `caps` costs just ONE threshold power at k>0 is insufficient for the new goal.
 Stochastic fcurv(p(t,σ)) symmetrized difference charged with a^k too (movement of W),
 and normalize out a^-2 just before plugging in here. Use odd+even pricing ONLY on the same
 tag/twilight integral.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Noise
open Function Filter Set Lattice Wilson RG Push.SectorMeasure
open Multi Multi.Vacuum.Jets Multi.Puff WardBin.Lies ProofPorts.CommonComplexProduction.Score
open Pressure PhysicalNext.JointLoad.Heir Next Next.SectorChange AnalyticBridge.LocalGaussian
open Finset MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{C:Gaussian.Table (I × G.ColorIndex)}{K B u t A T a w D d η s P:ℝ}{c:Side}
local notation "μ" C => Gaussian.cloud C
section sigma
-- compatibility for ratio under reflection
variable {J : Config G c→ Gaussian.Table (I×G.ColorIndex)} (χ:Chi)
set_option quotPrecheck false
local notation "alt"=>Carillon.vary (1:Config G c) J
lemma even_vary (z:(Prices G I)): alt (-z)=alt z :=by
    funext p; simp only [Carillon.vary,Density.replace,Density.spice,add_zero]; congr! 4 -- inspect
    all_goals simp [Gaussian.force, Matrix.mulVec_neg,dotProduct_neg,neg_dotProduct]
variable {W : Directions G c→Prop}
variable (f:(Prices G I) → Config G c→ℂ)(σ:Config G c→ℂ)
protected def half (F K:Config G c →ℂ) := (1/2:ℂ) • (F + K)
protected def voll (t:(Prices G I) → Config G c→ℂ) (Γ:(Prices G I)→ℂ)(F:(Prices G I) → Config G c→ℂ) (z:(Prices G I)) : Config G c→ℂ := Γ z • (t z * F z)
private lemma agree_half (F F' : Config G c→ℂ)(l:List (Directions G c))(n:ℕ)(hF:Crest n F 1)(hh:Crest n F' 1)(hl:l.length≤n):leftDerivs (Noise.half F F') l 1 = (leftDerivs F l 1 + leftDerivs F' l 1)/2:=by
  rw [Noise.half,scaled_left,Crest.sum_at l hl _ hF hh]; ring
private lemma plateau {a b: Config G c→ℂ} {n:ℕ} (l k: Directions G c)(h:Crest (n+2) a 1)(he:Crest (n+2) b 1)(hs:a 1=1)(hp:b 1=0)(hg:leftDerivs b [k] 1=0 ∧ leftDerivs b [l] 1=0): leftDerivs (a*b) [k,l] 1 =leftDerivs b [k,l] 1 := by
   have H : leftDerivs (a*b) [l] =ᶠ[𝓝 1] (leftDerivs a [l]*b+a* leftDerivs b [l]) :=by
      filter_upwards [h.near,he.near] with V hv he; exact multiplication l hv he
   rw [show [k,l]=[k]++[l] from rfl, YM.Work.G07.left_append,agrees H]
   rw [Crest.sum_at [k] (show [k].length ≤ n+1 by simp) _ (crest_product (h.falls l) (shorten he)) (crest_product (shorten h) (he.falls l)), multiplication k (h.falls ..) (shorten he),multiplication k (shorten h) (he.falls ..),← YM.Work.G07.left_append]
   simp [hp,hg,hs]
   rw [← YM.Work.G07.left_append]; rfl
variable {θ Γ: (Prices G I) → ℝ}{r: (Prices G I) → Config G c →ℂ}{V:ℝ}
-- f0 and f, all statements for derivatives on direction W that already contains thermal
-- charge T. t>0 is quota threshold. Need only cost at z on guard. σ is deterministic display at zero. scalar normalization f'/B.threshold² already inside f (hence same in σ).
omit [DecidableEq I] in
theorem circulationT (z:(Prices G I))(M N:ℝ)(m n:ℕ) (a b:Directions G c)(hs:W a)(hs':W b)(hf:Crest 2 σ 1)(hh:σ 1=0)(he1l:∀ j:Directions G c,W j → leftDerivs σ [j] 1=0)
   (hr:r (-z)=r z)(hΓ:Γ (-z)=Γ z)(hz:‖Γ z‖≤1)
   (hR:Γ z ≠0 → Band 2 W 1 (t*M*(powers z^n)) 1 (r z) ∧ r z 1=1)(hg : Γ z≠0 → Crest 2 (f z) 1 ∧ Crest 2 (f (-z)) 1)
   (hF:Γ z ≠0 → Band 2 W 1 (t*N) (u^2*(powers z^m)/t^2) ((Noise.half (f z) (f (-z))) - σ)) (ht:0<t)(hM:0≤M)(hN:0≤N):
     let G:=Noise.voll r (fun y=>(Γ y:ℂ)) f
     ‖(leftDerivs (G z) [a,b] 1+leftDerivs (G (-z)) [a,b] 1)/2-leftDerivs σ [a,b] 1‖ ≤
          ‖Γ z-1‖*‖leftDerivs σ [a,b] 1‖ + (M+N)^2*u^2*(powers z^(m+2*n)) := by
   intro v
   let C:=r z; let Y:=Noise.half (f z) (f (-z)); let g:ℂ:= Γ z
   change ‖(leftDerivs (g • (C*f z)) _ _ + leftDerivs ((Γ (-z):ℂ) • (r (-z)*f (-z))) _ _)/_ - _‖ ≤ _
   rw [hΓ,hr,scaled_left,scaled_left]
   let k(F:Config _ _→ℂ):=leftDerivs F [a,b] 1
   have hv : 0≤ (M+N)^2*u^2*powers z^(m+2*n):=by positivity [powers_pos z]
   by_cases he:Γ z=0
   · dsimp [g]; rw [he]; simp; exact hv
   obtain ⟨hP,h1⟩:=hR he; obtain ⟨hf',hf''⟩:=hg he
   have h': (k (C*f z) + k (C*f (-z)))/2 = k (C*Y) :=by
     rw [show C*Y=Noise.half (C*f z) (C*f (-z)) from ?_]; swap; · ext1 i; change _ * ((1/2:ℂ)* (_+_))= (1/2:ℂ)*(_*_+_*_); ring
     exact (agree_half _ _ [a,b] 2 (crest_product hP.readable hf') (crest_product hP.readable hf'') (show [a,b].length ≤ 2 by simp)).symm -- method?
   let G:= Y-σ
   have hQ:=hP.multiply (hF he)
   have h2 : k (C*Y)= k σ+k (C*G):=by
      have hi:k (C*σ)=k σ:= plateau (n:=0) b a hP.readable hf h1 hh ⟨he1l _ hs,he1l _ hs'⟩
      rw [show C*Y=C*σ+C*G from by unfold G; rw [mul_sub,add_sub_cancel]]
      exact (Crest.sum_at [a,b] (show [a,b].length ≤ 2 by simp) 1 (crest_product hP.readable hf) hQ.readable).trans (congr_arg (· + k (C*G)) hi)
   let P := (powers z^n)
   have hP':1 ≤ P:= one_le_pow₀ (grows z)
   have hZ0:= powers_pos z
   have ht' : ‖k (C*G)‖ ≤ (M+N)^2*u^2*powers z^(m+2*n):=by
     apply (hQ.caps [a,b] (by simp) ?_).trans
     · change 1*_*(_+_)^2 ≤ _; rw [one_mul,pow_add,pow_mul']; change _*(_*P+_)^2 ≤ _*_*(_*P^2)
       calc
        _ ≤ u^2*powers z^m/t^2*((M+N)*t*P)^2:=by gcongr; nlinarith only [show t*N ≤ t*N*P from le_mul_of_one_le_right (mul_nonneg ht.le hN) hP']
        _ = _ := by field_simp
     simp [hs,hs']
   have hg:‖g‖ ≤1:= (Complex.norm_real _).trans_le hz
   change ‖(g*k _ + g*k _)/2 - k σ‖ ≤ ‖Γ z-1‖*‖k σ‖+_
   rw [show (g*k (C*f z)+_)/2=g*((k (C*f z)+k (C*f (-z)))/2) from by ring, h',h2,show g*(k σ+k (C*G))-k σ=(g-1)*k σ+g*k (C*G) from by ring]; apply (norm_add_le ..).trans
   rw [norm_mul,norm_mul,show g-1=((Γ z-1:ℝ):ℂ) from by simp [g],Complex.norm_real]; exact add_le_add (by rfl) ((mul_le_mul hg ht' (norm_nonneg _) zero_le_one).trans_eq (one_mul ..))
end sigma
#print axioms circulationT
end YM.RG12.Noise
