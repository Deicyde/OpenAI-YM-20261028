import YM.Next.RANK.Cabal

/-!
# Step forecasts for the restricted W law
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k} {τ ε : ℝ}
variable {U T} (E : Emulator (d:=d) c R x b hk h q T τ U ε)

private lemma comb_τ {Q : poly (Chamber G C.S (i+1) p)} {z₁ z₂ B L w δ C₀ Y : ℝ} (X : roomTest C.path.levels b k p d q)
    (hr : Metal b c R hk ε τ z₁ B Y L) (H : Healthy z₁ (dolmens x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U)
    (hv : 0<ε) (hq : Q.vars⊆ spokes x b hk d T.2.val (C:=C)) (hu : totalDegree Q ≤ D)
    (he : coin Q ≤ w) (f : E.Θ →ℂ) (u : E.Θ→ℝ) (hh :
      letI := E.M
      Guarded u z₂ E.μ ∧ Measurable f) (hy : 0 ≤ C₀) (hf : ∀ z, 0<u z → ‖f z‖≤ C₀) (hi : 0 ≤ δ) (hΔ : ∀ V, 0 < u V → ‖f V - rose E Q V‖ ≤ δ) :
    letI:= E.M
    Integrable (fun z=> (↑(u z):ℂ)*f z) E.μ ∧ ‖(∫ z, (↑(u z):ℂ)*f z ∂ E.μ) - elegance b c x hk h T U ((R i).read Q)‖ ≤
      δ + ε*(w^2 * Common.priced B (2*D)) + z₂/ε + w*(ε*Common.priced B D):= by
  letI:=E.M; letI:IsProbabilityMeasure E.μ:= E.initial.norm
  let g:= rose E Q; obtain ⟨hh,hm⟩:= hh
  have hg:Integrable g E.μ:= carries_int E.initial _ _
  obtain ⟨h1,h₂⟩:= release u f g hh hg hm ⟨_,hy,hf⟩ hi hΔ
  let X':= Q.vars; let m:= colorMean R c b x hk h T.1 T.2.val U
  have hm' : m=fun i=>(↑(means E i):ℂ) := funext (fun i=>hr.path _ i)
  have hP j (he':j∈X'): ‖m j‖≤ B:= predicts T X h hr U H j (hq he')
  let Z:=R i; have hy: L≤ B:=by linarith only [hv,hr.wake]
  have hs a (ha : a∈ X') v (he : v ∈ X') : ‖E.P.cov a v‖≤ B:= by
    have ht := E.reach a (hq ha) v (hq he); have hv:= (hr.φ.tide a v).trans hy
    exact le_trans ((le_trans (le_of_eq (congr_arg norm (sub_add_cancel ..).symm)) (norm_add_le ..)).trans (add_le_add ht (hr.φ.tide ..))) (by linarith only [hr.wake])
  obtain ⟨h3,h4⟩:=squareFits (means E) Q E.initial hu hr.grain (fun j he=> (Complex.abs_re_le_norm _).trans (hP j he)) hs
  have hp : 0≤ coin Q:= Rise.sign _ _ zero_le_one
  have hR: ε * (w^2 * Common.priced B (2*D)) + z₂/ε ≥ ‖(∫ z, (↑(u z):ℂ)*g z ∂ E.μ) -∫ z,g z ∂ E.μ‖ := escaped hh hv hg h3
    (h4.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp he 2) (zero_le_one.trans (priced_up _ hr.grain))))
  let F:= blend Z.Q m Q
  have hZ : F=elegance b c x hk h T U ((R i).read Q):=by unfold elegance text Valve.read; rw [pipes,reads_val, ← blend_components]; rfl
  have hC: ‖(∫ z, g z ∂ E.μ)- F‖ ≤ w*(ε*Common.priced B D):= by
    dsimp only [g,rose]; rw [payment _ E.initial,← hm']
    exact (differently Q.vars Q le_rfl hr.grain hu hP hs (fun i _ j _=> (hr.φ.tide i j).trans hy) hv.le (fun i H j hJ=> E.reach _ (hq H) _ (hq hJ))).trans
      (mul_le_mul_of_nonneg_right he (mul_nonneg hv.le (zero_le_one.trans (priced_up _ hr.grain))))
  refine ⟨h1,?_⟩; rw [← hZ]; apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (le_trans (add_le_add ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h₂ hR)) hC) ?_); exact le_of_eq (by ring)

def grant₁ (B ε w : ℝ) (D : ℕ) := defect B ε w D + ε*(w^2*Common.priced B (2*D)) + ε+ w*(ε*Common.priced B D)
def grant₂ (B ε w : ℝ) (D : ℕ) := 2*capZ B D w*defect B ε w D + ε*((w^2)^2*Common.priced B (2*(2*D))) + 2*ε+w^2*(ε*Common.priced B (2*D))

section
variable {P : poly (Chamber G C.S (i+1) p)} {B w L Y φ}
variable (u : Index x b C.path.levels p d (show i+1≤k from hk))
variable (X : roomTest C.path.levels b k p d q) (hr : Metal b c R hk ε τ φ B Y L) (H : Healthy φ (dolmens x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U)
variable (hv : 0<ε) (hL : ε≤1) (hu : tests (C:=C) x b hk T.2.val u) (hQ : totalDegree P ≤ D) (hP : Poetic P) (hw : coin P ≤ w)
variable (hp : ∀ t∈ P.vars, spotP b (i+1) d (show i+1≤k from hk) x u.val t (C:=C))
include X hr H hv hL hu hQ hP hw hp

-- unscaled forecast. applies only on the common mask from the step
lemma worn_single :
    letI:= E.M
    let f:= fun z=> (↑(chance E u z):ℂ)* traceU E u P z
    Integrable f E.μ ∧ ‖(∫ z, f z ∂ E.μ)-elegance b c x hk h T U ((R i).read P)‖ ≤ grant₁ B ε w D := by
  have hh : P.vars⊆spokes x b hk d T.2.val (C:=C):= fun i hi=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,u, hu,hp i hi⟩
  have he := talent E u P X hr hv hL hu hP hp hQ hw
  have hc:= mul_nonneg ((Rise.sign _ _ zero_le_one).trans hw) (zero_le_one.trans (priced_up D hr.grain))
  have h': 0 ≤ defect B ε w D:= by unfold defect; have := zero_le_one.trans hr.grain; have := (Rise.sign _ _ zero_le_one).trans hw; positivity
  letI:= E.M; obtain ⟨hs,hX⟩:= comb_τ E X hr H hv hh hQ hw (traceU E u P) (chance E u) ⟨E.lives u hu,prime_cont ..⟩
      hc (fun i hi=> (he i hi).1) h' (fun i hi=>(he i hi).2.1)
  have ht : ε^2/ε=ε:= by field_simp
  exact ⟨hs,(by rw [ht] at hX; exact hX)⟩

lemma worn_pair (j : Index x b C.path.levels p d (show i+1≤k from hk)) (hJ : tests (C:=C) x b hk T.2.val j)
    (Y' : poly (Chamber G C.S (i+1) p)) (hy : totalDegree Y' ≤ D) (hF : Poetic Y') (hb : coin Y' ≤ w)
    (he' : ∀ t∈ Y'.vars, spotP b (i+1) d hk x j.val t (C:=C)) :
    letI:= E.M
    let f:= fun z=> ((↑(chance E u z):ℂ)* traceU E u P z)*((↑(chance E j z):ℂ)* traceU E j Y' z)
    Integrable f E.μ ∧ ‖(∫ z, f z ∂ E.μ)-elegance b c x hk h T U ((R i).read (P*Y'))‖ ≤ grant₂ B ε w D:= by
  letI:= E.M; haveI:=E.initial.norm
  let L':= P*Y'; let M:=fun x=> E.Γ u x*E.Γ j x
  let a:=traceU E u P; let f:=traceU E j Y'
  have ht:L'.vars ⊆ spokes x b hk d T.2.val (C:=C):= Finset.Subset.trans (MvPolynomial.vars_mul ..) (Finset.union_subset
    (fun i hi=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,hp i hi⟩) (fun i hi=> Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hJ,he' i hi⟩))
  have hc: L'.totalDegree≤ 2*D:= (totalDegree_mul ..).trans (le_trans (add_le_add hQ hy) (by omega))
  let k:= capZ B D w; let d1:= defect B ε w D; have hV:0≤w:= (Rise.sign _ _ zero_le_one).trans hw
  have hX:= talent E u P X hr hv hL hu hP hp hQ hw; have hY:= talent E j Y' X hr hv hL hJ hF he' hy hb
  have h₂:= E.lives u hu; have h₃:= E.lives j hJ
  have hz:0 ≤ k:= mul_nonneg hV (zero_le_one.trans (priced_up _ hr.grain)); have hd:0 ≤ d1:= by unfold d1 defect; have := hr.grain; positivity
  have hh z(hm:0<M z): ‖a z*f z‖≤ k*k ∧ ‖a z*f z-rose E L' z‖≤ k*d1+d1*k:= by
    have ht:0 < chance E u z:= pos_of_mul_pos_left hm (h₃.lower _); have hv:0 < chance E j z:= pos_of_mul_pos_right hm (h₂.lower _)
    obtain ⟨hu,he,h1⟩:= hX z ht; obtain ⟨hy,hp',hf⟩:=hY z hv
    rw [norm_mul,show rose E L' z= rose E P z * rose E Y' z from map_mul ..]; exact ⟨mul_le_mul hu hy (norm_nonneg (f z)) hz, indiv he hp' hu hf⟩
  have hb' : coin L'≤ w^2:= (Rise.funds 0 zero_le_one ..).trans ((mul_le_mul hw hb (Rise.sign _ _ zero_le_one) hV).trans_eq (pow_two ..).symm)
  obtain ⟨H₁,H₂⟩:= comb_τ E X hr H hv ht hc hb' (a*f) M ⟨guards_mul h₂ h₃,(prime_cont E u P).mul (prime_cont E j Y')⟩ (mul_nonneg hz hz) (fun i hi=> (hh i hi).1)
    (add_nonneg (mul_nonneg hz hd) (mul_nonneg hd hz)) (fun i hi=> (hh i hi).2)
  -- goal f integrable defeq needs product reshuffle
  rw [show (fun z=> ((↑(chance E u z):ℂ)* a z)*((↑(chance E j z):ℂ)* f z))=(fun z=>(↑(M z):ℂ)*(a*f) z) from funext fun i=> by simp only [M,chance,Complex.ofReal_mul, Pi.mul_apply]; ring]
  refine ⟨H₁,H₂.trans (le_of_eq ?_)⟩; unfold grant₂ capZ defect k capZ d1 defect
  field_simp; ring
end
end YM.Next.Rank.Tapes
