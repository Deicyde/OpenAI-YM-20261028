import YM.MergeProof.West.Rose
import YM.Next.RANK.Pageant


/-!
# Step forecasts for the restricted W law
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Set MeasureTheory Filter Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {V Ω : Type*}
variable {C : Family G} {i k l j m p q d D a n N : ℕ}
variable {R : Lead G C.S p}
variable {hN : k≤N} {b : ℝ} {x : Points n} {hk : i<k} {h : middle C.path.levels b k ≤ i}
variable {c : Course C N p k} {τ ε : ℝ}
variable {U T} (E : Mural (d:=d) c R x b hk h q T τ U ε)

lemma combFt {Q : poly (Chamber G C.S (i+1) p)} {z₁ z₂ B L w δ C₀ Y : ℝ} (X : roomTest C.path.levels b k p d q)
    (hr : Metal b c R hk ε τ z₁ B Y L) (H : Healthy z₁ (d_olm x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U)
    (hv : 0<ε) (hq : Q.vars⊆ sp_okes x b hk d T.2.val (C:=C)) (hu : totalDegree Q ≤ D)
    (he : coin Q ≤ w) (f : E.Θ →ℂ) (u : E.Θ→ℝ) (hh :
      letI := E.M
      Guarded u z₂ E.μ ∧ Measurable f) (hy : 0 ≤ C₀) (hf : ∀ z, 0<u z → ‖f z‖≤ C₀) (hi : 0 ≤ δ) (hΔ : ∀ V, 0 < u V → ‖f V - r_ose E Q V‖ ≤ δ) :
    letI:= E.M
    Integrable (fun z=> (↑(u z):ℂ)*f z) E.μ ∧ ‖(∫ z, (↑(u z):ℂ)*f z ∂ E.μ) - e_legance b c x hk h T U ((R i).read Q)‖ ≤
      δ + ε*(w^2 * Common.priced B (2*D)) + z₂/ε + w*(ε*Common.priced B D):= by
  letI:=E.M; letI:IsProbabilityMeasure E.μ:= E.initial.norm
  let g:= r_ose E Q; obtain ⟨hh,hm⟩:= hh
  have hg:Integrable g E.μ:= carries_int E.initial _ _
  obtain ⟨h1,h₂⟩:= release u f g hh hg hm ⟨_,hy,hf⟩ hi hΔ
  let X':= Q.vars; let m:= colorFt R c b x hk h T.1 T.2.val U
  have hm' : m=fun i=>(↑(d_means E i):ℂ) := funext (fun i=>hr.path _ i)
  have hP j (he':j∈X'): ‖m j‖≤ B:= predFt T X h hr U H j (hq he')
  let Z:=R i; have hy: L≤ B:=by linarith only [hv,hr.wake]
  have hs a (ha : a∈ X') v (he : v ∈ X') : ‖E.P.cov a v‖≤ B:= by
    have ht := E.reach a (hq ha) v (hq he); have hv:= (hr.φ.tide a v).trans hy
    exact le_trans ((le_trans (le_of_eq (congr_arg norm (sub_add_cancel ..).symm)) (norm_add_le ..)).trans (add_le_add ht (hr.φ.tide ..))) (by linarith only [hr.wake])
  obtain ⟨h3,h4⟩:=squareFits (d_means E) Q E.initial hu hr.grain (fun j he=> (Complex.abs_re_le_norm _).trans (hP j he)) hs
  have hp : 0≤ coin Q:= Rise.sign _ _ zero_le_one
  have hR: ε * (w^2 * Common.priced B (2*D)) + z₂/ε ≥ ‖(∫ z, (↑(u z):ℂ)*g z ∂ E.μ) -∫ z,g z ∂ E.μ‖ := escaped hh hv hg h3
    (h4.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp he 2) (zero_le_one.trans (priced_up _ hr.grain))))
  let F:= blend Z.Q m Q
  have hZ : F=e_legance b c x hk h T U ((R i).read Q):=by unfold e_legance text Valve.read; rw [pipes,reads_val, ← blend_components]; rfl
  have hC: ‖(∫ z, g z ∂ E.μ)- F‖ ≤ w*(ε*Common.priced B D):= by
    dsimp only [g,r_ose]; rw [payment _ E.initial,← hm']
    exact (differently Q.vars Q le_rfl hr.grain hu hP hs (fun i _ j _=> (hr.φ.tide i j).trans hy) hv.le (fun i H j hJ=> E.reach _ (hq H) _ (hq hJ))).trans
      (mul_le_mul_of_nonneg_right he (mul_nonneg hv.le (zero_le_one.trans (priced_up _ hr.grain))))
  refine ⟨h1,?_⟩; rw [← hZ]; apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (le_trans (add_le_add ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h₂ hR)) hC) ?_); exact le_of_eq (by ring)

variable (E : StageNow (d:=d) c R x b hk h q T τ U ε)

open Finset
lemma r_eparation (X : (j:Fin E.count) → (E.tag j).Θ → ℂ) (z : Prop) (a : ℂ) (p : ℝ)
    (h : ∀ j, letI:=(E.tag j).M; ‖(∫ u,X j u ∂(E.tag j).μ) - a‖ ≤ p) : ‖plaidFt E (fun j u=>dot z (X j u))-dot z a‖ ≤ p:= by
  let R (j:Fin E.count) :=
    letI := (E.tag j).M
    ∫ u,X j u ∂(E.tag j).μ
  have he : plaidFt E (fun j u=>dot z (X j u))-dot z a= ∑ j : Fin E.count,(E.weight j:ℂ)*(dot z (R j)-dot z a):= by
    unfold plaidFt mixedFt; simp only [mul_sub,Finset.sum_sub_distrib,extras]
    rw [← Finset.sum_mul,← Complex.ofReal_sum,E.total,Complex.ofReal_one,one_mul]
  rw [he]; apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ j : Fin E.count, E.weight j*p:= sum_le_sum fun j _=> by rw [norm_mul, dot_equal, Complex.norm_real,Real.norm_of_nonneg (E.pos j)]; exact mul_le_mul_of_nonneg_left (h j) (E.pos j)
    _ = _ := by rw [← sum_mul,E.total,one_mul]

section
variable (P : Manner n → poly (Chamber G C.S (i+1) p))

def inviteFt (T : Bale C k b p d x (show i≤k from hk.le)) (c : Course C N p k) (h : middle C.path.levels b k ≤ i) (j : PatchPt x b C.path.levels p d (show i+1≤k from hk)) :=
    gloryFt x b p c.allow hk (h.trans (Nat.le_succ _)) T.1 j.val (anneals C c (i+1)) (P j.val)

lemma e_ngages i' (u : PatchPt x b C.path.levels p d (show i+1≤k from hk)) (z) :
    p_lanted E (inviteFt (hk:=hk) P T c h) i' u z= dot ((Ship.yard C b c.allow p).hand T.1) ((↑((E.tag i').Γ u z):ℂ)*traceFt (E.tag i') u (P u.val) z):= by rw [dot_move]; rfl

end
lemma plaidF_add (s t : (j:Fin E.count) → (E.tag j).Θ →ℂ) (h : ∀ j,letI:=(E.tag j).M; Integrable (s j) (E.tag j).μ) (H : ∀ j,letI:=(E.tag j).M; Integrable (t j) (E.tag j).μ) :
    plaidFt E (fun j z=> s j z+t j z)=plaidFt E s+plaidFt E t:= by
  unfold plaidFt mixedFt; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _=> ?_; letI:=(E.tag j).M; dsimp only; rw [integral_add (h j) (H j)]; exact mul_add ..
end YM.Next.Rank.Tapes.West
