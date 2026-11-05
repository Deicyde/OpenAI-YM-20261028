import YM.AnalyticNext.CUBIC_MATCH.Region.Expressions

set_option warningAsError false

/-!
# Spatial sums and moving-by-the-budget

Widths here measured in the COARSE cover. Translation pays the true move
of EACH input; no distance on an individual torus is used. A `TotalRep`
doesn't separately budget *absolute* outputs on the torus independent of
inputs/volume: crucial unnormalized uncut translation sum on the `Site`; no site-dependent tensor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side} {k : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι μ : Type*} {c : μ → Side} {θ B C : ℝ}

def relocate (y : Cover) : TapSet G k ≃ TapSet G k := Equiv.arrowCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.addRight y) (Equiv.refl _))
lemma relocate_applies (x : TapSet G k) (b : Cover) (i : Fin k) : (relocate b x) i=((x i).1+b,(x i).2) := rfl
lemma relocate_cost (x : TapSet G k) (b : Cover) : reachOf (relocate b x) ≤ reachOf x+k*size b := by
  unfold reachOf; simp only [relocate_applies]; exact (Finset.sum_le_sum (fun i _ => size_add _ b)).trans_eq (by simp [Finset.sum_add_distrib])
lemma relocate_price (x : TapSet G k) (b : Cover) (he : 0<θ) : wanes θ (reachOf x) ≤
    Real.exp (θ*k*size b)*wanes θ (reachOf (relocate b x)) := by
  unfold wanes; rw [← Real.exp_add]; apply Real.exp_monotone
  have h := relocate_cost x b
  have hh : θ*(reachOf (relocate b x):ℝ)≤θ*(reachOf x+(k:ℝ)*size b) := mul_le_mul_of_nonneg_left (by exact_mod_cast h) he.le
  linarith
lemma verse_move (x : TapSet G k) (b : Cover) (y : Site n) (a : Fin k → Dir G n) :
    verse (wrap n b + y) x a=verse y (relocate b x) a := by simp [verse,toneOf,relocate_applies,add_assoc]

lemma LocalRep.translateSite {f : SiteRead G c E} (h : LocalRep c k θ C f) (x : Cover) :
    LocalRep c k θ (Real.exp (θ*k*size x)*C) (fun p y a => f p (wrap (c p) x+y) a) := by
  obtain ⟨he,hC,A,hA,e⟩ := h; let s := relocate (G:=G) (k:=k) x
  let R := A ∘ s.symm
  have hp : 0≤Real.exp (θ*k*size x) := (Real.exp_pos _).le
  refine ⟨he,mul_nonneg hp hC,R,fun i => ?_,fun p y a => ?_⟩
  · obtain ⟨i,rfl⟩ := s.surjective i
    simp only [R, Function.comp_apply,s.symm_apply_apply]
    exact (hA i).trans ((mul_le_mul_of_nonneg_left (relocate_price i x he) hC).trans_eq (by unfold s; ring))
  dsimp only; rw [e]; unfold receive
  let f i := verse y i (fun _ => a) • R i
  refine Eq.trans ?_ (s.tsum_eq f)
  exact tsum_congr fun i => by
    unfold f; rw [verse_move]; simp only [s,R, Function.comp_apply, Equiv.symm_apply_apply]

lemma LocalRep.allFin [CompleteSpace E] [Fintype ι] {F : ι → SiteRead G c E} (he : 0<θ) (h : ∀ i,LocalRep c k θ C (F i)) :
    LocalRep c k θ ((Fintype.card ι:ℝ)*C) (fun p x a => ∑ i,F i p x a) := by simpa using LocalRep.fin Finset.univ he (fun i _ => h i)
lemma LocalRep.weighed [CompleteSpace E] [Fintype ι] {F : ι → SiteRead G c E} {w : ι → ℝ} (he : 0<θ) (h : ∀ i,LocalRep c k θ C (F i))
    (hw : ∀ i,0≤ w i) (hv : ∑ i,w i=1) : LocalRep c k θ C (fun p x a => ∑ i,w i • F i p x a) := by
  have ht := LocalRep.fin Finset.univ he (fun i _ => (h i).scaled (w i))
  simpa only [← Finset.sum_mul,abs_of_nonneg (hw _),hv,one_mul] using ht
lemma LocalRep.equalWeights [CompleteSpace E] [Fintype ι] [Nonempty ι] {F : ι → SiteRead G c E} (h : ∀ i,LocalRep c k θ C (F i)) :
    LocalRep c k θ C (fun p x a => (Fintype.card ι:ℝ)⁻¹ • ∑ i,F i p x a) := by
  have he := (h (Classical.arbitrary ι)).rate
  simp_rw [Finset.smul_sum]; apply LocalRep.weighed he h fun i => by positivity
  simp

/-- Translation-summed local compatible coefficient. -/
def TotalRep (c : μ → Side) (k : ℕ) (θ C : ℝ) (f : ∀ i,Dir G (c i) → E) :=
    ∃ g : SiteRead G c E, LocalRep c k θ C g ∧ ∀ i a, f i a=∑ y,g i y a
namespace TotalRep
variable {f g : ∀ i,Dir G (c i) → E}



variable [CompleteSpace E]



end TotalRep
end YM.CubicMatch
