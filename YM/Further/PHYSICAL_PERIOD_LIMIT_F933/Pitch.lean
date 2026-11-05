import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Tracery

/-! # Pinned gradients and projected germs

Volume accounting including logarithmic score. To deduce equality of pinned gradients
(not just sum in denominator testing), REQUIRE actual symmetry on covering systems.
Do not assume equality across branch choices; our use pays one constant tag on a
canonical system. Projection of Hessian as a compatibility observation is on
replicated backgrounds -- particularly suited even with forest and winding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Pitch
open Jacobi Macrame Macrame.Lace Polytrace   Function Lattice Gauge RG Tree Matrix Finset Precision Filter Exterior Bid Wilson Set Metric Push.Uniform
open Shingle
open scoped Topology ContDiff BigOperators Classical
variable {ι κ σ α : Type} [Fintype ι] [Fintype κ] [Fintype σ] [Fintype α]
  (i : σ→ι) (l:α→κ)

-- Cost/power estimates in REAL stored position representation
-- projection need not be surjection

def onpass (π : σ→ι) : Positions ι →L[ℝ] Positions σ := ContinuousLinearMap.pi fun a=>ContinuousLinearMap.proj (π a)
omit [Fintype σ] [Fintype ι] in
@[simp] lemma pass (p : σ→ι) (X : Positions ι) (b : σ) : onpass p X b=X (p b) := rfl
lemma pressure (p : σ→ι) (u : Positions ι) : ‖onpass p u‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro; exact norm_le_pi_norm u _

structure Shelter (F : Positions (ι⊕κ)→ℝ) (G : Positions (σ⊕α) → ℝ) (m : ℕ) : Prop where
  fold : Fold l m
  amount (x) : G (onpass (Sum.map i l) x)= (m:ℝ)*F x
  motion (x y : α) : l x=l y → ∃ a : σ→σ,∃ b:α→α, Injective b ∧ b x=y ∧ (Sum.map i l) ∘ (Sum.map a b) = Sum.map i l ∧
    ∀ X, G (onpass (Sum.map a b) X)=G X

namespace Shelter
variable {i l} {F : Positions (ι⊕κ)→ℝ} {G : Positions (σ⊕α)→ℝ} {m : ℕ} (h : Shelter i l F G m)
include h
local notation "P" => onpass (Sum.map i l)
omit [Fintype ι] [Fintype κ] in
lemma orbit (p : Positions (ι⊕κ)) (g : ContDiffAt ℝ ω G (P p)) (v w : α) (he : l v = l w) :
    blade (bolt (Sum.inr v)) G (P p) = blade (bolt (Sum.inr w)) G (P p) := by
  obtain ⟨a,b,hs,hb,hc,ht⟩ := h.motion v w he
  let S := onpass (Sum.map a b)
  have hz : S (P p)= P p := funext (fun j : σ⊕α=> congrArg p (congr_fun hc j))
  have hh : S (bolt (Sum.inr (b v))) = bolt (Sum.inr v) := by
    funext y; rcases y with y|y <;> simp [S,bolt, Pi.single_apply,hs.eq_iff]
  have hg : ContDiffAt ℝ ω G (S (P p)) := by rw [hz]; exact g
  conv_rhs => arg 2; rw [show G=G ∘ S from (funext ht).symm]
  unfold blade; rw [fderiv_comp _ (hg.differentiableAt (by simp)) S.differentiableAt,S.fderiv,ContinuousLinearMap.comp_apply,← hb,hh,hz]
lemma pinned (hm : 0<m) (p : Positions (ι⊕κ)) (g : ContDiffAt ℝ ω G (P p)) (f : ContDiffAt ℝ ω F p) (v : α) :
    blade (bolt (Sum.inr v)) G (P p)=blade (bolt (Sum.inr (l v))) F p := by
  have hv : P (bolt (Sum.inr (l v))) = ∑ j∈parcel l (l v), bolt (Sum.inr j) := by
    funext k; rw [Finset.sum_apply]
    cases k with
    | inl k => simp [bolt]
    | inr k =>
      simp only [bolt, pass,Sum.map_inr]
      by_cases he : l k=l v
      · simp [he, Pi.single_apply]
      simp [he, Pi.single_apply]
  have hr : blade (bolt (Sum.inr (l v))) (G ∘ P) p = (m:ℝ)* blade (bolt (Sum.inr v)) G (P p) := by
    unfold blade; rw [fderiv_comp _ (g.differentiableAt (by simp)) (P).differentiableAt,(P).fderiv, ContinuousLinearMap.comp_apply,hv,map_sum]
    rw [Finset.sum_congr rfl (fun i hh => show blade (bolt (Sum.inr i)) G (P p) = blade (bolt (Sum.inr v)) G (P p) from orbit h p g i v ((posted ..).mp hh)),Finset.sum_const, h.fold (l v), nsmul_eq_mul]
    -- bad
  have he : G ∘ P = fun q=>(m:ℝ)*F q := funext h.amount
  rw [he, product _ contDiffAt_const f, blade_const,mul_zero,add_zero] at hr
  exact mul_left_cancel₀ (show (m:ℝ)≠0 by exact_mod_cast hm.ne') hr.symm

lemma rollers (hm : 0<m) (p : Positions ι) (u : Positions κ) (g : ContDiffAt ℝ ω G (meetVar (onpass i p) (onpass l u))) (f : ContDiffAt ℝ ω F (meetVar p u)) (v : α) :
    Slope G (meetVar (onpass i p) (onpass l u)) v=Slope F (meetVar p u) (l v) := by
  have hh : P (meetVar p u)=meetVar (onpass i p) (onpass l u) := by funext j; cases j <;> rfl
  have he := h.pinned hm (meetVar p u) (by rw [hh]; exact g) f v; rw [hh] at he
  simpa only [Slope,entry,iteratedFDeriv_one_apply,Matrix.cons_val_zero] using he

omit h in
lemma horizontal (p) (he : ContDiffAt ℝ ω F p) : ContDiffAt ℝ ω (Slope F) p := by
  apply contDiffAt_pi.mpr; intro v; exact (tend_entry he ![Sum.inr v]).1

lemma intensity (hm : 0<m) (p : Positions ι) (u : Positions κ) (g : ContDiffAt ℝ ω G (meetVar (onpass i p) (onpass l u)))
    (f : ContDiffAt ℝ ω F (meetVar p u)) :
    Shingle.Every l (block G (meetVar (onpass i p) (onpass l u))) (block F (meetVar p u)) := by
  have hs := slope_block f; have hS := slope_block g
  let W := meetVar (τ:=α) (onpass i p)
  let e := onpass l u

  have he : Slope G ∘ W ∘ onpass l =ᶠ[𝓝 u] onpass l ∘ Slope F ∘ meetVar p := by
    have hζ : ContinuousAt (W ∘ onpass l) u := (show HasFDerivAt W _ e from meet_derivative (onpass i p) e).continuousAt.comp (onpass l).continuous.continuousAt
    have hη := (meet_derivative (τ:=κ) p u).continuousAt
    filter_upwards [hζ.tendsto.eventually (g.eventually (by simp)),hη.tendsto.eventually (f.eventually (by simp))] with y hy hx
    funext j; exact rollers h hm p y hy hx j
  have hQ : Slope G ∘ W ∘ onpass l = (Slope G ∘ W) ∘ onpass l := rfl
  have hQ' : onpass l ∘ Slope F ∘ meetVar p= onpass l ∘ (Slope F ∘ meetVar p) := rfl
  have hC : DifferentiableAt ℝ (Slope G ∘ W) e := ((hS.1).differentiableAt (by simp)).comp _ (meet_derivative (τ:=α) ..).differentiableAt
  have hc : DifferentiableAt ℝ (Slope F ∘ meetVar p) u := ((hs.1).differentiableAt (by simp)).comp _ (meet_derivative (τ:=_) _ _).differentiableAt
  have hx := Filter.EventuallyEq.fderiv_eq (𝕜:=ℝ) he
  rw [hQ,fderiv_comp _ hC (onpass l).differentiableAt,fderiv_comp _ (onpass l).differentiableAt hc,(onpass l).fderiv] at hx
  let P' := block G (W e); let Q' := block F (meetVar p u)
  have ht (x : Positions κ) : P' *ᵥ (onpass l x)=onpass l (Q' *ᵥ x) := by
    have hx := congr_arg (fun A : Positions κ →L[ℝ] Positions α=>A x) hx
    simp only [ContinuousLinearMap.comp_apply,W,hS.2,(onpass l).fderiv,hs.2] at hx
    exact hx
  unfold Every; ext j k
  specialize ht (bolt k)
  rw [Matrix.mul_apply, left l]; change (∑ a,P' j a * seam l a k)=Q' (l j) k
  have he := congr_fun ht j
  rw [pass,Matrix.mulVec, dotProduct] at he
  simp only [Matrix.mulVec,dotProduct,pass,bolt,Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ, ↓reduceIte] at he
  simpa only [seam,Matrix.of_apply,mul_ite,mul_one,mul_zero] using he
end Shelter
end YM.Further.PhysicalPeriodLimitF933.Pitch
