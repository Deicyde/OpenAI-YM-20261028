import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.LocalLedger
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Rainy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Peg
import YM.Planned.STATIONARY_JET_PORT.AtHome
/-!
# Uniform fixed-order finite-parameter perturbation germs. Prepares
 arc estimates on transition of nonanalytic parameter. Need NO space-uniform value
 bound at another β for x derivatives when warping the base integrand. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented  Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums   
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {j : ℕ}
open Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E→ℝ} {k l v : ℕ} {x : E} {θ b C r s w p : ℝ}

abbrev confirm (k:ℕ) (a:ℝ) (U : E→ℝ) := Brush k a 1 U
abbrev up (f : E→ℝ) x:= Real.exp (f x)-1

lemma pranced (n : ℕ) {M C : ℝ} (h : 0 ≤ M) (hc : 0 ≤ C) : ∃ p : ℝ, 0 ≤ p ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (f:E→ℝ) (c:ℝ), confirm n c (up f) x → |f x| ≤ M → c ≤ C → confirm n (p*c) f x := by
  let a:= Real.exp (-M)-1; let b:= Real.exp M-1; let e (x:ℝ):= Real.log (1+x)
  have ha : a ≤ 0 := sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr h))
  have hb : 0 ≤ b := sub_nonneg.mpr (Real.one_le_exp h)
  let n':=max 1 n
  obtain ⟨D,hD,H⟩:= Brush.compact (f:=e) (s:=Set.Icc a b) (k:=n') isCompact_Icc (fun x hx=> by
    have ht:0<1+x:=by linarith [hx.1,show -1 < a from (by unfold a; linarith [Real.exp_pos (-M)])]
    exact (contDiffAt_const.add contDiffAt_id).log ht.ne')
  have he i (hi:i∈Set.Icc a b) : |e i|≤ D*‖i‖:= by
    have ht:= (convex_Icc a b).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=e) (fun i hi=> (((H i hi).smaller (show 1≤n' from le_max_left ..)).smooth.differentiableAt (by norm_num))) (C:=D) (fun i hi=> by rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 (H i hi)).2 1 (le_max_left ..)) (show 0 ∈ Set.Icc a b from ⟨ha,hb⟩) hi
    rw [show e 0=0 by simp [e],sub_zero, sub_zero] at ht; exact ht
  let p:= (D+n.factorial*D); let q:= clump n C D; have hq:0 ≤ q:= by unfold q clump; positivity
  refine ⟨p+q,add_nonneg (by unfold p; positivity) hq,?_⟩; intro E _ _ x f c hv hM hC
  let Z:= up f; have hm : Z x∈ Set.Icc a b:= ⟨sub_le_sub_right (Real.exp_monotone (abs_le.mp hM).1) _,sub_le_sub_right (Real.exp_monotone (abs_le.mp hM).2) _⟩
  have hS:= (H _ hm).smaller (show n≤n' from le_max_right ..)
  have hf : f=e ∘ Z:=funext fun x=> by simp [Z,e, up]
  have hh := hv.nonneg; rcases le_total c 1 with hi|hi
  · apply (Brush.even hv hS hi hD.le ((he _ hm).trans (mul_le_mul_of_nonneg_left hv.bound hD.le))).shimmy (EventuallyEq.of_eq hf)|>.climb _ le_rfl; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hq) hh
  exact ((composite (hv.climb hC le_rfl) hS).shimmy (EventuallyEq.of_eq hf)).climb ((le_mul_of_one_le_right hq hi).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by unfold p; positivity)) hh)) le_rfl

lemma confound (n : ℕ) {p q : ℝ} (h:0≤p) (he:0≤q) : ∃ s : ℝ, 0 ≤ s ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (f g:E→ℝ) (c d:ℝ), confirm n c (up f) x → confirm n d (g-f) x → c≤p → d≤q → confirm n (d*s) (up g - up f) x := by
  obtain ⟨D,hD,H⟩:= Brush.compact (k:=n) (s:=Set.Icc (-q) q) (f:=fun x:ℝ=>Real.exp x-1) isCompact_Icc (fun x _=> by fun_prop)
  obtain ⟨C,hC,h₁⟩:= Brush.expands n
  let R:= C+clump n q D; have hR:0≤R:= add_nonneg hC (by unfold clump; positivity)
  refine ⟨(p+1)*R*3^n, by positivity,?_⟩; intro E _ _ x f g c d hf hv hp ht; let g':= up (g-f)
  have he := hf.nonneg
  have hg:Brush n (d*R) 1 g' x:= by
    have hr:=hv.nonneg; rcases le_total d 1 with hh|hh
    · rw [mul_comm d]; exact (h₁ E x d 1 _ hv hh).climb (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by unfold clump; positivity)) hr) le_rfl
    exact (composite (hv.climb ht le_rfl) (H _ (abs_le.mp (hv.bound.trans ht)))).climb ((le_add_of_nonneg_left hC).trans (le_mul_of_one_le_left hR hh)) le_rfl
  let p' y := Real.exp (f y)
  have hp: Brush n (p+1) 1 p' x:=by
    refine (((hf.climb hp le_rfl).gathering ((Brush.certified zero_le_one (1:ℝ)).climb ?_ le_rfl)).shimmy (Eventually.of_forall fun _=> Eq.symm (sub_add_cancel ..))); simp
  refine (hp.paints hg|>.trim).shimmy (Eventually.of_forall fun i=> ?_)|>.climb ?_ le_rfl
  · unfold g' p'; change (Real.exp _-1)-(Real.exp _-1)=_* (Real.exp (g i-f i)-1); rw [Real.exp_sub]; field_simp; ring
  exact le_of_eq (by ring)
end YM.PhysicalNext.Repeat.Alabaster
