import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Eskim

/-!
# Germ on protected Hot rheology. Uniform rates for all projectors

Respect Supports patch. Need exponential coefficients small even where
∂ comes entirely from protected columns at giant |z|. Craft the nonlinear
pin through calibrated receipts. Compact enough across all Y.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open Pulse Itinerary Scroll Vine Polar Frond Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {X : Coat T F} {z : Air f G} {E Y Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] {x : E}
variable {a α β γ d η σ w s : ℝ} {j : ℕ}
namespace Brush
lemma exalt {f : E→Y} (p : Brush j w d f x) (h : ‖f x‖≤1) : Brush j 1 ((1+w)*d) f x := by
  have hp: 1≤1+w := le_add_of_nonneg_right p.nonneg
  refine ⟨p.smooth,mul_nonneg (zero_le_one.trans hp) p.pos,?_⟩
  rintro (_|i) hi
  · unfold normJ; simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using! h
  rw [one_mul,mul_pow]; exact (p.order _ hi).trans (mul_le_mul_of_nonneg_right
    ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hp (by omega))) (pow_nonneg p.pos _))

lemma even {F : E→Y} {g : Y→Z} (h : Brush j w d F x) (hg : Brush j σ 1 g (F x)) (hv : w≤1) (hp : 0≤s)
    (he : ‖g (F x)‖≤s*w) : Brush j ((s+j.factorial*σ)*w) d (fun i=>g (F i)) x := by
  have hw:=h.nonneg; have ht:=hg.nonneg
  refine ⟨(h.pine hg).smooth,h.pos,fun i hi=>?_⟩
  by_cases hm:i=0
  · rw [hm,normJ,norm_iteratedFDeriv_zero,pow_zero,mul_one]; exact he.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hw)
  let v := w^((i:ℝ)⁻¹); have heq : v^i=w := Real.rpow_inv_natCast_pow hw hm
  have hV:0≤v := Real.rpow_nonneg hw _
  have hx : v≤1 := by by_contra! hx; exact lt_irrefl 1 (lt_of_lt_of_le (one_lt_pow₀ hx hm) (by rw [heq]; exact hv))
  have hh : ∀ u,0<u → u ≤ i → normJ u F x≤ (v*d)^u := by
    intro u hu hi'; rw [mul_pow]; apply (h.order _ (hi'.trans hi)).trans; rw [← heq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hV hx hi') (pow_nonneg h.pos _)
  have hh':= ((hg.smaller hi).compound (h.smaller hi).smooth (mul_nonneg hV h.pos) hh).order i le_rfl
  rw [mul_pow,heq,← mul_assoc] at hh'; apply hh'.trans
  have hy: (i.factorial:ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_le hi
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hy ht).trans (le_add_of_nonneg_left hp)) hw) (pow_nonneg h.pos _)

lemma expands (j : ℕ) : ∃ C : ℝ, 0≤C ∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d : ℝ) (f : E→ℝ),
    Brush j w d f x → w≤1 → Brush j (C*w) d (fun i=> Real.exp (f i)-1) x := by
  obtain ⟨v,hv,hp⟩:= Brush.compact (k:=j) (s:=Set.Icc (-1:ℝ) 1) (f:=fun x => Real.exp x-1) isCompact_Icc
    (fun i hi=> Real.contDiff_exp.contDiffAt.sub contDiffAt_const)
  refine ⟨_, by exact add_nonneg (by norm_num : 0≤(2:ℝ)) (mul_nonneg (Nat.cast_nonneg (α:=ℝ) j.factorial) hv.le),?_⟩
  intro E _ _ x w d f hf hw
  have hh : |f x|≤1 := hf.bound.trans hw
  exact even hf (hp _ (abs_le.mp hh)) hw (by norm_num) ((Real.abs_exp_sub_one_le hh).trans (mul_le_mul_of_nonneg_left hf.bound (by norm_num)))
lemma zi {f : E→Y} (h : f=ᶠ[𝓝 x] fun _=>0) (hv : 0≤w) (hd : 0≤d) : Brush j w d f x := by
  refine ((Brush.certified hd (0:Y)).climb ?_ le_rfl).shimmy h; rwa [norm_zero]
end Brush
namespace Silica.Clutch
open Brush
variable {U : E → Config G c} {f' : E → Directions G f} {W : E→ Air f G} (H : Clutch X z a β s x j U f' W)
include H
lemma tipped : (vary X (U x))=X := by rw [H.atV]; rfl
lemma unseat : f' x=worldZ X β z := ((H.moving x)).symm.trans (by rw [tipped H,H.birth])
lemma base0 (hp : Room P S T X.x) (hz : X.manifest) : f' x=X.liftA β z := (unseat H).trans (shine X hp hz β z).symm
lemma budded (i : Bond f) (he : ‖f' x i‖≤ η) : Brush j (s+η) 1 (fun y=> f' y i) x := by
  rw [unseat H] at he; refine ((H.bud i).gathering ((Brush.certified zero_le_one _).climb he le_rfl)).shimmy ?_
  exact Eventually.of_forall fun j=> (sub_add_cancel ..).symm
lemma fostered (i : Bond f) {b:ℝ} (h : 0<b*X.t) (hp : ¬ (fun y=> X.cone b (f' y) i)=ᶠ[𝓝 x] fun _=>0) :
    ‖f' x i‖ ≤ 2*b*X.t ∧ Brush j (s+2*b*X.t) 1 (fun y=> f' y i) x := by
  suffices hh: ‖f' x i‖≤2*b*X.t from ⟨hh,H.budded _ hh⟩
  by_contra! he; apply hp
  filter_upwards [((H.budded i le_rfl).smooth.continuousAt).norm.eventually (lt_mem_nhds he)] with j hj
  by_contra ht; exact ((X.amount h (f' j) i ht)).not_gt hj

lemma darling (Y : Finset (Bond f)) (p : ¬ (fun y=> X.enforce (2*a) (f' y) Y)=ᶠ[𝓝 x] fun _=>0) :
    (∀ i∈Y, Brush j (s+4*a*X.t) 1 (fun y=> f' y i) x) ∧
      ∀ᶠ y in 𝓝 x, ∀ i∈Y, (vary X (U y)).input (f' y) i=X.input (worldZ X β z) i := by
  have hp: 0<2*a*X.t := by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse
  have hh i (hi:i∈Y) : ¬ (fun y=> X.cone (2*a) (f' y) i)=ᶠ[𝓝 x] fun _=>0 := fun h=> p (h.mono fun x hx=> Finset.prod_eq_zero hi hx)
  have hz i (hi:i∈Y): ‖f' x i‖≤ 4*a*X.t := ((H.fostered i hp (hh _ hi)).1).trans_eq (by ring)
  refine ⟨fun i hi=> H.budded i (hz i hi),?_⟩
  have he i (hi:i∈Y) : ∀ᶠ y in 𝓝 x, ‖f' y i‖ < 8*a*X.t := ((H.budded i le_rfl).smooth.continuousAt).norm.eventually
    (gt_mem_nhds ((hz i hi).trans_lt (show 4*a*X.t < 8*a*X.t by nlinarith only [hp])))
  filter_upwards [H.patch,(Finset.eventually_all _).2 he] with y hy hh i hi; apply hy.same; right
  change _ ≤ 4*(2*a)*X.t; exact (hh i hi).le.trans_eq (by ring)
end Silica.Clutch
end YM.ConnectedActivityE6.Blaze
