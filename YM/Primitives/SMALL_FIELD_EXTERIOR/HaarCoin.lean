import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Primitives.SMALL_FIELD_EXTERIOR.Squares
import YM.Push.STATIONARY_UNIFORM.Array



/-!
# Hessian cost for the TRUE local Haar density

In counting coords of forests. Charge before choosing any period. The
correction is block diagonal but not assumed log-concave; pay it at the same
addresses and only on this domain. This is not a claim about Fresnel or
absolute values of analytic continuations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior.HaarCoin
open Function Set Filter Metric MeasureTheory Matrix
open Lattice Precision Push.Uniform Tree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {ι : Type} [Fintype ι] -- decidability via classical
variable {P : ChartRatio G} {r R m k : ℝ}

def brow (G : Gauge) : Points G.ColorIndex ≃L[ℝ] G.Color := (PiLp.continuousLinearEquiv 2 ℝ _).symm
def pick (G : Gauge) (i : ι) : Points (ι × G.ColorIndex) →L[ℝ] Points G.ColorIndex :=
    (brow G).symm.toContinuousLinearMap ∘L (ContinuousLinearMap.proj (R:=ℝ) i ∘L (tint G ι).toContinuousLinearMap)

lemma pick_ap (x : Points (ι × G.ColorIndex)) (i j) : pick G i x j=x (i,j) := rfl
lemma picked (x : Points (ι × G.ColorIndex)) (i) : brow G (pick G i x)=(tint G ι x) i := rfl

/-- Negative-log of probability Haar density on one chart. -/
def taxes (P : ChartRatio G) (y : Points G.ColorIndex) : ℝ := -Real.log (P.scale * P.J (brow G y))

structure Stamp (P : ChartRatio G) (R m k : ℝ) : Prop where
  paid : LocalRatio P
  pos : 0 < R
  levy : 0 < m
  entry : 0 ≤ k
  fits : MapsTo (brow G) (cube G.ColorIndex R) (ball 0 P.radius)
  stays (y : Points G.ColorIndex) : y∈cube G.ColorIndex R → m ≤ P.scale * P.J (brow G y)
  germs : SmallFieldExterior.Regular R 2 (taxes P)
  bills (y : Points G.ColorIndex) : y∈cube G.ColorIndex R → ∀ i j, |curvature (taxes P) y i j| ≤ k



lemma pick_mem (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r ≤ R) (v : Points (ι × G.ColorIndex))
    (hv : v∈cube _ r) (i : ι) : pick G i v∈cube G.ColorIndex R :=
  (cube_iff h.pos.le).2 fun j => ((cube_iff hr).1 hv (i,j)).trans hp

def wag (P : ChartRatio G) (i : ι) := taxes P ∘ pick G i

def dues (P : ChartRatio G) (ι : Type) [Fintype ι] : Points (ι × G.ColorIndex) → ℝ := ∑ i : ι,wag P i

lemma wag_smooth (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) (i : ι) : SmallFieldExterior.Regular r 2 (wag P i) :=
  fun x hx => (h.germs _ (pick_mem h hr hp x hx i)).comp _ (pick G i).contDiff.contDiffAt
lemma dues_smooth (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) (ι : Type) [Fintype ι] : SmallFieldExterior.Regular r 2 (dues P ι) :=
  SmallFieldExterior.Regular.fsum _ (fun i _ => wag_smooth h hr hp i)

-- Decidability-tracking helpers; pc computed with StepData keys.
private lemma pick_yes (i : ι) (j : G.ColorIndex) : pick G i (Pi.single (i,j) 1)=Pi.single j 1 := by
  ext l; rw [pick_ap]; by_cases hi : l=j <;> simp [hi]
private lemma pick_no {i u : ι} (h : u ≠ i) (j : G.ColorIndex) : pick G i (Pi.single (u,j) 1)=0 := by
  ext l; rw [pick_ap]; simp [Ne.symm h]
private lemma pc_pick (i j : ι) (p : G.ColorIndex) {f : Points G.ColorIndex → ℝ} {x} (h : DifferentiableAt ℝ f (pick G i x)) :
    pc (j,p) (f ∘ pick G i) x = if i=j then pc p f (pick G i x) else 0 := by
  unfold pc; rw [fderiv_comp _ h (pick G i |>.differentiableAt),ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply]
  by_cases hb : i=j
  · subst j; rw [pick_yes,if_pos rfl]
  rw [pick_no (Ne.symm hb), map_zero, if_neg hb]
private lemma wag_second (i : ι) (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) (x : Points (ι × G.ColorIndex))
    (hx : x∈cube _ r) (j l : ι × G.ColorIndex) :
    curvature (wag P i) x j l = if i=l.1 then (if i=j.1 then curvature (taxes P) (pick G i x) j.2 l.2 else 0) else 0 := by
  let H := taxes P; let L := pick G i; let T := wag P i
  have hf := pick_mem h hr hp x hx i
  have he := h.germs _ hf
  have hv : pc l T=ᶠ[𝓝 x] (if i=l.1 then pc l.2 H ∘ L else 0) := by
    have ht := he.eventually (by norm_num)
    filter_upwards [L.continuous.continuousAt.tendsto.eventually ht] with y hy
    have he := pc_pick i l.1 l.2 (x:=y) (hy.differentiableAt two_ne_zero)
    rw [Prod.eta] at he
    split_ifs with hb
    · rw [if_pos hb] at he; exact he
    rw [if_neg hb] at he; exact he
  change pc j (pc l T) x=_
  by_cases hh : i=l.1
  · rw [if_pos hh] at hv ⊢
    rw [pc,hv.fderiv_eq]; exact pc_pick i j.1 j.2 (f:=pc l.2 H) (x:=x) ((h.germs.tangent l.2).diff one_ne_zero hf)
  rw [if_neg hh] at hv ⊢
  rw [pc,hv.fderiv_eq]; simp

lemma duty_matrix (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r ≤ R) (x : Points (ι × G.ColorIndex)) (hx : x∈cube _ r)
    (j l : ι × G.ColorIndex) :
    curvature (dues P ι) x j l = if l.1=j.1 then curvature (taxes P) (pick G l.1 x) j.2 l.2 else 0 := by
  have hf i := wag_smooth h hr hp i x hx
  have hv : pc l (dues P ι)=ᶠ[𝓝 x] ∑ i : ι,pc l (wag P i) := by
    have he : ∀ i : ι, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 (wag P i) y := fun i => (hf i).eventually (by norm_num)
    filter_upwards [eventually_all.mpr he] with y hy
    rw [Finset.sum_apply]; exact pc_sum l _ fun i _ => (hy i).differentiableAt two_ne_zero
  change fderiv ℝ _ x (Pi.single j 1)=_
  rw [hv.fderiv_eq]; change pc j _ _=_
  rw [pc_sum (f:=fun i => pc l (wag P i)) j _ (fun i _ => ((wag_smooth h hr hp i).tangent l).diff one_ne_zero hx)]
  change (∑ i : ι, curvature (wag P i) x j l) = _
  simp_rw [wag_second _ h hr hp x hx j l]; simp

def tariff (G : Gauge) (k : ℝ) : ℝ := k * Fintype.card G.ColorIndex
lemma Stamp.receipt (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) : Charged r (dues P ι) (-tariff G k) := by
  intro x hx
  let S := curvature (dues P ι) x
  have hc (i : ι × G.ColorIndex) : ∑ j, |S i j| ≤ tariff G k := by
    unfold S; rw [Fintype.sum_prod_type];
    rw [Finset.sum_eq_single_of_mem i.1 (Finset.mem_univ _)]
    · calc
        _ ≤ ∑ _j : G.ColorIndex, k := Finset.sum_le_sum fun j _ => by
          rw [duty_matrix h hr hp x hx i]; simp only [if_true]; exact h.bills _ (pick_mem h hr hp x hx _) _ _
        _ = _ := by simp [tariff,mul_comm k]
    intro b _ hb; simp [duty_matrix h hr hp x hx,hb]
  have he j : ∑ i, |S i j| ≤ tariff G k := by
    have hh : S.IsSymm := isHermitian_iff_isSymm.mp (curvature_sym (dues_smooth h hr hp _ _ hx))
    conv_lhs => arg 2; ext i; rw [show S i j = S j i from hh.apply j i]
    exact hc j
  intro v
  rw [neg_mul]; exact (abs_le.mp (quadratic_test hc he v)).1

lemma Stamp.still (h : Stamp P R m k) (hr : 0 ≤ r) (hp : r≤R) {w : ι → ℝ} (hw : ∀ i,w i ≠ 0)
    (x : Points (ι × G.ColorIndex)) (hx : x∈cube _ r) :
    conjugated (fun i => w i.1) (curvature (dues P ι) x)=curvature (dues P ι) x := by
  ext i j
  rw [conjugated,Matrix.of_apply,duty_matrix h hr hp x hx i j]
  split_ifs with he
  · rw [he]; field_simp [hw]
  simp
end YM.Primitives.SmallFieldExterior.HaarCoin
