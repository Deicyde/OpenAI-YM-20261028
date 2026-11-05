import YM.Push.FREE_RESOLVENT.ListJets
import YM.Push.FREE_RESOLVENT.Weights
import YM.Push.LOCAL_SPLITTING.Calculus


/-!
Ordered *left*, finite-order germ prices for sector multipliers. Keep slot
order and multiplicity (even inside products); uniform perturbation budgets
for all charged directions of a step. No price/derivative on a hard flag.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d
open Function Filter Lattice Wilson RG Next.Foundations Push.Local FreeResolvent.TestD
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
section masks
variable {τ : Type*}
lemma lo_mem {l : List τ} (m : Masks l) {x : τ} (h : x ∈ lo l m) : x ∈ l := by
  induction l with
  | nil => simp [lo] at h
  | cons i l ih =>
    cases m <;> simp only [lo,List.mem_cons] at *
    · exact h.imp_right (ih _)
    exact Or.inr (ih _ h)
lemma hi_mem {l : List τ} (m : Masks l) {x : τ} (h : x ∈ hi l m) : x ∈ l := by
  induction l with
  | nil => simp [hi] at h
  | cons i l ih =>
    cases m <;> simp only [hi,List.mem_cons] at *
    · exact Or.inr (ih _ h)
    exact h.imp_right (ih _)

lemma routes (l : List τ) (a b X Y : ℝ) :
    (∑ m : Masks l, (a*X^(lo l m).length)*(b*Y^(hi l m).length)) = (a*b)*(X+Y)^l.length := by
  induction l with
  | nil => simp [Masks,lo,hi]
  | cons i l ih =>
    rw [masks_sum]
    simp_rw [lo,hi,List.length_cons,pow_succ,
      show ∀ x y : ℝ, a*(x*X)*(b*y)=X*(a*x*(b*y)) by intros; ring,
      show ∀ x y : ℝ, a*x*(b*(y*Y))=Y*(a*x*(b*y)) by intros; ring,
      ← Finset.mul_sum,ih]
    ring
end masks

section calculus
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {V : Config G n} {k : ℕ} {f : Config G n → E} {g : Config G n → F}

lemma left_bilinear (p : E →L[ℝ] F →L[ℝ] H) (l : List (Directions G n)) (h : Chart k f V) (h' : Chart k g V)
    (hl : l.length ≤ k) : leftDerivs (fun W => p (f W) (g W)) l V = ∑ m : Masks l, p (leftDerivs f (lo l m) V) (leftDerivs g (hi l m) V) := by
  induction l generalizing V with
  | nil => simp [Masks,lo,hi,leftDerivs]
  | cons i l ih =>
    have he : l.length < k := hl
    have ht := HasDerivAt.fun_sum (u:= (Finset.univ : Finset (Masks l))) fun m _ =>
      ((p.hasFDerivAt.comp_hasDerivAt _ (left_has i (lt_of_le_of_lt (len_low l m) he) h)).clm_apply
        (left_has i (lt_of_le_of_lt (len_high l m) he) h'))
    rw [leftDerivs, masks_sum, ← Finset.sum_add_distrib]
    simpa only [zero_smul, Work.G07.at_zero_increment, comp_apply, lo,hi] using
      (ht.congr_of_eventuallyEq (f₁:=fun t => leftDerivs (fun W => p (f W) (g W)) l (increment V (t • i))) (by
        filter_upwards [chart_near h i,chart_near h' i] with t hu hv
        exact ih hu hv he.le)).deriv
end calculus

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Value and ordered-left-jet majorant through k (`growth` charged once per derivative).
Always a real `ContDiffAt` germ, even for derivatives at boundaries of health sets. -/
structure Bound (k : ℕ) (D : Directions G n → Prop) (V : Config G n) (f : Config G n → E) (a growth : ℝ) : Prop where
  smooth : Chart k f V
  nn : 0 ≤ a
  size : 0 ≤ growth
  pays (l : List (Directions G n)) : l.length ≤ k → (∀ x ∈ l,D x) → ‖leftDerivs f l V‖ ≤ a * growth^l.length

variable {k : ℕ} {D : Directions G n → Prop} {V : Config G n} {f f' : Config G n → E} {g g' : Config G n → F}
  {a b c d K L : ℝ}

namespace Bound
lemma value (h : Bound k D V f a K) : ‖f V‖ ≤ a := by simpa only [List.length_nil, pow_zero, mul_one,leftDerivs] using h.pays [] (by simp) (by simp)
lemma simple (h : Bound k D V f a 1) (l : List (Directions G n)) (hl : l.length ≤ k) (he : ∀ x ∈ l, D x) : ‖leftDerivs f l V‖ ≤ a := by simpa using h.pays l hl he
lemma lower {j : ℕ} (h : Bound k D V f a K) (hj : j ≤ k) : Bound j D V f a K :=
  ⟨h.smooth.of_le (Nat.cast_le.mpr hj),h.nn,h.size,fun l hl => h.pays l (hl.trans hj)⟩
lemma weaker {b T : ℝ} (h : Bound k D V f a K) (hb : a ≤ b) (ht : K ≤ T) : Bound k D V f b T :=
  ⟨h.smooth,h.nn.trans hb,h.size.trans ht,fun l hl he => (h.pays l hl he).trans
    (mul_le_mul hb (pow_le_pow_left₀ h.size ht _) (pow_nonneg h.size _) (h.nn.trans hb))⟩
lemma flatten (h : Bound k D V f a K) (hh : 1 ≤ K) : Bound k D V f (a*K^k) 1 := by
  refine ⟨h.smooth,mul_nonneg h.nn (pow_nonneg h.size _),zero_le_one,fun l hl he => ?_⟩
  simp only [one_pow,mul_one]; exact (h.pays l hl he).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hh hl) h.nn)
lemma congr {g : Config G n → E} (h : Bound k D V f a K) (hh : g ∘ increment V =ᶠ[𝓝 0] f ∘ increment V) :
    Bound k D V g a K := ⟨h.smooth.congr_of_eventuallyEq hh,h.nn,h.size,fun l hl he => by rw [left_congr l _ hh]; exact h.pays l hl he⟩
lemma const (x : E) (ha : ‖x‖ ≤ a) (hh : 0 ≤ K) : Bound k D V (fun _ => x) a K := by
  have hx := (norm_nonneg _).trans ha
  refine ⟨contDiffAt_const,hx,hh,fun l _ _ => ?_⟩
  rw [Work.G07.left_const]; split
  next h => simpa [h] using ha
  next _ => rw [norm_zero]; exact mul_nonneg hx (pow_nonneg hh _)
lemma add (h : Bound k D V f a K) (he : Bound k D V f' b K) : Bound k D V (fun W => f W+f' W) (a+b) K := by
  refine ⟨h.smooth.add he.smooth,add_nonneg h.nn he.nn,h.size,fun l hl hh => ?_⟩
  rw [add_mul, ← Pi.add_def, left_add l h.smooth he.smooth hl]
  exact (norm_add_le ..).trans (add_le_add (h.pays l hl hh) (he.pays l hl hh))
lemma neg (h : Bound k D V f a K) : Bound k D V (fun W => -f W) a K := by
  refine ⟨h.smooth.neg,h.nn,h.size,fun l hl he => ?_⟩
  change ‖leftDerivs ((-ContinuousLinearMap.id ℝ E : E →L[ℝ] E) ∘ f) l V‖ ≤ _
  rw [left_linear _ _ h.smooth hl]; simpa using h.pays l hl he
lemma sum {ι : Type*} (s : Finset ι) {f : ι → Config G n → E} {a : ι → ℝ} (h : ∀ i∈s, Bound k D V (f i) (a i) K) (he : 0≤K) :
    Bound k D V (fun W => ∑ i∈s, f i W) (∑ i∈s, a i) K := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (0:E) (norm_zero.le) he
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (h i (by simp)).add (ih fun i hi => h i (by simp [hi]))
lemma bilinear (p : E →L[ℝ] F →L[ℝ] H) (hp : ∀ u v, ‖p u v‖ ≤ ‖u‖*‖v‖) (h : Bound k D V f a K)
    (hh : Bound k D V g b L) : Bound k D V (fun W => p (f W) (g W)) (a*b) (K+L) := by
  refine ⟨(p.contDiff.contDiffAt.comp 0 h.smooth).clm_apply hh.smooth,mul_nonneg h.nn hh.nn,add_nonneg h.size hh.size,fun l hl he => ?_⟩
  rw [left_bilinear p l h.smooth hh.smooth hl,← routes l]; apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum; intro m _
  exact (hp _ _).trans (mul_le_mul
    (h.pays _ ((len_low l m).trans hl) (fun _ hi => he _ (lo_mem _ hi)))
    (hh.pays _ ((len_high l m).trans hl) (fun _ hi => he _ (hi_mem _ hi))) (norm_nonneg _) (mul_nonneg h.nn (pow_nonneg h.size _)))
lemma first (h : Bound (k+1) D V f a 1) {v : Directions G n} (he : D v) : Bound k D V (leftDerivs f [v]) a 1 := by
  refine ⟨leftDerivs_chart [v] k (by simpa [Chart,add_comm] using h.smooth), h.nn,h.size,fun l hl hh => ?_⟩
  rw [← Work.G07.left_append]; simp only [one_pow,mul_one]
  exact h.simple _ (by simpa) (List.forall_mem_append.mpr ⟨hh,by simpa using he⟩)
end Bound

/-- Two calculations and a perturbation bound (same growth charged in error). -/
structure Compare (k : ℕ) (D : Directions G n → Prop) (V : Config G n) (f f' : Config G n → E) (a e K : ℝ) : Prop where
  west : Bound k D V f a K
  east : Bound k D V f' a K
  swing : Bound k D V (fun W => f W-f' W) e K

namespace Compare

lemma weaker (h : Compare k D V f f' a b K) (ha : a ≤ c) (hb : b ≤ d) (he : K ≤ L) : Compare k D V f f' c d L :=
  ⟨h.west.weaker ha he,h.east.weaker ha he,h.swing.weaker hb he⟩
lemma lower {j : ℕ} (h : Compare k D V f f' a b K) (he : j ≤ k) : Compare j D V f f' a b K :=
  ⟨h.west.lower he,h.east.lower he,h.swing.lower he⟩
lemma congr {g g' : Config G n → E} (h : Compare k D V f f' a b K) (hw : g ∘ increment V =ᶠ[𝓝 0] f ∘ increment V)
    (he : g' ∘ increment V =ᶠ[𝓝 0] f' ∘ increment V) : Compare k D V g g' a b K := ⟨h.west.congr hw, h.east.congr he, h.swing.congr (hw.sub he)⟩
lemma same (h : Bound k D V f a K) : Compare k D V f f a 0 K := ⟨h,h,by simpa using Bound.const (k:=k) (D:=D) (V:=V) (0:E) (norm_zero.le) h.size⟩

lemma flatten (h : Compare k D V f f' a b K) (he : 1 ≤ K) : Compare k D V f f' (a*K^k) (b*K^k) 1 :=
  ⟨h.west.flatten he,h.east.flatten he,h.swing.flatten he⟩
lemma add (h : Compare k D V f f' a b K) {g g' : Config G n → E} (e : Compare k D V g g' c d K) :
    Compare k D V (fun W => f W + g W) (fun W => f' W + g' W) (a+c) (b+d) K := by
  refine ⟨h.west.add e.west,h.east.add e.east,?_⟩; simpa only [add_sub_add_comm] using h.swing.add e.swing
lemma neg (h : Compare k D V f f' a b K) : Compare k D V (fun W => -f W) (fun W => -f' W) a b K :=
  ⟨h.west.neg,h.east.neg,by simpa only [neg_sub_neg,neg_sub] using h.swing.neg⟩
lemma sub (h : Compare k D V f f' a b K) {g g' : Config G n → E} (e : Compare k D V g g' c d K) :
    Compare k D V (fun W => f W - g W) (fun W => f' W - g' W) (a+c) (b+d) K := by simpa only [sub_eq_add_neg] using h.add e.neg
lemma const (x y : E) (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) (hxy : ‖x-y‖ ≤ b) (hh : 0 ≤ K) :
    Compare k D V (fun _ => x) (fun _ => y) a b K := ⟨Bound.const _ hx hh,Bound.const _ hy hh,Bound.const _ hxy hh⟩
lemma sum {ι : Type*} (s : Finset ι) {f f' : ι → Config G n → E} {a b : ι → ℝ} (h : ∀ i∈s, Compare k D V (f i) (f' i) (a i) (b i) K) (hh : 0≤K) :
    Compare k D V (fun W => ∑ i∈s, f i W) (fun W => ∑ i∈s, f' i W) (∑ i∈s, a i) (∑ i∈s, b i) K :=
  ⟨Bound.sum _ (fun i hi => (h i hi).west) hh,Bound.sum _ (fun i hi => (h i hi).east) hh, by
    simpa only [Finset.sum_sub_distrib] using Bound.sum s (fun i hi => (h i hi).swing) hh⟩
lemma univ {ι : Type*} [Fintype ι] {f f' : ι → Config G n → E} (h : ∀ i, Compare k D V (f i) (f' i) a b K) (hh : 0≤K) :
    Compare k D V (fun W => ∑ i, f i W) (fun W => ∑ i, f' i W) (Fintype.card ι*a) (Fintype.card ι*b) K := by
  simpa using sum Finset.univ (fun i _ => h i) hh
lemma bilinear (p : E →L[ℝ] F →L[ℝ] H) (hp : ∀ u v, ‖p u v‖ ≤ ‖u‖*‖v‖) (h : Compare k D V f f' a b K)
    (hh : Compare k D V g g' c d L) : Compare k D V (fun W => p (f W) (g W)) (fun W => p (f' W) (g' W)) (a*c) (b*c+a*d) (K+L) := by
  have he (W : Config G n) : p (f W) (g W) - p (f' W) (g' W) = p (f W-f' W) (g W) + p (f' W) (g W-g' W) := by
    simp only [map_sub,sub_apply]; abel
  exact ⟨h.west.bilinear p hp hh.west,h.east.bilinear p hp hh.east, by simp_rw [he]; exact (h.swing.bilinear p hp hh.west).add (h.east.bilinear p hp hh.swing)⟩
lemma mul {f f' g g' : Config G n → ℝ} (h : Compare k D V f f' a b K) (hh : Compare k D V g g' c d L) :
    Compare k D V (fun W => f W * g W) (fun W => f' W * g' W) (a*c) (b*c+a*d) (K+L) := h.bilinear (ContinuousLinearMap.mul ℝ ℝ) norm_mul_le hh
lemma scale {f f' : Config G n → ℝ} (h : Compare k D V f f' a b K) (u : ℝ) :
    Compare k D V (fun W => u * f W) (fun W => u * f' W) (|u| * a) (|u| * b) K := by
  have he : Compare k D V (fun _ => u) (fun _ => u) |u| 0 0 := same (Bound.const _ (Real.norm_eq_abs _).le le_rfl)
  simpa using he.mul h
lemma prod {ι : Type*} (s : Finset ι) {f f' : ι → Config G n → ℝ} {a b : ι → ℝ} [DecidableEq ι]
    (h : ∀ i∈s, Compare k D V (f i) (f' i) (a i) (b i) K) : Compare k D V (fun W => ∏ i∈s, f i W) (fun W => ∏ i∈s, f' i W)
      (∏ i∈s, a i) (∑ i∈s, b i*∏ j∈s.erase i,a j) (s.card*K) := by
  induction s using Finset.induction_on with
  | empty => simpa using same (f:=fun _ => (1:ℝ)) (Bound.const _ (norm_one.le) (K:=0) le_rfl)
  | insert i s hi ih =>
    have he j (hj : j∈s) : ∏ x∈(insert i s).erase j, a x = a i * ∏ x∈s.erase j,a x := by
      have ht : i ≠ j := fun h => hi (h ▸ hj)
      rw [Finset.erase_insert_of_ne ht, Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h))]
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm _ K,
      Finset.sum_insert hi, Finset.erase_insert hi, Finset.sum_congr rfl (show ∀ j∈s, b j * _ = a i*(b j * ∏ x∈s.erase j,a x) by intros; rw [he,mul_left_comm]; assumption)]
    simpa only [Finset.prod_insert hi,Finset.mul_sum] using (h i (by simp)).mul (ih fun j hj => h j (by simp [hj]))
lemma apply_clm {g g' : Config G n → E →L[ℝ] F} (h : Compare k D V g g' a b K) (hh : Compare k D V f f' c d L) :
    Compare k D V (fun W => (g W) (f W)) (fun W => (g' W) (f' W)) (a*c) (b*c+a*d) (K+L) :=
  h.bilinear ((ContinuousLinearMap.apply ℝ F).flip) (fun u v => u.le_opNorm v) hh
lemma first (h : Compare (k+1) D V f f' a b 1) {v : Directions G n} (he : D v) :
    Compare k D V (leftDerivs f [v]) (leftDerivs f' [v]) a b 1 := by
  refine ⟨h.west.first he,h.east.first he,(h.swing.first he).congr ?_⟩
  have H {w : Config G n → E} (hw : Chart (k+1) w V) : ∀ᶠ y : Directions G n in 𝓝 0, Chart 1 w (increment V y) :=
    chart_eventually (by rw [Work.G07.at_zero_increment]; exact hw.of_le (Nat.cast_le.mpr (Nat.le_add_left 1 k))) (fun i => by
      simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
  filter_upwards [H h.west.smooth,H h.east.smooth] with y hx hy
  exact ((left_has v (l:=[]) (by simp) hx).sub (left_has v (l:=[]) (by simp) hy)).deriv.symm
end Compare
end YM.AnalyticBridge.MarginalMultiplier3b1d
