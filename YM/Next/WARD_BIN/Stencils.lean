import Mathlib.Analysis.ODE.ExistUnique
import YM.Analysis.Polydisc
import YM.Analysis.SmoothJets
import YM.Next.WARD_BIN.Haar
import YM.PCalc.Band
import YM.Source.Construction
import YM.Work.G07.Stencil



/-!
# Bounds on one *microscopic* stencil

No growth of the stencil attempted here. We count at the desired position and
order/power; all side lengths which can accommodate the stencil. `ℤ` for the
threshold exponent as one physical link derivative may cost 1/t (when later
used with a power of β this can be innocuous).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Filter Function Set MeasureTheory Wilson Lattice Source  Labels RG Work.G07
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {S : Finset Cover}

section geometry

/-- For any origin on the torus; the choice of causal chart for the stencil. -/
def FitsIn (S : Finset Cover) (n : Side) := ∀ x∈S,Lattice.lift (wrap n x) = x

lemma fits_injective (h : FitsIn S n) : Set.InjOn (wrap n) S :=
  fun _ hx _ hy e => (h _ hx).symm.trans ((congr_arg Lattice.lift e).trans (h _ hy))

lemma large_fits (S : Finset Cover) : ∃ N : ℕ, ∀ n : Side, N ≤ n.val → FitsIn S n := by
  let v (p : Cover) := Finset.univ.sup fun i => (p i).natAbs
  let M := S.sup v
  refine ⟨2*M+1, fun n hn x hx => lift_eq_iff.mpr ⟨rfl,fun i => ?_⟩⟩
  have he := Finset.le_sup (f:=v) hx
  have hp : (x i).natAbs ≤ M := (Finset.le_sup (f:=fun i => (x i).natAbs) (Finset.mem_univ i)).trans he
  omega

lemma someFits (S : Finset Cover) : ∃ n, FitsIn S n := by
  obtain ⟨N,H⟩ := large_fits S; exact ⟨⟨N+1,Nat.zero_lt_succ _⟩,H _ (Nat.le_succ _)⟩

def footprint (S : Finset Cover) (o : Site n) := S.image fun p => wrap n p + o

def places {F : Type*} (o : Site n) (f : CoverConfig G → F) : Config G n → F := f ∘ expandAt o

def edgeAt (e : Edge Cover) (o : Site n) : Edge (Site n) := (wrap n e.1 + o,e.2)

def above (o : Site n) (U : CoverConfig G) : Config G n := fun e => U (Lattice.lift (e.1-o),e.2)

@[fun_prop] lemma above_cont (o : Site n) : Continuous (above (G:=G) o) := continuous_pi fun _ => continuous_apply _

variable {F : Type*}

lemma fromAbove {f : CoverConfig G → F} (hf : LocalOn S f) (h : FitsIn S n)
    (o : Site n) (U : CoverConfig G) : places o f (above o U) = f U := by
  apply hf (expandAt o (above o U)) U
  intro i hi _
  change U (Lattice.lift (wrap n _ + o - o),i.2) = _
  rw [add_sub_cancel_right, h i.1 hi]

lemma slides_cover (U : CoverConfig G) (A : G.Color) {e : Edge Cover} (ht : e.1∈S)
    {Z : CoverConfig G} (hz : Agrees S U Z) : Agrees S (slide e U A) (slide e Z A) := by
  intro i hi hk
  by_cases he : i = e
  · subst i; simp only [slide,update_self,hz e ht hk]
  rw [slide,slide,update_of_ne he,update_of_ne he,hz i hi hk]

lemma slopes_cover [NormedAddCommGroup F] [NormedSpace ℝ F] {f : CoverConfig G → F} (hf : LocalOn S f)
    {e : Edge Cover} (ht : e.1∈S) (a : G.Color) : LocalOn S (slope e a f) := by
  intro U V hUV
  rw [slope,slope,show (fun t : ℝ => f (slide e U (t • a))) = _ from
    funext fun t => hf _ _ (slides_cover _ _ ht hUV)]

lemma slide_at (U : Config G n) (A : G.Color) (o : Site n) {e : Edge Cover} (ht : e.1∈S)
    (he : FitsIn S n) : Agrees S (expandAt o (slide (edgeAt e o) U A)) (slide e (expandAt o U) A) := by
  intro i hi _
  change slide _ _ _ (edgeAt i o) = _
  by_cases hx : i = e
  · subst i; simp only [slide,update_self]; rfl
  have hp : edgeAt i o ≠ edgeAt e o := by
    intro h
    exact hx <| Prod.ext (fits_injective he hi ht (add_right_cancel (congrArg Prod.fst h))) (show (edgeAt i o).2 = (edgeAt e o).2 from congrArg Prod.snd h)
  simp only [slide,update_of_ne hp,update_of_ne hx]; rfl

lemma slopes_at [NormedAddCommGroup F] [NormedSpace ℝ F] {f : CoverConfig G → F} (hf : LocalOn S f)
    (h : FitsIn S n) (o : Site n) {e : Edge Cover} (ht : e.1∈S) (a : G.Color) :
    slope (edgeAt e o) a (places o f) = places o (slope e a f) := by
  funext i
  unfold slope places
  simp_rw [Function.comp_apply]
  apply congrFun (a:=0) (congr_arg (fun g : ℝ → F => deriv g) ?_)
  exact funext (fun t => hf _ _ (slide_at i (t • a) o ht h))

end geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℤ}

/-- A budget at all finite orders, *constants* allowed to depend on each.
Call later with requirements actually priced. No gauge assumption here. -/
structure Affordable (S : Finset Cover) (j : ℤ) (f : CoverConfig G → F) : Prop where
  uses : LocalOn S f
  paid (k P : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ n : Side, FitsIn S n → ∀ b : BudgetPoint,
    b.power=P → ∀ o : Site n, LeftBound k (b.dirBound o) (Healthy b.threshold (footprint S o))
      1 (c * b.threshold^j) (places o f)

namespace Affordable

variable {u v : CoverConfig G → F}

/-- Transfer old `pop`/rate techniques to the call-specific margins. -/
theorem fromRate {i : ℕ} (hu : LocalOn S u) (h : ∀ k P, Rate k P S i 0 u) : Affordable S (i:ℤ) u := by
  refine ⟨hu,fun k P => ?_⟩; obtain ⟨c,hc,hV⟩ := h k P
  refine ⟨c,hc,fun n _ b hb o => ?_⟩
  simpa only [pow_zero,zpow_natCast,footprint,places,Function.comp_def] using hV b hb n o

lemma widen (h : Affordable S j u) {T : Finset Cover} (ht : S ⊆ T) : Affordable T j u := by
  refine ⟨fun U V e => h.uses U V (fun i hi hj => e i (ht hi) (ht hj)),fun k P => ?_⟩
  obtain ⟨c,hc,H⟩ := h.paid k P
  refine ⟨c,hc,fun n hn b hb o => ?_⟩
  have hx := H n (fun x hx => hn _ (ht hx)) b hb o
  refine ⟨hx.smooth,hx.nonneg,fun l hl he U hs => ?_⟩
  exact hx.bound _ hl he U (Finset.disjoint_of_subset_left (Finset.image_subset_image ht) hs)

lemma postcomp (h : Affordable S j u) (L : F →L[ℝ] E) : Affordable S j fun U => L (u U) := by
  refine ⟨fun U V he => congrArg L (h.uses U V he),fun k P => ?_⟩
  obtain ⟨c,hc,H⟩ := h.paid k P
  refine ⟨‖L‖*c,by positivity,fun n hn b hb o => ?_⟩
  rw [mul_assoc]; exact (H n hn b hb o).postcomp _

lemma zero : Affordable S j (fun _ : CoverConfig G => (0:F)) := by
  refine ⟨fun _ _ _ => rfl,fun k P => ⟨0,le_rfl,fun n hn b hb o => ?_⟩⟩
  simpa only [places, Function.comp_def, zero_mul,norm_zero] using LeftBound.const (D:=b.dirBound o) (r:=(1:ℝ)) (k:=k)
    (Z:=Healthy b.threshold (footprint S o)) zero_le_one (0:F)

lemma const (c : F) : Affordable S 0 fun _ : CoverConfig G => c := by
  refine ⟨fun _ _ _ => rfl,fun k P => ⟨‖c‖,norm_nonneg _,fun n hn b hb o => ?_⟩⟩
  rw [zpow_zero,mul_one]; exact LeftBound.const zero_le_one c

lemma add (hu : Affordable S j u) (hv : Affordable S j v) : Affordable S j fun U => u U+v U := by
  refine ⟨fun U V e => by simp only [hu.uses U V e,hv.uses U V e],fun k P => ?_⟩
  obtain ⟨c,hc,H⟩ := hu.paid k P; obtain ⟨d,hd,D⟩ := hv.paid k P
  exact ⟨c+d,by positivity,fun n hn b hb o => by rw [add_mul]; exact (H n hn b hb o).add (D n hn b hb o)⟩

lemma sub (hu : Affordable S j u) (hv : Affordable S j v) : Affordable S j fun U => u U-v U := by
  simp_rw [sub_eq_add_neg]
  exact hu.add (hv.postcomp (-ContinuousLinearMap.id ℝ F))

lemma sum {J : Type*} (I : Finset J) (f : J → CoverConfig G → F) (h : ∀ i∈I, Affordable S j (f i)) :
    Affordable S j fun U => ∑ i∈I, f i U := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using zero (F:=F) (j:=j) (G:=G) (S:=S)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add
      (ih fun p hp => h _ (Finset.mem_insert_of_mem hp))

lemma mul {T : Type*} [NormedRing T] [NormedAlgebra ℝ T] {u v : CoverConfig G → T} {l : ℤ}
    (hu : Affordable S j u) (hv : Affordable S l v) : Affordable S (j+l) fun U => u U*v U := by
  refine ⟨fun U V e => by simp only [hu.uses U V e,hv.uses U V e],fun k P => ?_⟩
  obtain ⟨c,hc,H⟩ := hu.paid k P; obtain ⟨d,hd,D⟩ := hv.paid k P
  refine ⟨2^k*c*d,by positivity,fun n hn b hb o => ?_⟩
  rw [zpow_add₀ b.threshold_pos.ne',show 2^k*c*d*(b.threshold^j*b.threshold^l)=
    2^k*(c*b.threshold^j)*(d*b.threshold^l) by ring]
  exact (H n hn b hb o).mul (D n hn b hb o) zero_le_one

lemma prod {J : Type*} {T : Type*} [NormedCommRing T] [NormedAlgebra ℝ T] (i : Finset J) (f : J → CoverConfig G → T) (w : J → ℤ)
    (h : ∀ j∈i, Affordable S (w j) (f j)) : Affordable S (∑ j∈i,w j) fun U => ∏ j∈i,f j U := by
  classical
  induction i using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; simpa using const (S:=S) (G:=G) (1:T)
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi,Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).mul
      (ih fun p hp => h _ (Finset.mem_insert_of_mem hp))

/- finite linear/multilinear assemblies use the same physical probe.
Derive instead of assuming any multilin closure. -/


lemma multilinear [FiniteDimensional ℝ F] {k : ℕ} (X : Fin k → CoverConfig G → F)
    (w : Fin k → ℤ) (h : ∀ i, Affordable S (w i) (X i)) (B : Tensor.T F E k) :
    Affordable S (∑ i,w i) fun U => B fun i => X i U := by
  classical
  let b := Module.finBasis ℝ F
  let Y i t := fun (U : CoverConfig G) => b.coord t (X i U)
  let J := Fin (Module.finrank ℝ F)
  have he (U) : B (fun i => X i U) = ∑ x : Fin k → J, (∏ i, Y i (x i) U) • B (fun i => b (x i)) := by
    let V (i : Fin k) (t : J) := Y i t U • b t
    have hi : (fun i => X i U) = fun i => ∑ j:J,V i j := funext fun i => (b.sum_repr _).symm
    rw [hi, B.map_sum]
    exact Finset.sum_congr rfl fun x _ => B.map_smul_univ (fun i => Y i (x i) U) (fun i => b (x i))
  rw [funext he]; refine sum _ (fun i U => _) fun i _ => ?_
  have hh (i : Fin k) (t : J) : Affordable S (w i) (Y i t) :=
    (h _).postcomp (b.coord t).toContinuousLinearMap
  exact (prod Finset.univ (fun j => Y j (i j)) w (fun j _ => hh j (i j))).postcomp
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (B fun j => b (i j)))

end Affordable

lemma exp_local (U : Config G n) {X : Type*} [TopologicalSpace X] (V : X → Config G n)
    (x : X) (hx : V x = U) (h : ∀ i : Edge (Site n), ContinuousAt (fun y => V y i) x) :
    let L (t : X) (e : Edge (Site n)) := G.plog (G.mat (V t e * (U e)⁻¹))
    L x=0 ∧ ContinuousAt L x ∧ ∀ᶠ z in 𝓝 x, increment U (L z) = V z := by
  intro L
  have he (e : Edge (Site n)) : Tendsto (fun y => V y e * (U e)⁻¹) (𝓝 x) (𝓝 1) := by
    simpa only [hx, mul_inv_cancel] using ((h e).tendsto.mul_const (U e)⁻¹)
  refine ⟨funext (fun i => ?_),continuousAt_pi.mpr (fun i => ?_),?_⟩
  · simp [L,hx]
  · have ht := (G.continuous_mat.tendsto (1:G.El)).comp (he i)
    have hg := (G.plog_diff.continuousAt.tendsto).comp ht
    simpa only [L, hx, mul_inv_cancel, G.mat_one, Function.comp_def, ContinuousAt] using! hg
  have hp := eventually_all.mpr (fun i => (he i).eventually G.plog_right)
  filter_upwards [hp] with z hz
  ext1 i; exact (congrArg (· * U i) (hz i)).trans (inv_mul_cancel_right ..)

omit [NormedSpace ℝ F] in
lemma left_cont (f : Config G n → F) (h : ∀ U, ContinuousAt (fun v => f (increment U v)) 0) : Continuous f := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  let L (t : Config G n) (e : Edge (Site n)) := G.plog (G.mat (t e*(x e)⁻¹))
  obtain ⟨(hx : L x=0), (hh : ContinuousAt L x), he⟩ := exp_local x id x rfl
    (fun i => (continuous_apply i).continuousAt)
  apply ContinuousAt.congr_of_eventuallyEq (f:=fun y => f (increment x (L y)))
    ((show ContinuousAt (fun v => f (increment x v)) (L x) from hx.symm ▸ (h x)).comp hh)
  exact he.mono fun y hy => congr_arg f hy.symm

namespace Affordable
variable {u : CoverConfig G → F}

-- Use a real BudgetPoint (k may vary but order here doesn't enter)
def test (t : ℝ) (h : 0<t) (he : t ≤ 1) : BudgetPoint := ⟨2,6,1,1,t,le_rfl,le_rfl,
  zero_lt_one,Nat.zero_lt_one,h,he⟩

lemma fitted (h : Affordable S j u) (k : ℕ) (hn : FitsIn S n) (o : Site n) : LeftSmooth k (places o u) :=
  ((h.paid k 2).choose_spec.2 _ hn (test 1 zero_lt_one le_rfl) rfl o).smooth

lemma smooth_cover_slide {e : Edge Cover} (ht : e.1∈S) (h : Affordable S j u)
    (U : CoverConfig G) : ContDiff ℝ ∞ (fun k => u (slide e U k)) := by
  obtain ⟨n,H⟩ := someFits S
  let V : Config G n := above 0 U
  have hs : ContDiff ℝ ∞ (fun v => places (0:Site n) u (increment V v)) :=
    (h.fitted 0 H 0) [] le_rfl V
  let i := edgeAt e (0:Site n)
  let L := ContinuousLinearMap.single ℝ (fun _ : Edge (Site n) => G.Color) i
  have hp (k : G.Color) : increment V (L k)=slide i V k := by
    rw [← show (1 : ℝ) • k=k from one_smul ℝ k, slide_increments (A:=k)]
    rw [one_smul,one_smul]; rfl
  have hm : Agrees S (expandAt 0 V) U := fun a ha _ => by
    change U (Lattice.lift (wrap n _ + 0-0),a.2) = _
    rw [add_sub_cancel_right,H a.1 ha]
  have hx (k : G.Color) : places (0:Site n) u (increment V (L k))=u (slide e U k) := by
    rw [hp k]
    exact (h.uses _ _ (slide_at V k 0 ht H)).trans (h.uses _ _ (slides_cover _ _ ht hm))
  rw [← funext hx]; exact hs.comp L.contDiff

lemma placed_cont (h : Affordable S j u) (hn : FitsIn S n) (o : Site n) : Continuous (places o u) :=
  left_cont _ fun U => ((h.fitted 0 hn o) [] le_rfl U).continuous.continuousAt

lemma cont (h : Affordable S j u) : Continuous u := by
  obtain ⟨n,hn⟩:=someFits S
  rw [← funext (fromAbove h.uses hn (0:Site n))]; exact (h.placed_cont hn _).comp (above_cont _)

private lemma scales {v : Config G n → F} {D : Directions G n → Prop} {Z : Config G n → Prop}
    {k : ℕ} {c : ℝ} (h : LeftBound k D Z 1 c v) (t : ℝ) (ht : 0 ≤ t) :
    LeftBound k D Z 1 (t*c) fun U => t • v U := by
  let L := t • ContinuousLinearMap.id ℝ F
  refine ⟨h.smooth.postcomp L,mul_nonneg ht h.nonneg,fun l hl ha U hU => ?_⟩
  have hp := h.bound l hl ha U hU
  rw [one_pow,mul_one] at hp ⊢
  change ‖leftDerivs (fun U => L (v U)) l U‖ ≤ _
  rw [left_linear h.smooth L hl]; change ‖t • leftDerivs v l U‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg ht]; exact mul_le_mul_of_nonneg_left hp ht

lemma budget_slope (h : Affordable S j u) {e : Edge Cover} (he : e.1∈S) (a : G.Color) (ha : ‖a‖ ≤ 1) :
    Affordable S (j-1) (slope e a u) := by
  refine ⟨slopes_cover h.uses he a,fun k P => ?_⟩
  obtain ⟨c,hc,H⟩ := h.paid (k+1) P
  refine ⟨c,hc,fun n hn b hb o => ?_⟩
  have hu := H n hn b hb o
  let i := edgeAt e o
  let t := b.threshold
  have ht : 0<t := b.threshold_pos
  let D : Directions G n := t • Pi.single i a
  have hD : b.dirBound o D := by
    intro y
    by_cases h : y=i
    · subst y
      simp only [D, Pi.smul_apply, Pi.single_eq_same]
      rw [norm_smul,Real.norm_of_nonneg ht.le]
      exact (mul_le_of_le_one_right ht.le ha).trans (le_mul_of_one_le_right ht.le (one_le_pow₀ (by simp)))
    have hx : D y=0 := by simp [D,h]
    rw [hx,norm_zero]; exact mul_nonneg ht.le (by positivity)
  have hh (U : Config G n) : leftDerivs (places o u) [D] U = t • slope i a (places o u) U := by
    simp only [leftDerivs, slope]
    simp_rw [slide_increments]
    have he := deriv_comp_mul_left t (fun x : ℝ => places o u (increment U (x • (Pi.single i a)))) 0
    rw [mul_zero] at he; rw [← he]
    dsimp only [D]; simp_rw [mul_smul, smul_comm _ t]
  have hq (U : Config G n) : slope i a (places o u) U = t⁻¹ • leftDerivs (places o u) [D] U := by rw [hh, inv_smul_smul₀ ht.ne']
  rw [← slopes_at h.uses hn o he, funext hq,zpow_sub₀ ht.ne', zpow_one,show c*(b.threshold^j/b.threshold) = t⁻¹ * (c*t^j*1) by unfold t; ring]
  exact scales (hu.inner_derivative zero_le_one hD) t⁻¹ (by positivity)

lemma fitsFlow {f : CoverConfig G → ℂ} (h : Affordable S j f) (a : G.Color) (ha : ‖a‖ ≤ 1)
    (hn : FitsIn S n) {e : Edge Cover} (he : e.1∈ S) (o : Site n) : HasFlow (edgeAt e o) a (places o f) := by
  have hx := h.placed_cont hn o
  refine ⟨envelope_continuous hx,?_,fun U => ?_⟩
  · rw [slopes_at h.uses hn o he]; exact envelope_continuous ((h.budget_slope he a ha).placed_cont hn o)
  simp_rw [slide_increments]; exact ((h.fitted 0 hn o).has (l:=[]) (by simp) U _).differentiableAt
end Affordable
end YM.WardBin
