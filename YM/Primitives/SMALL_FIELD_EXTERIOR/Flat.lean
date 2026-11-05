import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import YM.Primitives.SMALL_FIELD_EXTERIOR.Identity



/-!
# Flat start for approximate Poisson solvability

We only need L²-approximation on **this box**, so don't need the full tensor
Fourier/Neumann basis results for the operator. Use elliptic images of
products of cosines and uniform density. No assumptions on positive dimension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} {n : ι → ℤ} {r : ℝ}

namespace Modes
-- Use integer frequencies for convenient product formulas.
def pace (r : ℝ) (k : ℤ) := k*(Real.pi/(2*r))
def bell (r : ℝ) (i : ι) (k : ℤ) : Points ι → ℝ := fun x => Real.cos (pace r k * (x i+r))
def melody (r : ℝ) (n : ι → ℤ) (s : Finset ι) : Points ι → ℝ := ∏ i∈s, bell r i (n i)
omit [DecidableEq ι] in
lemma bell_smooth (r : ℝ) (i : ι) (k : ℤ) : ContDiff ℝ ω (bell r i k) := by
  unfold bell; fun_prop
lemma melody_smooth (r : ℝ) (n : ι → ℤ) (s : Finset ι) : ContDiff ℝ ω (melody r n s) := by
  induction s using Finset.induction with
  | empty => simp only [melody, Finset.prod_empty]; exact contDiff_const
  | insert i s hi ih => unfold melody; rw [Finset.prod_insert hi]; exact (bell_smooth ..).mul ih

-- projection then scalar differentiation
private lemma projected (i j : ι) {f : ℝ → ℝ} {z : ℝ} {x : Points ι} (hf : HasDerivAt f z (x i)) :
    pc j (fun x : Points ι => f (x i)) x=z* Pi.single (M:=fun _ => ℝ) j (1:ℝ) i := by
  let F : Points ι →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hp : HasFDerivAt f _ (F x) := hf.hasFDerivAt
  change fderiv ℝ (f ∘ F) x _=_
  rw [(hp.comp x F.hasFDerivAt).fderiv]; simp [F,mul_comm]

def tolling (r : ℝ) (i : ι) (k : ℤ) := fun x : Points ι => -Real.sin (pace r k*(x i+r))*pace r k
private lemma slope (r : ℝ) (i j : ι) (k : ℤ) (x : Points ι) : pc j (bell r i k) x = tolling r i k x * (Pi.single (M:=fun _ => ℝ) j (1:ℝ) i) := by
  apply projected i j (f:=fun a : ℝ => Real.cos (pace r k * (a+r)))
  simpa only [tolling,mul_one] using (((hasDerivAt_id' _).add_const r).const_mul (pace r k)).cos
private lemma slope' (r : ℝ) (i j : ι) (k : ℤ) (x : Points ι) :
    pc j (tolling r i k) x = -(pace r k ^2) * bell r i k x * (Pi.single (M:=fun _ => ℝ) j (1:ℝ) i) := by
  apply projected i j (f:=fun a : ℝ => -Real.sin (pace r k * (a+r))*pace r k)
  convert! (((((hasDerivAt_id' (x i)).add_const r).const_mul (pace r k)).sin).neg.mul_const (pace r k)) using 1
  unfold bell; ring
private lemma ignore (s : Finset ι) (hi : i∉s) : pc i (melody r n s)=0 := by
  induction s using Finset.induction with
  | empty => simp only [melody, Finset.prod_empty]; exact pc_const _ _
  | insert j s hj ih =>
    have hh : j ≠ i ∧ i ∉ s := by simpa [eq_comm] using hi
    rw [show melody r n (insert j s) = bell r j (n j)*melody r n s from Finset.prod_insert hj]
    funext x
    rw [pc_mul _ ((bell_smooth ..).differentiable (by simp) _) ((melody_smooth ..).differentiable (by simp) _), ih hh.2]
    simp [slope,hh.1]
lemma anywhere (i : ι) : melody r n Finset.univ= melody r n (Finset.univ.erase i) * bell r i (n i) :=
  (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
lemma here (i : ι) : pc i (melody r n Finset.univ) = melody r n (Finset.univ.erase i) * tolling r i (n i) := by
  nth_rw 1 [anywhere i]
  funext x
  rw [pc_mul _ ((melody_smooth ..).differentiable (by simp) _) ((bell_smooth ..).differentiable (by simp) _),ignore (Finset.univ.erase i) (by simp)]
  simp [slope]

omit [Fintype ι] [DecidableEq ι] in
lemma face {x : Points ι} (hr : 0 < r) (hx : |x i|=r) (k : ℤ) : tolling r i k x=0 := by
  unfold tolling
  rcases abs_cases (x i) with ⟨he,hh⟩ | ⟨he,hh⟩
  · rw [he] at hx
    rw [hx,show pace r k*(r+r)=(k:ℝ)*Real.pi from ?_, Real.sin_int_mul_pi]; ring
    unfold pace; field_simp; ring
  rw [he] at hx; rw [show x i= -r by linarith]; simp
lemma neumann (hr : 0 < r) (n : ι → ℤ) : Neumann r (melody r n Finset.univ) := by
  refine ⟨melody_smooth ..,fun i x _ hx => ?_,fun i j h x _ hx => ?_⟩
  · rw [here, Pi.mul_apply,face hr hx,mul_zero]
  rw [pc_comm i j ((melody_smooth ..).contDiffAt.of_le le_top), here i, pc_mul j ((melody_smooth ..).differentiable (by simp) _) (by unfold tolling; fun_prop), slope', face hr hx]
  simp [h]
lemma struck (r : ℝ) (n : ι → ℤ) : elliptic 0 (melody r n Finset.univ)=(∑ i, pace r (n i)^2) • melody r n Finset.univ := by
  unfold elliptic; rw [Finset.sum_smul]; refine Finset.sum_congr rfl fun i _ => funext fun x => ?_
  have hc : pc i (0:Points ι → ℝ)=0 := pc_const i 0
  rw [row, hc, zero_mul, zero_sub, here i]
  simp only [Pi.neg_apply,Pi.smul_apply,smul_eq_mul,pc_mul i ((melody_smooth ..).differentiable (by simp) x)
    (show DifferentiableAt ℝ (tolling r i (n i)) x by unfold tolling; fun_prop), slope', ignore (i:=i) (Finset.univ.erase i) (by simp)]
  rw [anywhere i]; simp; ring

abbrev MC (r : ℝ) (ι : Type) [Fintype ι] := ContinuousMap (cube ι r) ℝ

def tone (r : ℝ) (n : ι → ℤ) : MC r ι := ⟨fun x => melody r n Finset.univ x.val,
  (melody_smooth ..).continuous.comp continuous_subtype_val⟩

def note (r : ℝ) (i : ι) : MC r ι := ⟨fun x => bell r i 1 x.val, (bell_smooth ..).continuous.comp continuous_subtype_val⟩
private def chorus (r : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] := Submodule.span ℝ (Set.range (@tone ι _ _ r))
private def opus (r : ℝ) (ι : Type) [Fintype ι] [DecidableEq ι] := Algebra.adjoin ℝ (Set.range (@note ι _ r))
lemma combine (i : ι) (n : ι → ℤ) (r : ℝ) :
    note r i * tone r n = (1/2:ℝ) • (tone r (Function.update n i (n i+1))+tone r (Function.update n i (n i-1))) := by
  ext x
  have he a : melody r (Function.update n i a) (Finset.univ.erase i)=melody r n (Finset.univ.erase i) :=
    Finset.prod_congr rfl (fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
  change bell r i 1 x.val * melody r n Finset.univ x.val = (1/2:ℝ)*(melody r _ Finset.univ x.val+melody r _ Finset.univ x.val)
  rw [anywhere (n:=n) i,anywhere (n:=Function.update n i (n i+1)) i,anywhere (n:=Function.update n i (n i-1)) i,he,he]
  let A := pace r (n i)*(x.val i+r)
  let B := pace r 1*(x.val i+r)
  simp only [Pi.mul_apply, bell,Function.update_self]
  rw [show pace r (n i+1)*(x.val i+r)=A+B by unfold A B pace; push_cast; ring,
    show pace r (n i-1)*(x.val i+r)=A-B by unfold A B pace; push_cast; ring,
    Real.cos_add,Real.cos_sub]
  unfold A B; ring
lemma tone_zero (r : ℝ) : tone r (0 : ι→ℤ)=1 := by ext x; change melody r _ _ _=1; simp [melody,bell,pace]
private lemma included (n : ι → ℤ) : tone r n ∈ chorus r ι := Submodule.subset_span ⟨n,rfl⟩
private lemma multiply (i : ι) {f : MC r ι} (hf : f∈chorus r ι) : note r i * f ∈ chorus r ι := by
  refine Submodule.span_induction (x:=f) (p:=fun f _ => note r i*f∈chorus r ι) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨n,rfl⟩; rw [combine]; exact (chorus r ι).smul_mem _ ((chorus r ι).add_mem (included _) (included _))
  · rw [mul_zero]; exact (chorus r ι).zero_mem
  · intro a b ha hb he hh; rw [mul_add]; exact (chorus r ι).add_mem he hh
  intro c f ha he; rw [mul_smul_comm]; exact (chorus r ι).smul_mem c he
private lemma from_opus {f : MC r ι} (hf : f∈opus r ι) : f ∈ chorus r ι := by
  have he : ∀ g∈chorus r ι, f*g∈chorus r ι := by
    refine Algebra.adjoin_induction (p := fun f _ => ∀ g∈chorus r ι,f*g∈chorus r ι) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨i,rfl⟩ g hg; exact multiply i hg
    · intro c g hg; rw [← Algebra.smul_def]; exact (chorus r ι).smul_mem c hg
    · intro a b ha hb ea eb g hg; rw [add_mul]; exact (chorus r ι).add_mem (ea _ hg) (eb _ hg)
    intro a b ha hb ea eb g hg; rw [mul_assoc]; exact ea _ (eb _ hg)
  simpa only [mul_one] using he 1 ((tone_zero r (ι:=ι)) ▸ included 0)
private lemma clear (hr : 0 < r) : (opus r ι).SeparatesPoints := by
  intro x y hne
  obtain ⟨i,hi⟩ : ∃ i, x.val i ≠ y.val i := by
    by_contra! he; exact hne (Subtype.ext (funext he))
  have hp : 0 < pace r 1 := by unfold pace; positivity
  let θ (z : cube ι r) := pace r 1*(z.val i + r)
  have ht (z) : θ z ∈ Icc 0 Real.pi := by
    obtain ⟨hl,hh⟩ := abs_le.mp ((cube_iff hr.le).1 z.property i)
    exact ⟨mul_nonneg hp.le (by linarith),
      (mul_le_mul_of_nonneg_left (show z.val i+r ≤ 2*r by linarith) hp.le).trans_eq (by unfold pace; field_simp; simp)⟩
  refine ⟨_,⟨note r i,(show note r i ∈ opus r ι from Algebra.subset_adjoin (mem_range_self i)),rfl⟩, ?_⟩
  change Real.cos (θ x) ≠ Real.cos (θ y)
  intro hx
  have hw := mul_left_cancel₀ hp.ne' (Real.strictAntiOn_cos.injOn (ht x) (ht y) hx)
  exact hi (add_right_cancel hw)

private def rendered (f : MC r ι) := ∃ u, Neumann r u ∧ ∃ c : ℝ, ∀ x : cube ι r,
    f x=elliptic 0 u x.val+c
private lemma reached (hr : 0 < r) (n : ι → ℤ) : rendered (tone r n) := by
  by_cases h : n=0
  · subst n; rw [tone_zero]
    refine ⟨0, Neumann.const 0,1,fun x => ?_⟩; rw [elliptic_zero]; simp
  let m := melody r n Finset.univ; let C : ℝ := ∑ i,pace r (n i)^2
  have hm := neumann hr n
  have hC : 0 < C := by
    apply Finset.sum_pos' (fun i _ => sq_nonneg _)
    obtain ⟨i,hi⟩ : ∃ i,n i ≠ 0 := by by_contra! hx; exact h (funext hx)
    have hp : pace r (n i) ≠ 0 := mul_ne_zero (by exact_mod_cast hi) (by positivity)
    exact ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hp⟩
  refine ⟨C⁻¹ • m,hm.smul _,0,fun x => ?_⟩
  rw [elliptic_smul _ hm, struck]
  change m x.val=C⁻¹*(C*m x.val)+0; field_simp; simp
private lemma performed (hr : 0 < r) (f : MC r ι) (hf : f∈chorus r ι) : rendered f := by
  refine Submodule.span_induction (p:=fun f _ => rendered f) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨g,rfl⟩; exact reached hr g
  · refine ⟨0, Neumann.const 0,0,fun x => ?_⟩; simp [elliptic_zero]
  · rintro a b ha hb ⟨u,hu,c,hc⟩ ⟨v,hv,d,hd⟩
    refine ⟨u+v,hu.add hv,c+d,fun x => ?_⟩
    change a x + b x = _; rw [hc,hd,elliptic_add _ hu hv,Pi.add_apply]; ring
  rintro d f hf ⟨u,hu,c,hc⟩
  refine ⟨d • u,hu.smul _,d*c,fun x => ?_⟩
  change d*(f x)=_; rw [hc,elliptic_smul _ hu]; change _=d*(elliptic 0 u x.val)+_; ring

/-- Continuous-on square data f. Approximants actually in the image of Neumann
class plus arbitrary constant. -/
lemma plays (hr : 0 < r) {f : Points ι → ℝ} (hf : ContinuousOn f (cube ι r)) {ε : ℝ} (he : 0 < ε) :
    ∃ u, Neumann r u ∧ ∃ c : ℝ, ∀ x∈cube ι r, |f x-(elliptic 0 u x+c)| ≤ ε := by
  letI : CompactSpace (cube ι r) := isCompact_iff_compactSpace.mp (cube_compact r)
  obtain ⟨g,hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints (opus r ι) (clear hr)
    _ (continuousOn_iff_continuous_restrict.mp hf) ε he
  obtain ⟨u,hu,c,hc⟩ := performed hr g.val (from_opus g.property)
  refine ⟨u,hu,c,fun x hx => ?_⟩
  let z : cube ι r := ⟨x,hx⟩
  change |f z.val-(elliptic 0 u z.val+c)| ≤ ε
  rw [← hc z,abs_sub_comm]; exact (hg z).le
end Modes

/-- Approximation up to arbitrary L² error (in the flat norm), for a
forcing function defined and continuous on the box. Include an arbitrary
constant shift; the elliptic image itself will have tilted mean zero. -/
def Approximate (r : ℝ) (V : Points ι → ℝ) := ∀ f : Points ι → ℝ, ContinuousOn f (cube ι r) → ∀ ε : ℝ, 0 < ε →
    ∃ u, Neumann r u ∧ ∃ c : ℝ,size r 0 (f-(elliptic V u+(fun _ => c))) ≤ ε

lemma approximate_flat (hr : 0 < r) : Approximate (ι:=ι) r 0 := by
  intro f hf ε he
  let m := size r (0:Points ι → ℝ) 1
  have hm : 0 ≤ m := size_nn ..
  let k := ε/(m+1)
  have hk : 0 < k := by unfold k; positivity
  obtain ⟨u,hu,c,hc⟩ := Modes.plays hr hf hk
  refine ⟨u,hu,c,?_⟩
  let F : Points ι → ℝ := elliptic 0 u+fun _ => c
  have hF : ContinuousOn F (cube ι r) := (hu.elliptic1 (Regular.coefficient 0)).cOn.add continuousOn_const
  calc
    size r 0 (f-F) ≤ k*m := size_le_mul continuousOn_const (hf.sub hF) (show ContinuousOn (1:Points ι → ℝ) _ from continuousOn_const) hk.le
      (fun x hx => by simpa [F] using hc x hx)
    _ ≤ k*(m+1) := mul_le_mul_of_nonneg_left (by linarith) hk.le
    _ = ε := div_mul_cancel₀ _ (by positivity)
end YM.Primitives.SmallFieldExterior
