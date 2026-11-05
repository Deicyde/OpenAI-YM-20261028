import YM.WilsonBulk.Series.Leib
import YM.Analysis.SmoothJets
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Branch log germ to Tape (formal only)

Real in chart coordinates z; display κ multiplied by direct inverse spaced
powers elsewhere. Includes mixed-derivative terms for branch transports, no
holomorphic gauge assumptions. Build directly from EXACT factorial policy
normalized `Analysis.D` available system. This supplies higher-order
coordinate rewriting inside finite Ward calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical BigOperators Topology ContDiff
open Analysis Finset Function PowerSeries Filter
variable {A E : Type} {α β : Type} [CommRing A] [Algebra ℝ A] [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype α]

abbrev Tabletop (α : Type) := α → ℝ
def spike (i : α) : Tabletop α := Pi.single i 1
omit [Fintype α] in
@[simp] lemma spike_proj (j i : α) : spike i j= if j=i then 1 else 0 := by simp [spike,Pi.single_apply]
lemma spike_all (x : Tabletop α) : x=∑ i,x i • spike i := by ext1 j; simp [Finset.sum_apply,mul_ite]
def leafD (i : α) := fun f : Tabletop α→E=> Analysis.D (spike i) f
variable {f g h : Tabletop α→ℝ} {n : ℕ} {T : Tape α}
lemma leaf_at (i : α) {f : Tabletop α→E} (h : ContDiffAt ℝ ω f 0) : ContDiffAt ℝ ω (leafD i f) 0 := Analysis.dSmooth h _ le_top
-- extraction stitches directly

def photo (f : Tabletop α→ℝ) (n : ℕ) : Page α n := fun v=> (n.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ n f 0 (spike ∘ v)
def ink (f : Tabletop α → ℝ) : Tape α := PowerSeries.mk fun n=> script (photo f n)
lemma ink_power (f : Tabletop α→ℝ) (n : ℕ) : coeff n (ink f)=script (photo f n) := coeff_mk ..
lemma ink_norm (f : Tabletop α→ℝ) : constantCoeff (ink f)= MvPolynomial.C (f 0) := by rw [← coeff_zero_eq_constantCoeff,ink_power,script_scalar]; simp [photo]
lemma photo_regular (hf : ContDiffAt ℝ ω f 0) (n : ℕ) : Regular (photo f n) := fun i=> funext fun v=>congr_arg _ (@Analysis.sym_Jet (Tabletop α) ℝ _ _ _ _ n f 0 (hf.of_le le_top) (spike ∘ v) i)
lemma trial (f : Tabletop α→ℝ) (hf : ContDiffAt ℝ ω f 0) (i : α) (n : ℕ) : photo (leafD i f) n = ((n+1:ℕ):ℝ) • margin (photo f (n+1)) i := by
  ext1 v; unfold photo margin leafD; simp only [Pi.smul_apply]; rw [← Analysis.cons_inner (hf.of_le (m:=↑(n+1:ℕ)) le_top),smul_smul]; congr 1
  · rw [Nat.factorial_succ]; push_cast; field_simp
lemma ink_player (hf : ContDiffAt ℝ ω f 0) (i : α) : player i (ink f)=X* ink (leafD i f) := by
  ext1 n; rw [player,parallel_D]; cases n with
  | zero=> rw [coeff_zero_X_mul,coeff_zero_eq_constantCoeff,ink_norm]; simp
  | succ j=> rw [ink_power,script_deriv _ (photo_regular hf _), coeff_succ_X_mul,ink_power,trial _ hf,script_scale]
-- Euler clock recurrence
lemma ink_time (hf : ContDiffAt ℝ ω f 0) : clockD _ (ink f)=∑ i:α,ink (leafD i f) * named i := by
  ext1 n; rw [clock_coeff]; simp only [map_sum,named,coeff_mul_C,ink_power]; rw [script_trace,Finset.smul_sum]; refine sum_congr rfl fun i _=> ?_; rw [trial _ hf,script_scale,mul_comm, smul_mul_assoc]
lemma ink_grade1 (hf : ContDiffAt ℝ ω f 0) : coeff 1 (ink f)= ∑ i,MvPolynomial.C (leafD i f 0)*MvPolynomial.X i := by
  have h:= congr_arg (fun p:Tape α=>constantCoeff p) (ink_time hf)
  rw [← coeff_zero_eq_constantCoeff,clock_coeff] at h
  simpa [← constantCoeff_eq, named,ink_norm] using! h
lemma ink_of (hf : f=ᶠ[𝓝 0] g) : ink f=ink g := by ext1 n; simp only [ink_power]; unfold photo; rw [(hf.iteratedFDeriv ℝ n).self_of_nhds]
lemma ink_const (r : ℝ) : ink (fun _ : Tabletop α=> r)= C (MvPolynomial.C r) := by
  ext1 n; cases n with
  | zero=> rw [coeff_zero_eq_constantCoeff_apply, ink_norm,coeff_zero_C]
  | succ n=> rw [ink_power, coeff_succ_C, show photo (fun _ : Tabletop α=>r) (n+1)=0 from by ext1 i; simp [photo, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _)],script_zero]
lemma ink_named (i : α) : ink (fun z : Tabletop α=>z i)=X*named i := by
  let P := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:α=>ℝ) i
  change ink P=_
  apply clock_unique
  · rw [ink_norm,map_zero,map_zero,map_mul,constantCoeff_X,zero_mul]
  rw [ink_time P.contDiff.contDiffAt]
  have he (j) : leafD j P = (fun _=> spike j i) := funext fun x=> by rw [leafD,D,P.fderiv]; rfl
  simp [he,ink_const,apply_ite,named,clock_X,clock_C]
-- generic ring operations on ω
lemma ink_add (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) : ink (f+g)=ink f+ink g := by
  ext1 n; rw [map_add,ink_power,ink_power,ink_power]; refine Eq.trans (congr_arg _ ?_) (script_plus ..)
  ext1 v; unfold photo; simp only [iteratedFDeriv_add_apply (hf.of_le (m:=n) le_top) (hg.of_le le_top), Pi.add_apply,_root_.add_apply,smul_add]
lemma ink_neg (f : Tabletop α→ℝ) : ink (-f)= - ink f := by
  ext1 n; rw [map_neg,ink_power,ink_power,show photo (-f) n=(-1:ℝ) • photo f n from ?_,script_scale]
  · simp
  ext1 i; simp [photo, iteratedFDeriv_neg]

lemma ink_mul (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) : ink (f*g)=ink f*ink g := by
  ext1 n; induction n using Nat.strong_induction_on generalizing f g with
  | h n ih=>
    cases n with
    | zero=> simp [ink_norm]
    | succ n=>
      have hs (i) : Steps (n+1) (ink (leafD i (f*g))) (ink (leafD i f)*ink g+ink f*ink (leafD i g)) := by
        rw [ink_of (g:=leafD i f*g+ f*leafD i g) ?_,ink_add (f:=leafD i f*g) (g:=f*leafD i g) ((leaf_at i hf).mul hg) (hf.mul (leaf_at i hg))]
        swap
        · filter_upwards [hf.eventually (by simp),hg.eventually (by simp)] with x hx hy; simp [leafD,D,fderiv_mul (hx.differentiableAt (by simp)) (hy.differentiableAt (by simp))]; ring
        exact Steps.add (fun j hj=> ih j hj (leaf_at i hf) hg) (fun j hj=> ih j hj hf (leaf_at i hg))
      refine smul_right_injective _ (show ((n+1:ℕ):ℝ)≠0 by positivity) ?_
      dsimp only
      rw [← clock_coeff,← clock_coeff, D_leib, ink_time (f:=f*g) (hf.mul hg),ink_time hf,ink_time hg,mul_sum,sum_mul,← sum_add_distrib]
      simp only [map_sum]; refine sum_congr rfl fun i _=>?_
      rw [← (show (ink (leafD i f)*ink g+ink f*ink (leafD i g))*named i = _+_ from ?xor)]
      exact Steps.mul (hs i) (Steps.self (p:=named i)) n (by omega)
      case xor => ring
lemma ink_sub (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) : ink (f-g)=ink f-ink g := by simp only [sub_eq_add_neg]; rw [ink_add (g:=-g) hf hg.neg, ink_neg]
lemma cont_diff_sum (s : Finset β) (F : β→Tabletop α→ℝ) (h : ∀ b∈s,ContDiffAt ℝ ω (F b) 0) : ContDiffAt ℝ ω (∑ i∈s,F i) 0 := by
  rw [show (∑ i∈s,F i)=(fun x =>∑ i∈s,F i x) from by ext; simp]
  exact ContDiffAt.sum h
lemma ink_sum (s : Finset β) (F : β→Tabletop α→ℝ) (h : ∀ b∈s,ContDiffAt ℝ ω (F b) 0) : ink (∑ i∈s,F i)=∑ i∈s,ink (F i) := by
  induction s using Finset.induction with
  | empty=> rw [sum_empty,sum_empty]; exact (ink_const 0).trans (by simp)
  | insert i s hi ih=> simp_rw [sum_insert hi]; have hx : ∀ b∈s,ContDiffAt ℝ ω (F b) 0:= fun _ k=> h _ (mem_insert_of_mem k); rw [ink_add (h _ (mem_insert_self ..)) (cont_diff_sum s F hx),ih hx]
end YM.WilsonBulk.Sheet
