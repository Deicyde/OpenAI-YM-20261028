import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import YM.Primitives.SMALL_FIELD_EXTERIOR.Cube


/-!
# Slicing the cube and the boundary terms

The variational proof uses Neumann probes. Here is the integration of a
single boundary differential (on the ACTUAL box, not inserting a smooth
multiplier), in arbitrary finite counting coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι]

/-- C^n germs at every point, *including faces*. No derivative norm
convention hidden in this condition. -/
def Regular (r : ℝ) (n : ℕ∞ω) (f : Points ι → ℝ) : Prop := ∀ x∈cube ι r, ContDiffAt ℝ n f x

variable {r c : ℝ} {n k : ℕ∞ω} {f g : Points ι → ℝ}
lemma Regular.mono (h : Regular r n f) (hk : k ≤ n) : Regular r k f := fun x hx => (h x hx).of_le hk
lemma Regular.coefficient (a : ℝ) : Regular r n (fun _ : Points ι => a) := fun _ _ => contDiffAt_const
lemma Regular.coordinate (i : ι) : Regular r n (fun x : Points ι => x i) := fun _ _ => contDiffAt_apply _ _ _ _
lemma Regular.cOn (h : Regular r n f) : ContinuousOn f (cube ι r) := fun x hx => (h x hx).continuousAt.continuousWithinAt
lemma Regular.diff (h : Regular r n f) (hn : n ≠ 0) {x} (hx : x∈cube ι r) : DifferentiableAt ℝ f x := (h x hx).differentiableAt hn
lemma Regular.add (h : Regular r n f) (h' : Regular r n g) : Regular r n (f+g) := fun x hx => (h x hx).add (h' x hx)
lemma Regular.mul (h : Regular r n f) (h' : Regular r n g) : Regular r n (f*g) := fun x hx => (h x hx).mul (h' x hx)
lemma Regular.sub (h : Regular r n f) (h' : Regular r n g) : Regular r n (f-g) := fun x hx => (h x hx).sub (h' x hx)

lemma Regular.smul (h : Regular r n f) (c : ℝ) : Regular r n (c • f) := fun x hx => contDiffAt_const.smul (h x hx)
lemma Regular.fsum {α : Type*} {f : α → Points ι → ℝ} (s : Finset α) (h : ∀ i∈s, Regular r n (f i)) :
    Regular r n (∑ i∈s, f i) := by
  rw [show (∑ i∈s, f i)=fun x => ∑ i∈s, f i x from funext fun x => Finset.sum_apply ..]
  exact fun x hx => ContDiffAt.sum (fun i hi => h i hi _ hx)

variable [DecidableEq ι]
def pc (i : ι) (f : Points ι → ℝ) (x : Points ι) := fderiv ℝ f x (Pi.single i 1)

lemma pcat (i : ι) {x : Points ι} (hf : ContDiffAt ℝ n f x) (hk : k+1 ≤ n) :
    ContDiffAt ℝ k (pc i f) x := (hf.fderiv_right hk).clm_apply contDiffAt_const
lemma Regular.pc' (h : Regular r n f) (hk : k + 1 ≤ n) (i : ι) : Regular r k (pc i f) := fun x hx => pcat i (h x hx) hk
lemma Regular.tangent (h : Regular r 2 f) (i : ι) : Regular r 1 (pc i f) := h.pc' (by norm_num) _
lemma Regular.tangent_continuous (h : Regular r 1 f) (i : ι) : ContinuousOn (pc i f) (cube ι r) := (h.pc' (k:=0) (by simp) _).cOn
lemma pc_pc (i j : ι) {x : Points ι} (hf : ContDiffAt ℝ 2 f x) :
    pc i (pc j f) x = fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) := by
  let L := ContinuousLinearMap.apply ℝ ℝ (Pi.single (M:=fun _ => ℝ) j 1)
  have he := ((hf.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero)
  have ht : pc j f=L ∘ fderiv ℝ f := rfl
  rw [ht,pc,fderiv_comp _ L.differentiableAt he, L.fderiv]; rfl
lemma pc_comm (i j : ι) {x : Points ι} (hf : ContDiffAt ℝ 2 f x) : pc i (pc j f) x = pc j (pc i f) x := by
  rw [pc_pc i j hf,pc_pc j i hf]; exact hf.isSymmSndFDerivAt (by simp) _ _
lemma pc_plus (i : ι) {x : Points ι} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pc i (f+g) x=pc i f x+pc i g x := by rw [pc, fderiv_add hf hg]; rfl
lemma pc_minus (i : ι) {x : Points ι} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pc i (f-g) x=pc i f x-pc i g x := by rw [pc, fderiv_sub hf hg]; rfl
lemma pc_mul (i : ι) {x : Points ι} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pc i (f*g) x=f x*pc i g x+g x*pc i f x := by rw [pc, fderiv_mul hf hg]; rfl
lemma pc_smul (i : ι) (c : ℝ) {x : Points ι} (hf : DifferentiableAt ℝ f x) :
    pc i (c • f) x=c * pc i f x := by rw [pc, fderiv_const_smul hf]; rfl
lemma pc_exp_neg (i : ι) {x : Points ι} (hf : DifferentiableAt ℝ f x) :
    pc i (fun x => Real.exp (- f x)) x = - Real.exp (- f x) * pc i f x := by
  change pc i (Real.exp ∘ (-f)) x = _
  rw [pc, fderiv_comp _ Real.differentiableAt_exp hf.neg, fderiv_neg, ContinuousLinearMap.comp_apply,
    (Real.hasDerivAt_exp _).hasFDerivAt.fderiv]
  simp [pc]; ring
omit [Fintype ι] in
lemma pc_const (i : ι) (c : ℝ) : pc i (fun _ => c)=0 := by funext; simp [pc]
lemma pc_sum (i : ι) {x : Points ι} {α : Type*} (s : Finset α) {f : α → Points ι → ℝ}
    (h : ∀ i∈s,DifferentiableAt ℝ (f i) x) :
    pc i (∑ i∈s, f i) x=∑ j∈s, pc i (f j) x := by
  rw [show (∑ i∈s, f i)=fun x => ∑ i∈s, f i x from funext fun x => Finset.sum_apply ..,
    pc, fderiv_fun_sum h]
  simp [pc]

lemma faces_zero (hr : 0 ≤ r) (hf : Regular r 1 f) (i : ι)
    (h : ∀ x∈cube ι r, |x i|=r → f x=0) :
    (∫ x in cube ι r, pc i f x)=0 := by
  let I := Icc (-r) r
  let X := {j : ι // j=i}
  let Y := {j : ι // ¬j=i}
  let K := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) fun j => j=i
  let μ : Measure ℝ := volume.restrict I
  haveI : SigmaFinite μ := by unfold μ; infer_instance
  let ν : Measure (X → ℝ) := Measure.pi (fun _ => μ)
  let M : Measure (Y → ℝ) := Measure.pi (fun _ => μ)
  haveI : SFinite ν := inferInstanceAs (SFinite (Measure.pi (fun _ : X => μ)))
  haveI : SFinite M := inferInstanceAs (SFinite (Measure.pi (fun _ : Y => μ)))
  have he : Measure.pi (fun _ : ι => μ) = volume.restrict (cube ι r) := by rw [cube_pi hr]; exact (Measure.restrict_pi_pi ..).symm
  have ht : MeasurePreserving K (volume.restrict (cube ι r)) (ν.prod M) := by
    rw [← he]
    convert! measurePreserving_piEquivPiSubtypeProd (α:=fun _ : ι => ℝ) (fun _ => μ) (fun j => j=i) using 1
    unfold ν M
    congr
    apply Subsingleton.elim
  have hL := ht.symm
  have hi := (hL.integrable_comp_emb K.symm.measurableEmbedding (g:=pc i f)).mpr ((hf.tangent_continuous i).integrableOn_compact (cube_compact r))
  rw [← hL.integral_comp']
  change (∫ x, (pc i f ∘ K.symm) x ∂ν.prod M) = _
  rw [integral_prod_symm _ hi]
  have hm : M = volume.restrict (cube Y r) := by rw [cube_pi hr]; exact (Measure.restrict_pi_pi ..).symm
  rw [hm]
  refine (setIntegral_congr_fun (g:=fun _ => 0) (cube_meas _) (fun y hy => ?_)).trans (by simp)
  letI : Unique X := ⟨⟨⟨i,rfl⟩⟩, fun a => Subtype.ext a.property⟩
  let T := MeasurableEquiv.piUnique (fun _ : X => ℝ)
  have hu : MeasurePreserving T.symm μ ν := (measurePreserving_piUnique (fun _ : X => μ)).symm
  change (∫ x, pc i f (K.symm (x,y)) ∂ν) = 0
  rw [← hu.integral_comp' (fun x => pc i f (K.symm (x,y)))]
  let c : ℝ → Points ι := fun z => K.symm (T.symm z, y)
  change (∫ z in I, pc i f (c z)) = 0
  have hbase z : (c z) i = z := congr_fun (congr_arg Prod.fst (K.apply_symm_apply (T.symm z, y))) ⟨i,rfl⟩
  have hrest z (l : Y) : (c z) l.val = y l := congr_fun (congr_arg Prod.snd (K.apply_symm_apply (T.symm z, y))) l
  have ha z : c z=c 0+z • Pi.single i 1 := by
    funext j; by_cases hh : j=i
    · subst j; simp [hbase]
    let l : Y := ⟨j,hh⟩
    simp [hh,show c z j=y l from hrest z l,show c 0 j=y l from hrest 0 l]
  have hd z : HasDerivAt c (Pi.single i 1) z := by
    have hcomp : HasDerivAt (fun z : ℝ => c 0+z • Pi.single i (1:ℝ)) (Pi.single i 1) z := by
      convert! (hasDerivAt_const z (c 0)).add ((hasDerivAt_id' z).smul_const (Pi.single i 1)) using 1; simp
    rw [show c=(fun z : ℝ => c 0+z • Pi.single i (1:ℝ)) from funext ha]
    exact hcomp
  have hr' : -r ≤ r := by linarith
  have hb : MapsTo c I (cube ι r) := by
    intro z hz; apply (cube_iff hr).2
    intro j; by_cases e : j=i
    · subst j; rw [hbase]; exact abs_le.mpr hz
    let p : Y := ⟨j,e⟩
    exact (show c z j=y p from hrest z p) ▸ ((cube_iff hr).1 hy p)
  rw [show I=Icc (-r) r from rfl, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr']
  apply (intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=f ∘ c) _ _).trans
  · simp only [Function.comp_apply]
    rw [h (c r) (hb (right_mem_Icc.mpr hr')) (by rw [hbase,abs_of_nonneg hr]),
      h (c (-r)) (hb (left_mem_Icc.mpr hr')) (by rw [hbase,abs_neg,abs_of_nonneg hr]),sub_zero]
  · intro x hx; rw [uIcc_of_le hr'] at hx
    exact ((hf (c x) (hb hx)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt x (hd x)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hr' enorm_ne_top).mpr
  exact ((hf.tangent_continuous i).comp ((show Continuous c from continuous_iff_continuousAt.mpr
    fun z => (hd z).continuousAt).continuousOn) hb).integrableOn_Icc
end YM.Primitives.SmallFieldExterior
