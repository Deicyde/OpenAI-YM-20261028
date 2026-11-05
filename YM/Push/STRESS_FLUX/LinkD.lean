import YM.Next.FOUNDATIONS.SU2
import YM.Push.STRESS_FLUX.Force
import YM.Work.B04
import YM.Work.B06
import YM.Work.G07.Stencil

/-! Directed variations on the Wilson tori. A small regularity calculus and pullback/locality
formulas for the contact terms. Includes regularity of the genuine cutoff field `Family.O`
(polynomial on the *physical* links before doing any steps). No differentiation of the masks
in a `Format`. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Lattice Wilson Source Function Set Gauge MeasureTheory Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side}
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {f g : Config G n → V}

-- Always the *left* variation from the perspective of the specified read.
def Dlink (x : Site n) (d : Step) (c : G.Color) (f : Config G n → V) (U : Config G n) :=
    deriv (fun t : ℝ => f (bump x d c t U)) 0
structure RegularD (f : Config G n → V) : Prop where
  cont : Continuous f
  regular (x : Site n) (d : Step) : ∃ q : Config G n → G.Color →ₗ[ℝ] V, ∀ c : G.Color,
    Continuous (fun U => q U c) ∧ ∀ U, HasDerivAt (fun t : ℝ => f (bump x d c t U)) (q U c) 0

def RegularD.linear (h : RegularD f) (x : Site n) (d : Step) := (h.regular x d).choose
lemma RegularD.linear_eq (h : RegularD f) (x : Site n) (d : Step) (U : Config G n) (c : G.Color) :
    h.linear x d U c = Dlink x d c f U := (((h.regular x d).choose_spec c).2 U).deriv.symm
@[fun_prop] theorem RegularD.contD (h : RegularD f) (x : Site n) (d : Step) (c : G.Color) : Continuous (Dlink x d c f) := by
  simp_rw [show Dlink x d c f = fun U => h.linear x d U c from funext fun _ => (h.linear_eq ..).symm]; exact ((h.regular x d).choose_spec c).1
lemma RegularD.has (h : RegularD f) (x : Site n) (d : Step) (U : Config G n) (c : G.Color) :
    HasDerivAt (fun t : ℝ => f (bump x d c t U)) (Dlink x d c f U) 0 := by rw [← h.linear_eq]; exact ((h.regular x d).choose_spec c).2 U
lemma RegularD.const (v : V) : RegularD fun _ : Config G n => v := ⟨continuous_const,fun _ _ =>
  ⟨fun _ => 0,fun _ => ⟨continuous_const,fun _ => hasDerivAt_const ..⟩⟩⟩
lemma RegularD.add (hf : RegularD f) (hg : RegularD g) : RegularD (fun U => f U + g U) :=
  ⟨hf.cont.add hg.cont, fun x d => ⟨hf.linear x d + hg.linear x d,fun c => by
    simp only [Pi.add_apply,LinearMap.add_apply,RegularD.linear_eq]
    exact ⟨(hf.contD ..).add (hg.contD ..), fun U => (hf.has x d U c).add (hg.has x d U c)⟩⟩⟩

lemma RegularD.post (h : RegularD f) (L : V →L[ℝ] W) : RegularD (fun U => L (f U)) :=
  ⟨L.continuous.comp h.cont,fun x d => ⟨fun U => L.toLinearMap.comp (h.linear x d U), fun c => by
    simp only [LinearMap.comp_apply,ContinuousLinearMap.coe_coe, RegularD.linear_eq]
    exact ⟨L.continuous.comp (h.contD ..),fun U => L.hasFDerivAt.comp_hasDerivAt 0 (h.has x d U c)⟩⟩⟩
lemma RegularD.sub (hf : RegularD f) (hg : RegularD g) : RegularD (fun U => f U - g U) := by simp_rw [sub_eq_add_neg]; exact hf.add (hg.post (- ContinuousLinearMap.id ℝ V))
lemma RegularD.scale (hf : RegularD f) (c : ℝ) : RegularD (fun U => c • f U) := hf.post (c • ContinuousLinearMap.id ℝ V)

lemma RegularD.bilin {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (L : V →L[ℝ] W →L[ℝ] Z)
    {g : Config G n → W} (hf : RegularD f) (hg : RegularD g) : RegularD (fun U => L (f U) (g U)) := by
  refine ⟨(L.continuous.comp hf.cont).clm_apply hg.cont,fun x d => ?_⟩
  refine ⟨fun U => ((L.flip (g U)).toLinearMap ∘ₗ hf.linear x d U) + ((L (f U)).toLinearMap ∘ₗ hg.linear x d U),fun c => ?_⟩
  simp only [LinearMap.add_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,RegularD.linear_eq,ContinuousLinearMap.flip_apply]
  refine ⟨((L.continuous.comp (hf.contD ..)).clm_apply hg.cont).add ((L.continuous.comp hf.cont).clm_apply (hg.contD ..)),fun U => ?_⟩
  simpa only [Function.comp_def,bump_zero] using! ((L.hasFDerivAt.comp_hasDerivAt 0 (hf.has x d U c)).clm_apply (hg.has x d U c))

lemma RegularD.mul {M : Type*} [NormedRing M] [NormedAlgebra ℝ M] {f g : Config G n → M} (hf : RegularD f) (hg : RegularD g) :
    RegularD (fun U => f U * g U) := RegularD.bilin (ContinuousLinearMap.mul ..) hf hg
lemma regular_prod {M ι : Type*} [NormedCommRing M] [NormedAlgebra ℝ M] {s : Finset ι} {A : ι → Config G n → M} (h : ∀ i∈s, RegularD (A i)) :
    RegularD fun U => ∏ i∈s, A i U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact RegularD.const 1
  | insert i t hi ih => simp_rw [Finset.prod_insert hi]; exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))


lemma regular_link (e : Edge (Site n)) : RegularD fun U : Config G n => G.mat (U e) := by
  refine ⟨by fun_prop,fun x d => ?_⟩
  by_cases he : e = d.used x
  · let Y (U : Config G n) := G.mat (U e)
    let m := LinearMap.mul ℝ G.Mat
    have hd (c : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • c))) (G.colorMat c) 0 := by
      simp only [G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat c) (0:ℝ)
    cases h : d.neg
    · refine ⟨fun U => (m.flip (Y U)).comp G.colorMat, fun c => ⟨show Continuous (fun U : Config G n => G.colorMat c * G.mat (U e)) by fun_prop,fun U => ?_⟩⟩
      simp only [bump, modify,if_pos he,h,Bool.false_eq_true,if_false,G.mat_mul]; exact (hd c).mul_const _
    refine ⟨fun U => (m (Y U)).comp (-G.colorMat), fun c => ⟨show Continuous (fun U : Config G n => G.mat (U e) * -(G.colorMat c)) by fun_prop,fun U => ?_⟩⟩
    simp only [bump,modify,if_pos he,h, if_true, G.mat_mul,G.mat_inv]
    exact ((hd c).star.const_mul _).congr_deriv (by rw [G.colorMat_skew]; rfl)
  refine ⟨fun U => 0, fun c => ⟨continuous_const,fun U => ?_⟩⟩
  simp_rw [bump, modify,if_neg he]; apply hasDerivAt_const
lemma regular_inv {f : Config G n → G.El} (hf : RegularD fun U => G.mat (f U)) : RegularD fun U => G.mat (f U)⁻¹ := hf.post (starL' ℝ).toContinuousLinearMap
lemma regular_travel (x : Site n) (w : Walk) : RegularD fun U : Config G n => G.mat (travel U x w) := by
  induction w generalizing x with
  | nil => exact RegularD.const 1
  | cons d w ih =>
    have ht : RegularD fun U : Config G n => G.mat (d.read U x) := by dsimp only [Step.read]; split; exact regular_inv (regular_link _); exact regular_link _
    exact ht.mul (ih _)
lemma regular_plate (x : Site n) (a b : Step) : RegularD (fun U : Config G n => plate U x a b) :=
    ((((regular_travel ..).sub (regular_inv (regular_travel ..))).scale (1/2:ℝ)).post G.projectColor.toContinuousLinearMap)

lemma regular_places {d : ℕ} {F : Labels.Frame G d} (D : SectionData F) (v : F.Coeff) (o : Site n) : RegularD (D.places v o) := by
  have he (k : Index G D.stencil) : RegularD fun U => Source.entry (expandAt o U) k := by
    unfold Source.entry; split
    · exact ((regular_link (wrap n k.1.val.1 + o,k.1.val.2)).post ((Matrix.entryLinearMap ℝ ℂ k.2.1 k.2.2.1).toContinuousLinearMap)).post
        (starL' ℝ (A:=ℂ)).toContinuousLinearMap
    exact (regular_link (wrap n k.1.val.1 + o,k.1.val.2)).post ((Matrix.entryLinearMap ℝ ℂ k.2.1 k.2.2.1).toContinuousLinearMap)
  have hp (p : Formula G D.stencil) : RegularD fun U => MvPolynomial.aeval (entry (expandAt o U)) p := by
    induction p using MvPolynomial.induction_on with
    | C a => simp only [MvPolynomial.aeval_C,Algebra.algebraMap_self_apply]; exact RegularD.const a
    | add => simp only [map_add]; apply RegularD.add <;> assumption
    | mul_X p i hp => simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (he _)
  exact hp _
lemma regular_O (C : Family G) (N p d : ℕ) (t : C.label d) (x : Site (C.side N p)) : RegularD (C.O N p (d:=d) t x) := by
  unfold Family.O TransferData.cylinder initial
  exact (RegularD.const (_:ℂ)).mul (regular_places ..)
lemma regular_word (C : Family G) (N p : ℕ) {ι : Type*} (t : ι → C.book.Token) (x : ι → Site (C.side N p)) (s : Finset ι) :
    RegularD (fun U => ∏ i∈s, C.seen (t i) (x i) U) := regular_prod (fun _ _ => regular_O ..)


lemma Dlink_off {x : Site n} {d : Step} {B : Set (Site n)} (h : LocalOn B f) (hs : x∉B ∨ x+d.vec∉B) (c U) : Dlink x d c f U = 0 := by
  have he : (fun t => f (bump x d c t U)) = fun _ => f U := by
    funext t; apply h; intro i hI hi
    have hq : i≠d.used x := by rintro rfl; unfold Step.used at hI hi; unfold Step.vec at hs; split at hI <;> simp_all [← sub_eq_add_neg]
    unfold bump modify; rw [if_neg hq]
  unfold Dlink; rw [he]; exact deriv_const ..

@[fun_prop] lemma continuous_modify (x : Site n) (d : Step) (t : G.El) : Continuous (modify x d t) := by
  refine continuous_pi fun e => ?_; unfold modify; split
  · split <;> fun_prop
  fun_prop
lemma prior_modify (x : Site n) (d : Step) (t : G.El) : MeasurePreserving (modify x d t) (prior G n) (prior G n) := by
  apply measurePreserving_pi (fun _ => G.probHaar) (fun _ => G.probHaar) (f:=fun e y => if e=d.used x then (if d.neg then y*t⁻¹ else t*y) else y)
  intro e; split
  · split; exact measurePreserving_mul_right G.probHaar _; exact measurePreserving_mul_left G.probHaar _
  exact MeasurePreserving.id _
















end YM.StressFlux
