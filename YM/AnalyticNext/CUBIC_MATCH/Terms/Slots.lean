import YM.AnalyticNext.CUBIC_MATCH.Terms.Normal
import YM.AnalyticNext.CUBIC_MATCH.Terms.Products
import YM.Next.EXTRACTION.Tails
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Work.F02
import YM.Work.F03.Flat


set_option warningAsError false

/-!
# All terms through the uncut read

Real Taylor tests on signed channels. The gauge transport pays `W.ell`
using all its own paths. We never take analytic terms through any hard
cutoff. Scalar here excludes loops (even though they matter in the next
calculations). Local analytic justifications on actual curves can depend on
period. These formulae will then allow the uniform cost analysis separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function RG Wilson Lattice Tree Precision Exterior Metric Work.F02 Work.F03 Bid
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n c : Side}
  {σ C Λ : ℝ} {W : PathData G} {p : Clip} {k j : ℕ}
section terms
variable {U : ℝ → Config G n} {b : Face (Per n)} {A : ℕ → Atom G k}



lemma atom_story (hσ : 0 < σ) (h : SumBudget (fun i => (A i).budget σ) C)
    (x : Site n) (hf : ∀ i, ContDiffAt ℝ ω (fun s => G.mat (U s i)) 0) :
    HasSum (fun i => term j (fun t => (A i).unmasked (U t) x))
      (term j fun t => ∑' i,(A i).unmasked (U t) x) := by
  let a := fun t => physical (U t)
  let L i := atomExt (A i) x
  have he i z (hp : z∈ball (a 0) (radius σ)) := atomExt_bound (A i) (U 0) hσ z (ball_subset_closedBall hp) x
  have hh := compose_series j Complex.reCLM a (physical_contDiffAt hf) (radius_pos hσ) (f:=L)
    (fun i => atomExt_contDiff (A i) x) (h.2.1.mul_right _) he
  simp_rw [a,L,atomExt_real hσ h,atomExt_physical] at hh; exact hh

lemma atom_sum_smooth (hσ : 0 < σ) (h : SumBudget (fun i => (A i).budget σ) C)
    (x : Site n) (hf : ∀ i, ContDiffAt ℝ ω (fun s => G.mat (U s i)) 0) :
    ContDiffAt ℝ ω (fun t => ∑' i,(A i).unmasked (U t) x) 0 := by
  let a := fun t => physical (U t)
  let L (y : Ambient G n) := ∑' i,atomExt (A i) x y
  have he : ContDiffAt ℝ ω L (a 0) := (atomExt_series hσ h x (U 0)).contDiffAt.restrict_scalars ℝ
  have hp := Complex.reCLM.contDiff.contDiffAt.comp (0:ℝ) (he.comp _ (show ContDiffAt ℝ ω a 0 from physical_contDiffAt hf))
  have hh : Complex.reCLM ∘ (L ∘ a)=(fun t => ∑' i,(A i).unmasked (U t) x) := by
    funext t
    change Complex.reCLM (L (physical _))=_
    unfold L; rw [atomExt_real hσ h]; rfl
  rw [← hh]; exact hp

lemma slot_smooth (hf : ∀ i, ContDiffAt ℝ ω (fun s => G.mat (U s i)) 0) (b : Slot) (x : Site n) :
    ContDiffAt ℝ ω (fun t => b.atSite (U t) x) 0 := by
  have he : (fun t => b.atSite (U t) x) = fun t => colorReal G (slotExt b x (physical (U t))) := by
    funext t; rw [slotExt_physical,colorReal_up]
  rw [he]
  exact (colorReal G).contDiff.contDiffAt.comp _
    (((slotExt_contDiff b x (G:=G)).restrict_scalars ℝ).contDiffAt.comp _ (physical_contDiffAt hf))

lemma term_scaled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ) {g : ℝ → E} (h : ContDiffAt ℝ ω g 0) :
    term k (fun t => u • g t)=u • term k g := term_linear (u • ContinuousLinearMap.id ℝ E) (h.of_le le_top)

lemma test_ray (x : Dir G n) (i : Edge (Site n)) :
    ContDiffAt ℝ ω (fun t : ℝ => G.mat (represent (t • x) i)) 0 :=
  (represent_smooth i).contDiffAt.comp (f:=fun t : ℝ => t • x) 0 (by fun_prop)

lemma slot_first (a : Atom G k) (x : Site n) (d : Dir G n) :
    term k (fun s : ℝ => a.unmasked (represent (s • d)) x)=a.poly (fun i => faceCurl (slotFace (a.leg i) x) d) ∧
      ∀ j : ℕ, j < k → term j (fun s : ℝ => a.unmasked (represent (s • d)) x) = 0 := by
  let f (b : Fin k → G.ColorIndex) (i : Fin k) (t : ℝ) := (a.leg i).atSite (represent (t • d)) x (b i)
  have hg (b : Fin k → G.ColorIndex) i : ContDiffAt ℝ ω (f b i) 0 :=
    (ContinuousLinearMap.contDiff (PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) (b i))).contDiffAt.comp _
      (slot_smooth (U:=fun t : ℝ => represent (t • d)) (test_ray d) (a.leg i) x)
  have hf b i : f b i 0=0 := by
    unfold f; rw [zero_smul,atSite_path,show faceValue (represent (0:Dir G n)) (slotFace (a.leg i) x)=1 from YM.Push.stroll_zero ..,
      G.curvature_unit,map_zero]; rfl
  have hd b i : deriv (f b i) 0 = faceCurl (slotFace (a.leg i) x) d (b i) :=
    ((PiLp.proj (𝕜:=ℝ) 2 (fun _ => ℝ) (b i)).hasFDerivAt.comp_hasDerivAt 0 (slot_deriv (a.leg i) x d)).deriv
  have H b := rise_zero Finset.univ (f:=f b) (fun i _ => hg b i) (fun i _ => hf b i)
  simp only [Finset.card_univ,Fintype.card_fin,hd] at H
  have hp b : ContDiffAt ℝ ω (fun t => ∏ i,f b i t) 0 := contDiffAt_prod fun i _ => hg b i
  have hx j : term j (fun s : ℝ => a.unmasked (represent (s • d)) x)=
      ∑ b, a.coeff b * term j (fun t => ∏ i,f b i t) := by
    have hy b : ContDiffAt ℝ ω (fun t => a.coeff b • ∏ i,f b i t) 0 := (hp b).const_smul _
    refine (term_sum (k:=j) (g:=fun b t => a.coeff b • ∏ i,f b i t) (s:=Finset.univ) (fun b _ => (hy b).of_le le_top)).trans ?_
    exact Finset.sum_congr rfl fun b _ => term_scaled _ (hp b)
  constructor
  · rw [hx,Atom.poly]; exact Finset.sum_congr rfl fun b _ => congr_arg (a.coeff b * ·) (H b).2
  intro j hj; rw [hx]
  exact Finset.sum_eq_zero (fun b _ => by rw [(H b).1 j hj,mul_zero])

lemma preamble (hσ : 0<σ) (h : SumBudget (fun i => (A i).budget σ) C) (z : Dir G n) :
    term k (fun t : ℝ => uncut A (represent (t • z))) =
        ∑ x, ∑' i, (A i).poly (fun b => faceCurl (slotFace ((A i).leg b) x) z) ∧
      ∀ j,j<k → term j (fun t : ℝ => uncut A (represent (t • z)))=0 := by
  have he (x : Site n) (j : ℕ) := (atom_story (A:=A) (U:=fun t : ℝ => represent (t • z)) (j:=j) hσ h x (test_ray z)).tsum_eq
  have hh (j : ℕ) : term j (fun t : ℝ => uncut A (represent (t • z)))=∑ x : Site n,
      term j (fun t : ℝ => ∑' i, (A i).unmasked (represent (t • z)) x) := term_sum fun x _ =>
    (atom_sum_smooth (A:=A) (U:=fun t : ℝ => represent (t • z)) hσ h x (test_ray z)).of_le le_top
  constructor
  · rw [hh]; exact Finset.sum_congr rfl fun i _ => (he i k).symm.trans (tsum_congr fun a => (slot_first (A a) i z).1)
  intro j hj; rw [hh]
  apply Finset.sum_eq_zero; intro i _; rw [← he]; simp_rw [show ∀ b,
    term j (fun s : ℝ => (A b).unmasked (represent (s • z)) i)=0 from fun b => (slot_first (A b) i z).2 j hj]
  simp
end terms
end YM.CubicMatch
