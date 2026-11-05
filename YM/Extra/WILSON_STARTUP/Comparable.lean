import YM.Next.EXTRACTION.Tails
import YM.Work.B06
import YM.Work.G05.Taylor

/-!
# Finite jet equivalence of analytic germs in real chart coordinates

Calculus to specialize Kin.Planned to a more convenient top presentation
(startup-compatible). Does not use analyticity of a masked bulk.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Change
open Function Filter Precision Work
open scoped Topology BigOperators ContDiff Classical
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {k m : ℕ} {x : X}

structure Matches (k : ℕ) (F G : X → Y) (x : X) : Prop where
  left : ContDiffAt ℝ ω F x
  right : ContDiffAt ℝ ω G x
  jets : ∀ i ≤ k, iteratedFDeriv ℝ i F x = iteratedFDeriv ℝ i G x

variable {f g f₁ g₁ : X → Y} {u v : Y → Z} {s t : X → Z}

theorem Matches.value (h : Matches k f g x) : f x = g x := by simpa [Tensor.diagonal] using congr_arg (fun A => Tensor.diagonal A (0:X)) (h.jets 0 (Nat.zero_le _))

theorem Matches.unchanged (h : Matches k f g x) (hf : f =ᶠ[𝓝 x] f₁) (hg : g =ᶠ[𝓝 x] g₁) : Matches k f₁ g₁ x :=
  ⟨h.left.congr_of_eventuallyEq hf.symm,h.right.congr_of_eventuallyEq hg.symm,fun i hi =>
    ((hf.iteratedFDeriv ℝ i).self_of_nhds.symm.trans (h.jets i hi)).trans ((hg.iteratedFDeriv ℝ i).self_of_nhds)⟩

theorem matches_self (k : ℕ) (h : ContDiffAt ℝ ω f x) : Matches k f f x := ⟨h,h,fun _ _ => rfl⟩

theorem Matches.comp (h : Matches k u v (f x)) (hh : Matches k f g x) : Matches k (u ∘ f) (v ∘ g) x := by
  refine ⟨h.left.comp x hh.left,(hh.value ▸ h.right : ContDiffAt ℝ ω v (g x)).comp x hh.right,
    G05.jets_comp (hh.left.of_le le_top) (hh.right.of_le le_top) (h.left.of_le le_top) ?_ hh.value hh.jets ?_⟩
  · rw [← hh.value]; exact h.right.of_le le_top
  rw [← hh.value]; exact h.jets

theorem Matches.refl_comp (hh : Matches k f g x) (h : ContDiffAt ℝ ω u (f x)) : Matches k (u ∘ f) (u ∘ g) x :=
  (matches_self _ h).comp hh

theorem Matches.comp_refl (h : Matches k u v (f x)) (hh : ContDiffAt ℝ ω f x) : Matches k (u ∘ f) (v ∘ f) x :=
  h.comp (matches_self _ hh)

theorem Matches.prod (h : Matches k f g x) (hh : Matches k s t x) : Matches k (fun x => (f x,s x)) (fun x => (g x,t x)) x := by
  refine ⟨h.left.prodMk hh.left,h.right.prodMk hh.right,fun i hi => ?_⟩
  rw [iteratedFDeriv_prodMk h.left hh.left le_top,iteratedFDeriv_prodMk h.right hh.right le_top,h.jets i hi,hh.jets i hi]

theorem Matches.together (h : Matches k f g x) (hh : Matches k s t x) {H : Y → Z → ℝ}
    (he : ContDiffAt ℝ ω (uncurry H) (f x,s x)) : Matches k (fun x => H (f x) (s x)) (fun x => H (g x) (t x)) x :=
  (h.prod hh).refl_comp he

theorem Matches.add (h : Matches k f g x) (hh : Matches k f₁ g₁ x) : Matches k (f+f₁) (g+g₁) x :=
  (h.prod hh).refl_comp (u:=fun p : Y × Y => p.1+p.2) (contDiffAt_fst.add contDiffAt_snd)

theorem Matches.mul {f g f₁ g₁ : X → ℝ} (h : Matches k f g x) (hh : Matches k f₁ g₁ x) : Matches k (f*f₁) (g*g₁) x :=
  h.together hh (H:=(· * ·)) (contDiffAt_fst.mul contDiffAt_snd)

theorem matches_sum {ι : Type} {f g : ι → X → Y} (A : Finset ι) (h : ∀ i ∈ A, Matches k (f i) (g i) x) :
    Matches k (∑ i ∈ A,f i) (∑ i∈A,g i) x := by
  induction A using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact matches_self _ contDiffAt_const
  | insert i A hi ih => rw [Finset.sum_insert hi,Finset.sum_insert hi]; exact (h _ (by simp)).add (ih fun _ hv => h _ (by simp [hv]))

theorem matches_prod {ι : Type} {f g : ι → X → ℝ} (A : Finset ι) (h : ∀ i ∈ A, Matches k (f i) (g i) x) :
    Matches k (∏ i ∈ A,f i) (∏ i∈A,g i) x := by
  induction A using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact matches_self _ contDiffAt_const
  | insert i A hi ih => rw [Finset.prod_insert hi,Finset.prod_insert hi]; exact (h _ (by simp)).mul (ih fun _ hv => h _ (by simp [hv]))

theorem Matches.symm (h : Matches k f g x) : Matches k g f x := ⟨h.right,h.left,fun i hi => (h.jets i hi).symm⟩

theorem Matches.trans {u : X → Y} (h : Matches k f g x) (hh : Matches k g u x) : Matches k f u x :=
  ⟨h.left,hh.right,fun i hi => (h.jets i hi).trans (hh.jets i hi)⟩

theorem Matches.lower (h : Matches k f g x) (hh : m ≤ k) : Matches m f g x := ⟨h.left,h.right,fun i hi => h.jets i (hi.trans hh)⟩

theorem Matches.ahead (h : Matches (k+1) f g x) : Matches k (fderiv ℝ f) (fderiv ℝ g) x := by
  refine ⟨h.left.fderiv_right le_top,h.right.fderiv_right le_top,fun i hi => ?_⟩
  apply (continuousMultilinearCurryRightEquiv' ℝ i X Y).symm.injective
  simpa [iteratedFDeriv_succ_eq_comp_right] using h.jets (i+1) (by omega)

theorem Matches.behind (h : Matches k (fderiv ℝ f) (fderiv ℝ g) x)
    (hf : ContDiffAt ℝ ω f x) (hg : ContDiffAt ℝ ω g x) (hh : f x = g x) : Matches (k+1) f g x := by
  refine ⟨hf,hg,fun i hi => ?_⟩
  cases i with
  | zero => ext; simpa using hh
  | succ i => simp_rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]; exact congr_arg _ (h.jets i (by omega))

theorem Matches.pre_fderiv (h : Matches (k+1) f g x) (L : Z →L[ℝ] X) : Matches k (fun x => fderiv ℝ f x ∘L L) (fun x => fderiv ℝ g x ∘L L) x :=
  h.ahead.refl_comp (u:=fun A : X →L[ℝ] Y => A.comp L) (contDiffAt_id.clm_comp contDiffAt_const)

def vert (F : X × Y → Z) (x : X × Y) := fderiv ℝ (fun y => F (x.1,y)) x.2

theorem Matches.diff_vert {F G : X × Y → Z} {x : X × Y} (h : Matches (k+1) F G x) : Matches k (vert F) (vert G) x := by
  let L := ContinuousLinearMap.inr ℝ X Y
  have ht (Q : X × Y → Z) (hQ : ContDiffAt ℝ ω Q x) : (fun x => fderiv ℝ Q x ∘L L) =ᶠ[𝓝 x] vert Q := by
    filter_upwards [hQ.eventually (by simp)] with ⟨x,y⟩ hxy
    have hd : HasFDerivAt (fun y : Y => (x,y)) L y := (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
    exact ((hxy.differentiableAt (by simp)).hasFDerivAt.comp y hd).fderiv.symm
  exact (h.pre_fderiv L).unchanged (ht _ h.left) (ht _ h.right)

theorem Matches.apply_pi {ι : Type} [Fintype ι] {f g : X → ι → Y} (h : Matches k f g x) (i : ι) :
    Matches k (fun x => f x i) (fun x => g x i) x := h.refl_comp ((contDiff_apply ℝ Y i).contDiffAt)



end YM.WilsonStartup.Change
