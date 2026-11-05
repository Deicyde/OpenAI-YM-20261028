import YM.Push.FREE_RESOLVENT.Views

/-!
# Mixed jets before the affine precision

In real product chart, differentiate the fine axis ONCE for the kernel
coefficient, and then in the background through k. Need only vertical
entry bounds on actual arrays, not an analyticity radius with pre-L costs
on a full H.Score. Use this also comparing/pricing V-germs at *fixed*
center. Works including dimension zero input field spaces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Affine
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid Work.F03 TestD Filter Function Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {f c n : Side} {S : StepData c f}
variable {τ ι κ E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

section partials
variable [Fintype κ] [DecidableEq κ] [Fintype ι] {A : E × (κ → ℝ) → ι → ℝ} {k : ℕ}

abbrev matrix (A : E × (κ → ℝ) → ι → ℝ) := fun x : E => LinearMap.toMatrix'
  (fderiv ℝ (fun y => A (x,y)) 0).toLinearMap

/-- Entry as total gradient on the zero slice near origin: easier to align & bound. -/
lemma pairwise (hk : ContDiffAt ℝ ω A 0) (i j) :
    (fun x => matrix A x i j) =ᶠ[𝓝 0] fun x => fderiv ℝ (fun z => A z i) (x,0) (0,Pi.single j 1) := by
  have he : Tendsto (fun x : E => (x,(0:κ→ℝ))) (𝓝 0) (𝓝 0) := (continuous_id.prodMk (continuous_const (y:=(0:κ→ℝ)))).continuousAt.tendsto
  filter_upwards [he.eventually (hk.eventually (by simp))] with x h
  have hp := (h.differentiableAt (by simp)).hasFDerivAt
  let F : (κ → ℝ) → E × (κ → ℝ) := fun y => (x,y)
  let L := ContinuousLinearMap.inr ℝ E (κ → ℝ)
  have hF : HasFDerivAt F L 0 := (hasFDerivAt_const x (0:κ→ℝ)).prodMk (hasFDerivAt_id _)
  let M : (ι→ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  calc
    _ = (matrix A x *ᵥ Pi.single j 1) i := by simp
    _ = M (fderiv ℝ (A ∘ F) 0 (Pi.single j 1)) := by rw [matrix,LinearMap.toMatrix'_mulVec]; rfl
    _ = _ := by rw [(hp.comp (f:=F) 0 hF).fderiv, show fderiv ℝ (fun z => A z i) (x,0) = _ from
        (M.hasFDerivAt.comp (x,0) hp).fderiv]; rfl

lemma grad_smooth (h : ContDiffAt ℝ ω A 0) (K : ℕ) : ContDiffAt ℝ K (matrix A) 0 := by
  refine TestD.rectangle_smooth (fun i j => ?_)
  let f := fun z => A z i
  have h1 : ContDiffAt ℝ ω f 0 := contDiffAt_pi.mp h i
  have h2 : ContDiffAt ℝ K (fderiv ℝ f) 0 := h1.fderiv_right (by simp)
  exact ((h2.comp (f:=fun x => (x,0)) (0:E) (contDiffAt_id.prodMk contDiffAt_const)).clm_apply
    (g:=fun x => ((0:E), (Pi.single j 1:κ→ℝ))) contDiffAt_const).congr_of_eventuallyEq (pairwise h i j)

lemma stream (h : ContDiffAt ℝ ω A 0) (i j) (l : List τ) (v : τ → E) :
    jet v (matrix A) l 0 i j = iteratedFDeriv ℝ (l.length+1) (fun z => A z i) 0
      (Fin.snoc (α:=fun _ => E × (κ → ℝ)) (fun m => (v (l.get m),0)) (0,Pi.single j 1)) := by
  let f := fun z => A z i
  let L : E →L[ℝ] E × (κ → ℝ) := ContinuousLinearMap.inl ..
  let x : E × (κ → ℝ) := (0,Pi.single j 1)
  have h1 : ContDiffAt ℝ ω f 0 := contDiffAt_pi.mp h i
  have h2 : ContDiffAt ℝ l.length (fderiv ℝ f) 0 := h1.fderiv_right (by simp)
  have hg : ContDiffAt ℝ l.length ((fderiv ℝ f) ∘ L) 0 := h2.comp (0:E) (f:=L) L.contDiff.contDiffAt
  rw [← TestD.entry v l (grad_smooth h _) i j,identical v (pairwise h i j), iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  erw [show jet v _ l 0 = (jet v ((fderiv ℝ f) ∘ L) l 0) x from jet_linear (A:=(fderiv ℝ f) ∘ L) v l (ContinuousLinearMap.apply ℝ ℝ x) hg]
  unfold jet
  rw [Next.Foundations.jets_linear L h2]; rfl
end partials

section use
-- periodic finite-component locality & derivative tests
variable {F : pair G c f → ι → ℝ} {i : ι} {X : ℝ} [Fintype ι]

/-- Cap from full pair derivative (no norm equity on codomain needed). -/
lemma polar_focus (h : ContDiffAt ℝ ω F 0) (j : raw G f) (l : List (raw G c))
    (hx : 0 ≤ X) (he : ‖iteratedFDeriv ℝ (l.length+1) (fun z => F z i) 0‖ ≤ X) :
    ‖jet (ray G c) (matrix F) l 0 i j‖ ≤ X := by
  rw [stream h i j l]; apply (ContinuousMultilinearMap.le_of_opNorm_le he _).trans
  refine mul_le_of_le_one_right hx ?_; refine (Finset.prod_le_prod (fun a _ => norm_nonneg _) (g:=fun _ => 1) fun a _ => ?_).trans_eq (by simp)
  induction a using Fin.lastCases <;> simp only [Fin.snoc_last, Fin.snoc_castSucc,
    Prod.norm_def,norm_zero,max_le_iff]
  · exact ⟨zero_le_one,ray_nn j⟩
  exact ⟨ray_nn _,zero_le_one⟩

/-- mask in a test, not the physical cut. -/
def stopAt (S : StepData c f) (o : Site c) (R : ℕ) : pair G c f →L[ℝ] pair G c f :=
  (coarse G o R).prodMap (chop fun i : raw G f => separation o (home S i) ≤ R)

lemma sees_here (S : StepData c f) (o : Site c) (R : ℕ) (p : pair G c f) :
    View.Reads p (stopAt S o R p) S.sizes S.sizes S.kernel o o R := by
  constructor
  · intro z h i
    change _=if separation o (View.addr o z) ≤ R then _ else _
    rw [if_pos ((View.separation_view o z).trans h)]; rfl
  intro z h i
  have he := View.home_addr S o z i
  change _=if separation o (home S (View.fineAt S o z i)) ≤ R then _ else _
  rw [he,if_pos ((View.separation_view o z).trans h)]; rfl

lemma chops {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → Prop} [DecidablePred p] (i : ι) (h : ¬ p i) :
    chop p (Pi.single i (1:ℝ))=0 := by
  ext j
  change (if p j then ((Pi.single i (1:ℝ):ι→ℝ) j) else 0) = _
  by_cases j=i <;> simp_all

/-- Radius of possible numerical dependence for the polar gradient entry. -/
lemma coal (S : StepData c f) (o : Site c) (R : ℕ) (j : raw G f) (l : List (raw G c))
    (h : ContDiffAt ℝ ω F 0)
    (hv : (fun x => F (stopAt S o R x) i) =ᶠ[𝓝 0] fun x => F x i)
    (he : jet (ray G c) (matrix F) l 0 i j ≠ 0) :
    separation o (home S j) ≤ R ∧ ∀ x∈l, separation o (hearth x) ≤ R := by
  rw [stream h] at he
  let L := stopAt (G:=G) S o R
  let v := fun x => F x i
  have hh : (iteratedFDeriv ℝ (l.length+1) v 0)=(iteratedFDeriv ℝ (l.length+1) v 0).compContinuousLinearMap
      fun _ => L := by
    rw [← Next.Foundations.jets_linear L ((contDiffAt_pi.mp h i).of_le le_top)]
    exact ((show v ∘ L =ᶠ[𝓝 0] v from hv).iteratedFDeriv ..).eq_of_nhds.symm
  let w : Fin (l.length + 1) → pair G c f := Fin.snoc (α:=fun _ => pair G c f)
    (fun m : Fin l.length => (ray G c (l.get m),0)) (0,Pi.single j 1)
  have hb (i : Fin (l.length+1)) : L (w i) ≠ 0 := by
    intro h
    apply he; change (iteratedFDeriv ℝ (l.length+1) v 0) w=0
    rw [hh,ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact ContinuousMultilinearMap.map_coord_zero _ i h
  constructor
  · by_contra H; apply hb (Fin.last l.length)
    rw [show w _=(0,Pi.single j 1) from Fin.snoc_last ..]
    exact Prod.ext (map_zero (coarse G o R)) (chops (p:=fun i => separation o (home S i) ≤ R) j H)
  intro x hx; obtain ⟨t,ht⟩ := List.mem_iff_get.mp hx
  by_contra H; apply hb t.castSucc
  unfold w; rw [Fin.snoc_castSucc,ht]
  exact Prod.ext (chops (p:=fun i => separation o (hearth i) ≤ R) x H) (map_zero (chop (α:=raw G f) (fun i => separation o (home S i) ≤ R)))
end use
end YM.FreeResolvent.Affine
