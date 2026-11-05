import YM.UVExtension.Lamppost.Copy
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! # Lifting a finite number of angular jets. A different lift at each point/basis
      can restrict the real vehicle. Products evaluated BEFORE taking suprema. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Metric Filter Topology Set BoundedContinuousFunction Complex RG
open scoped BigOperators ContDiff Classical
variable {A Z E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [NormedAddCommGroup Z] [NormedSpace ℂ Z]
variable {j k : ℕ} {x:E} {X X' Y Y': E→ℂ} {F : A → E→ℂ} {T:Opening A Z}

variable [FiniteDimensional ℝ E]

/-- Hole applies also at singular Healthy boundaries. Lift need only be a germ for
    this probe and point. On the dense real chords it has the exact appointed jets.
    Now can use product estimates on these synthesized germs. -/
theorem forge (T : Opening A Z)
    (p : (i:ℕ) → (Fin i→ E) → Z→ℂ) (h : ∀ a, ContDiffAt ℝ (↑j) (F a) x) (hp:∀ i≤j,∀ v,Bumps T.span (p i v))
    (hv : ∀ a i, i≤j→∀ v,p i v (T.call a)=iteratedFDeriv ℝ i (F a) x v) :
    ∃ f:Z→ E → ℂ, (∀ z, ContDiffAt ℝ (↑j) (f z) x) ∧ (∀ a,Foil x j (f (T.call a)) (F a)) ∧
    (∀ (s:Set ℂ) (g:ℂ→Z), IsOpen s→ MapsTo g s T.span → DifferentiableOn ℂ g s → Luster s x j (fun z=> f (g z))) ∧
    ∀ z∈ T.span,∀ i≤j,∀ v,p i v z=iteratedFDeriv ℝ i (f z) x v := by
  let r:= Module.finBasis ℝ E; let D:= Fin (Module.finrank ℝ E)
  let K:= Σ i:Fin (j+1),Fin i.val → D; letI : Fintype K:=by unfold K; infer_instance
  let t(e :K):= r ∘ e.2
  let φ (f:E→ℂ)(e:K) := iteratedFDeriv ℝ e.1.val f x (t e)
  let M:= Finsupp.linearCombination ℂ fun i=>φ (F i); let H : Submodule ℂ (K→ℂ):= LinearMap.range M
  let U:= Module.finBasis ℂ H
  choose a ha using fun i=> (U i).property
  let X i (x:E):= ∑ j∈(a i).support,(a i) j • F j x
  have hh i : ContDiffAt ℝ (↑j) (X i) x:= ContDiffAt.sum (fun i hi=> (h _).const_smul _)
  have hU (i) (k:K): φ (X i) k= ((U i).val k):=by
    let g(π : A →₀ ℂ): K→ℂ := fun k=> ∑ i∈π.support,π i • φ (F i) k
    have hg : M (a i)=g (a i):= by funext i'; unfold M; rw [Finsupp.linearCombination_apply, Finsupp.sum,Finset.sum_apply]; rfl
    have he : k.1.val≤j:= Nat.le_of_lt_succ k.1.isLt
    rw [← ha,hg]; change iteratedFDeriv ℝ _ _ _ _= _; unfold X; rw [iteratedFDeriv_fun_sum_apply]; swap; · exact fun i _=> (h i|>.const_smul _).of_le (by exact_mod_cast he)
    rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i' hi; rw [iteratedFDeriv_const_smul_apply' ((h i').of_le (by exact_mod_cast he))]; rfl
  obtain ⟨L,hL⟩:= H.exists_isCompl
  let B:= (LinearMap.ofIsCompl hL LinearMap.id 0).toContinuousLinearMap
  have hB (x:H):B x.val=x := LinearMap.ofIsCompl_apply_left hL _
  let g (z:Z) (k:K):=p k.1.val (t k) z
  have hg : Bumps T.span g:= fun s v hs hh he=> by intro x hx; exact differentiableWithinAt_pi.mpr fun k=> hp k.1.val (Nat.le_of_lt_succ k.1.isLt) _ s v hs hh he x hx
  let c i z:= U.equivFun (B (g z)) i
  have hc i:Bumps T.span (c i):= by
    intro s v hs hv ht; apply (LinearMap.toContinuousLinearMap (LinearMap.proj (R:=ℂ) i ∘ₗ U.equivFun.toLinearMap) |>.differentiable).comp_differentiableOn (B.differentiable.comp_differentiableOn (hg s v hs hv ht))
  let f(z:Z)(x:E):= ∑ i,c i z * X i x
  have hf z : ContDiffAt ℝ (↑j) (f z) x := ContDiffAt.sum (fun i _=> contDiffAt_const.mul (hh i))
  have hΦ : ∀ a,Foil x j (f (T.call a)) (F a):= by
    intro a; refine ⟨hf _,fun i hi=>?_⟩
    have hΨ:g (T.call a)=φ (F a) := funext fun k=> hv _ _ (Nat.le_of_lt_succ k.1.isLt) _
    have hA:φ (F a) ∈ H:= ⟨Finsupp.single a 1,(by unfold M; simp)⟩
    have hT(k:K): φ (f (T.call a)) k=φ (F a) k:= by
      let f0 : H:=⟨φ (F a),hA⟩
      have hF i:c i (T.call a)=U.repr f0 i := by unfold c; rw [hΨ,show B (φ (F a))=f0 from hB f0]; rfl
      have hu : (f0.val k)=∑ i,U.repr f0 i • (U i).val k := by
        nth_rw 1 [← U.sum_repr f0]; simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply]; rfl
      change iteratedFDeriv ℝ _ (fun x=> ∑ i,c i (T.call a) • X i x) x _=f0.val k
      rw [hu,iteratedFDeriv_fun_sum_apply]; swap; · exact fun _ _=> ((hh _).const_smul _).of_le (by exact_mod_cast Nat.le_of_lt_succ k.1.isLt)
      rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro i _
      rw [iteratedFDeriv_const_smul_apply' ((hh _).of_le (by exact_mod_cast Nat.le_of_lt_succ k.1.isLt)),hF i,← hU]; rfl
    ext m
    apply congr_arg (fun f : MultilinearMap ℝ (fun _ : Fin i=> E) ℂ => f m) (Module.Basis.ext_multilinear (fun _ => r) ?_)
    exact fun v=> hT (⟨⟨i,Nat.lt_succ_of_le hi⟩,v⟩:K)
  have h' (s:Set ℂ) (v:ℂ→Z) (hs:IsOpen s) (hm:MapsTo v s T.span) (ht:DifferentiableOn ℂ v s) :Luster s x j (fun z=> f (v z)):= Luster.pluses (A:=ℂ) _ _ fun i (_:i∈Finset.univ)=> (Luster.summit (hc i _ _ hs hm ht)).times (Luster.resting (hh i))
  refine ⟨f,hf,hΦ,h',fun z hz i hi v=>?_⟩
  apply T.agrees _ _ (hp i hi v) (fun s g hs hm ht=> (h' s g hs hm ht).order i hi v) (fun k=> (hv k i hi v).trans ?_) hz
  rw [(hΦ k).congr i hi]
end YM.UVExtension.Lamppost
