import YM.AnalyticBridge.VERIFIED_RESET_STEP.Affine
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.PMOM
import YM.Push.BETA_TRANSPORT.Margins


/-!
# The inherited regular scalar and its weight-four cancellations

E:eq:3cid, polar & ordered, at the actual flat germ (`logHessian`
normalization). PMOM-style local gauge / holonomy substitution, now *only*
from the inherited null tests on the real value: no `PiVanish` premise. In
the joint weighted-flat map `optic` at positive degree ≤4, terms not seen
at all by a gauge move can be screened out together, leaving only two
weight-two legs (literal Hessian) or the first derivative. Then use
attenuation through the TRUE Taylor map, not a fake cancellation of jets in
the Lie basis. Const-any Hessian against the unrestricted third-cost leg
requires a separate gradient argument. No nonwrapping assumption removed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Lattice Wilson RG Labels Source Source.Drops Next.Foundations
  MultiNext.SignedSource MultiNext.SignedSource.Mom AnalyticBridge.VerifiedReset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {B : BudgetPoint} {X : Support n} {o : Site n} {k m : ℕ}
    {f : Config G n → ℝ}

structure Seed (B : BudgetPoint) (o : Site n) (X : Support n) (f : Config G n → ℝ) : Prop where
  good : B.Regular X f
  site : o∈X
  value : f 1 = 0
  mute : Nonwrapping X o → ∀ x y, IsAffineDirection o x → IsAffineDirection o y → logHessian f x y = 0

lemma Seed.family {A : Activities G n} (h : A.RegularFamily B) (i : ℕ) : Seed B (A.reg i).site (A.reg i).support (A.E i) :=
    ⟨h.smooth _, (A.reg i).anchor, h.at_flat _, h.vanish _⟩

private lemma base_const {f : E4 → G.Color} (hf : f∈Powers.space E4 G.Color 0) (x : E4) : f 0=f x := by
  simpa using (Mom.base hf).2 0 x
private lemma basis_sum (x : E4) : (∑ i : Axis, x i • basis i) = x := by
  simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using (EuclideanSpace.basisFun Axis ℝ).sum_repr x
private lemma linear_base {f : E4 → G.Color} (hf : f∈Powers.space E4 G.Color 1) :
    ∃ (c : G.Color) (M : Axis → G.Color), ∀ x : E4, f x = c + ∑ i : Axis, x i • M i := by
  obtain ⟨g,h,hg,hh,rfl⟩ := Mom.roof hf
  let L := fderiv ℝ g 0
  have he (x : E4) : g x=L x := by
    nth_rw 1 [Powers.tensor_form hg]; simp [L,Tensor.diagonal,Tensor.coeff,iteratedFDeriv_one_apply]
  refine ⟨h 0,(fun i => L (basis i)),fun x => ?_⟩
  change g x + h x= _; rw [← base_const hh,he,show L x=∑ i : Axis, x i • L (basis i) by nth_rw 1 [← basis_sum x]; rw [map_sum]; exact Finset.sum_congr rfl fun j _ => map_smul ..]; abel

private lemma pair_fit {v : Directions G n} (h : v ∈ Mom.Maps o X 2) :
    ∃ a : LinearJet G, Agrees X v (a.field o) := by
  obtain ⟨f,hf,hh⟩:= h
  choose c M hM using fun j => linear_base (hf j)
  refine ⟨⟨c,M⟩,fun i hi hx => ?_⟩
  rw [hh i, if_pos (show needed X i from ⟨hi,hx⟩), hM]
  rfl
private lemma single_fit {v : Directions G n} (h : screen X v ∈ Mom.Maps o X 1) :
    ∃ a : LinearJet G, a.positive=0 ∧ Agrees X v (a.field o) := by
  obtain ⟨f,hf,hh⟩ := h
  let a : LinearJet G := ⟨fun j => f j 0, 0⟩
  refine ⟨a,funext (fun j => sub_self _),fun i hi hx => ?_⟩
  have he := hh i; rw [Mom.screen_at,if_pos (show needed X i from ⟨hi,hx⟩)] at he
  simp only [LinearJet.field,a,Pi.zero_apply,smul_zero,Finset.sum_const_zero,add_zero]
  rw [he,if_pos (show needed X i from ⟨hi,hx⟩),← base_const (hf i.2)]

section cancel
variable (g : G.Simple) (h : Seed B o X f) (hX : Nonwrapping X o) (hn : 4 ≤ n.val)
include g h hn hX

lemma Seed.constant_hessian {u v : Directions G n} (hh : screen X u ∈ Mom.Maps o X 1) :
    logHessian f u v = 0 := by
  obtain ⟨a,he,ha⟩ := single_fit hh
  obtain ⟨s,hs⟩ := a.gradient_agrees hX hn he
  exact (hessian_agrees g h.good (c:=v) (fun i hi hx => (ha i hi hx).trans (hs i hi hx).symm) (fun _ _ _ => rfl)).trans (hessian_gradient g h.good s v)

omit hn in
private lemma quadratic {u v : Directions G n} (hu : u∈Mom.Maps o X 2) (hv : v∈Mom.Maps o X 2) :
    logHessian f u v = 0 := by
  obtain ⟨a,ha⟩:=pair_fit hu; obtain ⟨b,hb⟩:=pair_fit hv
  exact (hessian_agrees g h.good ha hb).trans (h.mute hX _ _ ((LinearJet.isAffine o).2 ⟨a,rfl⟩) ((LinearJet.isAffine o).2 ⟨b,rfl⟩))

set_option maxHeartbeats 1000000 in
lemma Seed.four : Mediator.valence (fun i => (Mom.Maps o X i (G:=G): Set _)) 4 (f ∘ increment 1) := by
  let K (i) := (Mom.Sites o X i (G:=G) (d:=4): Set (Mom.Slate G n 4))
  let L (i) := (Mom.Maps o X i (G:=G) : Set (Directions G n))
  let q := optic X o (G:=G) (d:=4)
  let F := f ∘ increment (1:Config G n)
  have hn' : 2 ≤ n.val := le_trans (by decide) hn
  have hf : ContDiffAt ℝ 4 F 0 := (h.good.smooth 1 (flat_ok B X)).of_le (Nat.cast_le (α:=ℕ∞ω) |>.mpr (le_trans (by decide : 4 ≤ 6) B.order_ge))
  have hg := flat_critical g h.good
  obtain ⟨hq,h₀⟩:=osmotic (d:=4) (G:=G) X o
  have hD : ContDiffAt ℝ 4 (F ∘ q) 0 := (h₀.symm ▸ hf).comp (f:=q) 0 (hq.of_le le_top)
  have hc : Mediator.curry K L 4 q := Mom.along o X hn' hX
  have hs : ∀ v∈K 2, fderiv ℝ q 0 v∈L 2 := fun v hv => by
    simpa [iteratedFDeriv_one_apply] using hc 1 one_pos (fun _ => 2) (fun _ => v) ⟨fun _ => ⟨by norm_num,hv⟩,by norm_num⟩
  apply Mediator.attenuation K L q F (hq.of_le le_top) h₀ hf (fun i hi hd => Mom.covers o X hX hn' i hi hd) hc
  let H := hol G
  letI : NormedAddCommGroup (Mom.Slate G n 4) := inferInstanceAs (NormedAddCommGroup ((Site n → G.Color) × Snap G 4))
  letI : NormedSpace ℝ (Mom.Slate G n 4) := inferInstanceAs (NormedSpace ℝ ((Site n → G.Color) × Snap G 4))
  have ht : ((fun x => (f x:ℂ)) ∘ increment 1) ∘ q=ᶠ[𝓝 (0:Mom.Slate G n 4)]
      (fun v => (f (H.testLinks 4 o (expand 4 v.2) 1):ℂ)) := Mom.appears (fun u v hv => congrArg Complex.ofReal (h.good.sites u v hv))
        (fun s x => congrArg Complex.ofReal (h.good.symmetry s x)) H
  let π : Mom.Slate G n 4 →L[ℝ] Mom.Slate G n 4 := (ContinuousLinearMap.inr ..).comp (ContinuousLinearMap.snd ..)
  have hP : F ∘ q =ᶠ[𝓝 0] (F ∘ q) ∘ π := by
    filter_upwards [ht,ht.comp_tendsto (show Tendsto π (𝓝 0) (𝓝 0) from by simpa using π.continuous.tendsto 0)] with v hv hv'
    exact Complex.ofReal_inj.mp (hv.trans hv'.symm)
  intro m a v hA
  by_cases hV : ∃ i, a i ≤ 1
  · obtain ⟨i,hi⟩ := hV
    have hv : π (v i) = 0 := Prod.ext rfl (funext fun j => ((hA.1 i).2.2 j (by omega)))
    have hm : m ≤ 4 := le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) (fun j _ => (hA.1 j).1)) hA.2
    rw [(hP.iteratedFDeriv (𝕜:=ℝ) m).eq_of_nhds,jets_linear π (hD.of_le (show (m:ℕ∞ω) ≤ 4 by exact_mod_cast hm)),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact ContinuousMultilinearMap.map_coord_zero _ i hv
  have hv (i) : 2 ≤ a i := by have h := not_exists.mp hV i; omega
  have hm : m*2 ≤ 4 := le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => 2) (fun j _ => hv j)) hA.2
  have hJ := Work.F03.hessian_comp h₀ (germ_diff h.good) (hq.of_le le_top) hg
  cases m
  · rw [iteratedFDeriv_zero_apply]; change F (q 0) = 0; rw [show q 0=0 from h₀]; exact (congrArg f (at_zero 1)).trans h.value
  · rename_i m
    by_cases he : m=0
    · subst m; rw [iteratedFDeriv_one_apply, show fderiv ℝ (F ∘ q) 0 = 0 from hJ.1]; rfl
    have he : m=1 := by omega
    subst m; rw [show v= ![v 0,v 1] from funext (fun i => by fin_cases i <;> rfl), show iteratedFDeriv ℝ 2 (F ∘ q) 0 _ = _ from hJ.2 (v 0) (v 1)]
    change logHessian f _ _=0
    have hz : a 0 = 2 ∧ a 1 = 2 := by have he : ∑ i,a i ≤ 4 := hA.2; rw [Fin.sum_univ_two] at he; have := hv 0; have := hv 1; omega
    exact quadratic g h hX (hs _ (hz.1 ▸ (hA.1 0).2)) (hs _ (hz.2 ▸ (hA.1 1).2))

lemma Seed.ghost {a : Fin m → ℕ} (v : Fin m → Directions G n) (ha : ∀ i, 0 < a i) (he : ∑ i,a i ≤ 4)
    (hs : ∀ i, screen X (v i)∈Mom.Maps o X (a i)) : iteratedFDeriv ℝ m (f ∘ increment 1) 0 v = 0 := by
  let F := f ∘ increment (1:Config G n)
  have hQ : F = F ∘ screen (G:=G) X := funext fun u => h.good.sites _ _ fun i hi hh => by
    rw [increment,increment,Mom.screen_at,if_pos (show needed X i from ⟨hi,hh⟩)]
  have hm : m ≤ B.order := (le_trans (by simpa using Finset.sum_le_sum (s:=Finset.univ) (f:=fun _ => 1) (fun j _ => (show 1 ≤ a j from ha j))) he).trans
    (le_trans (by decide : 4 ≤ 6) B.order_ge)
  have hf := (h.good.smooth 1 (flat_ok B X)).of_le (Nat.cast_le (α:=ℕ∞ω) |>.mpr hm)
  change iteratedFDeriv ℝ m F 0 v=0
  rw [hQ, jets_linear _ (f:=F) hf]
  exact h.four g hX hn m a _ ⟨fun i => ⟨ha i, hs i⟩,he⟩
end cancel
end YM.PhysicalNext.JointLoad.Heir
