import YM.Maxwell.Leg
import YM.Next.WARD_BIN.Sampling
import YM.Work.G01
import YM.Work.G04



/-!
# Equivariant lifts from the sampled divergence

For each Taylor slot choose a finite panel of linear divergence samples, and
lift back equivariantly to that Taylor slot so that the residual is in the shell.
Keep the higher-slot triangular errors for the actually tested Wilson stencils.
Also recall the different panel of curvature samples from the source library,
using its existing (coordinate-recovering) theorem. No assumption of a rank or
detector statement on the *physical* correlations is made here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Set Filter MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid
open Work.G01
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge}

private theorem finiteTests {P E F : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F] (d : P → E →ₗ[ℝ] F) :
    ∃ p : Finset P, ∀ x, (∀ i∈p, d i x = 0) → ∀ i,d i x=0 := by
  classical
  let v (p : Finset P) := ⨅ i∈p,LinearMap.ker (d i)
  obtain ⟨n,⟨p,rfl⟩,h⟩ := wellFounded_lt.has_min (range fun p => Module.finrank ℝ (v p))
    (range_nonempty _)
  refine ⟨p,fun x he i => ?_⟩
  have hp : v (insert i p) ≤ v p := by unfold v; rw [Finset.iInf_insert]; exact inf_le_right
  have hw : v p=v (insert i p) := Eq.symm <| hp.eq_of_not_lt (fun hh =>
    h _ ⟨insert i p,rfl⟩ (Submodule.finrank_lt_finrank_of_lt hh))
  have hx : x ∈ v p := (Submodule.mem_iInf _).mpr fun i => (Submodule.mem_iInf _).mpr fun hi => LinearMap.mem_ker.mpr (he i hi)
  rw [hw] at hx; exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx i) (Finset.mem_insert_self ..)

/- Split `D` equivariantly by averaging an honest generalized inverse.
No C* results needed; use Haar on G and real finite-dimensional vector measures. -/
private lemma lift_eqv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (P : G.El → E →L[ℝ] E) (Q : G.El → F →L[ℝ] F) (D : E →L[ℝ] F)
    (hP : Continuous P) (hQ : Continuous Q) (hp : ∀ u v x,P (u*v) x=P u (P v x))
    (hq : ∀ u v x, Q (u*v) x = Q u (Q v x)) (h1 : ∀ x, Q 1 x=x)
    (hd : ∀ u x, D (P u x)=Q u (D x)) :
    ∃ L : F →L[ℝ] E, (∀ x, D (L (D x))=D x) ∧ ∀ u x,L (Q u x) = P u (L x) := by
  classical
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ _
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ _
  let K := LinearMap.range D.toLinearMap
  let d := D.toLinearMap.rangeRestrict
  obtain ⟨A,hA⟩ := LinearMap.exists_rightInverse_of_surjective d (by simp [d])
  let X := LinearMap.toContinuousLinearMap (A.comp K.subtype.leftInverse)
  have he (x : E) : D (X (D x)) = D x := by
    have h : K.subtype.leftInverse (D x)=d x :=
      LinearMap.leftInverse_apply_of_inj K.ker_subtype (d x)
    change D (A _) = _; rw [h]
    exact congr_arg Subtype.val (LinearMap.congr_fun hA (d x))
  let L (u : G.El) := (P u⁻¹).comp (X.comp (Q u))
  have hc : Continuous L := (hP.comp continuous_inv).clm_comp (continuous_const.clm_comp hQ)
  have hL : Integrable L G.probHaar := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hF (x : F) : Integrable (fun u => L u x) G.probHaar :=
    (hc.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hU (x : F) : (∫ a,L a ∂G.probHaar) x = _ := ContinuousLinearMap.integral_apply hL x
  refine ⟨∫ a,L a ∂G.probHaar,?_,?_⟩
  · intro x; rw [hU, ← D.integral_comp_comm (hF _)]
    have hs (u : G.El) : D (L u (D x)) = D x := by
      change D (P u⁻¹ (X (Q u (D x))))= _; rw [hd, ← hd u, he, hd u, ← hq,inv_mul_cancel,h1]
    simp_rw [hs]; simp
  intro u x; rw [hU,hU, ← (P u).integral_comp_comm (hF _)]
  have hh (b) : L b (Q u x)=P u (L (b*u) x) := by
    simp only [L, ContinuousLinearMap.comp_apply, ← hq, ← hp,mul_inv_rev, mul_inv_cancel_left]
  simp_rw [hh]; exact integral_mul_right_eq_self (fun v => P u (L v x)) u

/-- Pointwise continuity in the group variable suffices for the frame actions. -/
private theorem operator_cont {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] (L : X → E →L[ℝ] F) (h : ∀ a, Continuous fun x => L x a) : Continuous L := by
  let b := Module.finBasis ℝ E
  let Y := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℝ (M':=F)).toLinearMap
  have he (x) : Y (fun i => L x (b i)) = L x := by
    apply ContinuousLinearMap.coe_injective; exact b.ext fun i => b.constr_basis ..
  rw [← funext he]; exact Y.continuous_of_finiteDimensional.comp (continuous_pi fun _ => h _)

lemma adjoint_cont {a : G.Color} : Continuous fun u : G.El => G.adjoint u a :=
  G.projectColor.continuous_of_finiteDimensional.comp ((G.continuous_mat.mul continuous_const).mul
    (continuous_star.comp G.continuous_mat))

variable {j d : ℕ}

lemma paint_cont : Continuous fun (u : G.El) => LinearMap.toContinuousLinearMap (Taylor.paint (j:=j) u) := by
  have hc : Continuous fun (u : G.El) => (G.adjoint u).toContinuousLinearMap :=
    operator_cont _ (fun p => adjoint_cont)
  refine operator_cont (E:=Taylor G j) (F:=Taylor G j) (X:=G.El) (fun u : G.El => (Taylor.paint (j:=j) u).toContinuousLinearMap) (fun x => ?_)
  refine Continuous.subtype_mk ?_ _
  apply continuous_pi; intro i
  let A := x.val i
  let Y (P : G.Color →L[ℝ] G.Color) := P.compContinuousMultilinearMap A
  let L : (G.Color →L[ℝ] G.Color) →ₗ[ℝ] Tensor.T E4 G.Color (j+1) := {
    toFun := Y
    map_add' p q := by ext; rfl
    map_smul' p q := by ext; rfl }
  exact L.continuous_of_finiteDimensional.comp hc

lemma curlDiv_paint (v : Taylor G j) (u : G.El) (i : Axis) (x : E4) :
    curlDiv i x (Taylor.paint u v) = G.adjoint u (curlDiv i x v) := by
  let U := (G.adjoint u).toContinuousLinearMap
  have he (i k : Axis) : Tensor.diagonal (Maxwell.takeCurl (Taylor.paint u v) k i)=
      U ∘ Tensor.diagonal (Maxwell.takeCurl v k i) := by
    rw [Maxwell.takeCurl_diag,Maxwell.takeCurl_diag]; funext z
    have hh (i a) : Maxwell.grad a ((Taylor.paint u v).value i) z = U (Maxwell.grad a (v.value i) z) :=
      Maxwell.grad_linear U (Tensor.diag_smooth (v.val i) ∞|>.contDiffAt) a
    simp only [Pi.sub_apply, Function.comp_apply, hh, map_sub]
  rw [curl_div_at, curl_div_at,map_sum]; apply Finset.sum_congr rfl
  intro k _; rw [he]; exact Maxwell.grad_linear U (Tensor.diag_smooth _ ∞|>.contDiffAt) k

lemma paint_comp (u v : G.El) (j : ℕ) (x : Taylor G j) :
    Taylor.paint (u*v) x = Taylor.paint u (Taylor.paint v x) := by
  apply Taylor.value_ext; funext i z; simp [G.adjoint_mul]

open Maxwell

/-- At a single Taylor slot, project away the equation-leg components. -/
private def panel (G : Gauge) (p : Finset (Axis × E4)) (j : ℕ) :
    Taylor G j →L[ℝ] (p → G.Color) := ContinuousLinearMap.pi (fun i => - curlDiv i.val.1 i.val.2)

private lemma choose_panel (G : Gauge) (j : ℕ) : ∃ (p : Finset (Axis × E4))
    (K : (p → G.Color) →L[ℝ] Taylor G j),
    (∀ v, takeCurl (v-K (panel G p j v)) ∈ onShell G.Color j) ∧
      ∀ u a,K (fun x => G.adjoint u (a x))=Taylor.paint u (K a) := by
  obtain ⟨p,hp⟩ := finiteTests (fun (p : Axis × E4) => (curlDiv (G:=G) (j:=j) p.1 p.2).toLinearMap)
  let V := Taylor G j
  let E := p → G.Color
  let D : V →L[ℝ] E := panel G p j
  have H (i : p) (v : V) : D v i= - curlDiv i.val.1 i.val.2 v := rfl
  let P (u : G.El) : V →L[ℝ] V := (Taylor.paint u).toContinuousLinearMap
  let Q (u : G.El) : E →L[ℝ] E := ContinuousLinearMap.pi (fun i =>
    (G.adjoint u).toContinuousLinearMap.comp (ContinuousLinearMap.proj i))
  have hQ : Continuous Q := operator_cont Q fun _ => continuous_pi fun _ => adjoint_cont
  have hh (u : G.El) (v) : D (P u v) = Q u (D v) := by
    funext i
    change - _ = G.adjoint u (- curlDiv i.val.1 i.val.2 v)
    rw [map_neg]; exact congrArg (fun x : G.Color => -x) (curlDiv_paint ..)
  obtain ⟨K,hK,hr⟩ := lift_eqv P Q D paint_cont hQ (fun u v x => paint_comp u v j x)
    (fun u v x => funext fun _ => G.adjoint_mul u v _)
    (fun x => funext fun i => G.adjoint_one (x i)) hh
  refine ⟨p,K, fun v => ⟨closedCurl _,fun b x => ?_⟩, hr⟩
  apply hp _ ?_ (b,x)
  intro i hi
  let z : p := ⟨i,hi⟩
  have he : -curlDiv i.1 i.2 (K (panel G p j v)) = -curlDiv i.1 i.2 v := congr_fun (hK v) z
  change curlDiv i.1 i.2 (v-_)=0
  rw [map_sub, neg_injective he,sub_self]

/- Combine the chosen Cover tests at one level (not necessarily the family
of *all* lower Taylor levels). -/
private lemma coordinates (H : Hol G) (i : Fin (d-1)) : ∃ (Y : Finset (Edge Cover))
    (L : ((e : (Y : Type)) → G.Color) →L[ℝ] Taylor G i.val)
    (T : Taylor G i.val →L[ℝ] Taylor G i.val),
      (∀ v, takeCurl (v-T v) ∈ onShell G.Color i.val) ∧
      (∀ u f, L (fun a => G.adjoint u (f a))=Taylor.paint u (L f)) ∧
      (∀ J∈through G d i.val, L (fun a => linearSample H a.val J)=T (J i)) := by
  classical
  obtain ⟨p,Q,hQ,h⟩ := choose_panel G i.val
  choose c hc using fun a : p => samples H i a.val.1 a.val.2
  let S (a : p) := (c a).support
  let Y := Finset.univ.biUnion fun a : p => (S a).image (fun x => (x,a.val.1))
  have hh (a : p) (x : S a) : (x.val,a.val.1)∈Y := Finset.mem_biUnion.mpr
    ⟨a,Finset.mem_univ _,Finset.mem_image_of_mem _ x.property⟩
  let L : ((e : Y) → G.Color) →L[ℝ] (p → G.Color) := ContinuousLinearMap.pi (fun a =>
    ∑ x : S a,c a x.val • (ContinuousLinearMap.proj (R:=ℝ) (φ:= fun _ : Y => G.Color) (⟨(x.val,a.val.1),hh a x⟩:Y)))
  let T := Q.comp (panel G p i.val)
  have ht (x : (e : Y) → G.Color) (a : p) : L x a =
      ∑ y : S a, c a y.val • x ⟨(y.val,a.val.1),hh a y⟩ := by simp only [L, ContinuousLinearMap.pi_apply, sum_apply]; rfl
  refine ⟨Y,Q.comp L,T,hQ, fun u f => ?_,fun J hJ => ?_⟩
  · change Q (L _) = Taylor.paint u (Q (L _))
    rw [← h]; apply congr_arg Q; funext x; rw [ht,ht,map_sum]
    exact Finset.sum_congr rfl fun j _ => (map_smul ..).symm
  change Q (L _)=Q _; apply congr_arg Q; funext x; rw [ht]
  let s := x.val.1; let f := fun v : Cover => c x v • linearSample H (v,s) J
  change ∑ y : S x,f y.val = -curlDiv _ _ (J _)
  rw [← Finset.sum_subtype (S x) (fun i => Iff.rfl) f]; exact hc x J hJ

/-- One choice of simultaneous panels. -/
structure Rays (G : Gauge) (d : ℕ) (H : Hol G) where
  edg : Finset (Edge Cover)
  lifts : ((e : (edg : Type)) → G.Color) →L[ℝ] Snap G d
  T (i : Fin (d-1)) : Taylor G i.val →L[ℝ] Taylor G i.val
  constrained (i : Fin (d-1)) (V) : takeCurl (V-T i V) ∈ onShell G.Color i.val
  eqv u (f) : lifts (fun a => G.adjoint u (f a))=Cast u (lifts f)
  triangular (p : Snap G d) (i : Fin (d-1)) : p∈through G d i.val → (lifts (fun a => linearSample H a.val p)) i=T i (p i)
  -- the other linear sampling (all snap slots) from G04
  k : ℕ
  slots : Fin k → RG.Slot
  point : ∀ v : RG.Slot, AnalyticAt ℝ (takes H d v) 0
  read : GaugePanel G k →ₗ[ℝ] Snap G d
  back p : read (fderiv ℝ (bring H d slots) 0 p)=p
  cov u x : read (rotates u x)=Cast u (read x)

lemma rays_exist (d : ℕ) (H : Hol G) : Nonempty (Rays G d H) := by
  classical
  choose Y L T hY he hc using coordinates (d:=d) H
  let X := Finset.univ.biUnion Y
  let r i : ((e : X) → G.Color) →L[ℝ] ((e : Y i) → G.Color) :=
    ContinuousLinearMap.pi (fun e => ContinuousLinearMap.proj (R := ℝ) (φ:=fun _ : X => G.Color)
      (⟨e.val,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,e.property⟩⟩:X))
  let Q : ((e : X) → G.Color) →L[ℝ] Snap G d := ContinuousLinearMap.pi fun i => (L i).comp (r i)
  have hp := Work.G02.answer Work.G01.answer G H d
  obtain ⟨k,B,h⟩ := Work.G03.answer G H d hp
  obtain ⟨R,hR,hr⟩ := (Work.G04.answer G H d k B hp h).detects
  exact ⟨⟨X,Q,T,hY,fun u f => funext fun i => he i u (r i f),fun p i ht => hc i p ht,k,B,hp.shot,R,hR,hr⟩⟩

end YM.WardBin
