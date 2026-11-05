import YM.Next.STATIONARY.Infrastructure.Jets
import YM.UVExtension.Projection.Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! Uniform boundedness buys fixed stencil prices. Used only for fixed lattices & jet order. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Filter Function Finset Stationary Asymptotics Tensor
open scoped Classical Topology BigOperators ContDiff
variable {I : Type} {X E Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

-- contour functions need not admit common radius for this lemma
--
def RLinear (f : X→Y) := ∃ P : X →L[ℝ] Y, f=P
variable {f g : X → Y}

lemma RLinear.mk (P : X →L[ℝ] Y) : RLinear P := ⟨P,rfl⟩
lemma RLinear.add (h : RLinear f) (he : RLinear g) : RLinear (f+g):=by
  obtain ⟨P,rfl⟩:=h; obtain ⟨Q,rfl⟩:=he; exact ⟨P+Q,rfl⟩
lemma RLinear.sub (h : RLinear f) (he : RLinear g) : RLinear (f-g):=by
  obtain ⟨P,rfl⟩:=h; obtain ⟨Q,rfl⟩:=he; exact ⟨P-Q,rfl⟩
lemma RLinear.mul (h : RLinear f) (a : ℝ) : RLinear (a • f):=by
  obtain ⟨P,rfl⟩:=h; exact ⟨a • P,rfl⟩
lemma RLinear.sum {J : Type*} (s : Finset J) (p : J→ X → Y) (h : ∀ i∈s,RLinear (p i)): RLinear fun x=> ∑ i∈s,p i x:=by
  induction s using Finset.induction with
  | empty => simp only [sum_empty]; exact ⟨0,rfl⟩
  | insert i s hs I => simp_rw [sum_insert hs]; exact (h i (mem_insert_self ..)).add (I fun j hj=> h j (mem_insert_of_mem hj))

section completeX
variable [CompleteSpace X]

theorem resists {U : ℕ → X → Y} (h : ∀ i,RLinear (U i)) (hv : ∀ x, Tendsto (fun i=> U i x) atTop (𝓝 (f x))) : RLinear f:=by
  choose D hD using h
  have hQ (x) : Tendsto (fun i=> D i x) atTop (𝓝 (f x)):= (hv x).congr' (Eventually.of_forall fun i=> congr_fun (hD i) x)
  obtain ⟨K,hK⟩:= banach_steinhaus (g:=D) (fun x=>
    let ⟨c,H⟩:= (hQ x).cauchySeq.isBounded_range.exists_norm_le; ⟨c,fun i=> H (D i x) ⟨i,rfl⟩⟩)
  let l : X →ₗ[ℝ] Y := {
     toFun:=f
     map_add' x y:= tendsto_nhds_unique (hQ _) (((hQ x).add (hQ y)).congr' (Eventually.of_forall fun i=> ((D i).map_add x y).symm))
     map_smul' a x := tendsto_nhds_unique (hQ _) ((tendsto_const_nhds (x:=a)|>.smul (hQ x)).congr' (Eventually.of_forall fun i=> (map_smul (D i) a x).symm)) }
  have hx x : ‖l x‖ ≤ K*‖x‖:= le_of_tendsto ((hQ x).norm) (Eventually.of_forall fun i=> ((D i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hK i) (norm_nonneg _)))
  exact ⟨l.mkContinuous K hx,rfl⟩

theorem expanded (j : ℕ) (D : X → T E Y j) (h : ∀ x,Sym (D x)) (he : ∀ v : E,RLinear fun x=> Tensor.diagonal (D x) v) (v) : RLinear fun x=> D x v:=by
  induction j with
  | zero => rw [show v=fun _=> 0 from Subsingleton.elim ..]; exact he _
  | succ i ih =>
    let C := fun x=> (D x).curryLeft (v 0)
    suffices H : RLinear fun x=> C x (Fin.tail v) by simpa [C,ContinuousMultilinearMap.curryLeft_apply] using H
    apply ih C (fun x=> freeze_sym _ (h x) _) (fun y=> ?_)
    let n : ℝ:= ↑(i+1:ℕ)
    have hn : n≠0 := by unfold n; positivity
    obtain ⟨s,hs⟩:= exists_seq_tendsto (𝓝[≠] (0:ℝ))
    let k x:= fun t:ℝ=> Tensor.diagonal (D x) (y+t • v 0)
    have hh x: HasDerivAt (k x) (n • Tensor.diagonal (C x) y) 0:= by
      let f := fun t:ℝ=> y+t • v 0
      have h0:f 0=y := by simp [f]
      have hp: HasDerivAt f (v 0) 0 := by simpa [f] using ((hasDerivAt_id' (0:ℝ)).smul_const (v 0) |>.const_add y)
      have he := ((Tensor.diag_smooth (D x) 1).differentiable one_ne_zero (f 0)).hasFDerivAt.comp_hasDerivAt _ hp
      rw [h0, Tensor.differential_diagonal _ (h x)] at he
      change HasDerivAt (k x) ((i+1) • diagonal (C x) y) 0 at he
      unfold n; rw [Nat.cast_smul_eq_nsmul]; exact he
    apply resists (U:=fun j x=> n⁻¹ • ((s j)⁻¹ • (k x (s j)-k x 0))) (fun j => (((he _).sub (he _)).mul ((s j)⁻¹)).mul _) fun x=> ?_
    simpa only [zero_add, inv_smul_smul₀ hn, comp_def] using! (tendsto_const_nhds (x:=n⁻¹)).smul ((hasDerivAt_iff_tendsto_slope_zero.mp (hh x)).comp hs)

variable {F : X→ E→ Y} [CompleteSpace Y] (hA : ∀ i, AnalyticAt ℝ (F i) 0)
include hA

lemma sane_radial (h : ∀ i : E, RLinear fun x=> F x i) (t : ℕ) : ∀ z,RLinear fun x=> diagonal (Tensor.coeff (F x) t 0) z := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro z
    let d i x:= Tensor.coeff (F x) i 0
    let T := fun (b:ℝ) (x:X) => ∑ i ∈ range t, (b^i) • diagonal (d i x) z
    have hj (b:ℝ):RLinear (T b):= RLinear.sum (range t) _ (fun i hi => (ih i (mem_range.mp hi) z).mul _)
    have hp x: Tendsto (fun b:ℝ => (b^t)⁻¹ • (F x (b • z)-T b x)) cutRay (𝓝 (diagonal (d t x) z)):=by
      obtain ⟨P,hP⟩:= hA x
      have hg i: diagonal (d i x) z=diagonal (P i) z:=by
        change (↑(i.factorial):ℝ)⁻¹ • (diagonal (iteratedFDeriv ℝ i (F x) 0) z)=_
        rw [diag_derivative hP,inv_smul_smul₀]; exact_mod_cast Nat.factorial_ne_zero i
      have hv := (hP.isBigO_sub_partialSum_pow (t+1)).comp_tendsto (along z)
      simp only [comp_def,zero_add,norm_smul] at hv
      apply scale_limit (f:=fun b:ℝ => F x (b • z)-T b x) t (diagonal _ z)
      have he (b:ℝ): P.partialSum (t+1) (b • z) = T b x+(b^t) • diagonal (d t x) z:= by
        rw [FormalMultilinearSeries.partialSum,sum_range_succ]; unfold T; congr 1
        · refine sum_congr rfl fun i _=> ?_; rw [hg]; exact Tensor.homogeneous ..
        rw [hg]; exact Tensor.homogeneous ..
      simp_rw [he,← sub_sub] at hv
      refine hv.trans (Asymptotics.isBigO_of_le' (c:=‖z‖^(t+1)) _ fun b => ?_)
      rw [norm_pow,norm_pow, Real.norm_of_nonneg (by positivity), mul_pow, mul_comm]
    obtain ⟨s,hs⟩:= exists_seq_tendsto cutRay
    exact resists (U:=fun i x=> ((s i)^t)⁻¹ • (F x (s i • z)-T (s i) x)) (fun i=> ((h _).sub (hj _)).mul _) fun x=> (hp x).comp hs

theorem RLinear.charge (h : ∀ i,RLinear fun x=> F x i) (t : ℕ) (p : Fin t → E) : RLinear fun x=> iteratedFDeriv ℝ t (F x) 0 p:=by
  have hx:= expanded (D:=fun x=> Tensor.coeff (F x) t 0) t (fun x=> Tensor.coeff_symm (hA x).contDiffAt) (sane_radial hA h t) p
  have hk:= hx.mul (↑t.factorial)
  have ht: (↑t.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero t
  convert hk using 1
  funext x; simp [Tensor.coeff,ht]
end completeX

lemma HLimit.bids {f : ℕ → Ortho I} {x : Ortho I} (h : HLimit f x) [FiniteDimensional ℝ Y] {p : Ortho I → Y} (he : RLinear p) : Tendsto (fun i=> p (f i)) atTop (𝓝 (p x)):=by
  obtain ⟨P,rfl⟩:=he
  let l := ((Module.finBasis ℝ Y).equivFun).toContinuousLinearEquiv
  apply l.toHomeomorph.isInducing.tendsto_nhds_iff.mpr
  refine tendsto_pi_nhds.mpr fun i=> ?_
  let v := ((ContinuousLinearMap.proj (R:=ℝ) i).comp l.toContinuousLinearMap).comp P
  have hv:= h.price ((InnerProductSpace.toDual ℝ (Ortho I)).symm v)
  simp_rw [InnerProductSpace.toDual_symm_apply] at hv; exact hv
end YM.UVExtension.Projection
