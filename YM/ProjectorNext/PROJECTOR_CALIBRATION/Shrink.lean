import YM.ProjectorNext.PROJECTOR_CALIBRATION.Force

/-! # Detecting the highest off-shell jet with gradients

An alternative to checking a preassigned finite difference stencil symbol at
each order. Use all samples on the cover, then reduce to a fixed finite set in
duality. Adapt G03 shrinking grid to a plaquette DIFFERENCE: only assert
detection of the onShell criterion on the **top homogeneous Taylor component**.
Lower components here may be affected by discretization corrections from on-
shell higher components; can't assume we can reconstruct *every*
homogeneous divergence without triangular error.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration.Div
open Lattice RG Wilson Source Source.Drops Labels Maxwell Work Work.G03 Function Tensor Analysis Set MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {j d : ℕ}

private lemma continuous_second (A : Taylor G j) (k i l : Axis) :
    Continuous (Maxwell.grad k (Maxwell.grad i (A.value l))) := by
  refine ((contDiff_iff_contDiffAt (n:=∞)).mpr fun x => grad_smooth k (grad_smooth i ?_ (n:=∞) (m:=∞) (by simp)) (by simp)).continuous
  exact (diag_smooth (A.val l) ∞).contDiffAt

/-- Averages of second derivatives. Extra variable for the transverse displacement. -/
def second (A : Taylor G j) (i l k : Axis) (x : E4) (t : ℝ) :=
    ∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, ∫ v : ℝ in 0..1,
      Maxwell.grad k (Maxwell.grad i (A.value l)) (x+(t*s) • basis l + (t*r) • basis i - (v*t) • basis k)

lemma continuous_average (A : Taylor G j) (i l k : Axis) :
    Continuous fun p : E4 × ℝ => second A i l k p.1 p.2 := by
  unfold second; iterate 3 apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_second A k i l).comp (by fun_prop)

lemma cell_difference (A : Taylor G j) (i l k : Axis) (x : E4) (t : ℝ) :
    t • second A i l k x t = meanPartial A i l x t - meanPartial A i l (x - t • basis k) t := by
  let F := Maxwell.grad i (A.value l)
  have hf : Continuous F := continuous_grad A i l
  have hd (y : E4) : DifferentiableAt ℝ F y :=
    (grad_smooth i (m:=∞) (n:=∞) (x:=y) (f:=A.value l) (diag_smooth (A.val l) ∞).contDiffAt (by simp)).differentiableAt (by simp)
  have he (z : E4) : t • (∫ v : ℝ in 0..1, grad k F (z - (v*t) • basis k)) = F z - F (z - t • basis k) := by
    rw [← intervalIntegral.integral_smul]
    have h (v : ℝ) : HasDerivAt (fun u : ℝ => -F (z - (u*t) • basis k))
        (t • grad k F (z - (v*t) • basis k)) v := by
      have hv : HasDerivAt (fun u : ℝ => z-u • (t • basis k)) (-(t • basis k)) v := by
        simpa using! HasDerivAt.const_sub z ((hasDerivAt_id' v).smul_const (t • basis k))
      simp_rw [smul_smul] at hv
      exact (((hd _).hasFDerivAt.comp_hasDerivAt v hv).neg).congr_deriv (by simp; rfl)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => h u)]
    · simp; abel
    exact ((((continuous_second A k i l).comp (f:=fun v => z-(v*t) • basis k) (by fun_prop)).const_smul t).intervalIntegrable ..)
  unfold second meanPartial
  simp_rw [← intervalIntegral.integral_smul]
  change (∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, ∫ v : ℝ in 0..1, t • grad k F _) = _
  have He (z : E4) := he z
  simp_rw [← intervalIntegral.integral_smul] at He
  simp_rw [He (x+_+_)]
  let f (x : E4) (s r : ℝ) := F (x+(t*s) • basis l+(t*r) • basis i)
  have h (s r : ℝ) : x+(t*s) • basis l+(t*r) • basis i-t • basis k =
      x-t • basis k+(t*s) • basis l+(t*r) • basis i := by abel
  simp_rw [h]
  change (∫ s : ℝ in 0..1, ∫ r : ℝ in 0..1, f x s r - f (x - t • basis k) s r) = _
  have ht (x : E4) : Continuous (fun p : ℝ × ℝ => f x p.1 p.2) := hf.comp (by fun_prop)
  have hg (x : E4) : Continuous (fun s => ∫ r : ℝ in 0..1, f x s r) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; exact ht x
  have hb (x : E4) (s) : IntervalIntegrable (fun r => f x s r) volume 0 1 :=
    ((ht x).comp (f:=fun (r : ℝ) => (s,r)) (by fun_prop)).intervalIntegrable ..
  simp_rw [intervalIntegral.integral_sub (hb _ _) (hb _ _), intervalIntegral.integral_sub ((hg _).intervalIntegrable _ _) ((hg _).intervalIntegrable _ _)]
  rfl

/-- Positive difference in k of the i,l net operator. -/
def quot (A : Taylor G j) (i l k : Axis) (x : E4) (t : ℝ) := second A i l k x t - second A l i k x t

lemma quot_zero (A : Taylor G j) (i l k : Axis) (x : E4) :
    quot A i l k x 0 = grad k (diagonal (takeCurl A i l)) x := by
  have hf (a b : Axis) : DifferentiableAt ℝ (grad a (A.value b)) x :=
    (grad_smooth a (m:=∞) (n:=∞) (x:=x) (f:=A.value b) (diag_smooth (A.val b) ∞).contDiffAt (by simp)).differentiableAt (by simp)
  rw [takeCurl_diag,grad,D, fderiv_sub (hf _ _) (hf _ _)]
  unfold quot second
  simp; rfl

lemma quot_diff (A : Taylor G j) (i l k : Axis) (x : E4) (t : ℝ) :
    t • quot A i l k x t = net A i l x t - net A i l (x-t • basis k) t := by
  simp_rw [quot,smul_sub,cell_difference,net]; abel

/-- Signed formula on plaquettes in canonical axis order. -/
def balance (A : Taylor G j) (x : E4) (ν : Axis) (q : PlaqAxes) (t : ℝ) : G.Color :=
    (if q.val.1=ν then quot A ν q.val.2 q.val.2 x t else 0) -
    (if q.val.2=ν then quot A q.val.1 ν q.val.1 x t else 0)

private lemma cast_sub (x : Cover) (i : Axis) : castPos (x-step i) = castPos x - basis i := by
  rw [eq_sub_iff_add_eq, ← castPos_step, sub_add_cancel]

lemma scale_balance (A : Taylor G j) (x : Cover) (ν : Axis) (q : PlaqAxes) (t : ℝ) :
    t • balance A (t • castPos x) ν q t =
      t^j • delta (fun y r => net A r.val.1 r.val.2 (castPos y) 1) x ν q := by
  simp_rw [balance,delta]
  split_ifs with h h'
  all_goals simp_all [cast_sub, smul_neg]
  all_goals rw [quot_diff, ← smul_sub t,scale_net,scale_net,smul_sub] <;> abel

lemma continuous_balance (A : Taylor G j) (ν : Axis) (q : PlaqAxes) :
    Continuous fun p : E4 × ℝ => balance A p.1 ν q p.2 := by
  unfold balance quot
  split_ifs <;> refine Continuous.sub ?_ ?_
  all_goals first | exact (continuous_average ..).sub (continuous_average ..) | exact continuous_const

private def term (A : Taylor G j) (x : E4) (ν k : Axis) := -grad k (diagonal (takeCurl A k ν)) x

lemma balance_zero (A : Taylor G j) (x : E4) (ν : Axis) :
    ∑ q : PlaqAxes, balance A x ν q 0 = -(∑ i : Axis, grad i (diagonal (takeCurl A i ν)) x) := by
  have hz : takeCurl A ν ν = 0 := by simp [takeCurl]
  have h0 : term A x ν ν = 0 := by
    unfold term; rw [hz]; change -fderiv ℝ (fun _ : E4 => (0 : G.Color)) x _ = 0; simp
  have hi (i : Axis) : ∑ q : PlaqAxes, (if (q.val=(ν,i) ∨ q.val=(i,ν)) then term A x ν i else 0) = term A x ν i := by
    by_cases h : i=ν
    · subst i; simp [h0]
    let a : PlaqAxes := PlaqAxes.ordered i ν h
    have he (q : PlaqAxes) : (q.val=(ν,i) ∨ q.val=(i,ν)) ↔ q=a := by
      rcases lt_or_gt_of_ne h with h|h
      all_goals rw [← Subtype.val_inj]; change (_ ∨ _ ↔ q.val = (min i ν,max i ν))
      · rw [min_eq_left h.le,max_eq_right h.le]; refine or_iff_right ?_
        intro hx; have hh := q.property; rw [hx] at hh; exact h.asymm hh
      rw [min_eq_right h.le,max_eq_left h.le]; refine or_iff_left ?_
      intro hx; have hh := q.property; rw [hx] at hh; exact h.asymm hh
    simp_rw [he]; simp
  change _ = -(∑ i : Axis, grad i _ _)
  rw [← Finset.sum_neg_distrib]
  change _ = ∑ i : Axis, term A x ν i
  calc
    _ = ∑ q : PlaqAxes, ∑ i : Axis, if (q.val=(ν,i) ∨ q.val=(i,ν)) then term A x ν i else 0 := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rcases q with ⟨⟨a,b⟩,hab⟩
      change a < b at hab
      have hn := hab.ne
      change balance A x ν ⟨(a,b),hab⟩ 0 = _
      by_cases h : a=ν
      · subst a
        simp only [balance, Ne.symm hn, ↓reduceIte,sub_zero,Prod.mk.injEq,true_and,and_false,or_false,Finset.sum_ite_eq,Finset.mem_univ]
        rw [quot_zero]; unfold term
        rw [show takeCurl A ν b = -takeCurl A b ν from (closedCurl A).antisymmetric ν b]
        change (fderiv ℝ (-diagonal (takeCurl A b ν)) x) _ = _
        rw [fderiv_neg]; rfl
      by_cases h' : b=ν
      · subst b
        simp [balance,h,term,quot_zero]
      simp [balance,h,h']
    _ = _ := by rw [Finset.sum_comm]; simp_rw [hi]

lemma linearFace_sum (A : Snap G d) (x : Cover) (q : PlaqAxes) :
    linearFace A x q = ∑ k : Fin (d-1), net (A k) q.val.1 q.val.2 (castPos x) 1 := by
  rw [linearFace, square_sum]
  simp only [edge_sum, castPos_step]
  have he := Fin.sum_univ_eq_sum_range (fun j : ℕ => net (expand d A j) q.val.1 q.val.2 (castPos x) 1) (d-1)
  simp only [expand,dif_pos (Fin.is_lt _)] at he -- dependent in RHS too?
  rw [he]
  simp_rw [net,partial_eq_diff,Finset.sum_sub_distrib]; unfold expand; abel

lemma delta_sum {ι : Type*} {m : Finset ι} (Y : ι → Cover → PlaqAxes → G.Color)
    (x : Cover) (ν : Axis) (q : PlaqAxes) :
    delta (fun x q => ∑ i ∈ m, Y i x q) x ν q = ∑ i ∈ m, delta (Y i) x ν q := by
  unfold delta
  split_ifs <;> simp [Finset.sum_sub_distrib, *]

/-- The samples detect the continuum equation leg of the top component:
if all sample gradients vanish on polynomial data with no Taylor orders
above k then top ordinary divergence vanishes. Prove by shrinking the cell
while staying on the actual infinite cover in the premises. -/
theorem detects (H : Hol G) (k : Fin (d-1)) {A : Snap G d} (hk : ∀ l, k<l → A l = 0)
    (h : ∀ x : Position, linearSample H d x A = 0) : takeCurl (A k) ∈ onShell G.Color k.val := by
  refine ⟨closedCurl _,?_⟩
  intro ν z
  let P (p : E4 × ℝ) := ∑ l : Fin (d-1), p.2^(k.val-l.val) • ∑ q : PlaqAxes, balance (A l) p.1 ν q p.2
  have he (x : Cover) : ∑ l : Fin (d-1), ∑ q : PlaqAxes, delta (fun y q => net (A l) q.val.1 q.val.2 (castPos y) 1) x ν q = 0 := by
    have hh := h (x,ν)
    rw [linearSample_eq] at hh
    have hy : linearFace A = fun y (q : PlaqAxes) => ∑ l : Fin (d-1), net (A l) q.val.1 q.val.2 (castPos y) 1 := funext fun y => funext fun q => linearFace_sum A y q
    rw [hy] at hh
    have hf (l : PlaqAxes) : delta (fun y (q : PlaqAxes) => ∑ i : Fin (d-1), net (A i) q.val.1 q.val.2 (castPos y) 1) (x,ν).1 (x,ν).2 l = ∑ i : Fin (d-1), delta (fun y (q : PlaqAxes) => net (A i) q.val.1 q.val.2 (castPos y) 1) x ν l := delta_sum (m:=Finset.univ) (fun i y q => net (A i) q.val.1 q.val.2 (castPos y) 1) x ν l
    simp_rw [hf] at hh; rw [Finset.sum_comm] at hh
    exact hh
  have hm (t : ℝ) (ht : 0<t) (x : Cover) : P (t • castPos x,t) = 0 := by
    apply smul_right_injective G.Color ht.ne'
    dsimp only [P]; rw [Finset.smul_sum,smul_zero]
    conv_rhs => rw [← smul_zero (t^k.val)] -- arguments
    rw [← he x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm t, Finset.smul_sum]
    simp_rw [scale_balance]
    rw [← Finset.smul_sum,smul_smul]
    by_cases hv : k < l
    · simp only [hk _ hv,G03.net_zero]
      simp [delta]
    rw [← pow_add,Nat.sub_add_cancel (by simpa using le_of_not_gt hv : l.val ≤ k.val)]
  have hZ : P (z,0) = ∑ q : PlaqAxes, balance (A k) z ν q 0 := by
    unfold P
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      by_cases hh : k < l
      · unfold balance quot
        have hq (a b c : Axis) : second (0 : Taylor G l.val) a b c z 0 = 0 := by
          unfold second grad D
          change (∫ _ : ℝ in 0..1, ∫ _ : ℝ in 0..1, ∫ _ : ℝ in 0..1, fderiv ℝ (fun x => fderiv ℝ (fun _ : E4 => (0:G.Color)) x _) _ _) = _
          simp
        simp [hk _ hh,hq]
      exact (congr_arg (fun y : ℝ => y • _) (zero_pow (Nat.sub_ne_zero_of_lt
        (show l.val < k.val from lt_of_le_of_ne (le_of_not_gt hh) (fun e => hl (Fin.ext e)))))).trans (zero_smul ..)
    simp
  have hp : Continuous P := continuous_finsetSum _ fun i _ => (continuous_snd.pow _).smul (continuous_finsetSum _ fun q _ => continuous_balance (A i) ν q)
  have ht : Tendsto (fun t : ℝ => P (t • castPos (index t z),t)) (𝓝[>] 0) (𝓝 (P (z,0))) :=
    (hp.tendsto _).comp ((shrink_grid z).prodMk_nhds (tendsto_id.mono_left nhdsWithin_le_nhds))
  have hc : Tendsto (fun _ : ℝ => (0:G.Color)) (𝓝[>] 0) (𝓝 (P (z,0))) := ht.congr' (eventually_nhdsWithin_of_forall fun t h => hm t h _)
  simpa [hZ,balance_zero] using tendsto_nhds_unique hc tendsto_const_nhds
end YM.ProjectorNext.Calibration.Div
