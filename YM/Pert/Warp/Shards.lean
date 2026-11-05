import YM.Pert.Warp.Rowdy
/-! Matching the two deletion rules (actual orbital Gaussian with imaginary counterterm and on-shell Maxwell generalized free). -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
namespace YM.Pert.Warp
open Align Lattice Orb MeasureTheory ProbabilityTheory Maxwell Function Full Labels Bare Wick Extra.FD.Pair Filter Topology
open scoped Topology
variable {N : Side} {G : Gauge} {r d : ℕ} {I : Type*} [DecidableEq I] {i : I}
variable (h : ℝ) (o : Grid N r) (z : Points r) (tag : I → Fin r) (code : I → CosKey G d)

def spline (s : Finset I): Fin r→ WickPol G := reduceEq ∘ (root tag code s)
lemma spline_eq (s : Finset I) (hi : i∈s) : update (spline tag code (s.erase i)) (tag i) (spline tag code (s.erase i) (tag i)*reduceEq (MvPolynomial.X (code i).val)) = spline tag code s := by
  funext k;by_cases hk : k=tag i
  · subst k; rw [update_self]
    unfold spline root; rw [comp_apply,comp_apply,←map_mul]; apply congrArg _; rw [Finset.filter_erase]; exact Finset.prod_erase_mul _ _ (Finset.mem_filter.mpr ⟨hi,rfl⟩)
  have hh : (s.filter (fun j=>tag j=k)).erase i = s.filter (fun j=>tag j=k) := Finset.erase_eq_of_notMem (fun h=>hk (Finset.mem_filter.mp h).2.symm)
  rw [update_of_ne hk]; unfold spline root; rw [comp_apply,comp_apply]; apply congrArg _; rw [Finset.filter_erase,hh]
lemma retape (s : Finset I) (k:Fin r) {i} (hi : i∈s.filter (tag · =k)) : update (spline tag code s) k (spline tag code (s.erase i) k) = spline tag code (s.erase i) := by
  rw [←spline_eq tag code s (Finset.mem_filter.mp hi |>.1), Finset.mem_filter.mp hi |>.2, update_idem _ _ _, update_eq_self]

def cut (s : Finset I) : ℂ := (moment G z) (spline tag code s)

theorem cut_one (hz : z∈conf r) (s : Finset I) (hi : i∈s) : cut z tag code s = ∑ j∈s.erase i, (indirect z (tag i) (tag j) (code i).val (code j).val : ℝ) * cut z tag code ((s.erase i).erase j) := by
  let w:=s.erase i
  let W:=spline tag code w
  let k:=tag i
  have he : cut z tag code s = ∑ k' : Others k, replace z W k' (ladder (code i : Labels.Key G) (z k) (z k') (W k')) := (congrArg (moment G z) (spline_eq tag code s hi).symm).trans (take_line z hz (code i).val (tag i) W) -- syntax? `(take_line z hz ...`)
  rw [he]
  let t (a : Fin r) := w.filter (fun j=>tag j=a)
  let E (j : I) := (indirect z (tag i) (tag j) (code i).val (code j).val : ℝ)
  let f (j:I) := (E j : ℂ) * cut z tag code (w.erase j)
  have hD (v : Others k): ladder (code i:Labels.Key G) (z k) (z v) (W v) = ∑ j∈t v.val,(E j:ℂ) • spline tag code (w.erase j) v.val := by
    have hd : z k-z v.val ≠ 0 := sub_ne_zero.mpr ((show Injective (WithLp.ofLp z) from hz).ne v.property.symm)
    rw [(show W v.val = reduceEq (∏ j∈t v.val,MvPolynomial.X (R:=ℂ) (code j).val) from rfl), D_kill _ _ (fun j=>(code j).val) _ _ hd]
    refine Finset.sum_congr rfl fun j (hj : j∈t v.val)=>?_ 
    have hv : tag j=v.val:=Finset.mem_filter.mp hj |>.2
    unfold E indirect spline root; rw [hv,comp_apply, Finset.filter_erase,if_neg v.property.symm]
  have hr (v : Others k) : replace z W v.val (ladder (code i:Labels.Key G) (z k) (z v) (W v)) = ∑ j∈t v.val, f j := by
    rw [hD,map_sum]; refine Finset.sum_congr rfl fun j (hj:j∈t v.val)=>?_ ; rw [map_smul, replace_at]; change (E j : ℂ) * _ = _; exact congrArg _ (congrArg _ (retape tag code w v.val hj))
  let F₀ (i' : Fin r) := ∑ j∈t i', f j
  have hh : ∑ u, F₀ u = ∑ j∈w, f j := Finset.sum_fiberwise w tag f
  have hh' := Finset.sum_erase_add (Finset.univ : Finset (Fin r)) F₀ (Finset.mem_univ k)
  have hk' : F₀ k=0 := by apply Finset.sum_eq_zero; intro a ha; unfold f E; rw [Finset.mem_filter.mp ha |>.2]; simp [indirect,k]
  have hbe : ∑i : Others k,F₀ i.val = ∑ i∈Finset.univ.erase k,F₀ i := Finset.sum_bij (fun a _=>a.val) (fun a _=>Finset.mem_erase_of_ne_of_mem a.property (Finset.mem_univ _)) (fun _ _ _ _ h=>Subtype.ext h) (fun a ha=>⟨⟨a,Finset.ne_of_mem_erase ha⟩,Finset.mem_univ _,rfl⟩) (fun _ _=>rfl)
  rw [hk',add_zero,← hbe,hh] at hh'; exact (Finset.sum_congr rfl fun a _=>hr a).trans hh'
lemma cut_cancel (hz : z∈conf r) (s : Finset I) : s.card • cut z tag code s = ∑ i∈s,∑ j∈s.erase i, (indirect z (tag i) (tag j) (code i).val (code j).val : ℝ) * cut z tag code ((s.erase i).erase j) := by rw [← Finset.sum_const]; exact Finset.sum_congr rfl fun a ha=>(cut_one z tag code hz s ha)
end YM.Pert.Warp
