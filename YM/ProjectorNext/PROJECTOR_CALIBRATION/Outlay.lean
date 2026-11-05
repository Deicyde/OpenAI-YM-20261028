import YM.ProjectorNext.PROJECTOR_CALIBRATION.Unpack

/-!
# Price the actual initial crossed cylinders before submitting to Campaign makers

Scale costs on ordered link derivatives on *good stencils* as in  ff.
Not an imputed bound on already masked insertions / α names. Fixed k,P and
label order, connectors, chosen S, all before periods etc; may need add to
pre-L/p_N receipts in a configuration with supported sizes growing at repeated
stages (not addressing such scheduling here).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration.Outlay
open Wilson Lattice RG Labels Work Work.G07 Tensor
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {s : Finset Cover} {k p d a : ℕ}

local notation "leg" j ":" q => Rate k p s j q
section Costs
variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : CoverConfig G → E} {n : ℕ}

lemma relax (h : Rate k p s n a f) : Rate k p s n 0 f := by
  obtain ⟨c,hc,h⟩ := h
  refine ⟨c,hc,fun b hb N o => ?_⟩
  have he := h b hb N o
  rw [pow_zero]
  refine ⟨he.1,he.2,fun l hl hi U hU => ?_⟩
  rw [one_pow,mul_one]
  exact (he.3 l hl hi U hU).trans (mul_le_of_le_one_right he.2
    (pow_le_one₀ (pow_nonneg b.threshold_pos.le a) (pow_le_one₀ b.threshold_pos.le b.threshold_le)))

lemma spare : Rate k p s n a (fun _ : CoverConfig G => (0:E)) := by
  refine ⟨0,le_rfl,fun b hb N o => ?_⟩
  simpa using (LeftBound.const (r:=b.threshold^a) (pow_nonneg b.threshold_pos.le _) (0:E) :
    LeftBound k (b.dirBound o) (Healthy b.threshold (s.image fun x => wrap N x+o)) (b.threshold^a) ‖(0:E)‖ _ (n:=N) (G:=G))

lemma rateSum {I : Type*} (w : Finset I) (Z : I → CoverConfig G → E) (h : ∀ i∈w, Rate k p s n a (Z i)) :
    Rate k p s n a (fun U => ∑ i∈w,Z i U) := by
  classical
  induction w using Finset.induction_on with
  | empty => simp; exact spare
  | insert i w hi ih => simp only [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj => h j (by simp_all))

lemma ratePi {I : Type*} [Fintype I] [FiniteDimensional ℝ E] (X : I → CoverConfig G → E) (h : ∀ i, Rate k p s n a (X i)) :
    Rate k p s n a (fun U i => X i U) := by
  classical
  let L (i : I) : E →ₗ[ℝ] I → E := LinearMap.single ℝ (fun _ => E) i
  rw [show (fun U i => X i U) = fun U => ∑ i,L i (X i U) from funext fun U => funext fun j => by
    simp [Finset.sum_apply,L,Finset.sum_pi_single]]
  exact rateSum _ _ fun i _ => (h i).postcomp (L i).toContinuousLinearMap

lemma credit {l : ℕ} [FiniteDimensional ℝ E] (B : Tensor.T E ℂ l) (f : Fin l → CoverConfig G → E)
    (n : Fin l → ℕ) (h : ∀ i, Rate k p s (n i) a (f i)) : Rate k p s (∑ i,n i) a (fun U => B fun i => f i U) := by
  induction l with
  | zero =>
    have he : (∑ i : Fin 0,n i)=0 := Finset.sum_of_isEmpty _
    rw [he,show (fun U => B fun i => f i U)=fun U : CoverConfig G => Tensor.diagonal B 0 from funext fun U => congr_arg B (Subsingleton.elim ..)]
    exact Rate.const _
  | succ l ih =>
    let b := Module.finBasis ℝ E
    let r (i) (U : CoverConfig G) : ℂ := (b.coord i (f 0 U) : ℝ)
    let X (i) U := (B.curryLeft (b i)) fun j => f j.succ U
    have hv (U) : B (fun i => f i U) = ∑ i, r i U * X i U := by
      rw [show (fun i => f i U)=Fin.cons (f 0 U) (fun j => f j.succ U) from (Fin.cons_self_tail _).symm]
      change B.curryLeft (f 0 U) _ = _; rw [← b.sum_repr (f 0 U),map_sum,sum_apply]
      simp only [map_smul,smul_apply,Complex.real_smul]; rfl
    simp_rw [Fin.sum_univ_succ n, funext hv]
    refine rateSum _ _ fun i _ => ((h 0).postcomp (Complex.ofRealCLM.comp (b.coord i).toContinuousLinearMap)).mul ?_
    exact ih (B.curryLeft (b i)) (fun j => f j.succ) (fun j => n j.succ) (fun j => h _)
end Costs

/- Relative (geometry only) holds for each particular finite support that
opens ALL curvature & energy probes' stencils. Export actual fixed S. -/
variable {H : Source.Hol G} (M : Machine H d) (F : Labels.Frame G d)

def faces (i : M.Outlet) (v : PlaqAxes) : Fin 3 → RG.Slot :=
    let x:= (M.address i).1
    ![⟨route 0 x 1,v⟩,⟨route 0 (x-step v.val.2) 1,v⟩,⟨route 0 (x-step v.val.1) 1,v⟩]

/-- Larger stencil used even for other u terms in certified cylinder,
including paths belonging only to the selected Machine. -/
def garden := M.curtain ∪ (Finset.univ.biUnion (fun i => (M.loops i).stencil) ∪
    (Finset.univ.biUnion fun (v : PlaqAxes) => Finset.univ.biUnion fun i : M.Outlet =>
      Finset.univ.biUnion fun j => (faces M i v j).stencil))

lemma housed : M.Release (garden M) :=
  let h : M.curtain ⊆ garden M := Finset.subset_union_left
  ⟨h M.served.anchor,fun _ => h (M.served.start _),fun _ => h (M.served.finish _),M.served.takes.enlarge h,
    fun _ _ => (M.served.routes ..).enlarge h,fun _ => (M.served.force _).enlarge h⟩

lemma estimates (k p : ℕ) : Rate k p (garden M) 1 0 M.estimate :=
    Rate.postcomp (ratePi (E:=G.Color) (G:=G) (fun i => (M.loops i).eval) fun i => paid_slot _
      (fun _ hx => Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hx⟩)))) M.recover.toContinuousLinearMap

lemma rate_channel (k p : ℕ) (i : M.Outlet) (c : G.Color) : Rate k p (garden M) 0 0 (fun U => M.channel i U c) := by
  have ht : Rate k p (garden M) 0 1 (fun U : CoverConfig G => G.mat (travel U _ (base (M.address i)))) := rate_path (0:Cover) _
  have hc := Rate.const (k:=k) (P:=p) (S:=garden M) (a:=1) (G:=G) (G.colorMat c)
  exact relax (((ht.mul hc).mul (ht.postcomp (starL' ℝ).toContinuousLinearMap)).postcomp ((M.tap i).toContinuousLinearMap.comp G.projectColor.toContinuousLinearMap))

lemma rate_valve (m : F.Index) (k p : ℕ) (i : M.Outlet) (c : G.Color) :
    Rate k p (garden M) ((F.grades m).2-1) 0 (M.valve F m i c) := by
  let l := (F.grades m).2
  unfold Machine.valve; simp_rw [Cross.mixSum]
  refine rateSum _ _ fun j _ => ?_
  let f (v : Fin l) (U) := Cross.cell M.U (M.estimate U) j (M.channel i U c) v
  let n (v : Fin l) : ℕ := if v=j then 0 else 1
  rw [show (F.grades m).2 - 1=∑ v,n v by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    rw [Finset.sum_congr rfl (g:=fun _ => 1) (fun k hk => if_neg (Finset.ne_of_mem_erase hk))]; simp [n,l]]
  refine credit (Machine.shade F m) f n ?_
  intro v; unfold f Cross.cell; by_cases hv : v=j
  · subst v; simp [n]; exact rate_channel M k p i c
  simp_rw [Function.update_of_ne hv,n,if_neg hv]
  unfold Cross.field; split
  · exact estimates M k p
  exact (estimates M k p).postcomp (LinearMap.toContinuousLinearMap M.U)
end YM.ProjectorNext.Calibration.Outlay
