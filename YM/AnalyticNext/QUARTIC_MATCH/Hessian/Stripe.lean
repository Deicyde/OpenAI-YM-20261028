import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Counting
import YM.AnalyticNext.QUARTIC_MATCH.Pre.GaugeDir
import YM.Next.FREE_KERNELS.PatchMean

/-!
# No dimension loss in patch averages

True S weights count repeats. Include small sizes. Exact positive row/column
invoices (pre-L), not replacing convolution weight with one representative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG
open Pre.Centered YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate InnerProductSpace

variable {c f : Side} (S : StepData c f)
local notation "M" => S.patch.L
local notation "L" => (S.patch.L.val:ℝ)

section tile
def window (t : Site M) : S.patch.Small := ⟨lift t, S.ratio.half_box S.patch.odd_side t⟩
lemma window_onto : Bijective (window S) := ⟨fun _ _ h => lift_inj (congr_arg Subtype.val h),
    fun t => ⟨wrap M t.val,Subtype.ext (S.ratio.half_lift S.patch.odd_side t.val t.property)⟩⟩
lemma tile_size : (Fintype.card S.patch.Small:ℝ)=L^4 := by
  rw [← Fintype.card_congr (Equiv.ofBijective _ (window_onto S)),site_card,Nat.cast_pow]
lemma tile (b : Site f) (g : Site f → ℝ) :
    ∑ v : Site c, ∑ a : S.patch.Small, g (b+wrap f a.val+S.ratio.embed v)=∑ v, g v := by
  have he (x : Site c) : ∑ a : S.patch.Small, g (b+wrap f a.val+S.ratio.embed x) =
      ∑ i : Site S.ratio.count, g (b+S.ratio.assemble (x,i)) := by
    rw [← (Equiv.ofBijective _ (window_onto S)).sum_comp]; refine Finset.sum_congr rfl fun i _ => ?_
    unfold Ratio.assemble; change g (b+wrap f (lift i)+_) = _; exact congr_arg g (show b+ wrap f (lift i) + S.ratio.embed x=b+(S.ratio.embed x + wrap f (lift i)) by abel)
  simp_rw [he]
  rw [← Fintype.sum_prod_type (fun i => g (b+ S.ratio.assemble i))]
  exact (S.ratio.splitSites.symm.trans (Equiv.addLeft b)).sum_comp _

private def bag (B : Type*) (n : ℕ) : (Fin n→B) × B ≃ (Fin (n+1)→B) where
  toFun p := Fin.cons p.2 p.1
  invFun g := (Fin.tail g,g 0)
  left_inv := by rintro ⟨a,b⟩; simp
  right_inv := by intro; simp

lemma rollers (n : ℕ) (b : Site f) (g : Site f → ℝ) :
    ∑ v : Fin (n+1) → S.patch.Small, ∑ x : Site c, g (b+wrap f (∑ i, (v i).val)+S.ratio.embed x)=
    (Fintype.card (Fin (n+1)→S.patch.Small) : ℝ)/L^4*∑ x, g x := by
  rw [← (bag _ n).sum_comp,← Fintype.card_congr (bag _ n)]
  rw [Fintype.sum_prod_type]
  have he (u : Fin n → S.patch.Small) : ∑ a : S.patch.Small, ∑ x : Site c, g (b+wrap f (∑ i, ((bag _ n (u,a)) i).val)+S.ratio.embed x) = ∑ x, g x := by
    rw [Finset.sum_comm]
    convert! tile S (b+wrap f (∑ i, (u i).val)) g using 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Fin.sum_univ_succ]
    simp only [bag, Equiv.coe_fn_mk, Fin.cons_zero,Fin.cons_succ,map_add]; congr 1; abel
  rw [Finset.sum_congr rfl (fun i _ => he i),Finset.sum_const,nsmul_eq_mul,Fintype.card_prod,Nat.cast_mul,tile_size,Finset.card_univ]
  field_simp

lemma covers (g : Site f→ℝ) : ∑ x : Site c, ∑ v : S.patch.Points,S.patch.weight v*g (atPoint S x v) = (L^4)⁻¹ * ∑ x, g x := by
  have he (x : Site c) : ∑ v : S.patch.Points,S.patch.weight v*g (atPoint S x v) =
      (Fintype.card S.patch.Rolls:ℝ)⁻¹ * ∑ i : S.patch.Rolls, g (atPoint S x (S.patch.addRoll i)) := by
    unfold Patch.weight; simp_rw [Finset.sum_mul,ite_mul,zero_mul]; rw [Finset.sum_comm]
    simp_rw [Finset.sum_ite_eq,Finset.mem_univ,if_true,← Finset.mul_sum]
  simp_rw [he,← Finset.mul_sum]; rw [Finset.sum_comm]
  have hh : ∑ i : S.patch.Rolls, ∑ x : Site c, g (atPoint S x (S.patch.addRoll i)) = (Fintype.card S.patch.Rolls:ℝ)/L^4*∑ x, g x := by
    have ha : ∀ n : ℕ, 0<n → ∑ v : Fin n→S.patch.Small, ∑ x : Site c, g (wrap f (∑ i, (v i).val)+S.ratio.embed x) = (Fintype.card (Fin n→S.patch.Small) : ℝ)/L^4*∑ x, g x := by
      rintro (_ | n) h
      · omega
      simpa only [zero_add] using rollers S n 0 g
    exact ha _ ((show 0<4 by norm_num).trans_le S.patch.order_cut)
  rw [hh]; field_simp
end tile

lemma mean_pos (i j) : 0 ≤ Precision.mean S i j := by
  let v : form 1 f := Pi.single j 1
  have hv (x) : 0 ≤ v x := by by_cases h : x=j <;> simp [v,h]
  have he : Precision.mean S i j=(Precision.mean S *ᵥ v) i := by unfold v; rw [Matrix.mulVec_single_one]; rfl
  rw [he,mean_run_real]; exact Finset.sum_nonneg fun a _ => mul_nonneg (S.patch.weight_nonneg _) (Finset.sum_nonneg fun k _ => hv _)
lemma palette_pos (i j) : 0 ≤ palette S i j := by
  let v : form 0 f := Pi.single j 1
  have hv (x) : 0 ≤ v x := by by_cases h : x=j <;> simp [v,h]
  have he : palette S i j=(palette S *ᵥ v) i := by unfold v; rw [Matrix.mulVec_single_one]; rfl
  rw [he,palette_site]; exact Finset.sum_nonneg fun a _ => mul_nonneg (S.patch.weight_nonneg _) (hv _)

lemma mean_rows (i) : ∑ j, Precision.mean S i j=L := by
  have he := mean_run_real S (fun _ => 1) i
  simpa only [mean,Matrix.mulVec,dotProduct,Finset.sum_const, Finset.card_range,nsmul_eq_mul,mul_one,← Finset.sum_mul,S.patch.weight_sum,one_mul] using he
lemma palette_rows (i) : ∑ j, palette S i j = 1 := by
  have he := palette_site S (fun _ => 1) i
  simpa only [palette, Matrix.mulVec,dotProduct,mul_one,S.patch.weight_sum] using he
lemma mean_columns (j) : ∑ i, Precision.mean S i j = (L^3)⁻¹ := by
  let v : form 1 f := Pi.single j 1
  have he (i) : Precision.mean S i j=(Precision.mean S *ᵥ v) i := by unfold v; rw [Matrix.mulVec_single_one]; rfl
  have hx (i : TypeFace 1) (k : ℕ) : ∑ x : Site c, ∑ a : S.patch.Points, S.patch.weight a*v (atPoint S x a+k • step (axisEquiv.symm i), i) =
      (L^4)⁻¹ * ∑ x : Site f, v (x,i) := by
    convert! covers S (fun x => v (x+k • step (axisEquiv.symm i),i)) using 1
    congr 1
    exact (Equiv.sum_comp (Equiv.addRight (k • step (axisEquiv.symm i) : Site f))  (fun x => v (x,i))).symm
  have hh (i : TypeFace 1) : ∑ x : Site c, (Precision.mean S *ᵥ v) (x,i)=L*((L^4)⁻¹*∑ x : Site f,v (x,i)) := by
    simp_rw [mean_run_real,Finset.mul_sum]
    conv_lhs => arg 2; intro x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]; simp_rw [hx i,Finset.sum_const,Finset.card_range,nsmul_eq_mul]; simp only [Finset.mul_sum]
  simp_rw [he]; rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [hh,← Finset.mul_sum];
  conv_lhs => rw [Finset.sum_comm, ← Fintype.sum_prod_type v]
  have hV : ∑ i : Body 1 f, v i=1 := by simp [v]
  rw [hV]; field_simp
lemma palette_columns (j) : ∑ i, palette S i j=(L^4)⁻¹ := by
  let v : form 0 f := Pi.single j 1
  have he (i) : palette S i j=(palette S *ᵥ v) i := by unfold v; rw [Matrix.mulVec_single_one]; rfl
  have hh (i : TypeFace 0) : ∑ x : Site c, (palette S *ᵥ v) (x,i)= (L^4)⁻¹*∑ x : Site f,v (x,i) := by
    rw [vac_only i]; simp_rw [palette_site]; exact covers S fun x => v (x,vac)
  simp_rw [he]; rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [hh,← Finset.mul_sum]; rw [Finset.sum_comm, ← Fintype.sum_prod_type v]; simp [v]

lemma palate (u : Body 0 f→ℂ) : ell2 (approached (palette S)*ᵥu) ≤ (L^2)⁻¹ * ell2 u :=
    smear (a:=1) (b:=(L^4)⁻¹) (fun i => by simp only [approached, Matrix.map_apply, Complex.norm_real, Real.norm_of_nonneg (palette_pos ..), palette_rows]; exact le_rfl)
      (by positivity) (fun j => by simp only [approached, Matrix.map_apply, Complex.norm_real, Real.norm_of_nonneg (palette_pos ..), palette_columns]; exact le_rfl)
      (by apply le_of_eq; field_simp) (by positivity) u
lemma palateT (u : Body 0 c→ℂ) : ell2 ((approached (palette S))ᴴ *ᵥ u) ≤ (L^2)⁻¹ * ell2 u :=
    smear (b:=1) (a:=(L^4)⁻¹) (fun i => by
      simp only [approached, conjTranspose_apply, norm_star,Matrix.map_apply, Complex.norm_real,
        Real.norm_of_nonneg (palette_pos ..), palette_columns]
      exact le_rfl)
      (by positivity) (fun j => by
        simp only [approached,conjTranspose_apply,norm_star, Matrix.map_apply, Complex.norm_real,
          Real.norm_of_nonneg (palette_pos ..), palette_rows]
        exact le_rfl)
      (by apply le_of_eq; field_simp) (by positivity) u
lemma fraction (u : Body 1 f→ℂ) : ell2 (approached (Precision.mean S)*ᵥ u) ≤ L⁻¹ * ell2 u :=
    smear (a:=L) (b:=(L^3)⁻¹) (fun i => by simp only [approached, Matrix.map_apply, Complex.norm_real, Real.norm_of_nonneg (mean_pos ..), mean_rows]; exact le_rfl)
      (by positivity) (fun j => by simp only [approached, Matrix.map_apply, Complex.norm_real, Real.norm_of_nonneg (mean_pos ..), mean_columns]; exact le_rfl)
      (by apply le_of_eq; field_simp) (by positivity) u
end YM.AnalyticNext.QuarticMatch.Hessian
