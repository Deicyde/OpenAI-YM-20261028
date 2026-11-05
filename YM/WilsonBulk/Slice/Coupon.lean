import YM.WilsonBulk.Slice.Planar

/-!
# Toll formula under analytic map (operator on formal display)

`tilt` is the determinant of the ordinary **vertical** part, with private
columns. Track sign across full germ by finding enough positive/negative
neighborhood, using formal values and real probability equations. No assumption
that all orientations use same sign; pay relative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology BigOperators Classical ContDiff Matrix
open Function Filter PowerSeries Matrix Finset
variable {α β κ ι E : Type} [Fintype α] [Fintype β] [Fintype κ] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {θ : Tabletop (Chamber α ι) → Tabletop α}
omit [Fintype β] in
lemma cont_diff_prod (p : β→Tabletop α→ℝ) (s : Finset β) (h : ∀ i∈s,ContDiffAt ℝ ω (p i) 0) : ContDiffAt ℝ ω (∏ i∈s,p i) 0 := by
  rw [show (∏ i∈s,p i)=(fun x:Tabletop α=>∏ i∈s, p i x) by ext1 x; rw [Finset.prod_apply]]; exact contDiffAt_prod h -- inspect
omit [Fintype β] in
lemma ink_product (p : β→Tabletop α→ℝ) (s : Finset β) (h : ∀ i∈s,ContDiffAt ℝ ω (p i) 0) : ink (∏ i∈s,p i)=∏ i∈s,ink (p i) := by
  induction s using Finset.induction with
  | empty=> rw [prod_empty,prod_empty]; exact (ink_const 1).trans (by simp)
  | insert i s hi ih=> have hz : ∀ i∈s,ContDiffAt ℝ ω (p i) 0:=fun _ hi=> h _ (mem_insert_of_mem hi); rw [prod_insert hi,prod_insert hi,ink_mul (h _ (mem_insert_self ..)) (cont_diff_prod p s hz),ih hz]
lemma field_left (α ι : Type) [Fintype α] [Fintype ι] (b : Tabletop ι) :
    let L := (assemble α ι).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _); ∀ x:Tabletop α, HasFDerivAt (fun y => Sum.elim y b) L x := by
  intro L x; rw [show (fun y=>Sum.elim y b)=(fun y:Tabletop α=> L y + Sum.elim (0:Tabletop α) b) from ?_]; exact L.hasFDerivAt.add_const _; ext1 v; ext1 i; cases i <;> first| exact (add_zero _).symm| exact (zero_add _).symm
def verticalChange (θ : Tabletop (Chamber α ι) → Tabletop α) (v : Tabletop (Chamber α ι)) (x : Tabletop α) := θ (Sum.elim x (lower α ι v))
lemma vert_link {ν : Tabletop (Chamber α ι)} (hθ : DifferentiableAt ℝ θ ν) : HasFDerivAt (verticalChange θ ν)
      ((fderiv ℝ θ ν).comp ((assemble α ι).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _))) (upper α ι ν) := by
  have h := hθ.hasFDerivAt; let g := fun v:Tabletop α=> Sum.elim v (lower α ι ν); have he : g ((upper α ι) ν)=ν:= mirror_pose _
  exact (show HasFDerivAt θ _ (g (upper α ι ν)) by rw [he]; exact h).comp _ (field_left _ _ _ _)
variable [DecidableEq α]
def tilted (θ : Tabletop (Chamber α ι)→Tabletop α) (z : Tabletop (Chamber α ι)) : Matrix α α ℝ := Matrix.of fun i j=> leafD (Sum.inl j) (fun x=> θ x i) z -- lemma all
lemma tilted_near {z : Tabletop (Chamber α ι)} (h : DifferentiableAt ℝ θ z) : tilted θ z= LinearMap.toMatrix' ((fderiv ℝ (verticalChange θ z) (upper α ι z)).toLinearMap) := by
  ext i j; rw [tilted, Matrix.of_apply, LinearMap.toMatrix'_apply, (vert_link h).fderiv]
  let Q := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:α=>ℝ) i
  let L := (assemble α ι).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)
  change fderiv ℝ (Q ∘ θ) z (spike (Sum.inl j))=Q ((fderiv ℝ θ z) (L (Pi.single j 1)))
  rw [fderiv_comp z Q.differentiableAt h, Q.fderiv]; refine congr_arg (fun u : Tabletop (Chamber α ι)=> Q ((fderiv ℝ θ z) u)) ?_; ext1 k; rw [spike_proj]; cases k <;> simp [L, assemble_,Pi.single_apply]
lemma fee_ordinary {z : Tabletop (Chamber α ι)} (h : DifferentiableAt ℝ θ z) : (tilted θ z).det=(fderiv ℝ (verticalChange θ z) (upper α ι z)).det := by rw [tilted_near h]; exact LinearMap.det_toMatrix' _
lemma fee_grain (hz : ContDiffAt ℝ ω θ 0) (he : θ 0=0) : ink (fun z=> (tilted θ z).det)=(gaugeHess (exposure θ)).det := by
  let H (i j : α) : Tabletop (Chamber α ι)→ℝ:= leafD (.inl j) (fun z=> θ z i)
  let V (i : Equiv.Perm α):= ((Equiv.Perm.sign i: ℤˣ):ℤ)
  let f (s : Equiv.Perm α) : Tabletop (Chamber α ι)→ℝ:= (V s:ℝ) • (∏ i, H (s i) i)
  have ha i j : ContDiffAt ℝ ω (H i j) 0:= leaf_at _ (contDiffAt_pi.mp hz i)
  have hb i j : inflow j (exposure θ i)=ink (H i j) := flash_player (contDiffAt_pi.mp hz i) (congr_fun he i) _
  rw [show (fun z=> (tilted θ z).det)=∑ i,f i by ext1 x; simp only [f,V,tilted,Matrix.det_apply,Units.smul_def,Matrix.of_apply,Finset.sum_apply,Finset.prod_apply,Pi.smul_apply,smul_eq_mul,zsmul_eq_mul]; exact sum_congr rfl fun i _=>rfl,ink_sum]; swap; · exact fun i _=> (cont_diff_prod _ _ (fun j _=>ha (i j) j)).const_smul (V i:ℝ)
  rw [Matrix.det_apply]; refine sum_congr rfl fun i _=>?_; unfold f; have ht := ink_product (fun j=> H (i j) j) univ (fun j _=>ha (i j) j)
  rw [ink_scale (cont_diff_prod _ _ (fun j _=>ha (i j) j)),ht,gaugeHess]; simp_rw [Matrix.of_apply,hb,Units.smul_def]; exact Int.cast_smul_eq_zsmul ..
lemma fee_jet (hz : ContDiffAt ℝ ω θ 0) : ContDiffAt ℝ ω (fun z=> (tilted θ z).det) 0 := by simp only [tilted,Matrix.det_apply',Matrix.of_apply]; refine ContDiffAt.sum fun i _=> contDiffAt_const.mul ?_; exact contDiffAt_prod fun j _=>leaf_at _ (contDiffAt_pi.mp hz (i j))
lemma levy_grain (hθ : ContDiffAt ℝ ω θ 0) (hz : θ 0=0) {V} (ht : Starting (exposure θ) V) (h : |(tilted θ 0).det|=1) :
    ContDiffAt ℝ ω (fun z=> |(tilted θ z).det|) 0 ∧ ink (fun z=> |(tilted θ z).det|)=levy V (exposure θ) := by
  let f:= fun z=> (tilted θ z).det
  let L:=gaugeHess (exposure θ)
  have hw : ink f=L.det:= fee_grain hθ hz
  have hx : f 0=V.det := by
    apply MvPolynomial.C_injective (Chamber α ι); rw [← ink_norm f,hw]; exact ht.jac
  have hf : ContDiffAt ℝ ω f 0:= fee_jet hθ
  have he : f 0 ≠0 := by intro he; change |f 0|=1 at h; rw [he,abs_zero] at h; exact zero_ne_one h
  rcases he.lt_or_gt with he|he
  · have hu : (fun z=> |f z|)=ᶠ[𝓝 0] -f:= (hf.continuousAt.eventually (gt_mem_nhds he)).mono fun z hz=> abs_of_neg hz
    refine ⟨hf.neg.congr_of_eventuallyEq hu,?_⟩
    have hh : |f 0|=1:= h; rw [abs_of_neg he, hx] at hh; change ink (fun z=>|f z|)= _ • L.det
    rw [ink_of hu,ink_neg,hw, show V.det=-1 by linarith only [hh]]; simp
  have hu : (fun z=>|f z|)=ᶠ[𝓝 0] f:= (hf.continuousAt.eventually (lt_mem_nhds he)).mono fun z hz=>abs_of_pos hz
  refine ⟨hf.congr_of_eventuallyEq hu,?_⟩; change |f 0|=1 at h; rw [abs_of_pos he,hx] at h; change ink (fun z=>|f z|)= V.det⁻¹ • L.det; rw [ink_of hu,hw,h]; simp
end YM.WilsonBulk.Sheet
