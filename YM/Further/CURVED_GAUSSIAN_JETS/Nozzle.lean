import YM.Further.CURVED_GAUSSIAN_JETS.WeightsD

/-!
# Common-orientation predictor coefficients, including where no row selected

Compute on the global a-space with zero tree and frozen displacement.
When a noise read touches that stencil, move to a weak patch gauge; the
same tags, relative orientation fixed. All other noise reads constant in a.
`Covered` the extra margin for this shape (coarse, can build into freezing).
No absolute continuity/derivative claim about sector probabilities here.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets.Shape
open Function Filter Matrix Gauge Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum FlatTree Progress.StationaryScenes Pockets Next.Fluctuations Work Set
open Green (wt wt_pos Both)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} (H : Finset F.Free)

def readBond (U : Config G f) (k : S.Choices) (p : Bond c) (x : Vec (Bits H G)) := S.prediction (restore H U x) k p

def nozzle (U : Config G f) (k : S.Choices) (b : Bond c) :=
    G.projectColor.toContinuousLinearMap ∘L ((ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat ((S.prediction U k b)⁻¹))) ∘L fderiv ℝ (fun x => G.mat (readBond H U k b x)) 0

def fluid (U : Config G f) (k : S.Choices) : Matrix (Shape.Page G c 1) (Bits H G) ℝ := row fun p=> nozzle H U k (wheel c |>.symm p)

def visits (p : Bond c) (j : Soft H) := separation p.1 (S.ratio.parent j.val.val.1) ≤ predReach S.patch
lemma read_zero (U : Config G f) (k : S.Choices) (p : Bond c) (j : Soft H)
    (hh : S.patch.Branches S.kernel G)
    (h : ¬ Shape.visits (S:=S) H p j) (x : G.ColorIndex) (t : ℝ) : readBond H U k p (t • (Pi.single (j,x) 1)) = S.prediction U k p := by
  apply prediction_near_eq hh; intro i hi
  have ht : free S H j ≠ (i.1,coord i.2) := by intro hv; apply h; unfold Shape.visits; change separation p.1 (S.ratio.parent (free S H j).1) ≤ _; rw [hv]; exact hi
  simp only [restore,test_smul, increment, collect, Pi.smul_apply,test_unit,if_neg ht,smul_zero,G.mat_lieExp_zero,one_mul]
lemma read_dead (U : Config G f) (k : S.Choices) (p : Bond c) (hS : S.patch.Branches S.kernel G) (he : ∀ j,¬Shape.visits (S:=S) H p j) (x : Vec (Bits H G)) : readBond H U k p x = S.prediction U k p := by
  apply prediction_near_eq hS; intro i hi
  rw [restore,increment]; suffices hh : collect G (test H x) i=0 by rw [hh,G.mat_lieExp_zero,one_mul]
  rw [test_eq,FlatTree.blank]; split; rfl
  unfold Pockets.use; split; rfl
  exact False.elim (he ⟨⟨i,‹_›⟩,‹_›⟩ hi)

def Covered (t : ℝ) (V : Config G c) : Prop := ∀ j : Soft H,∀ p∈RG.flags t V,extent S.patch+predReach S.patch < separation (S.ratio.parent j.val.val.1) p
lemma Covered.clean {V : Config G c} {t : ℝ} (h : Covered H t V) : Clean H V t := fun i y hy=> lt_of_le_of_lt (Nat.le_add_right ..) (h i y hy)
lemma weak_of_visits {V : Config G c} {t : ℝ} {j : Soft H} {p : Bond c} (hh : Covered H t V) (h : Shape.visits H p j) : Weak S.patch p.1 V t := by
  intro b hb; by_contra! he
  have hf := (RG.flags_spec t V b.1).mpr ⟨b,(by simp [RG.touched,Lattice.visits,square]),he⟩
  have hg := separation_triangle (S.ratio.parent j.val.val.1) p.1 b.1; rw [separation_comm _ p.1] at hg
  have hx := hh j b.1 hf; unfold Shape.visits at h; omega

private def send (p : Bond c) (h : Site f → G.El) : Dir G f →ₗ[ℝ] Dir G f where
  toFun := Pockets.field (S:=S) p.1 h
  map_add' x y := by funext i; simp only [Pockets.field,Pi.add_apply]; split <;> simp
  map_smul' r x := by funext i; simp only [Pockets.field,Pi.smul_apply]; split <;> simp
private lemma send_bound (p : Bond c) (h : Site f → G.El) (x : Dir G f) : ‖send (S:=S) p h x‖ ≤ ‖x‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=>by change ‖Pockets.field _ _ x i‖ ≤ _; unfold Pockets.field; split; rw [G.norm_adjoint]; exact norm_le_pi_norm ..; rw [norm_zero]; exact norm_nonneg _
private lemma read_at (k : S.Choices) (hS : S.patch.Branches S.kernel G) (p : Bond c) (h : Site f → G.El) {U : Config G f} {z : Dir G f}
    (hv : AgreeNear S.ratio.parent p.1 (reach S.patch) (gauge h U) (represent z)) (x : Vec (Bits H G)) :
    G.mat (readBond H U k p x) = G.mat ((h (S.ratio.embed p.1))⁻¹) * Ball.noise S k p (send (S:=S) p h (test H x),z) * G.mat (h (S.ratio.embed (p.1+Lattice.step p.2))) := by
  have ht := prediction_near_eq hS _ _ k p ((steps (v:=test H x) hv 1).shrink (by rw [separation_self]; unfold Pockets.reach; omega))
  rw [one_smul,Pockets.step,one_smul,predicted hS] at ht
  change h _ * readBond H U k p x * _⁻¹ = _ at ht
  unfold Ball.noise; rw [← G.mat_mul, ← G.mat_mul,show send (S:=S) p h (test H x) = Pockets.field _ _ (test H x) from rfl, ← ht]; change G.mat _ = G.mat (_⁻¹ * (_ * _ * _⁻¹) * _)
  congr 1; dsimp only [Function.comp_apply]; group

private def Receives (k : S.Choices) (V : Config G c) (D : ℝ) := ∀ b : Bond c, let U:=replica S.ratio V
    ContDiffAt ℝ ω (fun x=>G.mat (readBond H U k b x)) 0 ∧ ∀ j : Bits H G,
        ‖deriv (fun r : ℝ => G.mat (readBond H U k b (r • Pi.single j 1))) 0‖ ≤ D

private lemma receives (G : Gauge) (P : Patch) (K : KernelChoices) : ∃ t D : ℝ, 0<t ∧ 0<D ∧ ∀ {f c : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G →
    ∀ (k : S.Choices) (F : Forest S.ratio) (H : Finset F.Free) (V : Config G c) (r : ℝ), 0 ≤ r → r ≤ t → Covered H r V → Receives H k V D := by
  obtain ⟨C,δ,hC,hδ,h⟩ := patchGauge P G
  obtain ⟨s,D,hs,hD,hd⟩ := Ball.allows G P K
  refine ⟨min δ ((s/2)/C),D,lt_min hδ (div_pos (by positivity) hC), hD,fun {f c} S hp hK hS k F H V r hr hT he b=>?_⟩
  intro U
  by_cases ht : ∃ j,Shape.visits (S:=S) H b j; swap
  · simp_rw [read_dead H U k b hS.1.1 (not_exists.mp ht)]
    refine ⟨contDiffAt_const, fun j=>?_⟩; erw [deriv_const]; exact norm_zero.trans_le hD.le
  obtain ⟨j,hj⟩ := ht
  obtain ⟨g,z,hz,hg⟩ := h S hp (hp ▸ hS.2) hr (hT.trans (min_le_left ..)) _ V (hp ▸ weak_of_visits H he hj)
  have hzs : ‖z‖ < s := by have := (le_div_iff₀ hC).mp (hT.trans (min_le_right ..)); linarith
  have ha := read_at H k hS.1.1 b g (show AgreeNear _ _ _ _ _ from hp ▸ hg)
  change ∀ x, G.mat (readBond H U k b x)=_ at ha
  let L := send (S:=S) b g ∘ₗ Shape.translate H G
  let G0 := (Ball.noise (G:=G) S k b)
  have hA := (hd S hp hK (0,z) (by simpa [Prod.norm_def])).2 k b
  simp_rw [ha]; change ContDiffAt ℝ ω (fun x => G.mat _ * G0 (L x,z)*G.mat _) 0 ∧ _
  refine ⟨(contDiffAt_const.mul ((show ContDiffAt ℝ ω G0 (L 0,z) by rw [map_zero]; exact hA.analytic).comp 0 (f:=fun x=>(L x,z))
    (L.toContinuousLinearMap.contDiff.contDiffAt.prodMk contDiffAt_const))).mul contDiffAt_const, fun j=>?_⟩
  let y := L (Pi.single j 1)
  have hy : ‖(y,(0:Dir G f))‖ ≤ 1 := by rw [Prod.norm_def]; simp; exact (send_bound b g (test H (Pi.single j 1))).trans (test_unit_norm H j)
  change ‖deriv (fun r : ℝ => G.mat _ * G0 (L (r • Pi.single j 1),z)*G.mat _) 0‖ ≤ _
  simp_rw [L.map_smul]
  have hy' : HasDerivAt (fun r : ℝ => G0 (r • y,z)) (fderiv ℝ G0 (0,z) (y,0)) 0 := Ball.chart_diff (fun i hi=> (hd S hp hK i hi).2 k b) z y hzs
  erw [((hy'.const_mul (G.mat ((g _)⁻¹))).mul_const (G.mat (g _))).deriv]
  rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star _), Gauge.mul_frob_eq _ _ (G.mat_star_mul _)]
  have h₁ := (norm_iteratedFDeriv_one G0 (𝕜:=ℝ) (x:=(0,z))).symm.trans_le (hA.norm_le 1 (by decide))
  exact ((fderiv ℝ G0 (0,z)).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hy).trans
          h₁)

variable {k : S.Choices}
lemma nozzle_price (U : Config G f) (b : Bond c) (h : DifferentiableAt ℝ (fun x=> G.mat (readBond H U k b x)) 0) (x : Vec (Bits H G)) :
    ‖nozzle H U k b x‖ = noisePrice U (test H x) k (pole b) := by
  have hg := read_deriv H _ h x
  let Q := S.prediction U k b
  have he := hg.mul_const (G.mat (Q⁻¹))
  have ht := G.tangent_generates he (by simp only [zero_smul,readBond,restore_zero, ← G.mat_mul,Q,mul_inv_cancel,G.mat_one]) (fun r=> ⟨_,G.mat_mul _ _⟩)
  rw [noisePrice,show (wheel c).symm (pole b)=b from (wheel c).symm_apply_apply b]
  unfold readBond at hg; simp_rw [restore_line] at hg
  rw [eq_div_iff G.colorScale_pos.ne',mul_comm ‖_‖ G.colorScale,← G.colorMat_norm]
  change ‖G.colorMat (G.projectColor (fderiv ℝ (fun x => G.mat (readBond H U k b x)) 0 x * G.mat Q⁻¹))‖ = _
  erw [G.colorMat_project_self ht, hg.deriv]; rw [Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]; rfl

lemma fluid_range (U : Config G f) (k : S.Choices) (hS : S.patch.Branches S.kernel G) (i : Shape.Page G c 1) (j : Bits H G)
    (h : DifferentiableAt ℝ (fun x=> G.mat (readBond H U k ((wheel c).symm i.1) x)) 0)
    (he : ¬Shape.visits H ((wheel c).symm i.1) j.1) : Shape.fluid H U k i j = 0 := by
  obtain ⟨x,hx⟩ := (wheel c).surjective i.1
  have hh : ¬Shape.visits H x j.1 := by rwa [← hx, Equiv.symm_apply_apply] at he
  unfold Shape.fluid; rw [row_unit,← hx,Equiv.symm_apply_apply]; suffices nozzle H U k x (Pi.single j 1) = 0 by rw [this]; rfl
  rw [← norm_eq_zero,nozzle_price H U x (by rwa [← hx,Equiv.symm_apply_apply] at h),noisePrice,show (wheel c).symm (pole x)=x from (wheel c).symm_apply_apply _]
  simp_rw [←restore_line]; change ‖deriv (fun t : ℝ => G.mat (readBond H U k x (t • Pi.single (j.1,j.2) 1))) 0‖/G.colorScale=0
  simp_rw [read_zero H U k x j.1 hS hh j.2]; erw [deriv_const]; change ‖(0:G.Mat)‖ / _ = _; simp

theorem noise_allows (G : Gauge) (P : Patch) (K : KernelChoices) {w : ℝ} (hw : 0<w) : ∃ t D : ℝ, 0<t ∧ 0<D ∧ ∀ {f c : Side} (S : StepData c f), S.patch=P → S.kernel=K → Paid S G →
    ∀ (k : S.Choices) (F : Forest S.ratio) (H : Finset F.Free) (V : Config G c) (r : ℝ), 0 ≤ r → r ≤ t → Covered H r V → let U := replica S.ratio V
      (∀ b, ContDiffAt ℝ ω (fun x => G.mat (readBond H U k b x)) 0) ∧ Both (coarseSite S) (keySite H) (Shape.fluid H U k) w D D := by
  obtain ⟨t,D,ht,hD,h⟩ := receives G P K
  let s := (1+predReach P)*(P.L.val:ℝ)
  let L := Real.exp ((2*w)*s) * (D/G.colorScale)
  let E := L*(crowd G*Push.Uniform.countCost w)
  have hS := G.colorScale_pos; have hL : 0≤L := by unfold L; positivity
  refine ⟨t,1+E,ht,(by have := Push.Uniform.count_pos hw; unfold E; positivity),fun {f c} S hp hK hT k F H V r hr hr' hv=> ?_⟩
  intro U
  have he := h S hp hK hT k F H V r hr hr' hv
  refine ⟨fun b=>(he b).1,?_⟩
  have hh := both_pay (M:=Shape.fluid H U k) (Shape.coarse_count S) (Shape.key_count H) hw hL (fun i j => ?_)
  · exact ⟨fun i=>(hh.1 i).trans (by change E≤1+E; linarith),fun j=>(hh.2 j).trans (by change E≤1+E; linarith)⟩
  let b := (wheel c).symm i.1
  have ht := (he b).1.differentiableAt (by simp)
  by_cases h' : Shape.visits H b j.1
  · have ht' : ((separation (coarseSite S i) (keySite H j)):ℝ) ≤ s := by
      have hv := Next.Free.scaled_dist S.ratio (keySite H j) i.1.1
      have hh : separation (S.ratio.parent (keySite H j)) i.1.1 ≤ predReach P := by rw [separation_comm,←hp]; exact h'
      have hpos := S.ratio.count.property; have hc := (div_le_iff₀ (by exact_mod_cast hpos)).mp hv
      rw [show S.ratio.count=P.L by change S.patch.L=P.L; rw [hp]] at hc
      rw [separation_comm]; exact hc.trans (by unfold s; gcongr)
    apply mul_le_mul (Real.exp_monotone (by gcongr)) _ (abs_nonneg _) (Real.exp_pos _).le
    unfold Shape.fluid; rw [row_unit]
    apply (coord_paid ..).trans; rw [nozzle_price H U _ ht,noisePrice, show (wheel c).symm (pole b)=b from (wheel c).symm_apply_apply b]
    simp_rw [←restore_line]; exact div_le_div_of_nonneg_right ((he b).2 j) hS.le
  rw [fluid_range H U k hT.1.1 i j ht h', abs_zero,mul_zero]; exact hL
end YM.Further.CurvedGaussianJets.Shape
