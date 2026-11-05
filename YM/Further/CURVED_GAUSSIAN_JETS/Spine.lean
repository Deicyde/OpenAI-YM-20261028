import YM.Further.CURVED_GAUSSIAN_JETS.WeightsD

/-! # Compulsory plaquette coordinates in each channel -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
noncomputable section
namespace YM.Further.CurvedGaussianJets.Shape
open Function Filter Matrix Lattice Wilson Tree RG Precision Pressure Exterior Bid SectorNext.Vacuum FlatTree Progress.StationaryScenes Pockets Push.Uniform Work
open Green (wt wt_pos Both)
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} (H : Finset F.Free)

def turnFace (U : Config G f) (s : Signed) (p : Body 2 f) (v : Dir G f) :=
    G.curvature (faceValue (pull s 0 (increment U (collect G v))) ((Cut.turn f).symm p))

theorem turn_allows (G : Gauge) : ∃ C : ℝ, 0<C ∧ ∀ (f : Side) (U : Config G f) (s : Signed) (p : Body 2 f), Allows 1 (turnFace U s p) 0 C := by
  obtain ⟨K,hK,h⟩ := exp_receipt G 1
  let F (X Y : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : X →L[ℝ] Y) := ‖L‖
  let D := (2:ℝ)^1 * composeCost 1 K 1 * ‖(1:G.Mat)‖
  let C := F G.Mat G.Color (Ball.paint G) * travelCost G 1 4 D
  refine ⟨max 1 C,zero_lt_one.trans_le (le_max_left ..), fun f U s p=>?_⟩
  obtain ⟨⟨i,b⟩,rfl⟩ := (Cut.turn f).surjective p
  unfold turnFace; simp only [Equiv.symm_apply_apply,faceValue,travel_pull,← Ball.curvature_eq]
  let a := affine s (0:Site f) i
  let w := (square b.val.1 b.val.2).map (fun d=>d.rotate s)
  have hf (e : Bond f) : Allows 1 (fun x : Dir G f => G.mat (increment U (collect G x) e)) 0 D := by
    have hp := (represented h f).2.2 e 0 (by simp)
    have hu := Gauge.frob_mul_eq (1:G.Mat) (G.mat (U e)) (G.mat_mul_star _); rw [one_mul] at hu
    have ht := hp.times (allows_const (v:=G.mat (U e)) 0 hu.le) (g:=fun _=> U e)
    simpa only [represent,increment,Pi.one_apply,mul_one] using! ht
  exact ((travel_jets hf a (w:=w) (by simp [w,square] : w.length≤4)).linear (Ball.paint G) (le_refl _)).mono (le_max_right 1 C)
lemma turn_smooth (s : Signed) (p : Body 2 f) (U : Config G f) : ContDiffAt ℝ ω (fun x : Vec (Bits H G) => turnFace U s p (test H x)) 0 := by
  obtain ⟨M,hM,h⟩ := turn_allows G
  exact ((show test H (0:Vec (Bits H G)) = 0 from (Shape.translate H G).map_zero).symm ▸ (h f U s p).analytic).comp (f:=test H) 0 (test_smooth H).contDiffAt

def direct (U : Config G f) (s : Signed) (p : Body 2 f) : Vec (Bits H G) →L[ℝ] G.Color := fderiv ℝ (fun x : Vec (Bits H G) => turnFace U s p (test H x)) 0
def basic (U : Config G f) (s : Signed) : Matrix (Shape.Page G f 2) (Bits H G) ℝ := Shape.row (Shape.direct H U s)
lemma direct_eq (U : Config G f) (s : Signed) (p : Body 2 f) (x : Vec (Bits H G)) :
    HasDerivAt (fun t : ℝ=> G.curvature (faceValue (pull s 0 (restore H U (t • x))) ((Cut.turn f).symm p))) (Shape.direct H U s p x) 0 :=
  read_deriv _ _ ((turn_smooth H s p U).differentiableAt (by simp)) _
lemma pred_support {u : ℕ} (U : Config G f) (j : Bits H G) (r : ℝ) (p : Site f) (h : u < separation p (keySite H j)) :
    Next.Fluctuations.AgreeNear id p u (restore H U (r • Pi.single j 1)) U := by
  intro e he
  have he' : free S H j.1 ≠ (e.1,coord e.2) := by intro hh; rw [keySite,hh] at h; exact h.not_ge he
  rw [restore_line]; unfold Pockets.step increment collect
  simp only [Pi.smul_apply,test_unit,if_neg he',smul_zero,G.mat_lieExp_zero,one_mul]
lemma basic_range (U : Config G f) (s : Signed) (i : Shape.Page G f 2) (j : Bits H G)
    (h : 4 < separation (fineSite s i) (keySite H j)) : Shape.basic H U s i j=0 := by
  obtain ⟨p,hp⟩ := (Cut.turn f).surjective i.1
  rw [basic,row_unit, ← (direct_eq ..).deriv,← hp,Equiv.symm_apply_apply]
  simp_rw [faceValue, travel_pull]
  let w := List.map (fun d : Lattice.Step=>d.rotate s) (square p.2.val.1 p.2.val.2)
  have he r := Next.Fluctuations.travel_near (id : Site f → Site f) (fun x i=> E03.sep_step x i) _ U (affine s 0 p.1) w 4
    (by simp [w,square]) (pred_support H U j r (affine s 0 p.1) (by rw [←show fineSite s i=affine s 0 p.1 by rw [fineSite,←hp,affine,add_zero]; rfl]; exact h))
  unfold w at he; simp_rw [he]; rw [deriv_const]; rfl
lemma basic_local (G : Gauge) : ∃ C : ℝ, 0<C ∧ ∀ {f c : Side} (S : StepData c f) (F : Forest S.ratio) (H : Finset F.Free) (U : Config G f) (s : Signed) (i : Shape.Page G f 2) (j : Bits H G),
    |Shape.basic H U s i j| ≤ C := by
  obtain ⟨C,hC,h⟩ := turn_allows G
  refine ⟨C,hC,fun S F H U s i j=>?_⟩
  rw [Shape.basic,row_unit]
  let v := test H (Pi.single j (1:ℝ)); have hv := test_unit_norm H j
  let f := turnFace U s i.1
  have hh := h _ U s i.1
  have he := hh.norm_le _ (Nat.le_refl 1); rw [norm_iteratedFDeriv_one] at he
  have ht := ((show DifferentiableAt ℝ f ((0:ℝ) • v) by simpa only [zero_smul] using hh.analytic.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (0:ℝ) ((hasDerivAt_id' (0:ℝ)).smul_const v))
  rw [zero_smul,one_smul] at ht
  have hf := direct_eq H U s i.1 (Pi.single j 1); change HasDerivAt (fun t : ℝ=> f (test H (t • _))) _ _ at hf
  simp_rw [test_smul] at hf
  rw [hf.unique ht]
  exact (coord_paid ..).trans (((fderiv ℝ f 0).le_opNorm _).trans ((mul_le_of_le_one_right (norm_nonneg _) hv).trans he))

theorem basic_prices (G : Gauge) {w : ℝ} (hw : 0<w) : ∃ C : ℝ, 0<C ∧ ∀ {f c : Side} (S : StepData c f) (F : Forest S.ratio) (H : Finset F.Free) (U : Config G f) (s : Signed),
    Both (fineSite s) (keySite H) (Shape.basic H U s) w C C := by
  obtain ⟨C,hC,h⟩ := basic_local G
  let A := Real.exp ((2*w)*4) * C
  have hA : 0<A := mul_pos (Real.exp_pos _) hC
  let C := A*(crowd G*Push.Uniform.countCost w)
  have hp : 0≤C := by have := Push.Uniform.count_pos hw; unfold C; positivity
  refine ⟨C+1,by positivity,fun S F H U s=>?_⟩
  have he := both_pay (fine_count s) (Shape.key_count H) hw hA.le (M:=Shape.basic H U s) (fun i j=> ?_)
  · exact ⟨fun i=>(he.1 i).trans (by unfold C; linarith),fun j=>(he.2 j).trans (by unfold C; linarith)⟩
  by_cases hh : separation (fineSite s i) (keySite H j) ≤ 4
  · unfold A wt; apply mul_le_mul (Real.exp_monotone (by gcongr; exact_mod_cast hh)) (h S F H U s i j) (abs_nonneg _) (Real.exp_pos _).le
  rw [basic_range H U s i j (lt_of_not_ge hh),abs_zero,mul_zero]; exact hA.le
end YM.Further.CurvedGaussianJets.Shape
