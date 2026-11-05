import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.NearJet
import YM.Next.ROTATIONS.Journal
import YM.Next.ROTATIONS.Thaw
import YM.Next.SCHEDULE.Air
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.LocalJet
import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineFaces

/-!
# Sufficient data for true remote $V'$→flat $I$ evaluation

Not an extension of B globally for bonds near the tested component;
can evaluate even when other links bad. Speak in G chord size of
fine copied and pulled field. Factor costs fixed L and require actual
Branches. Keep all phase orientations (tested on shifted sites and reversed
using U-priced tangents). Rotate jitter with that price in next file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open Next.Fluctuations Next.SectorChange Motion SectorNext.Remainder.Affine Push.SectorMeasure 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f}

-- face analytic at any period (in absolute logs B and left perturbation)
private abbrev C4 (G : Gauge) := Fin 4 → G.Color
-- geometry identical to Remainder.Affine sqF in LARGE_FIELD_REMAINDERS/AffineFaces, private. repeat here for fderiv use.
private def squareF (x : C4 G × C4 G) :=
  let v i := G.lieExp (x.1 i)*G.lieExp (x.2 i)
  G.curvature (v 0*v 1*(v 2)⁻¹*(v 3)⁻¹)
private lemma smooth (G : Gauge) : ContDiffAt ℝ ω (squareF (G:=G)) 0 := by
  unfold squareF
  apply curvature_diff_mat
  let a i (x : C4 G × C4 G) := G.mat (G.lieExp (x.1 i))*G.mat (G.lieExp (x.2 i))
  have he (i : Fin 4) : ContDiff ℝ ω (a i) := (G.exp_jet.comp ((contDiff_apply ℝ _ _).comp contDiff_fst)).mul (G.exp_jet.comp ((contDiff_apply ℝ _ _).comp contDiff_snd))
  have h1 (i) : ContDiff ℝ ω (fun x => star (a i x)) := (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (he i)
  simp only [G.mat_mul,G.mat_inv]; exact (((he 0).mul (he 1)).mul (h1 2)).mul (h1 3)|>.contDiffAt
private lemma read_square (a b : Directions G n) (p : Cell n) :
    pTest (absolutize b) p a=squareF (a∘patchFace p,b∘patchFace p) := by
  let x:=p.1; let i := p.2.val.1; let j := p.2.val.2
  have ht : x+Lattice.step i+step j-step i=x+step j := by abel
  have ht' : x+Lattice.step i+step j+(-(step i:Site n))=x+step j := by abel
  unfold pTest faceValue
  change G.curvature (travel _ x (square i j)) = _
  simp only [square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,ht,ht',add_sub_cancel_right,mul_one]
  unfold increment absolutize
  change G.curvature ((G.lieExp (a (patchFace p 0))*G.lieExp (b (patchFace p 0))) * ((G.lieExp (a (patchFace p 1))*G.lieExp (b (patchFace p 1)))*
    ((G.lieExp (a (patchFace p 2))*G.lieExp (b (patchFace p 2)))⁻¹*(G.lieExp (a (patchFace p 3))*G.lieExp (b (patchFace p 3)))⁻¹))) = _
  simp only [squareF,Function.comp_apply,mul_assoc]

lemma face_cost (G : Gauge) : ∃ A r : ℝ, 0<A ∧ 0<r ∧ ∀ {n : Side} (i : Cell n) (Y : Directions G n),
      ‖Y‖ ≤ r → let U:=absolutize Y
      let H (w : Config G n):=fderiv ℝ (pTest w i) 0
      ContDiffAt ℝ ω (pTest U i) 0 ∧ ‖H U-H 1‖ ≤ A*‖Y‖ ∧ ‖H 1‖ ≤ A := by
  obtain ⟨C,M,hC,hM,h⟩ := linear (smooth G)
  refine ⟨C,M,hC,hM,fun {n} i Y hy => ?_⟩
  intro U H
  let L : Directions G n →L[ℝ] C4 G := (LinearMap.funLeft ℝ G.Color (patchFace i)).toContinuousLinearMap
  have hl (w : Directions G n) : ‖L w‖ ≤ ‖w‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => norm_le_pi_norm w _
  have hs : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using hl)
  obtain ⟨hx,hN,hJ⟩ := h (L Y) ((hl Y).trans hy)
  let F y := fun q : C4 G => squareF (q,y)
  have he v : pTest (absolutize v) i= (F (L v)) ∘ L := funext fun a => read_square ..
  have ht v (hv : ‖v‖ ≤ M) : ContDiffAt ℝ ω (pTest (absolutize v) i) 0 ∧ H (absolutize v) = (fderiv ℝ (F (L v)) 0).comp L := by
    have hx : ContDiffAt ℝ ω (F (L v)) (L 0) := by rw [map_zero]; exact (h _ ((hl v).trans hv)).1
    unfold H; rw [he,fderiv_comp _ (hx.differentiableAt (by simp)) L.differentiableAt, map_zero,L.fderiv]; exact ⟨hx.comp _ L.contDiff.contDiffAt,rfl⟩
  obtain ⟨hp,hL⟩ := ht Y hy
  have h0 : H 1 = (fderiv ℝ (F 0) 0).comp L := by
    have he := (ht 0 (by rw [norm_zero]; exact hM.le)).2; rw [map_zero,show absolutize (0:Directions G n)=1 by ext; simp [absolutize]] at he; exact he
  unfold U; rw [h0,hL]; refine ⟨hp,?_,?_⟩
  · rw [← ContinuousLinearMap.sub_comp]; apply (ContinuousLinearMap.opNorm_comp_le ..).trans; exact (mul_le_of_le_one_right (norm_nonneg _) hs).trans (hN.trans (mul_le_mul_of_nonneg_left (hl _) hC.le))
  exact (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) hs).trans hJ)

-- `Earns` alone doesn't have a rate near zero. Use this post-price even
-- for configurations not globally cleared by S. Different from perturbing
-- all tensor differentiability at a nonflat field.
theorem both (G : Gauge) (P : Patch) (K : KernelChoices) (hp : P.Branches K G) :
    ∃ A r : ℝ, 0<A ∧ 0<r ∧ ∀ t : ℝ, 0≤t → t≤r → ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (U : Config G f),
    (∀ i : Cell f, (∀ e : Bond f, separation (S.ratio.parent i.1) (S.ratio.parent e.1) ≤ 4 → G.chord (U e) ≤ t) →
      ContDiffAt ℝ ω (pTest U i) 0 ∧ ‖fderiv ℝ (pTest U i) 0-fderiv ℝ (pTest 1 i) 0‖ ≤ A*t ∧
        ‖fderiv ℝ (pTest (1:Config G f) i) 0‖ ≤ A) ∧
    (∀ (k : S.Choices) (i : Bond c), (∀ e : Bond f, separation i.1 (S.ratio.parent e.1) ≤ predReach P → G.chord (U e) ≤ t) →
      ContDiffAt ℝ ω (bTest U k i) 0 ∧ ‖fderiv ℝ (bTest U k i) 0-fderiv ℝ (bTest 1 k i) 0‖ ≤ A*t ∧
        ‖fderiv ℝ (bTest (1:Config G f) k i) 0‖ ≤ A) := by
  obtain ⟨B,x,hB,hx,H0⟩ := extend_interior G
  obtain ⟨A,r,hA,hr,H⟩ := face_cost G
  obtain ⟨C,w,hC,hw,Q⟩ := transfer_cost P K G hp
  let D:=(A+C)*(1+B)
  let m := min x ((min r w)/B)
  have HM : 0<m := lt_min hx (div_pos (lt_min hr hw) hB)
  refine ⟨D,m,by unfold D; positivity,HM,?_⟩
  intro t ht hm c f S Hs Hk U
  have hB' : B*t ≤ min r w := by rw [mul_comm]; exact (le_div_iff₀ hB).mp (hm.trans (min_le_right ..))
  have he (v : Site c) (b : ℕ) (hl : ∀ e : Bond f, separation v (S.ratio.parent e.1)≤ b → G.chord (U e) ≤ t) :
      ∃ y : Directions G f, ‖y‖ ≤ B*t ∧ AgreeNear S.ratio.parent v b U (absolutize y) := by
    obtain ⟨x,hx,hr⟩ := H0 S.ratio.parent v b U t ht (hm.trans (min_le_left ..)) hl
    refine ⟨collect G x,?_,?_⟩
    · exact ((pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => norm_le_pi_norm x _).trans hx
    intro e he; have hi := hr e he; change U e=G.lieExp (collect G x e)*1 at hi; rw [mul_one] at hi; exact hi
  have hx (v : Site c) (b : ℕ) (W : Config G f) (k : AgreeNear S.ratio.parent v b U W) (d : Directions G f) :
      AgreeNear S.ratio.parent v b (increment U d) (increment W d) := fun i hi => by unfold increment; rw [k i hi]
  have hDA : A ≤ D := by unfold D; nlinarith
  have hDC : C ≤ D := by unfold D; nlinarith
  constructor
  · intro i hl; obtain ⟨y,hy,hz⟩ := he _ _ hl
    have heq : pTest U i=pTest (absolutize y) i := funext fun d => congr_arg G.curvature (travel_near _ (Work.E03.parent_step S) _ _ i.1 _ 4 (by rfl : (square i.2.val.1 i.2.val.2).length≤4) (hx _ _ _ hz d))
    obtain ⟨hq,hg,hN⟩ := H i y (hy.trans (hB'.trans (min_le_left ..)))
    rw [heq]; refine ⟨hq,hg.trans ?_,hN.trans hDA⟩
    refine (mul_le_mul_of_nonneg_left hy hA.le).trans ?_; rw [← mul_assoc]; gcongr; unfold D; nlinarith
  intro k i hl; obtain ⟨y,hy,hz⟩ := he _ _ hl
  have hp : S.patch.Branches S.kernel G := by rwa [Hs,Hk]
  rw [← Hs] at hz
  have heq : bTest U k i=bTest (absolutize y) k i := funext fun d => by
    unfold bTest out; rw [prediction_near_eq hp U _ k i hz,prediction_near_eq hp (increment U _) _ k i (hx _ _ _ hz d)]
  obtain ⟨hq,hg,hN⟩ := Q S Hs Hk k i y (hy.trans (hB'.trans (min_le_right ..)))
  rw [heq]; refine ⟨hq,hg.trans ?_,hN.trans hDC⟩
  refine (mul_le_mul_of_nonneg_left hy hC.le).trans ?_; rw [← mul_assoc]; gcongr; unfold D; nlinarith
end YM.AnalyticBridge.LocalGaussianLaws.Remote
