import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Windows
import YM.Push.FREE_RESOLVENT.AffineGap
import YM.Push.FREE_RESOLVENT.Columns
import YM.Push.FREE_RESOLVENT.TrackBill
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Bore



set_option warningAsError false

/-!
# Matching actual affine rows (and the real unmasked Hessian check)

The unmasked free Hessian is a different object. Even in the log
coordinate germ the match to `Affine.primary` uses a *true length cut*, not
`Bed.metric.acts` pretending to be the cut metric. Another caveat:
`Affine.duct` takes a single `fderiv` of *all bonds simultaneously*. It can
default to zero when even one unrelated prediction is on a nonsmooth branch;
`Rows.move` only needs the selected bonds separately. Don't apply the
identification of Grams outside a legitimate differentiability region for the
*whole* free-side predictor! We give a concrete one near identity (output of
the analysis at this step, not an assumption that fields are globally there).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment
open Function Filter Set Lattice Wilson RG Precision Exterior Tree Matrix
open Next.SectorChange Next.SectorChange.Rows Pressure Pressure.Stores Bid
open FreeResolvent (insertion component flatten plant active ix)
open FreeResolvent.Affine
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (A : Stores S) (F : Forest S.ratio) (x : ℝ) (T : Tube G S) (k : S.Choices)

def launch : Gaussian.Vec (Raw G f) ≃L[ℝ] Directions G f := LinearEquiv.toContinuousLinearEquiv {
  toFun := fun a => collect G (decode a)
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := fun a => flatten (Flat.labels a)
  left_inv := by intro a; funext j; change a (_,coord (axisEquiv.symm j.2.1),_) = _; rw [show coord (axisEquiv.symm j.2.1)=j.2.1 from axisEquiv.apply_symm_apply j.2.1]
  right_inv := Flat.collected }

lemma relative_input (a : Prices G (Next.SectorChange.Active A x F)) :
    launch (insertion (address A F x) *ᵥ a) = Rows.fresh x (shots S x) A F (tape a) := by
  ext i j
  change (insertion (address A F x) *ᵥ a) (i.1,coord i.2,j) = Rows.fresh x (shots S x) A F (tape a) i j
  unfold Rows.fresh
  by_cases hi : i∉F.trunks
  · rw [dif_pos hi]; split
    next h => exact FreeResolvent.insertion_at (address A F x) _ (address A F x).injective (⟨⟨i,hi⟩,h⟩,j)
    next h =>
      apply FreeResolvent.insertion_misses
      rintro ⟨⟨b,l⟩,he⟩; have ht := FreeResolvent.plant_inj F (a₁:=live A F x (b,l)) (a₂:=(⟨i,hi⟩,j)) he
      have hu : b.val = ⟨i,hi⟩ := congr_arg Prod.fst ht
      exact b.property (hu.symm ▸ not_not.mp h)
  rw [dif_neg hi]; apply FreeResolvent.insertion_misses
  rintro ⟨b,he⟩
  have hz := (cull_address A F x b).symm.trans (congr_arg FreeResolvent.Mid.cull he)
  rw [show FreeResolvent.Mid.cull (i.1,coord i.2,j) = i from axis_junk i] at hz
  exact hi (hz ▸ b.1.val.property)
where
  axis_junk (i : Bond f) : (i.1,axisEquiv.symm (coord i.2))=i := Prod.ext rfl (axisEquiv.symm_apply_apply i.2)

lemma face_columns (B : Gaussian.Vec (Raw G c)) (s : Signed) (p : Cell f) (a : Gaussian.Vec (Raw G f)) :
    plaquetteJet S (represent (decode B)) s p (launch a) = decode (response S s B *ᵥ a) (p.1,plaquette p.2) := by
  let V := represent (decode B)
  have he := YM.Push.side _ (((Motion.plaquette_turn (S:=S) s V p (LocalJet.face_smooth .. |>.contDiffAt)).1).differentiableAt (by simp)) (launch a)
  have ht (t : ℝ) : facade S s V (t • launch a) = rays S s (B,t • a) := rfl
  simp_rw [ht] at he
  ext i
  let L := PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i
  have hh := hasDerivAt_pi.mp (face_path S s B a) (p.1,plaquette p.2,i)
  simp_rw [faces,show plaqEquiv.symm (plaquette p.2) = p.2 from plaqEquiv.symm_apply_apply p.2, Prod.mk.eta] at hh
  exact (L.hasFDerivAt.comp_hasDerivAt 0 he).unique hh

def WholeNoise (k : S.Choices) (B : Gaussian.Vec (Raw G c)) := ∀ s i,
    DifferentiableAt ℝ (fun a : Gaussian.Vec (Raw G f) => castNoise S s k i (B,a)) 0

lemma near_whole (h : S.patch.Branches S.kernel G) : ∀ᶠ B : Gaussian.Vec (Raw G c) in 𝓝 0, WholeNoise k B := by
  refine eventually_all.mpr fun s : Signed => eventually_all.mpr fun i : Bond c => ?_
  have he := (cast_smooth h s k i).eventually (by simp)
  have ht : Tendsto (fun B : Gaussian.Vec (Raw G c) => ((B,0):FreeResolvent.Affine.pair G c f)) (𝓝 0) (𝓝 0) :=
    (continuous_id.prodMk (continuous_const (y := (0:Gaussian.Vec (Raw G f))))).continuousAt
  filter_upwards [ht.eventually he] with B hB
  exact (hB.differentiableAt (by simp)).comp (f:=fun a => (B,a)) 0 ((differentiableAt_const B).prodMk differentiableAt_id)

lemma cast_turn (B : Gaussian.Vec (Raw G c)) (s : Signed) (i : Bond c) (h : S.patch.Branches S.kernel G) :
    (fun a => castNoise S s k i (B,a)) = (fun z => G.mat (predictorTurn (represent (decode B)) k s i z)) ∘ launch := by
  funext a; unfold castNoise predictorTurn predictGroup facade
  rw [Motion.increment_zero]
  simp only [Push.SectorMeasure.Oriented.carry s h k _ |>.2]
  rfl

lemma block_columns (B : Gaussian.Vec (Raw G c)) (s : Signed) (p : Bond c) (a : Gaussian.Vec (Raw G f))
    (h : S.patch.Branches S.kernel G) (H : WholeNoise k B) :
    blockJet (represent (decode B)) k s p (launch a) = decode (duct S s k B *ᵥ a) (p.1,coord p.2) := by
  let U (i : Bond c) (y : Directions G f) := predictorTurn (represent (decode B)) k s i y
  let Y (i : Bond c) (b : Gaussian.Vec (Raw G f)) := castNoise S s k i (B,b)
  let X := fderiv ℝ (Y p) 0 a
  have hy : HasDerivAt (fun t : ℝ => Y p (t • a)) X 0 := Push.side _ (H s p) a
  have hu (i b) : Y i b = G.mat (U i (launch b)) := congr_fun (cast_turn k B s i h) b
  have hz (i z) : G.mat (U i z) = Y i (launch.symm z) := by rw [hu,ContinuousLinearEquiv.apply_symm_apply]
  have hx (i) : DifferentiableAt ℝ (fun y => G.mat (U i y)) 0 := by
    rw [show (fun y => G.mat (U i y)) = _ from funext (hz i)]
    exact ((map_zero launch.symm).symm ▸ H s i : DifferentiableAt ℝ (Y i) (launch.symm 0)).comp 0 launch.symm.differentiableAt
  have he : U p 0=1 := mul_inv_cancel _
  simp_rw [hu,map_smul] at hy
  have hX : X ∈ G.lie := G.tangent_generates (f:=fun t : ℝ => G.mat (U p (t • launch a))) hy (by rw [zero_smul,he,G.mat_one]) fun i => ⟨_,rfl⟩
  have hc : DifferentiableAt ℝ (fun y => G.curvature (U p y)) 0 := by
    simp_rw [Gauge.curvature, G.mat_inv]
    refine G.projectColor.toContinuousLinearMap.differentiableAt.comp _ ?_
    exact ((hx p).sub ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).differentiableAt.comp _ (hx p))).const_smul (1/2:ℝ)
  have hh := Work.F03.curvature_of_hasDerivAt ((G.colorMat_project_self hX).symm ▸ hy : HasDerivAt
      (fun t : ℝ => G.mat (U p (t • launch a))) (G.colorMat (G.projectColor X)) 0)
  have hb : blockJet (represent (decode B)) k s p (launch a) = G.projectColor X := (Push.side _ hc _).unique hh
  rw [duct, LinearMap.toMatrix'_mulVec, hb]
  have hv : DifferentiableAt ℝ (fun a => gaugeQ S s k (B,a)) 0 := by
    apply differentiableAt_pi.mpr; intro i
    refine (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i.2.2).differentiableAt.comp _ ?_
    exact G.projectColor.toContinuousLinearMap.differentiableAt.comp _ (H s _)
  ext i
  let L := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : G.ColorIndex => ℝ) i).comp G.projectColor.toContinuousLinearMap
  have ht := (hasDerivAt_pi.mp (Push.side _ hv a) (p.1,coord p.2,i))
  simp only [gaugeQ,which] at ht
  rw [show axisEquiv.symm (coord p.2)=p.2 from axisEquiv.symm_apply_apply p.2,Prod.mk.eta] at ht
  change (G.projectColor X) i = _
  apply HasDerivAt.unique (f:= fun t : ℝ => G.projectColor (Y p (t • a)) i) (x:=0) _ ht
  exact L.hasFDerivAt.comp_hasDerivAt 0 (Push.side _ (H s p) a)

variable {σ E Λ : ℝ}
lemma path_sheet (h : T.up.Bounds T.high σ E Λ) : Sheet T.up σ E := h.rows

lemma faceKick_columns (B : Gaussian.Vec (Raw G c)) (s : Signed) (p : Twin f) (a : Gaussian.Vec (Raw G f))
    (hT : T.up.Bounds T.high σ E Λ) :
    faceKick T x (represent (decode B)) (launch a) s p =
      if p.2 then decode ((tracks S s T.up (shorter (till x)) B * response S s B) *ᵥ a) (p.1.1,plaquette p.1.2)
      else Real.sqrt T.high.direct • decode (response S s B *ᵥ a) (p.1.1,plaquette p.1.2) := by
  rw [faceKick]; split
  · rw [← Matrix.mulVec_mulVec,← flat_decode (response S s B *ᵥ a),← (reads_row S s _ _ hT.width.le (path_sheet T hT) B _ p.1).tsum_eq]
    unfold barrel; apply tsum_congr; intro i
    rw [fixed_facade]; simp only [shorter,decide_eq_true_eq]
    rw [face_columns B s (Work.F03.slotFace _ _) a]
    rfl
  rw [face_columns B s p.1 a]

lemma gram_dot (V : Config G c) (a b : Prices G (Next.SectorChange.Active A x F)) (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ) :
    let price (v : Prices G (Next.SectorChange.Active A x F)) := bump T x V k (fresh x (shots S x) A F (tape v))
    a ⬝ᵥ (Rows.gram T x V k (shots S x) A F *ᵥ b) =
      (Fintype.card Signed : ℝ)⁻¹ * ∑ s, ∑ i, inner ℝ (price a (s,i)) (price b (s,i)) := by
  intro price
  unfold Rows.gram; rw [← Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
  simp_rw [moved _ _ _ _ _ _ _ hT,selected_all _ _ _ _ _ _ _ h]
  unfold dotProduct; rw [Fintype.sum_prod_type, Fintype.sum_prod_type (f:=fun s : Slots S => _)]
  rw [Finset.mul_sum]; simp_rw [Work.F03.inner_color,Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have he : slip * slip = (Fintype.card Signed : ℝ)⁻¹ := by unfold slip; rw [← mul_inv,Real.mul_self_sqrt (by positivity)]
  change (slip*(price a _ j))*(slip*(price b _ j))=_
  rw [← he]; ring

lemma affineCore (B : Gaussian.Vec (Raw G c)) (h : S.patch.Branches S.kernel G) (H : WholeNoise k B) (hT : T.up.Bounds T.high σ E Λ) :
    let e := live (G:=G) A F x
    Rows.gram T x (represent (decode B)) k (shots S x) A F =
      (primary S F k T.high T.up (shorter (till x)) B).submatrix e e := by
  intro e
  have ht (v w : Prices G (Next.SectorChange.Active A x F)) :
      v ⬝ᵥ (Rows.gram T x (represent (decode B)) k (shots S x) A F *ᵥ w) =
      v ⬝ᵥ ((primary S F k T.high T.up (shorter (till x)) B).submatrix e e *ᵥ w) := by
    rw [gram_dot A F x T k _ _ _ h hT,primary,submatrix_submatrix, ← FreeResolvent.insertion.dot_compress, channels]
    let a := insertion (address A F x) *ᵥ v; let b := insertion (address A F x) *ᵥ w
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    let R := response S s B; let Q := duct S s k B; let D := tracks S s T.up (shorter (till x)) B * R
    change _ = a ⬝ᵥ (channel S s k T.high T.up (shorter (till x)) B *ᵥ b)
    rw [channel_qf]
    have hz {r n} (x y : FreeResolvent.Vec G n r) : x ⬝ᵥ y = ∑ i, inner ℝ (decode x i) (decode y i) := FreeResolvent.flat_dot (decode x) (decode y)
    change _ = T.high.direct*((R*ᵥa) ⬝ᵥ (R*ᵥb))+(D*ᵥa) ⬝ᵥ (D*ᵥb)+_ * ((Q*ᵥa) ⬝ᵥ (Q*ᵥb))
    rw [hz,hz,hz, ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv)
      (fun i => inner ℝ (decode (R *ᵥ a) i) (decode (R *ᵥ b) i)),
      ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site f)) plaqEquiv)
      (fun i => inner ℝ (decode (D *ᵥ a) i) (decode (D *ᵥ b) i)),
      ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv)
      (fun i => inner ℝ (decode (Q *ᵥ a) i) (decode (Q *ᵥ b) i)),Finset.mul_sum]
    rw [Fintype.sum_sum_type,Fintype.sum_prod_type,← Finset.sum_add_distrib]
    simp only [← relative_input,bump,Sum.elim_inl,Sum.elim_inr]; congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_bool]; simp_rw [faceKick_columns _ T _ _ _ _ hT]
      simp only [Bool.false_eq_true,↓reduceIte, real_inner_smul_left,real_inner_smul_right, ← mul_assoc _ _ (inner ..),Real.mul_self_sqrt T.high.quadratic_pos.le]
      exact add_comm ..
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
    simp only [noiseKick,block_columns k B s i _ h H,inner_neg_neg, real_inner_smul_left, real_inner_smul_right, ← mul_assoc _ _ (inner ..),Real.mul_self_sqrt S.kernel.penalty_pos.le]; rfl
  ext i j; simpa using ht (Pi.single i 1) (Pi.single j 1)

theorem affine_near (h : S.patch.Branches S.kernel G) (hT : T.up.Bounds T.high σ E Λ) :
    ∀ᶠ B : Gaussian.Vec (Raw G c) in 𝓝 0,
    Rows.gram T x (represent (decode B)) k (shots S x) A F =
      (primary S F k T.high T.up (shorter (till x)) B).submatrix (live A F x) (live A F x) :=
  (near_whole k h).mono fun B H => affineCore A F x T k B h H hT



end YM.AnalyticBridge.GaussianFieldAlignment
