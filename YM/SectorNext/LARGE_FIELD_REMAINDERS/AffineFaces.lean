import YM.SectorNext.LARGE_FIELD_REMAINDERS.AffineCharts


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Actual affine-row geometry: face wires

Retains the anchored p-leg paths; physical positive-link perturbation in one
channel's own orientations. Use in each turned channel only after verifying these
inputs (and use actual a in that channel, not the one in a reflected frame!).
Connect with E eq:affvd. Extension on frozen shell permitted through constructions
*if* those inputs still read correctly (true applicability test in Annulus).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder.Affine
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial  Next.Fluctuations Scales Metric   Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical  ContDiff

variable {G : Gauge} {n c f : Side} {S : StepData c f}

def patchFace (p : Cell n) : Fin 4 → Bond n :=
  let i := p.2.val.1; let j := p.2.val.2; let x := p.1
  ![(x,i),(x+step i,j),(x+step j,i),(x,j)]

def faceVar (W : Config G n) (a : Directions G n) (p : Cell n) :=
  deriv (fun t : ℝ => G.curvature (faceValue (increment W (t • a)) p)) 0

def flow (z : Site n → G.El) (a : Directions G n) : Directions G n := fun i => G.adjoint (z i.1) (a i)

lemma tip_turn (W : Config G n) (a : Directions G n) (p : Cell n) (z : Site n → G.El) :
    (fun t : ℝ => G.curvature (faceValue (increment (gauge z W) (t • flow z a)) p)) =
      fun t => G.adjoint (z p.1) (G.curvature (faceValue (increment W (t • a)) p)) := by
  funext t
  rw [show t • flow z a = (fun i : Bond n => G.adjoint (z i.1) ((t • a) i)) by ext i; simp [flow,map_smul],← increment_gauge,face_gauge,G.curvature_conjugate]

private abbrev C4 (G : Gauge) := Fin 4 → G.Color

private def sqF (x : C4 G × C4 G) :=
  let q i := G.lieExp (x.1 i) * G.lieExp (x.2 i)
  G.curvature (q 0 * q 1 * (q 2)⁻¹ * (q 3)⁻¹)

private lemma sqF_analytic (G : Gauge) : ContDiffAt ℝ ω (sqF (G:=G)) 0 := by
  unfold sqF
  apply curvature_diff_mat
  let a i (x : C4 G × C4 G) := G.mat (G.lieExp (x.1 i)) * G.mat (G.lieExp (x.2 i))
  have he (i : Fin 4) : ContDiff ℝ ω (a i) := (G.exp_jet.comp ((contDiff_apply ℝ _ _).comp contDiff_fst)).mul (G.exp_jet.comp ((contDiff_apply ℝ _ _).comp contDiff_snd))
  have h1 (i : Fin 4) : ContDiff ℝ ω (fun x => star (a i x)) :=
    (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp (he i)
  simp only [G.mat_mul,G.mat_inv]
  exact (((he 0).mul (he 1)).mul (h1 2)).mul (h1 3)|>.contDiffAt

private lemma steps_sq (W : Config G n) (a b : Directions G n) (p : Cell n)
    (h : ∀ i, W (patchFace p i)=G.lieExp (b (patchFace p i))) :
    G.curvature (faceValue (increment W a) p) = sqF (a∘patchFace p,b∘patchFace p) := by
  let x := p.1; let i := p.2.val.1; let j := p.2.val.2
  have ht : x+step i+step j-step i=x+step j := by abel
  have ht' : x+step i+step j+(-(step i:Site n))=x+step j := by abel
  rw [faceValue]; change G.curvature (travel _ x (square i j)) = _
  simp only [square,travel, Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,ht,ht',add_sub_cancel_right,mul_one]
  unfold increment
  change G.curvature ((G.lieExp (a (patchFace p 0))*_) * ((G.lieExp (a (patchFace p 1))*_)*
    ((G.lieExp (a (patchFace p 2))*_)⁻¹*(G.lieExp (a (patchFace p 3))*_)⁻¹))) = _
  rw [show W (x,i)=W (patchFace p 0) from rfl,show W (x+step i,j)=W (patchFace p 1) from rfl,
    show W (x+step j,i)=W (patchFace p 2) from rfl,show W (x,j)=W (patchFace p 3) from rfl]
  simp only [h,sqF,Function.comp_apply,mul_assoc]

-- transport derivative despite analytic information possibly in only transformed field
lemma differentiation_back {ι β : Type} [NormedAddCommGroup ι] [NormedSpace ℝ ι] [NormedAddCommGroup β]
    [NormedSpace ℝ β] (g : ι →L[ℝ] β) (f : β →L[ℝ] ι) (hl : LeftInverse f g)
    (a : ℝ → ι) (b : ℝ → β) (h : b=g∘a) (hd : DifferentiableAt ℝ b 0) :
    DifferentiableAt ℝ a 0 ∧ g (deriv a 0)=deriv b 0 := by
  have he : a=f∘b := funext fun t => by rw [h]; exact (hl (a t)).symm
  have hv : DifferentiableAt ℝ a 0 := by rw [he]; exact f.differentiableAt.comp 0 hd
  exact ⟨hv, h ▸ (g.hasFDerivAt.comp_hasDerivAt 0 hv.hasDerivAt).deriv.symm⟩

lemma ad_inv (z : G.El) : LeftInverse (G.adjoint z⁻¹).toContinuousLinearMap (G.adjoint z).toContinuousLinearMap := by
  intro i; change G.adjoint z⁻¹ (G.adjoint z i)=_
  rw [← G.adjoint_mul, inv_mul_cancel, G.adjoint_one]

set_option maxHeartbeats 680000 in
/-- Test one face at any orientation without composing Hessians on large
spaces. z fixed throughout the evaluation, all four possible fine-link readings
at small displacements and expanded on true logarithms of W in that gauge.
b costs can depend on L. -/
lemma face_affine (G : Gauge) : ∃ C r : ℝ, 0<C ∧ 0<r ∧ ∀ n : Side, ∀ (U W : Config G n) (a b : Directions G n)
    (p : Cell n) (z : Site n → G.El) (h : ℝ), 0 ≤ h → h ≤ r →
    (∀ i, ‖a (patchFace p i)‖ ≤ h) → (∀ i, ‖b (patchFace p i)‖ ≤ h) →
    (∀ i, U (patchFace p i) = increment W a (patchFace p i)) →
    (∀ i, gauge z W (patchFace p i)=G.lieExp (b (patchFace p i))) →
    DifferentiableAt ℝ (fun t : ℝ => G.curvature (faceValue (increment W (t • a)) p)) 0 ∧
    ‖G.curvature (faceValue U p) - (G.curvature (faceValue W p)+faceVar W a p)‖ ≤ C*h^2 ∧
    ‖G.curvature (faceValue W p)‖ ≤ C*h ∧ ‖faceVar W a p‖ ≤ C*h := by
  obtain ⟨C,r,hC,hr,h⟩ := charts (sqF (G:=G)) sqF (sqF_analytic G) (sqF_analytic G) 1
    (show _=0 by simp [sqF]) (by intro v; rw [one_smul])
  refine ⟨C,r,hC,hr,?_⟩; intro n U W a b p z s hs ht ha hb hU hW
  let y : C4 G := flow z a ∘ patchFace p
  have hy : ‖y‖ ≤ s := (pi_norm_le_iff_of_nonneg hs).mpr fun i => by unfold y flow; simp only [comp_apply, G.norm_adjoint]; exact ha i
  have hl : ‖b∘patchFace p‖ ≤ s := (pi_norm_le_iff_of_nonneg hs).mpr hb
  let g := gauge z W
  have he (t : ℝ) : G.curvature (faceValue (increment g (t • flow z a)) p) = sqF (t • y,b∘patchFace p) := steps_sq g _ b p hW
  let f := fun t : ℝ => G.curvature (faceValue (increment W (t • a)) p)
  let u := fun t : ℝ => sqF (G:=G) (t • y,b ∘ patchFace p)
  let Z := (G.adjoint (z p.1)).toContinuousLinearMap
  have hw : u = Z ∘ f := by
    rw [← show _ = Z∘f from tip_turn W a p z]; exact funext fun t : ℝ => (he t).symm
  obtain ⟨hf,hH, -,h1,h2⟩ := h s hs ht y (b∘patchFace p) hy hl
  have hJ := differentiation_back Z (G.adjoint (z p.1)⁻¹).toContinuousLinearMap (ad_inv _) f u hw hf
  have h3 : faceValue U p=faceValue (increment W a) p := by
    -- on those four positions
    have hv (x : Site n) (i j : Axis) : x+step i+step j-step i=x+step j:= by abel
    have hv' (x : Site n) (i j : Axis) : x+step i+step j+(-step i)=x+step j:= by abel
    simp only [faceValue,square,travel,Step.vec_pos,Step.vec_neg,Step.pos_read,Step.neg_read,hv,hv',add_sub_cancel_right]
    rw [show U (p.1,p.2.val.1)=_ from hU 0,show U (p.1+step p.2.val.1,p.2.val.2)=_ from hU 1,
      show U (p.1+step p.2.val.2,p.2.val.1)=_ from hU 2,show U (p.1,p.2.val.2)=_ from hU 3]; rfl
  have H (t : ℝ) : Z (f t)=u t := by rw [hw]; rfl
  have H0 : Z (G.curvature (faceValue W p))=sqF (0,b∘patchFace p) := by
    have heq : increment W (0:Directions G n) = W := by
      funext e; unfold increment; simp only [Pi.zero_apply,G.mat_lieExp_zero,one_mul]
    simpa only [heq,f,u,zero_smul] using! H 0
  have H1 : Z (G.curvature (faceValue U p))=sqF (y,b∘patchFace p) := by
    rw [h3]; simpa only [f,u,one_smul] using! H 1
  have hp : Z (faceVar W a p) = response sqF y (b∘patchFace p) := hJ.2
  have hv w : ‖w‖ = ‖Z w‖ := (G.norm_adjoint (z p.1) w).symm
  refine ⟨hJ.1, ?_,?_,?_⟩
  · rw [hv,map_sub,map_add,H1,H0,hp]; rwa [one_smul] at hH
  · rwa [hv,H0]
  rwa [hv,hp]
end YM.SectorNext.Remainder.Affine
