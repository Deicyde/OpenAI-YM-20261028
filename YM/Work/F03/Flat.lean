import YM.Work.F03.Calculus
import YM.Work.F03.Metric


/-!
# The unmasked flat germ in log coordinates

Prove its value/slope/Hessian before pulling back to relative tree coordinates. In
particular, use the *literal* rooted predictor here at its tag and orientation, not a
block average replacing this predictor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.F03
open Filter Function Lattice RG Wilson Precision Push Bid Exterior Bloch Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace

attribute [local instance] Gauge.frobInner

variable {G : Gauge} {n c f : Side} {B : Bed} {p : Clip} {W : PathData G}
  {u v σ C Λ : ℝ}

lemma quadratic_limit (hb : W.Bounds p σ C Λ) (ht : Attached B W) (hf : Floor B p n u v)
    (a : Dir G n) : Tendsto (fun t : ℝ => quadratic p W (represent (t • a)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (gaugeFiscal B a a / 2)) := by
  rw [metric_pair B hb ht _ _ hf]
  unfold quadratic
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ (fun x hx => ?_)
  have he := ((ell_limit W hb x a).norm.pow 2).div_const 2
  have hp := (price_limit (G := G) (V := fun t : ℝ => faceValue (represent (t • a)) x)
    (by rw [zero_smul]; exact stroll_zero ..) (face_deriv x a)).const_mul p.direct
  have hv := hp.add he
  -- use the same physical color norm in both terms
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, add_div, mul_div_assoc]
  refine hv.congr' (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
  ring

lemma exp_neg_color (x : G.Color) : G.lieExp (-x) = (G.lieExp x)⁻¹ := by
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  apply eq_inv_of_mul_eq_one_left
  apply G.mat_injective
  rw [G.mat_one, G.mat_mul, G.mat_lieExp, G.mat_lieExp, map_neg]
  have he : NormedSpace.exp (-G.colorMat x + G.colorMat x) =
      NormedSpace.exp (-G.colorMat x) * NormedSpace.exp (G.colorMat x) :=
     NormedSpace.exp_add_of_commute (Commute.refl _).neg_left
  rw [← he]; simp

lemma represent_link (a : Dir G n) (e : Edge (Site n)) :
    represent a e = G.lieExp (a (e.1, coord e.2)) := mul_one _

/-- Orientation includes shifted base and possibly inverse. -/
lemma represent_pulled (s : Signed) (a : Dir G n) (t : ℝ) :
    pull s 0 (represent (t • a)) = represent (t • pulled a s) := by
  funext e
  simp only [pull, Step.read, represent_link, Pi.smul_apply, pulled,
    show axisEquiv.symm (coord e.2)=e.2 from axisEquiv.symm_apply_apply _]
  split
  · rw [smul_neg, exp_neg_color]
  rfl

lemma main_limit (hb : W.Bounds p σ C Λ) (ht : Attached B W) (hf : Floor B p n u v)
    (hs : Sworn B n G) (a : Dir G n) :
    Tendsto (fun t : ℝ => mainTerm p W (represent (t • a)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (gaugeFiscal B a a / 2)) := by
  have hh (s : Signed) := ((quadratic_limit hb ht hf (pulled a s)).add
    (uncut_limit (k := 0) (pulled a s) W.cubic hb.width hb.three)).add
    (uncut_limit (k := 1) (pulled a s) W.quartic hb.width hb.four)
  unfold Sworn at hs
  simp_rw [hs, add_zero] at hh
  have he := (tendsto_finsetSum Finset.univ (fun s _ => hh s)).const_mul
    (Fintype.card Signed : ℝ)⁻¹
  have hp : (Fintype.card Signed : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  simpa only [mainTerm, Patch.average, represent_pulled, mul_div_assoc,
    Finset.sum_div, add_div, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    inv_mul_cancel_left₀ hp] using he

abbrev Logs (G : Gauge) (c f : Side) := Dir G c × Dir G f

def flat (S : StepData c f) (k : S.Choices) (p : Clip) (W : PathData G) (z : Logs G c f) : ℝ :=
  mainTerm p W (represent z.2) + noiseTaylor S (represent z.1) (represent z.2) k

lemma represent_rate (a : Dir G n) (e : Edge (Site n)) :
    HasDerivAt (fun t : ℝ => G.mat (represent (t • a) e)) (G.colorMat (a (e.1, coord e.2))) 0 := by
  let v := a (e.1, coord e.2)
  have he : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v
  have hd : HasFDerivAt (fun x => G.mat (G.lieExp x)) G.colorMat.toContinuousLinearMap
      ((0:ℝ) • v) := by rw [zero_smul]; exact G.expDiff_zero
  simp_rw [represent_link, Pi.smul_apply]
  exact hd.comp_hasDerivAt 0 he

lemma represent_smooth (e : Edge (Site n)) :
    ContDiff ℝ ω (fun v : Dir G n => G.mat (represent v e)) := by
  simp_rw [represent_link]
  exact G.exp_jet.comp (contDiff_apply ℝ G.Color (e.1, coord e.2))

variable {S : StepData c f}

def residual (S : StepData c f) (z : Logs G c f) := z.1 - bills S z.2

def flatHess (S : StepData c f) (B : Bed) (x y : Logs G c f) : ℝ :=
  gaugeFiscal B x.2 y.2 + S.kernel.penalty *
    ∑ i : Body 1 c, inner ℝ (residual S x i) (residual S y i)

lemma noise_limit (h : S.patch.Branches S.kernel G) (k : S.Choices) (z : Logs G c f) :
    Tendsto (fun t : ℝ => noiseTaylor S (represent (t • z.1)) (represent (t • z.2)) k / t ^ 2)
      (𝓝[≠] 0) (𝓝 (S.kernel.penalty *
        (∑ i : Body 1 c, inner ℝ (residual S z i) (residual S z i)) / 2)) := by
  simp_rw [noiseTaylor, mul_div_assoc, Finset.sum_div,
    ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site c)) axisEquiv) (fun i =>
      inner ℝ (residual S z i) (residual S z i) / 2)]
  refine Tendsto.const_mul _ (tendsto_finsetSum _ (fun e _ => ?_))
  change Tendsto _ _ (𝓝 (inner ℝ (residual S z (e.1,coord e.2))
    (residual S z (e.1,coord e.2)) / 2))
  rw [real_inner_self_eq_norm_sq]
  have he : S.prediction (represent ((0:ℝ) • z.2)) k e = 1 := by
    rw [zero_smul,link_one,settled S h e k]
  apply price_limit (G := G) (V := fun t : ℝ => represent (t • z.1) e *
    (S.prediction (represent (t • z.2)) k e)⁻¹)
  · rw [he, zero_smul, link_one]; simp
  simp only [G.mat_mul, G.mat_inv]
  have hv : HasDerivAt (fun v : ℝ => G.mat (S.prediction (represent (v • z.2)) k e))
      (G.colorMat (bills S z.2 (e.1,coord e.2))) 0 := prices S h e k z.2
  convert! (represent_rate z.1 e).mul hv.star using 1
  rw [he]
  simp [Gauge.colorMat_skew, residual, sub_eq_add_neg]

lemma flat_limit (h : S.patch.Branches S.kernel G) (k : S.Choices)
    (hb : W.Bounds p σ C Λ) (ht : Attached B W) (hf : Floor B p f u v) (hs : Sworn B f G)
    (z : Logs G c f) : Tendsto (fun t : ℝ => flat S k p W (t • z) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (flatHess S B z z / 2)) := by
  simp_rw [flat, flatHess, add_div]
  exact (main_limit hb ht hf hs z.2).add (noise_limit h k z)

lemma price_smooth {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : X → G.El}
    (h : ContDiffAt ℝ ω (fun x : X => G.mat (A x)) 0) :
    ContDiffAt ℝ ω (fun x : X => G.price (A x)) 0 := by
  have he (x : X) : G.price (A x) = ‖G.mat (A x) - 1‖ ^ 2 / G.colorScale ^ 2 / 2 := by
    rw [← div_pow]; change _ = G.chord _ ^ 2 / 2; rw [G.chord_price]; ring
  simp_rw [he]
  exact (((contDiff_norm_sq ℝ).contDiffAt.comp 0 (h.sub contDiffAt_const)).div_const _).div_const _

lemma flat_smooth (h : S.patch.Branches S.kernel G) (k : S.Choices) (hi : Fires W p) :
    ContDiffAt ℝ ω (flat S k p W) 0 := by
  have hv (e : Edge (Site c)) : ContDiffAt ℝ ω (fun z : Logs G c f => G.mat
      (S.prediction (represent z.2) k e)) 0 :=
    (prediction_cont S h e k).comp (f:=Prod.snd) (0 : Logs G c f) contDiffAt_snd
  have hm : ContDiffAt ℝ ω (fun a : Dir G f => mainTerm p W (represent a)) 0 := hi.crown
    (0:Dir G f) f represent link_one (fun i => (represent_smooth i).contDiffAt)
  unfold flat noiseTaylor
  apply ContDiffAt.add
  · exact hm.comp (f := Prod.snd) (0 : Logs G c f) contDiffAt_snd
  refine ContDiffAt.mul (contDiffAt_const (c := S.kernel.penalty)) (ContDiffAt.sum fun i _ => ?_)
  apply price_smooth (A := fun z : Logs G c f => represent z.1 i * (S.prediction (represent z.2) k i)⁻¹)
  simp only [G.mat_mul, G.mat_inv]
  exact ((represent_smooth (G:=G) i).contDiffAt.comp (f := Prod.fst) (0:Logs G c f) contDiffAt_fst).mul
    ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (hv i))

lemma parts_add (x y : Dir G n) (i : G.ColorIndex) :
    parts G 1 (x+y) i = parts G 1 x i + parts G 1 y i := rfl

lemma gaugeFiscal_add (x y z : Dir G n) :
    gaugeFiscal B (x+y) z = gaugeFiscal B x z + gaugeFiscal B y z := by
  unfold gaugeFiscal; simp_rw [parts_add, add_dotProduct, Finset.sum_add_distrib]

lemma flat_jets (h : S.patch.Branches S.kernel G) (k : S.Choices)
    (hb : W.Bounds p σ C Λ) (ht : Attached B W) (hf : Floor B p f u v) (hs : Sworn B f G)
    (hi : Fires W p) :
    flat S k p W 0 = 0 ∧ fderiv ℝ (flat S k p W) 0 = 0 ∧ ∀ x y,
      iteratedFDeriv ℝ 2 (flat S k p W) 0 ![x,y] = flatHess S B x y := by
  apply hessian_of_limit ((flat_smooth h k hi).of_le le_top) (flat_limit h k hb ht hf hs)
  · intro x y z
    have hw : bills S (x.2+y.2) = bills S x.2 + bills S y.2 := by
      ext i j; simp only [bills, parts_add, mulVec_add, Pi.add_apply]; rfl
    have he : residual S (x+y) = residual S x + residual S y := by
      unfold residual; simp only [Prod.fst_add, Prod.snd_add, hw]; abel
    simp only [flatHess, Prod.snd_add, gaugeFiscal_add, he, Pi.add_apply, inner_add_left,
      Finset.sum_add_distrib, mul_add]
    abel
  intro x y
  simp_rw [flatHess, metric_pair B hb ht _ _ hf]
  congr 1
  · apply Finset.sum_congr rfl; intro i _
    rw [real_inner_comm (faceCurl _ x.2), real_inner_comm (ellLine W _ x.2)]
  congr 1; apply Finset.sum_congr rfl; intro i _
  exact real_inner_comm _ _

end YM.Work.F03
