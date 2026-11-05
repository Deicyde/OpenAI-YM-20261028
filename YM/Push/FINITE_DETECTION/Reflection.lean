import YM.Next.EXTRACTION.Tails
import YM.Push.FINITE_DETECTION.Response

/-! Reflection in component tensors at the two-point detector axis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Kelvin
open Function Set Filter Analysis Maxwell WaveOn Tensor
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j l : ℕ}

def pole := basis timeAxis
lemma pole_in : pole ∈ away := by change pole ≠ 0; apply norm_ne_zero_iff.mp; simp [pole]
abbrev σ : Ortho := Signed.reflect timeAxis
abbrev flipE : E4 ≃ₗᵢ[ℝ] E4 := σ.motion
lemma σ_inv : σ⁻¹ = σ := ((map_inv Signed.inclusionO _).symm.trans (congr_arg Signed.inclusionO (Signed.mirror_inv _)))
lemma flip_pole : flipE pole = -pole := by ext i; simp [pole,flipE]; split <;> simp_all

def sign (a : Axis) := if a = timeAxis then (-1:ℝ) else 1
@[simp] lemma sign_sq (a : Axis) : sign a * sign a = 1 := by unfold sign; split <;> norm_num
lemma flipE_at (x : E4) (a : Axis) : flipE x a = sign a * x a := by simp [sign]
@[simp] lemma flipE_flip (x : E4) : flipE (flipE x) = x := by ext1 a; rw [flipE_at,flipE_at,← mul_assoc,sign_sq,one_mul]
lemma flipE_basis (a : Axis) : flipE (basis a) = sign a • basis a := by ext i; rw [flipE_at]; simp; split <;> simp_all

abbrev pairSign (a b : Axis) := sign a * sign b

def turning (Y : Maxwell.Field F) : Maxwell.Field F := fun a b x => pairSign a b • Y a b (flipE x)

def reflectedJet : TwoJet F j →ₗ[ℝ] TwoJet F j where
  toFun Q a b := pairSign a b • ((Q a b).compContinuousLinearMap fun _ => flipE.toContinuousLinearMap)
  map_add' Q Y := by funext a b; ext1 u; apply smul_add
  map_smul' c Q := by funext a b; ext1 u; exact smul_comm _ c _

lemma apply_jet (Q : TwoJet F j) (a b : Axis) (v : Fin j → E4) : reflectedJet Q a b v = pairSign a b • Q a b (flipE ∘ v) := rfl
lemma diag_jet (Q : TwoJet F j) : actual (reflectedJet Q) = turning (actual Q) := rfl
@[simp] lemma reflected_twice (Q : TwoJet F j) : reflectedJet (reflectedJet Q) = Q := by
  funext a b; ext1 u
  rw [apply_jet,apply_jet,smul_smul,mul_mul_mul_comm,sign_sq,sign_sq,mul_one,one_smul]
  exact congr_arg _ (funext fun i => flipE_flip (u i))

lemma coeff_reflect (Y : Maxwell.Field F) {x : E4} (h : ∀ a b, smoothAt (Y a b) (flipE x)) :
    nth (turning Y) j x = reflectedJet (nth Y j (flipE x)) := by
  funext a b
  let L := flipE.toContinuousLinearEquiv
  have he := L.iteratedFDerivWithin_comp_right (Y a b) (uniqueDiffOn_univ) (mem_univ (L x)) j
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  change coeff ((pairSign a b) • ((Y a b) ∘ L)) j x = _
  rw [coeff_smul _ (by exact ((h a b).comp x L.contDiff.contDiffAt |>.of_le (allOrders _))), coeff,he]; ext1 u
  rw [apply_jet]; rfl

lemma grad_turning (Y : Maxwell.Field F) {x : E4} (i a b : Axis) (h : smoothAt (Y a b) (flipE x)) :
    grad i (turning Y a b) x = (sign i * pairSign a b) • grad i (Y a b) (flipE x) := by
  let L := flipE.toContinuousLinearMap
  have hf : DifferentiableAt ℝ (Y a b) (L x) := h.differentiableAt (by simp)
  change fderiv ℝ (pairSign a b • ((Y a b) ∘ L)) x _ = _
  rw [fderiv_const_smul (hf.comp x L.differentiableAt),smul_apply,fderiv_comp x hf L.differentiableAt,L.fderiv,
    ContinuousLinearMap.comp_apply, show L (basis i) = _ from flipE_basis i,map_smul]; rw [smul_smul,mul_comm]; rfl

theorem reflected_mem (Y : Shell G j) : reflectedJet Y.val ∈ onShell _ _ := by
  have h := wave_actual Y.property
  have hs x a b := h.smooth a b (flipE x) trivial
  refine ⟨⟨fun a b u r => congr_arg (fun z => pairSign a b • z) (Y.property.1.coeffSym a b (flipE ∘ u) r), ?_,?_⟩, ?_⟩
  · intro a b; ext1 u; rw [apply_jet, Y.property.1.antisymmetric a b]; simp only [pairSign,mul_comm,apply_jet,neg_apply,smul_neg]
  · intro a b c x
    change grad a (turning (actual Y.val) b c) _ + grad b (turning (actual Y.val) c a) _ + grad c (turning (actual Y.val) a b) _ = _
    rw [grad_turning _ _ _ _ (hs x b c),grad_turning _ _ _ _ (hs x c a),grad_turning _ _ _ _ (hs x a b)]
    rw [show sign b * pairSign c a = sign a * pairSign b c by unfold pairSign; ring,
      show sign c * pairSign a b = sign a * pairSign b c by unfold pairSign; ring,← smul_add, ← smul_add,
      h.cycle a b c (flipE x) trivial,smul_zero]
  intro b x
  change ∑ i, grad i (turning (actual Y.val) i b) _ = _
  simp_rw [grad_turning _ _ _ _ (hs x _ _),pairSign,← mul_assoc,sign_sq,one_mul,← Finset.smul_sum,h.divergence b (flipE x) trivial, smul_zero]

def mirrorJet : Shell G j →ₗ[ℝ] Shell G j :=
  (reflectedJet.comp (onShell _ _).subtype).codRestrict _ reflected_mem
@[simp] lemma mirror_twice (Y : Shell G j) : mirrorJet (mirrorJet Y) = Y := Subtype.ext (reflected_twice _)

lemma gaugeMirror (Y : Shell G j) : gaugeJet (mirrorJet Y) = Labels.Taylor.turn σ (gaugeJet Y) := by
  apply Labels.Taylor.value_ext; funext i x
  change (contracted (reflected_mem Y).1).value i x = _
  rw [Labels.Taylor.turn_value,σ_inv, Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ hj => ?_),
    show σ.val i i = sign i by simp [σ,Signed.reflect,Signed.ortho,Signed.matrix_at,Signed.mirror,sign,eq_comm]]
  · change (contracted (reflected_mem Y).1).value i x = sign i • (contracted Y.property.1).value i (σ.move x)
    rw [contracted_diag,contracted_diag,smul_comm (sign i),Finset.smul_sum (r := sign i)]; congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    change x k • actual (reflectedJet Y.val) k i x = _
    rw [diag_jet, turning,show σ.move x k = _ from flipE_at x k]; simp only [actual,smul_smul,pairSign]; congr 1; ring
  simp [σ,Signed.reflect,Signed.ortho,Signed.matrix_at,Signed.mirror,hj]

lemma frob_reflected (Y P : TwoJet G.Color j) : frob (G := G) (reflectedJet Y) P = frob Y (reflectedJet P) := by
  simp only [frob_apply,apply_jet]
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro u _
  rw [show flipE ∘ basis ∘ u = fun i => sign (u i) • (basis ∘ u) i from funext fun i => flipE_basis _,
    (Y i k).map_smul_univ, (P i k).map_smul_univ]; simp; ring

lemma R_flip (x : E4) : R (flipE x) = R x := by simp [R, Ortho.move_norm]
lemma inversion_flip (x : E4) : inversion (flipE x) = flipE (inversion x) := by
  rw [inversion,R_flip]; exact ((map_neg flipE _).trans (congr_arg Neg.neg (map_smul flipE ..))).symm
lemma turning_inverted (Y : Maxwell.Field F) : inverted (turning Y) = turning (inverted Y) := by
  funext a b x
  let u := inversion (flipE x)
  have he (b : Axis) : iota x (fun a b => turning Y a b (inversion x)) b =
      sign b • iota (flipE x) (fun a b => Y a b u) b := by
    rw [iota,iota,Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _
    rw [turning,← inversion_flip, flipE_at]
    dsimp only; rw [smul_smul, smul_smul]; congr 1; dsimp [pairSign]; ring
  have hh (a b : Axis) (v : F) : x a • sign b • v = pairSign a b • flipE x a • v := by
    rw [flipE_at, smul_smul, smul_smul]; congr 1
    unfold pairSign; calc
      _ = (sign a * sign a) * (x a * sign b) := by rw [sign_sq,one_mul]
      _ = _ := by ring
  conv_lhs => unfold inverted adjust
  dsimp only
  rw [he,he,turning,← inversion_flip]
  conv_rhs => unfold turning inverted adjust
  rw [hh a b,hh b a,show pairSign b a = pairSign a b from mul_comm ..,← smul_sub,smul_comm (2 * R x),
    ← smul_sub,smul_comm (R x ^ 2),R_flip]

def asProbe (Y : Shell G j) := constrain (frob Y.val)

def form (p : Probe G j) (q : Probe G l) := pairing pole_in p (q.comp mirrorJet)

lemma toProbe_reflected (Y : Shell G j) : asProbe (mirrorJet Y) = (asProbe Y).comp mirrorJet := by
  ext1 x; exact frob_reflected ..

lemma response_flip (Y : Shell G j) : reflectedJet (nth (responded G (frob Y.val)) l pole) =
    nth (responded G (frob (mirrorJet Y).val)) l (-pole) := by
  have hp : flipE (-pole) = pole := by rw [map_neg,flip_pole,neg_neg]
  let F := responded G (frob Y.val)
  let F' := responded G (frob (mirrorJet Y).val)
  change reflectedJet (nth F l pole) = nth F' l (-pole)
  conv_lhs => rw [← hp,← coeff_reflect F (fun a b => (response (frob (G := G) Y.val)).smooth _ _ _ (hp.symm ▸ pole_in))]
  funext a b
  apply GermCoeff
  have hv : -pole ∈ away := neg_ne_zero.mpr pole_in
  filter_upwards [open_away.mem_nhds hv] with x hx
  have hw : flipE x ∈ away := by
    change flipE x ≠ 0; exact (map_ne_zero_iff flipE flipE.injective).mpr hx
  change pairSign a b • F a b (flipE x) = F' a b x
  rw [show F a b (flipE x) = _ from response_eq Y a b hw,smul_comm,
    show F' a b x = _ from response_eq (mirrorJet Y) a b hx]; congr 1
  change turning (inverted (actual Y.val)) a b x = inverted (actual (reflectedJet Y.val)) a b x
  rw [diag_jet, turning_inverted]

theorem reflection_form (Y : Shell G j) (Z : Shell G l) :
    form (asProbe Y) (asProbe Z) = form (asProbe Z) (asProbe Y) := by
  rw [form,form, exchange,← toProbe_reflected Z,← toProbe_reflected Y]
  change legKernel (asProbe (mirrorJet Z)) (asProbe Y) (-pole) = legKernel (asProbe Z) (asProbe (mirrorJet Y)) pole
  unfold asProbe
  rw [concrete (G := G) (frob (mirrorJet Z).val) (frob Y.val) (neg_ne_zero.mpr pole_in),
    concrete (G := G) (frob Z.val) (frob (mirrorJet Y).val) pole_in, contraction,contraction]
  change _ = (-1)^j * frob (G := G) (reflectedJet Y.val) _
  rw [frob_reflected,response_flip]
end YM.Push.FiniteDetection.Kelvin
