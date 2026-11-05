import YM.Push.FINITE_DETECTION.Variables

/-! Covariance of the leg detector calculation for all signed axes, any
nonzero displacement. Pulled-back (not pushed-forward) jet convention in
`turn`, for evaluating a raw `Labels.tensor s.ortho` observable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Free.Hyper
open Function Set Filter Analysis Maxwell WaveOn Tensor Kelvin
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j l : ℕ}

abbrev Rₛ (s : Signed) := s.ortho.motion
def flip (s : Signed) (a : Axis) : ℝ := if s.flip a then -1 else 1
lemma flip_sq (s : Signed) (a : Axis) : flip s a * flip s a = 1 := by unfold flip; split <;> norm_num
abbrev sign₂ (s : Signed) (a b : Axis) := flip s a * flip s b
lemma moves_at (s : Signed) (x : E4) (a : Axis) : Rₛ s x (s.perm a) = flip s a * x a := by
  simp [flip,Rₛ,Signed.ortho_move]
lemma moves_basis (s : Signed) (a : Axis) : Rₛ s (basis a) = flip s a • basis (s.perm a) := by
  ext i; obtain ⟨k,rfl⟩ := s.perm.surjective i; rw [moves_at]; simp; split <;> simp_all

def pull (s : Signed) (Y : Maxwell.Field F) : Maxwell.Field F := fun a b x => sign₂ s a b • Y (s.perm a) (s.perm b) (Rₛ s x)

def turns (s : Signed) : TwoJet F j →ₗ[ℝ] TwoJet F j where
  toFun Q a b := sign₂ s a b • ((Q (s.perm a) (s.perm b)).compContinuousLinearMap fun _ => (Rₛ s).toContinuousLinearMap)
  map_add' Q Y := by funext a b; ext1 u; apply smul_add
  map_smul' c Q := by funext a b; ext1 u; exact smul_comm _ c _

lemma apply_turns (s : Signed) (Q : TwoJet F j) (a b : Axis) (v : Fin j → E4) :
    turns s Q a b v = sign₂ s a b • Q (s.perm a) (s.perm b) (Rₛ s ∘ v) := rfl
lemma diag_turns (s : Signed) (Q : TwoJet F j) : actual (turns s Q) = pull s (actual Q) := rfl

lemma coeff_pull (s : Signed) (Y : Maxwell.Field F) {x : E4} (h : ∀ a b, smoothAt (Y a b) (Rₛ s x)) :
    nth (pull s Y) j x = turns s (nth Y j (Rₛ s x)) := by
  funext a b
  let L := (Rₛ s).toContinuousLinearEquiv
  let f := Y (s.perm a) (s.perm b)
  have he := L.iteratedFDerivWithin_comp_right f (uniqueDiffOn_univ) (mem_univ (L x)) j
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  change coeff ((sign₂ s a b) • (f ∘ L)) j x = _
  rw [coeff_smul _ (by exact ((h (s.perm a) (s.perm b)).comp x L.contDiff.contDiffAt |>.of_le (allOrders _))), coeff,he]; ext1 u
  rw [apply_turns]; rfl

lemma grad_pull (s : Signed) (Y : Maxwell.Field F) {x : E4} (i a b : Axis)
    (h : smoothAt (Y (s.perm a) (s.perm b)) (Rₛ s x)) :
    grad i (pull s Y a b) x = (flip s i * sign₂ s a b) • grad (s.perm i) (Y (s.perm a) (s.perm b)) (Rₛ s x) := by
  let L := (Rₛ s).toContinuousLinearMap
  let f := Y (s.perm a) (s.perm b)
  have hf : DifferentiableAt ℝ f (L x) := h.differentiableAt (by simp)
  change fderiv ℝ (sign₂ s a b • (f ∘ L)) x _ = _
  rw [fderiv_const_smul (hf.comp x L.differentiableAt),smul_apply,fderiv_comp x hf L.differentiableAt,L.fderiv,
    ContinuousLinearMap.comp_apply, show L (basis i) = _ from moves_basis s i,map_smul]; rw [smul_smul,mul_comm]; rfl

theorem turns_mem (s : Signed) (Y : Shell G j) : turns s Y.val ∈ onShell _ _ := by
  have h := wave_actual Y.property
  have hs x a b := h.smooth (s.perm a) (s.perm b) (Rₛ s x) trivial
  refine ⟨⟨fun a b u r => congr_arg (fun z => sign₂ s a b • z) (Y.property.1.coeffSym _ _ (Rₛ s ∘ u) r), ?_,?_⟩, ?_⟩
  · intro a b; ext1 u; rw [apply_turns, Y.property.1.antisymmetric (s.perm a) (s.perm b)]; simp only [sign₂,mul_comm,apply_turns,neg_apply,smul_neg]
  · intro a b c x
    change grad a (pull s (actual Y.val) b c) _ + grad b (pull s (actual Y.val) c a) _ + grad c (pull s (actual Y.val) a b) _ = _
    rw [grad_pull _ _ _ _ _ (hs x b c),grad_pull _ _ _ _ _ (hs x c a),grad_pull _ _ _ _ _ (hs x a b)]
    rw [show flip s b * sign₂ s c a = flip s a * sign₂ s b c by unfold sign₂; ring,
      show flip s c * sign₂ s a b = flip s a * sign₂ s b c by unfold sign₂; ring,← smul_add, ← smul_add,
      h.cycle (s.perm a) (s.perm b) (s.perm c) (Rₛ s x) trivial,smul_zero]
  intro b x
  change ∑ i, grad i (pull s (actual Y.val) i b) x = _
  simp_rw [grad_pull s _ _ _ _ (hs x _ _),sign₂,← mul_assoc,flip_sq,one_mul,← Finset.smul_sum]
  rw [Equiv.sum_comp s.perm (fun i => grad i (actual Y.val i _) _), h.divergence (s.perm b) _ trivial,smul_zero]

def turn (s : Signed) : Shell G j →ₗ[ℝ] Shell G j :=
  ((turns s).comp (onShell _ _).subtype).codRestrict _ (turns_mem s)

lemma turn_inv (s : Signed) (Y : TwoJet F j) : turns s (turns s⁻¹ Y) = Y := by
  funext a b; ext1 u
  have he (i) : Hyper.flip s⁻¹ (s.perm i) = Hyper.flip s i := by simp [Hyper.flip]
  rw [apply_turns,apply_turns]; simp only [sign₂, he,smul_smul,mul_mul_mul_comm,flip_sq,mul_one,one_smul,Signed.inv_perm,Equiv.symm_apply_apply]
  apply congr_arg _; funext v; dsimp [Rₛ]; rw [show s⁻¹.ortho = s.ortho⁻¹ from map_inv Signed.inclusionO s,Ortho.inv_move]

lemma gaugeTurn (s : Signed) (Y : Shell G j) : gaugeJet (turn s Y) = Labels.Taylor.turn s.ortho⁻¹ (gaugeJet Y) := by
  have hs : s.ortho⁻¹ = s⁻¹.ortho := (map_inv Signed.inclusionO s).symm
  apply Labels.Taylor.value_ext; funext i x
  change (contracted (turns_mem s Y).1).value _ _ = _
  rw [Labels.Taylor.turn_value, inv_inv, Finset.sum_eq_single_of_mem (s.perm i) (Finset.mem_univ _) (fun j _ hj => ?_),
    show s.ortho⁻¹.val i (s.perm i) = Hyper.flip s i by rw [hs]; simp [Hyper.flip,Signed.ortho,Signed.matrix_at]]
  · change (contracted (turns_mem s Y).1).value i x = Hyper.flip s i • (contracted Y.property.1).value (s.perm i) (Rₛ s x)
    rw [contracted_diag,contracted_diag,smul_comm (Hyper.flip s i),Finset.smul_sum (r := Hyper.flip s i)]; congr 1
    refine Fintype.sum_equiv s.perm _ _ fun k => ?_
    change x k • actual (turns s Y.val) k i x = _
    rw [diag_turns, pull, moves_at]; simp only [actual,smul_smul,sign₂]; congr 1; ring
  obtain ⟨j,rfl⟩ := s.perm.surjective j
  have he : j ≠ i := fun h => hj (congr_arg _ h)
  rw [show s.ortho⁻¹.val i (s.perm j) = 0 by rw [hs]; simp [Signed.ortho,Signed.matrix_at,he],zero_smul]

lemma frob_turn (s : Signed) (Y P : TwoJet G.Color j) : frob (G := G) (turns s Y) (turns s P) = frob Y P := by
  simp only [frob_apply,apply_turns]
  apply Finset.sum_congr rfl; intro c _
  refine Fintype.sum_equiv s.perm _ _ fun i => ?_
  refine Fintype.sum_equiv s.perm _ _ fun k => ?_
  let e := Equiv.piCongrRight fun _ : Fin j => s.perm
  refine Fintype.sum_equiv e _ _ fun u => ?_
  rw [show Rₛ s ∘ basis ∘ u = fun i => Hyper.flip s (u i) • (basis ∘ (e u)) i from funext fun i => moves_basis _ _,
    (Y _ _).map_smul_univ, (P _ _).map_smul_univ]
  change ((Hyper.flip s i * Hyper.flip s k) * ((∏ t, Hyper.flip s (u t)) * _)) * ((Hyper.flip s i * Hyper.flip s k) * ((∏ t, Hyper.flip s (u t)) * _)) = _
  rw [mul_mul_mul_comm, mul_mul_mul_comm (Hyper.flip ..),flip_sq,flip_sq,mul_one,one_mul,mul_mul_mul_comm,← Finset.prod_mul_distrib]
  simp_rw [flip_sq,Finset.prod_const_one,one_mul]; rfl

lemma pull_inverted (s : Signed) (Y : Maxwell.Field F) : inverted (pull s Y) = pull s (inverted Y) := by
  funext a b x
  let u := inversion (Rₛ s x)
  have hR : R (Rₛ s x) = R x := by simp [R, Ortho.move_norm]
  have hu : Rₛ s (inversion x) = u := by rw [inversion,map_neg,map_smul]; dsimp only [u,inversion]; rw [hR]
  have he (b : Axis) : iota x (fun a b => pull s Y a b (inversion x)) b =
      Hyper.flip s b • iota (Rₛ s x) (fun a b => Y a b u) (s.perm b) := by
    rw [iota,iota,Finset.smul_sum]; refine Fintype.sum_equiv s.perm _ _ fun k => ?_
    rw [pull, moves_at]
    dsimp only; rw [smul_smul, smul_smul, hu]; congr 1; dsimp [sign₂]; ring
  have hh (a b : Axis) (v : F) : x a • Hyper.flip s b • v = sign₂ s a b • Rₛ s x (s.perm a) • v := by
    rw [moves_at, smul_smul, smul_smul]; congr 1
    unfold sign₂; calc
      _ = (Hyper.flip s a * Hyper.flip s a) * (x a * Hyper.flip s b) := by rw [flip_sq,one_mul]
      _ = _ := by ring
  conv_lhs => unfold inverted adjust
  dsimp only
  rw [he,he,pull,hu]
  conv_rhs => unfold pull inverted adjust
  rw [hh a b,hh b a,show sign₂ s b a = sign₂ s a b from mul_comm ..,← smul_sub,smul_comm (2 * R x),← smul_sub,smul_comm (R x ^ 2),hR]

def aspect (s : Signed) (p : Probe G j) := p.comp (turn s)
lemma asProbe_turn (s : Signed) (Y : Shell G j) : aspect s (asProbe Y) = asProbe (turn s⁻¹ Y) := by
  ext1 x
  exact (frob_turn (G := G) s (turns s⁻¹ Y.val) x.val) ▸ by rw [turn_inv]; rfl

lemma response_turn (s : Signed) (Y : Shell G j) {x} (hx : x ≠ 0) : turns s (nth (responded G (frob Y.val)) l (Rₛ s x)) =
    nth (responded G (frob (turn s Y).val)) l x := by
  let F := responded G (frob Y.val)
  let F' := responded G (frob (turn s Y).val)
  change turns s (nth F l _) = nth F' l x
  rw [← coeff_pull s F (fun a b => (response (frob (G := G) Y.val)).smooth _ _ _ ((map_ne_zero_iff _ (Rₛ s).injective).mpr hx))]
  funext a b
  apply GermCoeff
  filter_upwards [open_away.mem_nhds hx] with x hx
  have hw : Rₛ s x ∈ away := (map_ne_zero_iff _ (Rₛ s).injective).mpr hx
  change sign₂ s a b • F (s.perm a) (s.perm b) (Rₛ s x) = F' a b x
  rw [show F _ _ (Rₛ s x) = _ from response_eq Y (s.perm a) (s.perm b) hw,smul_comm,
    show F' a b x = _ from response_eq (turn s Y) a b hx]; congr 1
  exact congr_fun (congr_fun (congr_fun ((diag_turns s Y.val) ▸ pull_inverted s (actual Y.val)).symm a) b) x

theorem leg_invariant (s : Signed) (p : Probe G j) (q : Probe G l) {x : E4} (h : x ≠ 0) :
    legKernel (aspect s p) (aspect s q) (Rₛ s x) = legKernel p q x := by
  obtain ⟨Y,rfl⟩ := fullPair.2 p; obtain ⟨Z,rfl⟩ := fullPair.2 q
  change legKernel (aspect s (asProbe Y)) (aspect s (asProbe Z)) _ = legKernel (asProbe _) (asProbe _) _
  rw [asProbe_turn,asProbe_turn]; unfold asProbe
  rw [concrete _ _ ((map_ne_zero_iff _ (Rₛ s).injective).mpr h),concrete _ _ h,contraction,contraction]; congr 1
  have he : Rₛ s⁻¹ (Rₛ s x) = x := by change s⁻¹.ortho.move _ = _; rw [show s⁻¹.ortho = s.ortho⁻¹ from map_inv Signed.inclusionO s]; exact Ortho.inv_move s.ortho x
  have ht := response_turn (l := l) s⁻¹ Y ((map_ne_zero_iff _ (Rₛ s).injective).mpr h); rw [he] at ht
  rw [← ht]; exact frob_turn ..
end YM.Push.FiniteDetection.Free.Hyper
