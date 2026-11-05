import YM.Push.FINITE_DETECTION.Leading
import YM.Push.FINITE_DETECTION.Reflection


/-!
# The change of probe triangular by Taylor order

Centered after inversion. In particular the order-j probe with its added
lower Taylor orders tests zero against all reflected probes of smaller
order at the pole. Its own pivot is `gain j` times the Euclidean tensor
metric on **actual Shell**. No assertion that the raw field can itself be
centered by this transformation at cutoffs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection.Kelvin
open Maxwell WaveOn Tensor Analysis Function Filter Set
open scoped Topology BigOperators ContDiff
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Gauge} {j l : ℕ}

lemma R_pole : R pole = 1 := by simp [R,pole]
def place (x : E4) := pole + inversion x
lemma place_pole : place pole = 0 := by simp [place,inversion,R_pole]
lemma place_smooth : smoothAt place pole := contDiffAt_const.add (((R_smooth pole_in).smul contDiffAt_id).neg)
lemma place_axis (i : Axis) : grad i place pole = -flipE (basis i) := by
  change fderiv ℝ (fun x => pole + inversion x) pole (basis i) = _
  rw [fderiv_const_add,show inversion = -(fun x : E4 => R x • x) from rfl,fderiv_neg]
  have he := fderiv_fun_smul (f := id) ((R_smooth pole_in).differentiableAt (by simp)) (differentiableAt_id : DifferentiableAt ℝ id pole)
  ext k
  change -((fderiv ℝ (fun x : E4 => R x • id x) pole) (basis i)) k = -flipE (basis i) k
  rw [he,add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,R_pole,one_smul, fderiv_id,
    show (fderiv ℝ R pole) (basis i) = _ from R_deriv pole_in i]
  rw [R_pole]
  simp [basis_eq,pole]; split_ifs <;> simp_all; norm_num

lemma place_deriv (x) : fderiv ℝ place pole x = -flipE x := by
  rw [← space_expand x]
  simp_rw [map_sum, map_smul,show ∀ i : Axis, (fderiv ℝ place pole) (basis i) = -flipE (basis i) from place_axis,smul_neg,Finset.sum_neg_distrib]

def centerField (Y : TwoJet F j) : Maxwell.Field F := inverted fun a b x => actual Y a b (pole + x)

def adjustCost (a k : Axis) (y : E4) : ℝ := 2 * R y ^ 3 * y k * y a
lemma adjustCost_smooth (a k : Axis) : smoothAt (adjustCost a k) pole := by
  exact ((contDiffAt_const.mul ((R_smooth pole_in).pow _)).mul (compAxis k).contDiff.contDiffAt).mul (compAxis a).contDiff.contDiffAt

lemma center_expand (Y : TwoJet F j) (k m : Axis) : centerField Y k m =
    dressed (Y k m) (fun y => R y ^ 2) place - ((∑ i : Axis, dressed (Y i m) (adjustCost i k) place) -
      ∑ i : Axis, dressed (Y i k) (adjustCost i m) place) := by
  funext y
  have he (k m : Axis) : R y ^ 2 • (2*R y) • y k • iota y (fun a b => actual Y a b (place y)) m =
      ∑ i : Axis, dressed (Y i m) (adjustCost i k) place y := by
    simp only [iota,Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl; intro a _; change _ = adjustCost _ _ _ • _
    unfold adjustCost; congr 1; ring
  simp only [centerField, inverted, adjust,show pole + inversion y = place y from rfl,Pi.sub_apply,Finset.sum_apply,smul_sub]; rw [he,he]; rfl
lemma coeff_center (Y : TwoJet F j) (k m : Axis) :
    nth (centerField Y) l pole k m = coeff (dressed (Y k m) (fun y => R y ^ 2) place) l pole -
      ((∑ i : Axis, coeff (dressed (Y i m) (adjustCost i k) place) l pole) -
        ∑ i : Axis, coeff (dressed (Y i k) (adjustCost i m) place) l pole) := by
  let f (k m i : Axis) := dressed (Y i m) (adjustCost i k) place
  have he k m i : smoothAt (f k m i) pole := dressed_smooth _ (adjustCost_smooth _ _) place_smooth
  have ht k m : smoothAt (∑ i : Axis, f k m i) pole := by rw [Finset.sum_fn]; exact ContDiffAt.sum fun _ _ => he _ _ _
  have hc {a b : E4 → F} (ha : smoothAt a pole) (hb : smoothAt b pole) :
      coeff (a-b) l pole = coeff a l pole - coeff b l pole := by
    rw [sub_eq_add_neg, sub_eq_add_neg, coeff_add (g := -b) (ha.of_le (allOrders _)) (hb.neg.of_le (allOrders _)), neg_coeff]
  rw [nth,center_expand,hc (dressed_smooth _ ((R_smooth pole_in).pow _) place_smooth)
    (show smoothAt ((∑ i : Axis, f k m i) - ∑ i : Axis, f m k i) pole from (ht k m).sub (ht m k)), hc (ht k m) (ht m k),
    coeff_sum _ _ _ _ (fun i _ => ((he k m i)).of_le (allOrders _)), coeff_sum _ _ _ _ (fun i _ => ((he m k i)).of_le (allOrders _))]

lemma center_lower (Y : Shell G j) (hl : l < j) : nth (centerField Y.val) l pole = 0 := by
  have he (s) (hs : smoothAt s pole) a b := lower_term _ (Y.property.1.coeffSym a b) hs place_smooth place_pole hl
  funext k m
  simp only [coeff_center,he _ ((R_smooth pole_in).pow _),he _ (adjustCost_smooth _ _),Finset.sum_const_zero,sub_self,Pi.zero_apply]

lemma center_diag_term (Y : Shell G j) (k m : Axis) (v : Fin j → E4) (s : E4 → ℝ) (hs : smoothAt s pole) :
    coeff (dressed (Y.val k m) s place) j pole v = (-1 : ℝ)^j • s pole • Y.val k m (flipE ∘ v) := by
  rw [head_term _ (Y.property.1.coeffSym k m) hs place_smooth place_pole, show fderiv ℝ place pole ∘ v = fun i => (-1:ℝ) • (flipE ∘ v) i by
    ext1 i; exact (place_deriv _).trans (neg_one_smul ℝ _).symm,
    ContinuousMultilinearMap.map_smul_univ]; rw [smul_comm (s pole)]; simp
lemma center_diag (Y : Shell G j) : nth (centerField Y.val) j pole = (-1 : ℝ)^j • reflectedJet Y.val := by
  funext k m; ext1 u
  let f (k m) := Y.val k m (flipE ∘ u)
  have he (k m) : (∑ i : Axis, coeff (dressed (Y.val i m) (adjustCost i k) place) j pole u) =
      (-1 : ℝ)^j • if k=timeAxis then (2:ℝ) • f timeAxis m else 0 := by
    simp_rw [center_diag_term _ _ _ _ _ (adjustCost_smooth _ _), ← Finset.smul_sum]
    dsimp [adjustCost]; simp [R,pole]; split <;> simp_all [f]
  have hz a : f a a = 0 := by
    have hv : f a a = - f a a := congr_arg (fun x : T E4 G.Color j => x (flipE ∘ u)) (Y.property.1.antisymmetric a a)
    have hm : (2:ℝ) • f a a = 0 := by rw [two_smul]; nth_rw 1 [hv]; simp
    exact (smul_eq_zero.mp hm).resolve_left (by norm_num)
  simp only [coeff_center, sub_apply, sum_apply, he,center_diag_term Y k m u _ ((R_smooth pole_in).pow 2),R_pole,one_pow,one_smul,
    Pi.smul_apply, smul_apply,apply_jet,← smul_sub]
  congr 1
  change f k m - _ = pairSign k m • f k m
  simp only [pairSign, sign]; split_ifs with h h'
  · subst k; subst m; rw [hz]; simp
  · subst k; rw [two_smul]; simp
  · subst m
    have he : f k timeAxis = - f timeAxis k := congr_arg (fun x : T E4 G.Color j => x (flipE ∘ u)) (Y.property.1.antisymmetric k timeAxis)
    rw [he, two_smul]; simp
  simp

/-! ### Modified probes -/
def translated (Y : Shell G j) (i : ℕ) : Shell G i := ⟨nth (actual Y.val) i pole,(wave_actual Y.property).jets isOpen_univ trivial⟩
lemma translated_self (Y : Shell G j) : translated Y j = Y :=
  Subtype.ext <| funext fun k => funext fun m => diag_response _ (Y.property.1.coeffSym k m) _

lemma center_decompose (Y : Shell G j) : centerField Y.val = ∑ i ∈ Finset.range (j+1), inverted (actual (translated Y i).val) := by
  funext k m x
  let Z (i : ℕ) a b := actual (translated Y i).val a b (inversion x)
  have he a b : actual Y.val a b (pole + inversion x) = ∑ i ∈ Finset.range (j+1), Z i a b :=
    diag_translate _ (Y.property.1.coeffSym a b) _ _
  simp only [centerField,inverted,adjust,iota, he,smul_sub,Finset.sum_apply,Finset.sum_sub_distrib,Finset.smul_sum]
  congr 1
  dsimp only [Z]
  rw [Finset.sum_comm (s := (Finset.univ : Finset Axis)),Finset.sum_comm (s := (Finset.univ : Finset Axis))]

def ratio (j i : ℕ) := gain j / gain i
@[simp] lemma ratio_mul_gain (j i : ℕ) : ratio j i * gain i = gain j := div_mul_cancel₀ _ gain_pos.ne'

lemma sum_modified (Y : Shell G j) : (∑ i ∈ Finset.range (j+1), ratio j i • nth (responded G (frob (translated Y i).val)) l pole) =
    gain j • nth (centerField Y.val) l pole := by
  funext k m; simp only [Finset.sum_apply,Pi.smul_apply,nth]
  let f (i) := responded G (frob (translated Y i).val) k m
  have hf (i) := response (frob (translated Y i).val) |>.smooth k m pole pole_in
  change ∑ i ∈ Finset.range (j+1), ratio j i • coeff (f i) l pole = _
  simp_rw [← coeff_smul _ (show ContDiffAt ℝ l (f _) pole from (hf _).of_le (allOrders _))]
  have hp : (∑ i ∈ Finset.range (j+1), ratio j i • f i) =ᶠ[𝓝 pole] gain j • centerField Y.val k m := by
    filter_upwards [open_away.mem_nhds pole_in] with x hx
    simp [center_decompose Y, f,response_eq _ k m hx,smul_smul, Finset.smul_sum]
  have he : smoothAt (centerField Y.val k m) pole := by
    rw [center_expand]; apply ContDiffAt.sub (dressed_smooth _ ((R_smooth pole_in).pow _) place_smooth)
    simp_rw [Finset.sum_fn]; exact ContDiffAt.sub (ContDiffAt.sum (fun i _ => dressed_smooth _ (adjustCost_smooth _ _) place_smooth))
      (ContDiffAt.sum (fun i _ => dressed_smooth _ (adjustCost_smooth _ _) place_smooth))
  rw [← coeff_sum _ _ _ _ (fun i _ => (show ContDiffAt ℝ ∞ (ratio j i • f i) pole from (hf i).const_smul (ratio j i)).of_le (allOrders _)),
    GermCoeff _ hp, coeff_smul _ (he.of_le (allOrders _))]

def column (Y : Shell G j) (i : ℕ) := ratio j i • asProbe (translated Y i)
@[simp] lemma column_self (Y : Shell G j) : column Y j = asProbe Y := by simp [column,ratio, gain_pos.ne',translated_self]

def against (Y : Shell G j) (q : Probe G l) := ∑ i ∈ Finset.range (j+1), form (column Y i) q
lemma column_factor (Y : Shell G j) (Z : Shell G l) i s : form (column Y i) (column Z s) =
    ratio j i * ratio l s * form (asProbe (translated Y i)) (asProbe (translated Z s)) := by
  rw [form,column,column,form,map_smul]
  change ratio j i * pairing pole_in (asProbe _) (ratio l s • (asProbe (translated Z s)).comp mirrorJet) = _
  rw [map_smul, smul_eq_mul, mul_assoc]
lemma against_formula (Y : Shell G j) (Z : Shell G l) :
    against Y (asProbe Z) = (-1)^l * gain j * frob (mirrorJet Z).val (nth (centerField Y.val) l pole) := by
  unfold against
  have he i : form (column Y i) (asProbe Z) = (-1)^l * frob (mirrorJet Z).val
      (ratio j i • nth (responded G (frob (translated Y i).val)) l pole) := by
    rw [form,column,map_smul,← toProbe_reflected,map_smul]
    change ratio j i * legKernel (asProbe _) (asProbe _) _ = _
    rw [asProbe,asProbe,concrete _ _ pole_in,contraction]; change _ = (-1)^l * (ratio j i * _); ring
  simp_rw [he,← Finset.mul_sum,← map_sum,sum_modified Y,map_smul,smul_eq_mul,mul_assoc]
lemma against_lower (Y : Shell G j) (Z : Shell G l) (hl : l < j) : against Y (asProbe Z) = 0 := by
  rw [against_formula,center_lower Y hl,map_zero]; simp
lemma against_self (Y Z : Shell G j) : against Y (asProbe Z) = gain j * frob Z.val Y.val := by
  rw [against_formula,center_diag, map_smul,smul_eq_mul]
  rw [show frob (G := G) (mirrorJet Z).val (reflectedJet Y.val) = _ from frob_reflected Z.val (reflectedJet Y.val), reflected_twice]
  have h : ((-1 : ℝ)^j) * (-1)^j = 1 := by rw [← mul_pow]; simp
  rw [show ∀ x : ℝ, (-1 : ℝ)^j * gain j * ((-1)^j * x) = gain j * (((-1 : ℝ)^j) * (-1)^j * x) by intros; ring, h,one_mul]

def pairCol (Y : Shell G j) (Z : Shell G l) :=
  ∑ i ∈ Finset.range (j+1), ∑ s ∈ Finset.range (l+1), form (column Y i) (column Z s)
lemma pairCol_symmetric (Y : Shell G j) (Z : Shell G l) : pairCol Y Z = pairCol Z Y := by
  unfold pairCol; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro i _
  rw [column_factor,column_factor,reflection_form, mul_comm (ratio j i)]
lemma pairCol_reduce (Y : Shell G j) (Z : Shell G l) : pairCol Y Z = ∑ s ∈ Finset.range (l+1), ratio l s * against Y (asProbe (translated Z s)) := by
  unfold pairCol against; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro s _; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  unfold form; rw [column]
  -- right hand column only
  change pairing pole_in (column Y i) (ratio l s • (asProbe (translated Z s)).comp mirrorJet) = _
  rw [map_smul]; rfl
lemma pairCol_diag (Y Z : Shell G j) : pairCol Y Z = gain j * frob Z.val Y.val := by
  rw [pairCol_reduce,Finset.sum_range_succ,translated_self,against_self,
    Finset.sum_eq_zero (fun i hi => by rw [against_lower _ _ (Finset.mem_range.mp hi),mul_zero])]; simp [ratio,gain_pos.ne']
lemma pairCol_lower (Y : Shell G j) (Z : Shell G l) (hl : l<j) : pairCol Y Z = 0 := by
  rw [pairCol_reduce]
  exact Finset.sum_eq_zero fun i hi => by rw [against_lower _ _ (lt_of_lt_of_le (Finset.mem_range.mp hi) hl),mul_zero]
lemma pairCol_distinct (Y : Shell G j) (Z : Shell G l) (hne : j≠l) : pairCol Y Z = 0 := by
  rcases lt_or_gt_of_ne hne with h|h
  · rw [pairCol_symmetric]; exact pairCol_lower Z Y h
  exact pairCol_lower Y Z h
end YM.Push.FiniteDetection.Kelvin
