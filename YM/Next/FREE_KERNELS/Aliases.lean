import Mathlib.Analysis.Normed.Group.Tannery
import YM.CellFourier.Alias
import YM.Next.FREE_KERNELS.Glue

/-!
# Odd dilation arithmetic

Residue axes centered, composing *aliases* without any folding assumptions.
Physical operators may live on tori of even side; only dilation and the
cumulative factors in the centered-alias claims are odd.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

variable {L M : Side}

lemma lift_inj {L : Side} : Function.Injective (@lift L) := by
  intro a b h; simpa using congrArg (wrap L) h

@[simp] lemma lift_origin (L : Side) : lift (0 : Site L)=0 := by funext i; simp [lift]

lemma mul_side_real (L M : Side) : ((L*M).val:ℝ)=(L.val:ℝ)*(M.val:ℝ) := by push_cast; rfl
lemma mul_side_complex (L M : Side) : ((L*M).val:ℂ)=(L.val:ℂ)*(M.val:ℂ) := by push_cast; rfl

lemma abs_nat (z : ℤ) : |(z:ℝ)|=(z.natAbs:ℝ) := by
  rw [← Int.cast_natCast (R:=ℝ), Int.natCast_natAbs, Int.cast_abs]

lemma centers_odd (l : Site L) (ho : Odd L.val) (i : Axis) :
    -(L.val:ℤ)+1 ≤ 2*lift l i ∧ 2*lift l i ≤ L.val-1 := by
  obtain ⟨h1,h2⟩ := lift_centers l i
  obtain ⟨v,hv⟩ := ho
  omega

lemma abs_odd (l : Site L) (ho : Odd L.val) (i : Axis) :
    2*|(lift l i:ℝ)| ≤ L.val-1 := by
  obtain ⟨h1,h2⟩ := centers_odd l ho i
  have h3 : -(L.val:ℝ)+1 ≤ 2*(lift l i:ℝ) := by exact_mod_cast h1
  have h4 : 2*(lift l i:ℝ) ≤ L.val-1 := by exact_mod_cast h2
  grind

lemma lift_negate (l : Site L) (ho : Odd L.val) : lift (-l)=-lift l := by
  refine lift_eq_iff.mpr ⟨by simp, fun i => ?_⟩
  obtain ⟨h1,h2⟩ := centers_odd l ho i
  simp only [Pi.neg_apply]; omega

lemma alias_value (p : Momentum) (l : Site L) (i : Axis) :
    aliasAt p l i = (p i+2*(Real.pi:ℂ)*(lift l i))/(L.val:ℂ) := by
  simp only [aliasAt, mon,Pi.add_apply, Pi.smul_apply,smul_eq_mul,reciprocal]
  ring

lemma alias_re (p : Momentum) (l : Site L) (i : Axis) :
    (L.val:ℝ)*(aliasAt p l i).re = (p i).re+2*Real.pi*(lift l i) := by
  have he := congr_arg (fun q : Momentum => (q i).re) (alias_scale p l)
  rw [← Nat.cast_smul_eq_nsmul ℂ] at he
  simpa [reciprocal] using he

lemma alias_im (p : Momentum) (l : Site L) (i : Axis) :
    (L.val:ℝ)*(aliasAt p l i).im=(p i).im := by
  have he := congr_arg (fun q : Momentum => (q i).im) (alias_scale p l)
  rw [← Nat.cast_smul_eq_nsmul ℂ] at he
  simpa using he

lemma alias_reverse (p : Momentum) (ho : Odd L.val) (l : Site L) :
    aliasAt (-p) (-l) = -aliasAt p l := by
  ext i; simp [alias_value,lift_negate l ho]; ring

lemma alias_real {p : Momentum} (hp : physical p) (l : Site L) : physical (aliasAt p l) :=
  (alias_conj p l).symm.trans (congr_arg (aliasAt · l) hp)

lemma alias_in_cube_precise {p : Momentum} {η : ℝ} (hp : p ∈ cube η) (l : Site L) (ho : Odd L.val) :
    aliasAt p l ∈ cube (η/L.val) := by
  have hL := side_pos L
  constructor
  · intro i
    rw [lt_div_iff₀ hL,mul_comm, ← abs_of_pos hL, ← abs_mul,alias_im]
    exact hp.1 i
  intro i
  have hm := hp.2 i
  have hb := abs_odd l ho i
  have hπ := Real.pi_pos
  rw [← mul_lt_mul_iff_right₀ hL, mul_add, mul_div_cancel₀ η hL.ne']
  calc
    (L.val:ℝ)*|(aliasAt p l i).re| = |(p i).re+2*Real.pi*(lift l i:ℝ)| := by rw [← alias_re,abs_mul, abs_of_pos hL]
    _ ≤ |(p i).re|+2*Real.pi*|(lift l i:ℝ)| := by
      refine (abs_add_le ..).trans ?_
      rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    _ < _ := by nlinarith

lemma alias_in_cube {p : Momentum} {η : ℝ} (hη : 0<η) (hp : p ∈ cube η) (l : Site L) (ho : Odd L.val) :
    aliasAt p l ∈ cube η :=
  cube_mono (div_le_self hη.le (by exact_mod_cast L.property)) (alias_in_cube_precise hp l ho)

lemma alias_in_real {p : Momentum} {η : ℝ} (hη : 0<η) (hp : p ∈ realCube η) (l : Site L) (ho : Odd L.val) :
    aliasAt p l ∈ realCube η :=
  ⟨alias_real hp.1 _, (alias_in_cube hη (mem_cube_real hp hη) l ho).2⟩

lemma alias_base {p : Momentum} (hp : p ∈ baseCube) (l : Site L) (ho : Odd L.val) :
    aliasAt p l ∈ baseCube := by
  refine ⟨alias_real hp.1 _,fun i => le_of_forall_pos_le_add fun ε hε => ?_⟩
  exact (alias_in_real hε (base_subset_realCube hε hp) l ho).2 i |>.le

/-- Mixed radices with both intervals centered. -/
def jointAlias (L M : Side) (l : Site L) (r : Site M) := wrap (L*M) (lift l+L.val • lift r)

lemma joint_lift (ho : Odd L.val) (ho' : Odd M.val) (l : Site L) (r : Site M) :
    lift (jointAlias L M l r)=lift l+L.val • lift r := by
  refine lift_eq_iff.mpr ⟨rfl, fun i => ?_⟩
  obtain ⟨h1,h2⟩ := centers_odd l ho i
  obtain ⟨h3,h4⟩ := centers_odd r ho' i
  have he : (0:ℤ)<L.val := by exact_mod_cast L.property
  simp only [Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply, PNat.mul_coe, Nat.cast_mul]; constructor <;> nlinarith

lemma joint_heads (x : Cover) : wrap L (L.val • x)=0 := by
  funext i
  simp [wrap,nsmul_eq_mul]

def radices (ho : Odd L.val) (ho' : Odd M.val) : (Site L × Site M) ≃ Site (L*M) :=
    Equiv.ofBijective (Function.uncurry (jointAlias L M))
      ((Fintype.bijective_iff_injective_and_card _).mpr (by
        refine ⟨?_,by rw [Fintype.card_prod, site_card, site_card, site_card, PNat.mul_coe, mul_pow]⟩
        rintro ⟨l,r⟩ ⟨l',r'⟩ h
        have he := congr_arg lift h
        simp only [uncurry_apply_pair, joint_lift ho ho'] at he
        have hl := congr_arg (wrap L) he
        simp only [map_add,wrap_lift,joint_heads,add_zero] at hl
        subst l'
        congr 1
        apply lift_inj
        ext i
        have hh := congr_fun (add_left_cancel he) i
        simp only [nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply] at hh
        have hm : (L.val:ℤ) ≠ 0 := by exact_mod_cast L.property.ne'
        exact mul_left_cancel₀ hm hh))

lemma alias_refine (ho : Odd L.val) (ho' : Odd M.val) (p : Momentum) (l : Site L) (r : Site M) :
    aliasAt (aliasAt p l) r=aliasAt p (radices ho ho' (l,r)) := by
  ext i
  simp only [alias_value]
  change _ = (p i+2*(Real.pi:ℂ)*(lift (jointAlias L M l r) i))/((L*M).val:ℂ)
  rw [joint_lift ho ho', mul_side_complex]
  simp only [Pi.add_apply,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  have hL := side_ne L
  have hM := side_ne M
  field_simp; ring

/-- Aliases permute up to fine reciprocal shifts when moving between coarse cubes. -/
lemma alias_exchange (p : Momentum) (l : Site L) (x : Cover) : ∃ y : Cover,
    aliasAt (p+reciprocal x) l=aliasAt p (l+wrap L x)+reciprocal y := by
  obtain ⟨z,hz⟩ := cover_of_eq (n:=L) (lift (l+wrap L x)) (lift l+x) (by simp)
  refine ⟨z,?_⟩
  ext i
  have hh := congr_fun hz i
  simp only [Pi.add_apply, nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply] at hh
  have he : (lift l i:ℂ)+(x i)=(lift (l+wrap L x) i:ℂ)+(L.val:ℂ)*(z i) := by exact_mod_cast hh
  simp only [alias_value, Pi.add_apply,reciprocal]
  have hL := side_ne L
  field_simp
  linear_combination 2*(Real.pi:ℂ)*he

lemma Moderate.on_alias {ι : Type*} {w : ι → ℝ} {f : ι → Momentum → ℂ} (h : Moderate w f)
    (L : ι → Side) (ho : ∀ i, Odd (L i).val) (l : ∀ i, Site (L i)) :
    Moderate w fun i p => f i (aliasAt p (l i)) := by
  obtain ⟨η,C,hp,hb,hh⟩ := h
  refine ⟨η,C,hp,hb,fun i => ⟨fun p hx => ?_,fun p hx => (hh i).bound _ (alias_in_cube hp hx _ (ho i))⟩⟩
  exact ((hh i).hol _ (alias_in_cube hp hx _ (ho i))).comp p (by unfold aliasAt; fun_prop)
end YM.Next.Free
