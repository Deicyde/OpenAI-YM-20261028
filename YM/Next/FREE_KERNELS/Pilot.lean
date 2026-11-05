import YM.Next.FREE_KERNELS.Portions

/-!
# Analytic stationary column formula

`pilot` is with factor L (constants before L). Fill `gains` BEFORE Laurent
coefficient extraction. Do not treat `pipe` as itself analytic.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

lemma mask1_scale (x : Axis → ℂ) (c : ℂ) : mask 1 (fun i => c*x i)=c • mask 1 x := by rw [mask_scale,pow_one]
lemma mask1_bill (c : ℂ) (f : Axis → ℂ) : c • (1:Frequency 1 1)-mask 1 f=mask 1 (fun i => c-f i) := by
  ext a b; simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mask_value]; split <;> ring

variable {j t : ℕ}

namespace Flight

def priorG (k : ℝ) (P : Flight j t) (p : Momentum) := mask 1 fun a => (P.land.bulb k p a)⁻¹

def sluice (k : ℝ) (P : Flight j t) (p : Momentum) :=
    (P.land.bend k p)⁻¹ • (mirage 1 0 p*priorG k P p)

def ahead (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) := if l=0 then
    (mask 1 (P.wing.bulb k (toe P p))*flux P 1 (toe P p)*priorG k P p)
  else span P p • (mask 1 (portD k P p l)*flux P 1 (aliasAt p l)*priorG k P p)

def rebates (k : ℝ) (P : Flight j t) (p q : Momentum) (i : Axis) :=
    massFilter P.patch (-q)*scaleD P.L k P.wing q i*yen (fun x => rail P.L (x i)) q / scaleD 1 k P.land p i

def fled (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) (i : Axis) :=
    let q := aliasAt p l
    massFilter P.patch (-q)*((∑ i, portD k P p l i)/abide k P p -
      portD k P p l i*yen (fun x => rail P.L (x i)) q / P.land.bulb k p i)

def rests (k : ℝ) (P : Flight j t) (p : Momentum) (i : Axis) :=
    (massFilter P.patch (toe P p))⁻¹*(tailings k P p i/P.land.bulb k p i-hills k P p/abide k P p)

def gains (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) := if l=0 then rests k P p else fled k P p l

def pilot (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) := ahead k P p l +
    mask 1 (gains k P p l) * signal P.L 0 (aliasAt p l)*sluice k P p

section matching
variable (k : ℝ) (hk : 0 < k) (P : Flight j t) {p : Momentum} (hp : p∈realCube zone) (he : p≠0) (l : Site P.L)
include hp he

lemma converge_field : fieldI 1 k P.land p=P.span p • priorG k P p := by
  have hh i : (scaleD 1 k P.land p i)⁻¹=P.span p*(P.land.bulb k p i)⁻¹ := by rw [scaleD_one,Train.D_bulb k _ hp he,inv_div,div_eq_mul_inv]; rfl
  unfold fieldI priorG; simp_rw [hh]; rw [mask1_scale]

include hk in
lemma converge_pipe : pipe 1 k P.land p=(P.span p)⁻¹ • sluice k P p := by
  unfold pipe sluice; rw [P.converge_field k hp he,Matrix.mul_smul,smul_smul,smul_smul]
  congr 1
  unfold scaleR span
  rw [Train.recover_rho k hk _ hp he]
  simp only [(by simp : (((1:Side).val):ℂ)=1),one_pow,one_mul, _root_.mul_inv_rev]
  have hm := divisor_ne P.land.mass hp he; ring_nf
  field_simp

lemma ahead_match : ahead k P p l=fieldD P.L k P.wing (aliasAt p l)*flux P 1 (aliasAt p l)*fieldI 1 k P.land p := by
  rw [P.converge_field k hp he]; unfold ahead fieldD; split
  · next hh =>
      subst l
      have heq (a) : scaleD P.L k P.wing (toe P p) a=(P.span p)⁻¹*P.wing.bulb k (toe P p) a := by
        unfold toe; rw [← portD_match k P hp _ (Or.inr he) a,portD, span_root]; ring
      have ht : scaleD P.L k P.wing (aliasAt p (0: Site P.L))=fun a => (P.span p)⁻¹*P.wing.bulb k (toe P p) a := funext heq
      rw [ht,mask1_scale,Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul, mul_inv_cancel₀ (show P.span p≠0 from divisor_ne _ hp he),one_smul]
  have hu : portD k P p l = scaleD P.L k P.wing (aliasAt p l) := funext (portD_match k P hp l (Or.inr he))
  rw [hu,Matrix.mul_smul]

include hk in
lemma gains_match (i : Axis) : weightsE k P p (aliasAt p l)-rebates k P p (aliasAt p l) i=
    span P p*gains k P p l i := by
  let S := P.span p; have hS : S≠0 := divisor_ne _ hp he
  let a := P.tabE k p; let b := P.abide k p
  have ha : a≠0 := tabE_puncture k hk P hp he
  have hb : b=S*a := P.record_abide k hp he
  have hb' : b ≠ 0 := hb ▸ mul_ne_zero hS ha
  let g := P.land.bulb k p
  have hg i : g i≠0 := Train.bulb_glows _ hk _ hp _
  have he' i : scaleD 1 k P.land p i=g i/S := by rw [scaleD_one,Train.D_bulb k _ hp he]; rfl
  by_cases hl : l=0
  · subst l; let q := toe P p
    let y := massFilter P.patch q; let z := massFilter P.patch (-q)
    have hy : y≠0 := mass_filter_live _ hp
    let h := hills k P p
    let R := tailings k P p i
    let H := P.wing.bulb k q i
    have hh (a) : scaleD P.L k P.wing q a=P.wing.bulb k q a/S := Eq.trans (portD_match k P hp 0 (Or.inr he) a).symm (by unfold portD; rw [span_root])
    have hf : y*z*fore k P p=b-S*h := by unfold b abide; unfold y z yen h q S; ring
    have hm : y*z*H*yen (fun x => rail P.L (x i)) q=g i-S*R := by
      unfold g; rw [bulb_network k P hp he]; unfold y z H heel yen pullLine q S R; ring!
    have ht : total k P q=fore k P p/S := by unfold total fore; simp_rw [hh, Finset.sum_div]; rfl
    have hj : weightsE k P p q=(b-S*h)/(S*y*a) := by
      unfold weightsE; rw [ht, ← hf];
      change z*_/a=_; field_simp
    have hrr : rebates k P p q i=(g i-S*R)/(y*g i) := by
      unfold rebates; rw [hh, he', ← hm]
      change z*(H/S)*_/(g i/S)=_
      field_simp
    unfold gains; rw [if_pos rfl,hj,hrr];
    change (b-S*h)/_-(g i-S*R)/_=S*(y⁻¹*(R/g i-h/b))
    rw [hb]; have hh := hg i; field_simp; ring
  unfold gains; rw [if_neg hl]
  have hy (a : Axis) : portD k P p l a=scaleD P.L k P.wing (aliasAt p l) a := portD_match k P hp l (Or.inr he) a
  unfold weightsE rebates fled
  simp_rw [hy]; rw [he' i];
  let q := aliasAt p l
  let z := massFilter P.patch (-q); let t := total k P q
  let h := scaleD P.L k P.wing q i; let v := yen (fun x => rail P.L (x i)) q
  change z*t/a-z*h*v/(g i/S)=S*(z*(t/b-h*v/g i))
  rw [hb]; have hm := hg i; field_simp

omit hp he in
lemma mon_rebate (p : Momentum) :
    let q := aliasAt p l
    fieldD P.L k P.wing q * flux P 1 q * fieldI 1 k P.land p * signal 1 0 p=
      mask 1 (rebates k P p q)*signal P.L 0 q := by
  intro q
  have he : signal 1 0 p=mask 1 (fun i => rail P.L (q i))*signal P.L 0 q := by
    unfold signal
    rw [mask_insert,mask_nil,Matrix.mul_one]
    unfold q; simp_rw [hinges_rule]
  rw [he,← Matrix.mul_assoc]; unfold fieldD flux fieldI hinges rebates
  rw [Matrix.transpose_smul,mask_trans,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,mask_mul,mask_mul,mask_mul,← mask1_scale]
  congr 2; funext i; unfold yen; ring
include hk in
lemma pilot_match : pilot k P p l=scriptA k P p (aliasAt p l) := by
  let q := aliasAt p l
  let B := ahead k P p l
  let r := fieldI 1 k P.land p
  let x := signal 1 0 p
  let b := signal P.L 0 q
  let pp := pipe 1 k P.land p
  let f := fieldD P.L k P.wing q*flux P 1 q
  let E := weightsE k P p q
  have hs : f*r=B := (ahead_match k P hp he l).symm
  have hh : B*x=mask 1 (rebates k P p q)*b := by rw [← hs]; exact P.mon_rebate k l p
  have hm : scriptA k P p q=B+(E • (1 : Frequency 1 1)-mask 1 (rebates k P p q))*b*pp := by
    unfold scriptA; rw [rotor_split 1 k hk P.land hp he]
    change f*(r-r*x*pp)+E • (b*pp)=_
    simp only [Matrix.sub_mul,Matrix.mul_sub,← Matrix.mul_assoc,hs,hh,Matrix.smul_mul,Matrix.one_mul]; abel
  have hS : span P p≠0 := divisor_ne _ hp he
  rw [show scriptA k P p (aliasAt p l)=_ from hm,mask1_bill]
  rw [show (fun i => E - rebates k P p q i)=fun i => span P p*gains k P p l i from funext (gains_match k hk P hp he l)]
  rw [mask1_scale, show pp=_ from converge_pipe k hk P hp he, Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,smul_smul, inv_mul_cancel₀ hS,one_smul]; rfl
end matching
end Flight
end YM.Next.Free
