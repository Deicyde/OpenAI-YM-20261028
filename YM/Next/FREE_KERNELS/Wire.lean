import YM.Next.FREE_KERNELS.Pilot

/-!
# The dual column on 2-cochains

Normalization in `wire`: rescaled by L². `brace` removes the external
divisor in the PRINCIPAL alias; others only need the pole expression for Pi
times its Y multiplier.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

def twice (x : Axis → ℂ) : Frequency 2 2 := Matrix.diagonal fun a => ∑ i∈a.val,x i
lemma inventory_second (x : Axis → ℂ) (c : ℂ) (a : TypeFace 2) :
    inventory a (fun i => 1-c*x i)=1-c*(∑ i∈a.val,x i)+c^2*inventory a x := by
  obtain ⟨p,rfl⟩ := plaqEquiv.surjective a
  change inventory (plaquette p) _=1-c*(∑ i∈(plaquette p).val,x i)+c^2*inventory (plaquette p) x
  simp [inventory,plaquette,p.property.ne]; ring
lemma mask_second (x : Axis → ℂ) (c : ℂ) :
    1-mask 2 (fun i => 1-c*x i)=c • (twice x-c • mask 2 x) := by
  ext a b
  simp only [mask,twice,Matrix.one_apply,Matrix.diagonal_apply,Matrix.sub_apply, Matrix.smul_apply,smul_eq_mul]
  split <;> try rw [inventory_second]
  all_goals ring

lemma mask1_sub (x y : Axis → ℂ) : mask 1 (fun i => x i-y i)=mask 1 x-mask 1 y := by
  ext a b; rw [Matrix.sub_apply,mask_value,mask_value,mask_value]; split <;> simp

variable {j t : ℕ}

namespace Flight

def latch (P : Flight j t) (p : Momentum) (r : ℕ) :=
    (massFilter P.patch (P.toe p))⁻¹ • mask r (fun i => (rail P.L (P.toe p i))⁻¹)

def footY (k : ℝ) (P : Flight j t) (p : Momentum) :=
    yen (massFilter P.patch) (P.toe p) * P.land.bend k p / P.wing.bend k (P.toe p)

def brace (k : ℝ) (P : Flight j t) (p : Momentum) :=
    let x (i) := P.tailings k p i / P.land.bulb k p i
    pulse k P.wing (P.toe p)*(twice x-P.span p • mask 2 x)

def mouth (k : ℝ) (P : Flight j t) (p : Momentum) := mask 1 (P.land.bulb k p)

def copper (k : ℝ) (P : Flight j t) (p : Momentum) :=
    let s := P.latch p 2 * signal 1 1 p
    P.footY k p • flux P 2 (P.toe p) + (P.brace k p*s*P.mouth k p-pulse k P.wing (P.toe p)*s*mask 1 (P.tailings k p)) * mirage 1 1 p

def levy (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) :=
    yen (massFilter P.patch) (aliasAt p l)*P.land.bend k p / P.portR k p l

def notch (k : ℝ) (P : Flight j t) (p : Momentum) := P.span p ^ 2 • 1 -
    P.span p • (pulse k P.land p * signal 1 1 p * P.mouth k p * mirage 1 1 p)

def stake (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) :=
    let q := aliasAt p l
    pulse k P.wing q * signal P.L 1 q * mask 1 (P.portD k p l)* flux P 1 q * mirage 1 1 p +
    P.levy k p l • (flux P 2 q * P.notch k p)

def wire (k : ℝ) (P : Flight j t) (p : Momentum) (l : Site P.L) := if l=0 then copper k P p else stake k P p l

section matchingWire
variable (k : ℝ) (hk : 0<k) (P : Flight j t) {p : Momentum} (hp : p∈realCube zone) (he : p≠0)
include hp
lemma undo_hinges (r : ℕ) : hinges P r (toe P p)*latch P p r=1 ∧ latch P p r*hinges P r (toe P p)=1 := by
  have hM := mass_filter_live P hp
  have h (i : Axis) : rail P.L (toe P p i)≠0 := by
    unfold toe; rw [alias_zero_eq]; apply norm_pos_iff.mp; apply plankMin_pos.trans_le (rail_lower P.L _ _)
    rw [narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos _).ne']; exact zone_in_disk _ (mem_cube_real hp zone_pos) _
  obtain ⟨ha,hb⟩ := mask_undo r _ h
  unfold hinges latch; rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_smul];
  rw [ha,hb,smul_smul,smul_smul,inv_mul_cancel₀ (show massFilter P.patch (P.toe p)≠0 from hM),mul_inv_cancel₀ (show massFilter P.patch (P.toe p)≠0 from hM),one_smul]; exact ⟨rfl,rfl⟩

include he
lemma bank_mouth : mouth k P p=P.span p • fieldD 1 k P.land p := by
  have h i : scaleD 1 k P.land p i=P.land.bulb k p i/P.span p := by rw [scaleD_one,Train.D_bulb k _ hp he]; rfl
  unfold mouth fieldD; rw [← mask1_scale]; congr! 2 with a; rw [h,mul_div_cancel₀ _ (show P.span p≠0 from divisor_ne _ hp he)]

lemma notch_match : notch k P p=P.span p^2 • (1-cloud k P p) := by
  unfold notch cloud; rw [bank_mouth k P hp he]; simp only [Matrix.mul_smul,Matrix.smul_mul,smul_sub,pow_two,smul_smul]

lemma portion_field : hinges P 1 (toe P p)*fieldD P.L k P.wing (toe P p)*flux P 1 (toe P p)=
    fieldD 1 k P.land p-mask 1 (P.tailings k p) := by
  let S := P.span p
  let q := toe P p
  have hh i : scaleD P.L k P.wing q i=P.wing.bulb k q i/S := by
    rw [← portD_match k P hp _ (Or.inr he)]; unfold portD; rw [span_root]
  unfold hinges flux fieldD; simp only [hinges,transpose_smul,mask_trans, Matrix.smul_mul, Matrix.mul_smul,smul_smul]
  rw [mask_mul,mask_mul,← mask1_scale,← mask1_sub]; congr! 2 with i
  rw [hh,scaleD_one,toe_feed k P hp he i]; unfold heel pullLine yen S; ring!

include hk
lemma foot_is : footY k P p=P.chainY k p (toe P p) := by
  let S := span P p
  have hS : S≠0 := divisor_ne _ hp he
  have h := Train.recover_rho k hk P.land hp he
  change _ = S^2*_ at h
  unfold chainY
  rw [← portR_match k hk P hp 0 (Or.inr he), portR,span_root]
  unfold scaleR footY
  rw [h]; change _=_*(((↑((1:Side).val)):ℂ)^4*(S^2*_))/(S^2*_); simp; field_simp

lemma brace_match : span P p • brace k P p=pulse k P.wing (toe P p)-P.footY k p • (flux P 2 (toe P p)*pulse k P.land p*hinges P 2 (toe P p)) := by
  let q := toe P p
  let c := massFilter P.patch q
  let d := massFilter P.patch (-q)
  let f := P.land.bulb k p
  let g := P.wing.bulb k q
  let h := P.land.bend k p; let u := P.wing.bend k q
  have hg (i) : g i≠0 := Train.bulb_glows _ hk _ (toe_regular P hp) _
  have hu : h≠0 := Train.bend_live _ hk _ hp
  have hf (i) : f i≠0 := Train.bulb_glows _ hk _ hp _
  let a := pulse k P.wing q
  let E i := rail P.L (q i); let F i := rail P.L ((-q) i)
  let Z (i) := P.heel k p i / f i
  have hm : footY k P p • (flux P 2 q*pulse k P.land p*hinges P 2 q)=a*mask 2 Z := by
    have heq (i) : (g i)⁻¹ * Z i = c*d*(F i * (f i)⁻¹ * E i) := by
      unfold Z heel pullLine yen c d F f E g q at *; field_simp [hg i]; ring!
    unfold a pulse hinges flux
    simp only [hinges,transpose_smul,mask_trans,Matrix.smul_mul,Matrix.mul_smul,smul_smul,mask_mul]
    change (c*d*h/u*(c*(h⁻¹*d))) • mask 2 (fun i => F i*(f i)⁻¹*E i)=
      u⁻¹ • mask 2 (fun i => (g i)⁻¹*Z i)
    simp_rw [heq]; rw [mask_scale,smul_smul]; congr 1; field_simp
  change _ = a-_
  rw [hm,show a-a*mask 2 Z=a*(1-mask 2 Z) from by rw [mul_sub,mul_one]]
  let x i := tailings k P p i/f i
  have heq (i : Axis) : Z i=1-span P p*x i := by
    unfold Z x; have hm := bulb_network k P hp he i; have hi := hf i; change f i=_ at hm; field_simp; rw [hm]; ring
  rw [show Z=(fun i => 1-span P p*x i) from funext heq,mask_second,Matrix.mul_smul]; rfl

lemma stake_match (l : Site P.L) (hl : l≠0) : stake k P p l=P.scriptT k p (aliasAt p l) := by
  let q := aliasAt p l
  have heq : chainY k P p q=P.levy k p l*span P p^2 := by
    unfold chainY levy; rw [portR_match k hk P hp l (Or.inl hl)]
    unfold scaleR span; rw [Train.recover_rho k hk _ hp he]; unfold q; simp; ring
  unfold stake scriptT
  dsimp only
  rw [notch_match k P hp he, Matrix.mul_smul,smul_smul,heq, show P.portD k p l=scaleD P.L k P.wing q from funext (portD_match k P hp _ (Or.inl hl))]; rfl
lemma copper_match : copper k P p=P.scriptT k p (toe P p) := by
  let q := P.toe p
  let f₁ := hinges P 1 q
  let v := flux P 2 q
  let f₂ := hinges P 2 q
  let u := flux P 1 q
  let D := fieldD P.L k P.wing q
  let D' := fieldD 1 k P.land p
  let d := signal 1 1 p
  let δ := signal P.L 1 q
  let m := mirage 1 1 p
  let H := pulse k P.wing q
  let H' := pulse k P.land p
  let L := latch P p 2
  let y := footY k P p
  let s := P.span p
  let R := mask 1 (P.tailings k p)
  have hi : f₂*L=1 := (P.undo_hinges hp 2).1
  have hj : L*f₂=1 := (P.undo_hinges hp 2).2
  have ht : f₂*δ=d*f₁ := hinge_transport P 1 0 p
  have hD : f₁*D*u=D'-R := portion_field k P hp he
  have hb : s • brace k P p=H-y • (v*H'*f₂) := brace_match k hk P hp he
  have hh : δ=L*d*f₁ := by rw [Matrix.mul_assoc,← ht,← Matrix.mul_assoc,hj,Matrix.one_mul]
  have heq : H*δ*D*u*m=(H*(L*d)*(D'-R))*m := by rw [hh, ← hD]; simp only [Matrix.mul_assoc]
  have hv : brace k P p*(L*d)*P.mouth k p=
      H*(L*d)*D'-y • (v*H'*d*D') := by
    rw [bank_mouth k P hp he]
    change brace k P p * (L*d) *(s • D')=_; rw [Matrix.mul_smul,← Matrix.smul_mul, ← Matrix.smul_mul,hb]
    simp only [Matrix.sub_mul, Matrix.smul_mul];
    have hx : v*H'*f₂*(L*d)*D'=v*H'*d*D' := by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc f₂ L,hi,Matrix.one_mul]
    rw [hx]
  unfold copper scriptT
  change y • v+(brace k P p*(L*d)*P.mouth k p-H*(L*d)*R)*m=H*δ*D*u*m+P.chainY k p q • (v*(1-H'*d*D'*m))
  rw [show P.chainY k p q=y from (foot_is k hk P hp he).symm,hv,heq];
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_one,smul_sub,Matrix.mul_assoc]; abel

lemma wire_match (l : Site P.L) : wire k P p l = scriptT k P p (aliasAt p l) := by
  unfold wire; split
  · next h => subst l; exact copper_match k hk P hp he
  next h => exact stake_match k hk P hp he l h
end matchingWire
end Flight
end YM.Next.Free
