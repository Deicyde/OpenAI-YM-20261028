import YM.Next.FREE_KERNELS.Signal

/-!
# The two columns, punctured algebra

Alias coefficients in A and T here are RESCALED BY L and L² respectively.
`weightsE` uses a sum, not mean, in both numerator and denominator (so E
unchanged). Keep their off-divisor formulas for identifying across folds. No
continuation claim here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {j t : ℕ}

lemma scaleD_one (k : ℝ) (v : Train j) (p a) : scaleD 1 k v p a=v.levelD k a p := by simp [scaleD]

lemma alias_regular {P : Flight j t} {p : Momentum} (hp : p ∈ realCube zone) (l : Site P.L)
    (he : l ≠ 0 ∨ p ≠ 0) : aliasAt p l ∈ realCube zone ∧ aliasAt p l ≠ 0 := by
  refine ⟨alias_in_real zone_pos hp _ P.odd,?_⟩
  by_cases h : l=0
  · subst l; have he' := he.resolve_left (not_not.mpr rfl)
    intro hz; have hh := alias_scale p (0:Site P.L)
    rw [hz,lift_origin] at hh
    exact he' (by simpa [show reciprocal (0:Cover)=0 by ext; simp [reciprocal]] using hh.symm)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (show lift l≠0 by rw [← lift_origin P.L]; exact lift_inj.ne h)
  have hb := scaled_alias_lower l (mem_cube_real hp zone_pos) i hi
  intro hc
  rw [hc, Pi.zero_apply,norm_zero,mul_zero] at hb
  exact not_lt_of_ge hb (mul_pos zone_pos (up_pos ..))

lemma mass_filter_live (P : Flight j t) {p : Momentum} (hp : p ∈ realCube zone) : massFilter P.patch (aliasAt p (0 : Site P.L))≠0 := by
  unfold massFilter
  rw [alias_zero_eq]; apply pow_ne_zero
  have hh := Train.area_at_root P.L P.L le_rfl p hp
  exact norm_pos_iff.mp ((Real.exp_pos _).trans_le hh)

namespace Flight

def total (k : ℝ) (P : Flight j t) (q : Momentum) := ∑ i : Axis, scaleD P.L k P.wing q i

def tabE (k : ℝ) (P : Flight j t) (p : Momentum) := ∑ l : Site P.L,
    yen (massFilter P.patch) (aliasAt p l) * total k P (aliasAt p l)

def weightsE (k : ℝ) (P : Flight j t) (p q : Momentum) :=
    massFilter P.patch (-q)*total k P q/tabE k P p

def scriptA (k : ℝ) (P : Flight j t) (p q : Momentum) :=
    fieldD P.L k P.wing q * flux P 1 q * rotor 1 k P.land p + weightsE k P p q • (signal P.L 0 q * pipe 1 k P.land p)

def cloud (k : ℝ) (P : Flight j t) (p : Momentum) :=
    pulse k P.land p*signal 1 1 p*fieldD 1 k P.land p*mirage 1 1 p

def chainY (k : ℝ) (P : Flight j t) (p q : Momentum) :=
    yen (massFilter P.patch) q*scaleR 1 k P.land p/scaleR P.L k P.wing q

def scriptT (k : ℝ) (P : Flight j t) (p q : Momentum) :=
    pulse k P.wing q * signal P.L 1 q * fieldD P.L k P.wing q * flux P 1 q * mirage 1 1 p +
    chainY k P p q • (flux P 2 q * (1-cloud k P p))

section algebra
variable (k : ℝ) (hk : 0<k) (P : Flight j t)

include hk
lemma tabE_puncture {p : Momentum} (hp : p∈realCube zone) (he : p≠0) : P.tabE k p≠0 := by
  have hh (l : Site P.L) := alias_regular hp l (Or.inr he)
  have hb (q : Momentum) (hq : q∈realCube zone) : Silver (yen (massFilter P.patch) q) := by
    have hk : star (massFilter P.patch q)=massFilter P.patch (-q) := by unfold massFilter; rw [star_pow,Train.area_conj, show star q=q from hq.1]
    unfold yen; rw [← hk]; exact Silver.gram _
  have hc (q : Momentum) (hq : q∈realCube zone) (he : q≠0) : Silver (total k P q) ∧ 0 < (total k P q).re := by
    have hx (i) : Silver (scaleD P.L k P.wing q i) := ((Silver.side _).pow _).inv.mul (Train.D_cost _ hk _ _ hq.1)
    have hg (i) := (hx i).re_ne (scaleD_live _ _ hk _ hq he _)
    refine ⟨Silver.sum _ _ (fun i _ => hx i),?_⟩
    unfold total; rw [Complex.re_sum]; exact lt_of_lt_of_le (hg 0) (Finset.single_le_sum (f:=fun i => (scaleD _ _ _ _ i).re) (fun i _ => (hg i).le) (Finset.mem_univ _))
  let f (l : Site P.L) := yen (massFilter P.patch) (aliasAt p l) * total k P (aliasAt p l)
  have hs (l : Site P.L) := (hb _ (hh l).1).mul (hc _ (hh l).1 (hh l).2).1
  have h0 : 0<(f 0).re := by
    have hx := mass_filter_live P hp
    have hy := mass_filter_live P (realCube_neg hp)
    rw [show aliasAt (-p) (0:Site P.L)=-aliasAt p (0:Site P.L) from by simpa only [neg_zero] using alias_reverse p P.odd (0:Site P.L)] at hy
    have hY := hb _ (hh 0).1
    have hK := hc _ (hh 0).1 (hh 0).2
    unfold f; rw [hY.real_mul]; exact mul_pos (hY.re_ne (mul_ne_zero hx hy)) hK.2
  have hr : 0 < (tabE k P p).re := by
    unfold tabE; rw [Complex.re_sum]; exact lt_of_lt_of_le h0 (Finset.single_le_sum (f:=fun l => (f l).re) (fun l _ => (hs l).re_nonneg) (Finset.mem_univ _))
  intro h; rw [h, Complex.zero_re] at hr; exact lt_irrefl _ hr

lemma weights_plan {p : Momentum} (hp : p∈realCube zone) (he : p≠0) :
    ∑ l : Site P.L, weightsE k P p (aliasAt p l)*massFilter P.patch (aliasAt p l)=1 := by
  have hm := tabE_puncture k hk P hp he
  calc
    _ = (P.tabE k p)⁻¹ * ∑ l : Site P.L, yen (massFilter P.patch) (aliasAt p l)*total k P (aliasAt p l) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; unfold weightsE yen; ring
    _ = _ := inv_mul_cancel₀ hm

omit hk
lemma cube_flow (p : Momentum) :
    ∑ i : Site P.L, hinges P 1 (aliasAt p i)*fieldD P.L k P.wing (aliasAt p i)*flux P 1 (aliasAt p i) =
      fieldD 1 k P.land p-(k:ℂ)⁻¹ • 1 := by
  have hh (a : Axis) := Train.D_feedback k P.patch P.mono P.narrow P.wing a p
  ext a b
  have hs (p : Momentum) : hinges P 1 p*fieldD P.L k P.wing p * flux P 1 p=
      mask 1 (fun i => yen (pullLine P.patch i) p*scaleD P.L k P.wing p i) := by
    unfold hinges flux fieldD; simp only [hinges, transpose_smul,mask_trans,Matrix.smul_mul,Matrix.mul_smul,mask_mul]
    ext i j; simp only [mask_value,Matrix.smul_apply,smul_eq_mul]; split <;> (try unfold yen pullLine) <;> ring!
  simp_rw [hs]
  simp only [Matrix.sum_apply,fieldD, mask_value,scaleD_one, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs with h; swap; simp
  specialize hh (axisEquiv.symm a)
  change P.land.levelD _ _ _ = _ at hh
  rw [hh, smul_eq_mul, mul_one, add_sub_cancel_right]; unfold slide shuttle; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; unfold scaleD; ring!

lemma creek_dry (l : Site P.L) (p : Momentum) :
    mirage P.L 0 (aliasAt p l) * flux P 1 (aliasAt p l) * mirage 1 1 p=0 := by
  rw [flux_transport]; simp only [Matrix.mul_assoc,mirage_chain,Matrix.mul_zero]

include hk
lemma script_main {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) :
    ∑ l : Site P.L, hinges P 1 (aliasAt p l)*scriptA k P p (aliasAt p l) =
      1-(k:ℂ)⁻¹ • rotor 1 k P.land p := by
  let R := rotor 1 k P.land p
  let pp := pipe 1 k P.land p
  let g := signal 1 0 p
  let f (q) := hinges P 1 q*fieldD P.L k P.wing q*flux P 1 q
  have hh (l : Site P.L) : hinges P 1 (aliasAt p l)*scriptA k P p (aliasAt p l)=f (aliasAt p l)*R+
      ((weightsE k P p (aliasAt p l))*massFilter P.patch (aliasAt p l)) • (g*pp) := by
    let q := aliasAt p l
    have hu : hinges P 1 q*signal P.L 0 q=massFilter P.patch q • g := by
      rw [hinge_transport, hinges_nil, Matrix.mul_smul, Matrix.mul_one]
    unfold q at hu
    unfold f scriptA; simp only [Matrix.mul_add, Matrix.mul_smul,← Matrix.mul_assoc,hu,Matrix.smul_mul,smul_smul]; rfl
  simp_rw [hh]; rw [Finset.sum_add_distrib,← Matrix.sum_mul,← Finset.sum_smul,P.weights_plan k hk hp he,one_smul]
  change (∑ i, f _) * R + g*pp = _
  rw [show ∑ i : Site P.L, f (aliasAt p i) = _ from P.cube_flow k p, sub_mul]
  unfold R pp g; rw [rotor_before _ k hk _ hp he,smul_mul_assoc,one_mul]; abel

lemma script_cross {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) (l : Site P.L) :
    let q := aliasAt p l
    rotor P.L k P.wing q * scriptA k P p q=flux P 1 q * rotor 1 k P.land p := by
  intro q
  obtain ⟨hh,hq⟩ := alias_regular hp l (Or.inr he)
  unfold scriptA; rw [Matrix.mul_add]; simp only [Matrix.mul_smul,← Matrix.mul_assoc]
  rw [(rotor_immunity P.L k _ q).1, Matrix.zero_mul,smul_zero,add_zero, rotor_after P.L k hk _ hh hq]
  simp only [sub_mul,Matrix.one_mul]; unfold rotor
  have h : creek P.L k P.wing q * mirage P.L 0 q * flux P 1 q *
      (mirage 1 1 p * pulse k P.land p * signal 1 1 p)=0 := by
    have ht := creek_dry P l p
    change mirage P.L 0 q * flux P 1 q * _ =_ at ht
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,show creek _ _ _ _*_*_*mirage 1 1 p=
        creek P.L k P.wing q * (mirage P.L 0 q * flux P 1 q * mirage 1 1 p) by simp only [Matrix.mul_assoc],ht]
    simp
  rw [h,sub_zero]
/-- The cloud complement participates in `T` even when the output is
not a weighted gradient. -/
lemma cloud_kills {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) :
    mirage 1 1 p*(1-cloud k P p)=0 ∧ (1-cloud k P p)*pulse k P.land p*signal 1 1 p=0 := by
  let d := signal 1 1 p
  let m := mirage 1 1 p
  let D := fieldD 1 k P.land p
  let G := pulse k P.land p
  have h₁ : rotor 1 k P.land p*D*m=m := by
    rw [show rotor 1 k P.land p*D=_ from rotor_after 1 k hk P.land hp he]; unfold m
    rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,mirage_chain,Matrix.mul_zero,sub_zero]
  have h₂ : d*D*rotor 1 k P.land p=d := by
    rw [Matrix.mul_assoc,show D*rotor 1 k P.land p=_ from rotor_before 1 k hk P.land hp he]; unfold d
    rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,signal_chain,Matrix.zero_mul,sub_zero]
  change m*(1-G*d*D*m)=0 ∧ (1-G*d*D*m)*G*d=0
  constructor
  · rw [Matrix.mul_sub,Matrix.mul_one]; simp only [← Matrix.mul_assoc] at *; exact sub_eq_zero.mpr h₁.symm
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.sub_mul]; apply sub_eq_zero.mpr
  calc
    G*d=G*(d*D*rotor 1 k P.land p) := congr_arg _ h₂.symm
    _ = _ := by change G*(d*D*(m*G*d))=_; simp only [Matrix.mul_assoc]

lemma script_dual {p : Momentum} (hp : p ∈ realCube zone) (he : p≠0) (l : Site P.L) :
    let q := aliasAt p l
    mirage P.L 1 q * scriptT k P p q=flux P 1 q * mirage 1 1 p ∧
    scriptT k P p q * pulse k P.land p * signal 1 1 p=
      pulse k P.wing q * signal P.L 1 q * scriptA k P p q := by
  intro q
  let g := pulse k P.land p
  let h := pulse k P.wing q
  let a := mirage P.L 1 q
  let d := signal P.L 1 q
  let y := fieldD P.L k P.wing q
  let v := flux P 1 q
  let w := flux P 2 q
  let b := mirage 1 1 p
  let e := signal 1 1 p
  let Q := 1-cloud k P p
  have hh1 : b*Q=0 := (cloud_kills k hk P hp he).1
  have hh2 : Q*g*e=0 := (cloud_kills k hk P hp he).2
  have hs : a*w=v*b := flux_transport P 1 l p
  obtain ⟨hi,hi'⟩ := alias_regular hp l (Or.inr he)
  have hu : rotor P.L k P.wing q * y*(v*b) = v*b := by
    rw [show rotor P.L k P.wing q*y = _ from rotor_after P.L k hk P.wing hi hi', Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,
      ← Matrix.mul_assoc _ v, show mirage P.L 0 q*v*b=_ from creek_dry P l p,Matrix.mul_zero,sub_zero]
  have hy : scriptT k P p q=h*d*y*v*b + chainY k P p q • (w*Q) := rfl
  constructor
  · change a*scriptT k P p q=v*b
    have he : a*(h*d*y*v*b)=v*b := Eq.trans (by change _=a*h*d*y*(v*b); simp only [Matrix.mul_assoc]) hu
    rw [hy, Matrix.mul_add,he,Matrix.mul_smul,← Matrix.mul_assoc a,hs,Matrix.mul_assoc,hh1,Matrix.mul_zero,smul_zero,add_zero]
  change scriptT k P p q*g*e=h*d*(y*v*(b*g*e)+weightsE k P p q • (signal P.L 0 q * pipe 1 k P.land p))
  have hs0 : h*d*signal P.L 0 q=0 := by rw [Matrix.mul_assoc,show d*signal P.L 0 q=_ from signal_chain ..,Matrix.mul_zero]
  have hQ : w*Q*g*e=0 := by rw [Matrix.mul_assoc,Matrix.mul_assoc,← Matrix.mul_assoc Q,hh2,Matrix.mul_zero]
  rw [hy, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul,Matrix.smul_mul,hQ,smul_zero,add_zero,
      Matrix.mul_add,Matrix.mul_smul,← Matrix.mul_assoc (h*d) (signal P.L 0 q), hs0,Matrix.zero_mul,smul_zero,add_zero]; simp only [Matrix.mul_assoc]
end algebra
end Flight
end YM.Next.Free
