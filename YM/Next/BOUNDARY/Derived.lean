import YM.Next.BOUNDARY.Coordinates
import YM.Work.A10

/-!
# Wick-turning the infinitesimal response

Auxiliary `rankAction` on all of M4 by linear extension; used as a Lie algebra
map only on tangents. The extension is convenient to take derivatives without
chart hypotheses. We need the bracket test with the first input a coordinate
boost and second input *arbitrary* proper Lorentz algebra element, and spatial
rotation conjugations (no rotations assumed on the boundary!). The bracket sign
on two boosts comes from moving Θ through an off-diagonal element.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY.Descent
open Function Mink Table
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace

def tangent (X : M4) := star X = -(theta * X * theta)

def boostLike (X : M4) := star X = X ∧ theta*X = -(X*theta)

def spaceLikeGen (X : M4) := star X = -X ∧ theta * X = X*theta

lemma tangent_add {X Y : M4} (h : tangent X) (k : tangent Y) : tangent (X+Y) := by
  unfold tangent at *; rw [star_add,h,k,mul_add,add_mul, neg_add]

lemma tangent_smul {X : M4} (h : tangent X) (t : ℝ) : tangent (t • X) := by
  unfold tangent at *; rw [star_smul,star_trivial,h, mul_smul_comm,smul_mul_assoc, smul_neg]

lemma B_boostLike (a : SpaceAxis) : boostLike (B a) := ⟨B_star a,time_parity a⟩

lemma boostLike.tangent {X : M4} (h : boostLike X) : tangent X := by
  unfold Descent.tangent; rw [h.1,h.2, neg_mul,mul_assoc,theta_sq,mul_one,neg_neg]

lemma spaceLikeGen.tangent {X : M4} (h : spaceLikeGen X) : tangent X := by
  unfold Descent.tangent; rw [h.1,h.2,mul_assoc,theta_sq,mul_one]

lemma theta_mul_mul (X : M4) : theta*(theta*X)=X := by rw [← mul_assoc,theta_sq,one_mul]

lemma tangent_parts {X : M4} (h : tangent X) : ∃ A W, X=A+W ∧ spaceLikeGen A ∧ boostLike W := by
  let r := (1/2 : ℝ)
  have hp : r+r=1 := by dsimp only [r]; ring
  have hm : theta * star X = -(X * theta) := by
    unfold tangent at h; rw [h,mul_neg,← mul_assoc theta _ theta,theta_mul_mul]
  have ht : star X * theta = -(theta * X) := by
    unfold tangent at h; rw [h, neg_mul,mul_assoc _ theta,theta_sq,mul_one]
  refine ⟨r • (X-star X),r • (X+star X),?_,⟨?_,?_⟩,?_,?_⟩
  · rw [← smul_add,sub_add_add_cancel, smul_add,← add_smul,hp, one_smul]
  · rw [star_smul, star_trivial,star_sub,star_star,← neg_sub _ X,smul_neg]; abel
  · rw [mul_smul_comm, smul_mul_assoc,mul_sub, sub_mul,hm,ht]; congr 1; abel
  · rw [star_smul, star_trivial,star_add,star_star,add_comm (star X)]
  · rw [mul_smul_comm, smul_mul_assoc,← smul_neg,mul_add,add_mul,hm,ht]; congr 1; abel

def Ad (g : Lorentz) (X : M4) := mat g*X*mat g⁻¹

lemma Ad_one (X : M4) : Ad 1 X=X := by simp only [Ad, inv_one,mat_one,one_mul,mul_one]
lemma Ad_mul (g k : Lorentz) (X : M4) : Ad (g*k) X=Ad g (Ad k X) := by
  simp only [Ad,mul_inv_rev,mat_mul,mul_assoc]

lemma Ad_tangent {X : M4} (h : tangent X) (g : Lorentz) : tangent (Ad g X) := by
  unfold tangent at h ⊢
  unfold Ad
  rw [star_mul,star_mul,mat_star, inv_inv, mat_star,h]
  simp only [mul_assoc,mul_neg,neg_mul,theta_mul_mul]

lemma Ad_add (X Y : M4) (g : Lorentz) : Ad g (X+Y)=Ad g X + Ad g Y := by
  unfold Ad; rw [mul_add,add_mul]

/- Projections; diagonal θ invol and `BQ` set the sign. -/

def sk (X : M4) := (1/2 : ℝ) • (X-star X)

def skP : M4 →L[ℝ] Ortho.Skew := LinearMap.toContinuousLinearMap {
  toFun X := ⟨sk X, by
    change star (sk _) = _; simp [sk, ← smul_neg] ⟩
  map_add' x y := by
    apply Subtype.ext; change sk (x+y)=sk x + sk y
    unfold sk; rw [← smul_add,star_add]; congr 1; abel
  map_smul' r x := by
    apply Subtype.ext; change sk (r • x)= r • sk x
    rw [sk,sk,star_smul,star_trivial,← smul_sub,smul_comm] }

lemma skP_eval (X : M4) : (skP X).val=sk X := rfl

lemma sk_eq {X : M4} (h : star X = -X) : sk X = X := by
  unfold sk
  rw [h,sub_neg_eq_add,smul_add,← add_smul]; norm_num

lemma sk_skew (X : Ortho.Skew) : skP X.val = X := Subtype.ext (sk_eq X.property)

private def symmetricPart : M4→L[ℝ] M4 := (ContinuousLinearMap.id ℝ _) - Ortho.skewSpace.subtypeL.comp skP
private def twicePart : M4 →L[ℝ] M4 := ((ContinuousLinearMap.mul ℝ M4).flip theta).comp symmetricPart

variable {G : Gauge} {L : Register G} {S : Table L}
abbrev FieldOp (S : Table L) (d : ℕ) := (S.Field d →L[ℂ] S.Field d)

private lemma general (T : Type*) [NormedAddCommGroup T] [NormedSpace ℝ T] : ContinuousSMul ℝ T := inferInstance

local instance (d : ℕ) : ContinuousSMul ℝ (FieldOp S d) := general (FieldOp S d)

def lie (R : Rotation S) (d : ℕ) : Ortho.Skew →L[ℝ] FieldOp S d := LinearMap.toContinuousLinearMap {
  toFun y := LinearMap.toContinuousLinearMap (R.lie d y)
  map_add' x y := by
    ext u
    change R.lie d (x+y) u = R.lie d x u + R.lie d y u
    rw [map_add]; rfl
  map_smul' r x := by
    ext u
    change R.lie d (r • x) u = r • R.lie d x u; rw [map_smul]; rfl }

def rankAction (R : Rotation S) (d : ℕ) : M4 →L[ℝ] FieldOp S d :=
  (lie R d).comp skP + (-Complex.I) • ((lie R d).comp (skP.comp twicePart))

lemma rank_eq (R : Rotation S) (d : ℕ) (X : M4) : rankAction R d X=
    lie R d (skP X) + (-Complex.I) • lie R d (skP ((X-sk X)*theta)) := rfl

lemma rank_space (R : Rotation S) (d : ℕ) {A : M4} (h : spaceLikeGen A) :
    rankAction R d A=lie R d ⟨A,h.1⟩ := by
  have ht : skP A=⟨A,h.1⟩ := sk_skew (⟨A,h.1⟩ : Ortho.Skew)
  rw [rank_eq,ht,sk_eq h.1,sub_self,zero_mul, map_zero,map_zero, show -Complex.I • (0 : FieldOp S d)=0 from by ext x; simp,add_zero]

lemma off_skew {W : M4} (h : boostLike W) : W*theta ∈ Ortho.skewSpace := by
  change star _ = - _; rw [star_mul,star_theta,h.1,h.2]

lemma rank_boost (R : Rotation S) (d : ℕ) {W : M4} (h : boostLike W) :
    rankAction R d W = (-Complex.I) • lie R d ⟨W * theta,off_skew h⟩ := by
  have hm : sk W=0 := by simp only [sk,h.1,sub_self,smul_zero]
  have he : skP W=0 := Subtype.ext hm
  rw [rank_eq, hm, he,map_zero,zero_add,sub_zero]
  exact congr_arg _ (congr_arg _ (sk_skew (⟨W*theta,off_skew h⟩ : Ortho.Skew)))

lemma rank_B (R : Rotation S) (d : ℕ) (i : SpaceAxis) : rankAction R d (B i) = (-Complex.I) • lie R d (Q i) := by
  rw [rank_boost R d (B_boostLike i)]
  exact congr_arg _ (congr_arg _ (Subtype.ext (BQ i)))

section brackets
open Complex

def bracket {A : Type*} [Ring A] (X Y : A) := X*Y-Y*X

private lemma cross_parity {X A : M4} (h : boostLike X) (t : spaceLikeGen A) :
    theta*(X*A)=-(X*A*theta) ∧ theta*(A*X)=-(A*X*theta) := by
  constructor
  · rw [← mul_assoc,h.2,neg_mul,mul_assoc,mul_assoc,t.2]
  rw [← mul_assoc,t.2,mul_assoc,h.2,mul_neg,mul_assoc]

private lemma commutes_parity {X W : M4} (h : boostLike X) (t : boostLike W) :
    theta*(X*W)=X*W*theta := by
  rw [← mul_assoc, h.2, neg_mul,mul_assoc,t.2,mul_neg,neg_neg,mul_assoc]

lemma mixed_bracket {X A : M4} (h : boostLike X) (t : spaceLikeGen A) :
    boostLike (bracket X A) := by
  constructor
  · simp only [bracket,star_sub,star_mul,h.1,t.1,mul_neg,neg_mul]; abel
  unfold bracket; rw [mul_sub, sub_mul,(cross_parity h t).1,(cross_parity h t).2]; abel

lemma boost_bracket {X W : M4} (h : boostLike X) (t : boostLike W) :
    spaceLikeGen (bracket X W) := by
  constructor
  · simp only [bracket,star_sub,star_mul,h.1,t.1]; abel
  unfold bracket; rw [mul_sub,sub_mul,commutes_parity h t,commutes_parity t h]

lemma mixed_type (X : M4) {A : M4} (t : spaceLikeGen A) : bracket X A * theta = bracket (X*theta) A := by
  rw [bracket,bracket,sub_mul, mul_assoc X A, mul_assoc X theta, t.2,mul_assoc]

private lemma negative_factor (X : M4) {Y : M4} (h : boostLike Y) : X*theta*(Y*theta) = -(X*Y) := by
  rw [mul_assoc X,← mul_assoc theta,h.2,neg_mul,mul_assoc Y theta,theta_sq,mul_one,mul_neg]

lemma boost_type {X W : M4} (h : boostLike X) (t : boostLike W) : bracket (X*theta) (W*theta) = - bracket X W := by
  rw [bracket,bracket,negative_factor X t,negative_factor W h]; abel

variable (R : Rotation S) (d : ℕ) {H : S.RealSpin}

lemma bracket_euclidean (h : Spin.Port R H) (v w : Ortho.Skew) :
    bracket (lie R d v) (lie R d w)=lie R d (Org.bracket v w) := by
  ext u
  exact LinearMap.congr_fun ((Work.A10.answer H R h).1 d v w) u

private lemma rankMixed (h : Spin.Port R H) {A X : M4} (hu : boostLike X) (ht : spaceLikeGen A) :
    rankAction R d (bracket X A)=bracket (rankAction R d X) (rankAction R d A) := by
  rw [rank_boost R d (mixed_bracket hu ht),rank_boost R d hu,rank_space R d ht]
  let x : Ortho.Skew := ⟨X*theta,off_skew hu⟩
  let y : Ortho.Skew := ⟨A,ht.1⟩
  have he : (⟨bracket X A*theta, off_skew (mixed_bracket hu ht)⟩ : Ortho.Skew) = Org.bracket x y :=
    Subtype.ext (mixed_type X ht)
  rw [he, ← bracket_euclidean R d h x y]
  unfold bracket; ext v
  change (-I) • ((lie _ _ _ ((lie _ _ _) v)) - (lie _ _ _ ((lie _ _ _) v))) =
    (-I) • _ - (lie _ _ _) ((-I) • _)
  rw [map_smul, smul_sub]; rfl

private lemma rankTwo (h : Spin.Port R H) {X W : M4} (hu : boostLike X) (ht : boostLike W) :
    rankAction R d (bracket X W)=bracket (rankAction R d X) (rankAction R d W) := by
  rw [rank_space R d (boost_bracket hu ht),rank_boost R d hu,rank_boost R d ht]
  let x : Ortho.Skew := ⟨X*theta,off_skew hu⟩
  let y : Ortho.Skew := ⟨W*theta,off_skew ht⟩
  have he : (⟨bracket X W,(boost_bracket hu ht).1⟩ : Ortho.Skew)= -(Org.bracket x y) := by
    apply Subtype.ext
    change _= -(bracket _ _)
    rw [boost_type hu ht,neg_neg]
  rw [he,map_neg,← bracket_euclidean R d h x y]
  unfold bracket; ext v
  change -(lie _ _ _ (lie _ _ _ v)-lie _ _ _ (lie _ _ _ v)) =
    (-I) • lie R d x ((-I) • lie R d y v) - (-I) • lie R d y ((-I) • lie R d x v)
  rw [map_smul,map_smul,smul_smul,smul_smul,neg_mul_neg,I_mul_I,neg_smul,neg_smul,one_smul,one_smul]
  abel

lemma rank_bracket (h : Spin.Port R H) {X Y : M4} (hp : boostLike X) (hv : tangent Y) :
    rankAction R d (bracket X Y)=bracket (rankAction R d X) (rankAction R d Y) := by
  have he {T : Type} [Ring T] (X Y Z : T) : bracket X (Y+Z)=bracket X Y + bracket X Z := by
    simp only [bracket,mul_add,add_mul]; abel
  obtain ⟨A,W,rfl,ht,hw⟩ := tangent_parts hv
  rw [he,map_add,map_add,he,rankMixed R d h hp ht,rankTwo R d h hp hw]
end brackets

/- `Matches` does not already assert integrability or even invertibility of the
represented endomorphism. It is the compatibility used when multiplying
along differentiable paths. -/

def er (R : Rotation S) (d : ℕ) (k : Ortho) : FieldOp S d := (R.act d k).toContinuousLinearEquiv.toContinuousLinearMap

lemma er_one (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) (d : ℕ) : er R d 1=1 := by
  ext x; exact h.fixes d x

lemma er_mul (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) (d : ℕ) (k g : Ortho) :
    er R d (k*g)=er R d k * er R d g := by ext x; exact h.sends d k g x

def Matches (R : Rotation S) (d : ℕ) (g : Lorentz) (Z : FieldOp S d) :=
  ∀ X, tangent X → Z * rankAction R d X=rankAction R d (Ad g X) * Z

lemma Matches.mul {R : Rotation S} {d : ℕ} {g k : Lorentz} {V W : FieldOp S d}
    (h : Matches R d g V) (t : Matches R d k W) : Matches R d (g*k) (V*W) := by
  intro X ht
  rw [mul_assoc,t X ht,← mul_assoc, h _ (Ad_tangent ht _),Ad_mul, mul_assoc]

def orbitA (k : Ortho) (X : Ortho.Skew) : Ortho.Skew :=
  ⟨k.val*X.val*star k.val, by
    change star _ = -_
    rw [star_mul,star_mul,star_star,show star X.val= -X.val from X.2]; simp only [mul_assoc,mul_neg,neg_mul]⟩

lemma er_lie (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) (d : ℕ) (k : Ortho) (X : Ortho.Skew) :
    er R d k * lie R d X= lie R d (orbitA k X) * er R d k := by
  ext v; exact (Work.A10.answer H R h).2 d k X v

private lemma space_star {k : Ortho} (h : Lorentz.spatialTurn k) : theta * star k.val = star k.val * theta := by
  have he := congr_arg star (space_parity k h); rw [star_mul,star_mul,star_theta] at he; exact he.symm

private lemma space_boost {k : Ortho} (h : Lorentz.spatialTurn k) {X : M4} (hv : boostLike X) :
    boostLike (Ad (.room k h) X) := by
  let F := Ad (.room k h) X
  have hp := Ad_tangent hv.tangent (.room k h)
  have he : star F = F := by
    unfold F Ad; rw [room_mat_inv, mat_room, star_mul,star_mul,star_star,hv.1,mul_assoc]
  refine ⟨he,?_⟩
  change star F=-(theta*F*theta) at hp
  rw [he] at hp
  change theta*F= -(F*theta)
  exact Eq.symm (calc
    -(F*theta)= -(-(theta*F*theta)*theta) := congr_arg (fun y => -(y*theta)) hp
    _ = _ := by rw [neg_mul, neg_neg,mul_assoc _ theta theta,theta_sq,mul_one])

private lemma space_space {k : Ortho} (h : Lorentz.spatialTurn k) {X : M4} (hv : spaceLikeGen X) :
    spaceLikeGen (Ad (.room k h) X) := by
  let F := Ad (.room k h) X
  have he : star F = -F := by
    unfold F Ad; rw [mat_room,room_mat_inv]
    exact (orbitA k ⟨X,hv.1⟩).property
  refine ⟨he,?_⟩
  have hp := Ad_tangent hv.tangent (.room k h)
  change star F=-(theta*F*theta) at hp
  have hF : F=theta*F*theta := neg_injective (he.symm.trans hp)
  change theta*F=F*theta
  exact Eq.symm (calc
    F*theta=theta*F*theta*theta := congr_arg (· * theta) hF
    _ = _ := by rw [mul_assoc _ theta theta,theta_sq,mul_one])

lemma matches_space (R : Rotation S) {H : S.RealSpin} (h : Spin.Port R H) (d : ℕ)
    (k : Ortho) (hk : Lorentz.spatialTurn k) : Matches R d (.room k hk) (er R d k) := by
  intro X ht
  obtain ⟨A,W,rfl,ha,hw⟩ := tangent_parts ht
  rw [Ad_add,map_add,map_add,mul_add,add_mul]
  have hP := space_space hk ha; have hW := space_boost hk hw
  congr 1
  · rw [rank_space R d ha,rank_space R d hP,er_lie R h]
    have he : orbitA k ⟨A,ha.1⟩=⟨Ad (.room k hk) A,hP.1⟩ := by
      apply Subtype.ext; change _=Ad _ _; rw [Ad,mat_room,room_mat_inv]; rfl
    rw [he]
  rw [rank_boost R d hw,rank_boost R d hW]
  let Q : Ortho.Skew := ⟨W*theta,off_skew hw⟩
  have he : orbitA k Q = ⟨Ad (.room k hk) W * theta,off_skew hW⟩ := by
    apply Subtype.ext; change k.val*(W*theta)*star k.val = Ad _ W * theta
    rw [Ad, mat_room, room_mat_inv]
    simp only [mul_assoc, space_star hk]
  rw [show (⟨Ad (.room k hk) W*theta,off_skew hW⟩ : Ortho.Skew)=orbitA k Q from he.symm]
  ext v
  change er R d k ((-Complex.I) • (lie R d Q v)) = (-Complex.I) • lie R d (orbitA k Q) (er R d k v)
  rw [map_smul]
  exact congr_arg _ (DFunLike.congr_fun (er_lie R h d k Q) v)

end YM.Next.BOUNDARY.Descent
