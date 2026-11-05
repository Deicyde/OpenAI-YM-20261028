import YM.Next.BOUNDARY.Decomposition
import YM.Next.BOUNDARY.RotCurve


/-!
# Sewing the local velocities into a descended group law

At each factor of the moving decomposition we prove that right-factor velocities
in the two representations correspond under the stipulated Wick-turned `rankAction`.
This composes by `Matches`. Use the resulting full derivative along `g * boost(t)`
to establish the right boost law, including for arbitrary Lorentz g. Together
with spatial right equivariance we get the full group action without assuming
independence under arbitrary products or simple-connectedness.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY.Descent
open Function Filter NormedSpace Set Mink Table
open scoped Topology Matrix.Norms.Frobenius
attribute [local instance] fieldOp_smul fieldOp_top

variable {G : Gauge} {L : Register G} {S : Table L}
variable (R : Rotation S) (d : ℕ) {H : S.RealSpin}

def eb (a : SpaceAxis) (s : ℝ) : FieldOp S d := exp (s • rankAction R d (B a))

lemma eb_zero (a) : eb R d a 0=1 := by
  unfold eb; rw [show (0:ℝ) • rankAction R d (B a)=0 by ext v; simp, exp_zero]

lemma eb_inv (a) (t : ℝ) : eb R d a (-t)*eb R d a t=1 := by
  haveI : CompleteSpace (S.Field d) := FiniteDimensional.complete ℂ _
  letI : NormedAlgebra ℚ (FieldOp S d) := .restrictScalars ℚ ℂ _
  let P : FieldOp S d := t • rankAction R d (B a)
  have hp : exp (-P) * exp P=1 := by
    have he : exp (-P+P)=exp (-P)*exp P := exp_add_of_commute (x := -P) (y := P) (by exact (Commute.refl P).neg_left)
    rw [← he]; simp
  unfold eb
  rwa [show (-t) • rankAction R d (B a) = -P by ext v; simp [P]]

/- There are diamonds when locally specializing normed-ring lemmas to the
CLMs over ℂ viewed real for differentiation. `fieldOp_*` exposes propositional
instances locally. -/

lemma eb_right (a) (u) : HasDerivAt (eb R d a) (eb R d a u * rankAction R d (B a)) u := by
  haveI : CompleteSpace (S.Field d) := FiniteDimensional.complete ℂ _
  exact hasDerivAt_exp_smul_const (rankAction R d (B a)) u

lemma eb_left (a) (u) : HasDerivAt (eb R d a) (rankAction R d (B a)*eb R d a u) u := by
  haveI : CompleteSpace (S.Field d) := FiniteDimensional.complete ℂ _
  exact hasDerivAt_exp_smul_const' (rankAction R d (B a)) u

lemma Ad_deriv (X : M4) (a : SpaceAxis) (s : ℝ) :
    HasDerivAt (fun t => Ad (boost a t) X) (bracket (B a) (Ad (boost a s) X)) s := by
  have hv : HasDerivAt (fun t => mat (boost a (-t))) (-(mat (boost a (-s))*B a)) s := by
    simpa only [neg_smul,one_smul] using!
      (at_boost a (-s)).scomp (h := fun t : ℝ => -t) s (hasDerivAt_id' s).neg
  unfold bracket
  simp_rw [Ad, show ∀ t : ℝ, (boost a t)⁻¹=boost a (-t) from Ray.boost_neg _]
  have hd : HasDerivAt (fun t => mat (boost a t)*X*mat (boost a (-t)))
      (B a * mat (boost a s)*X*mat (boost a (-s)) + mat (boost a s)*X* (-(mat (boost a (-s))*B a))) s :=
    ((at_boost' a s).mul_const X).mul hv
  simpa only [mul_neg,mul_assoc,sub_eq_add_neg] using hd

private lemma deriv_mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {x : ℝ} {f g : ℝ→A} (F J : A)
    (h : HasDerivAt f F x) (t : HasDerivAt g J x) : HasDerivAt (fun u => f u*g u) (F*g x + f x * J) x := h.mul t

private lemma const_deriv {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] (f : ℝ → A)
    (h : ∀ t, HasDerivAt f 0 t) (s : ℝ) : f s = f 0 :=
  is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt) (fun t => (h t).deriv) s 0

private lemma neg_parameter {d : ℕ} (f : ℝ→ FieldOp S d) (F : FieldOp S d) (t : ℝ)
    (h : HasDerivAt f F (-t)) : HasDerivAt (fun t => f (-t)) (-F) t := by
  have he := HasDerivAt.scomp (F:=FieldOp S d) (𝕜:=ℝ) (h := fun t : ℝ => -t)
    (g₁ := f) (g₁' := F) t h (hasDerivAt_id' t).neg
  simpa only [neg_smul, one_smul] using! he

lemma eb_matches (h : Spin.Port R H) (a) (u : ℝ) : Matches R d (boost a u) (eb R d a u) := by
  intro X hp
  let Z := eb R d a
  let F t := rankAction R d (Ad (boost a t) X)
  let E := rankAction R d (B a)
  let f (t : ℝ) := Z (-t)*F t*Z t
  have hf (s : ℝ) : HasDerivAt f 0 s := by
    have hF : HasDerivAt F (E*F s-F s*E) s := by
      have hw : bracket E (F s) = rankAction R d (bracket (B a) (Ad (boost a s) X)) :=
        (rank_bracket R d h (B_boostLike a) (Ad_tangent hp _)).symm
      change HasDerivAt _ (bracket E (F s)) _
      rw [hw]; exact linear_path (T:=FieldOp S d) (E:=M4) (by exact rankAction R d)
        _ _ _ (Ad_deriv X a s)
    have hu := neg_parameter Z (Z (-s)*E) s (eb_right R d _ _)
    have hg := eb_left R d a s
    have hy : HasDerivAt f ((-(Z (-s)*E)* F s + Z (-s)*(E*F s-F s*E)) * Z s +
        (Z (-s)*F s) * (E*Z s)) s :=
      deriv_mul (A:=FieldOp S d) (f:=fun t => Z (-t)*F t) (g:=Z) (-(Z (-s)*E)*F s+Z (-s)*(E*F s-F s*E)) (E*Z s)
        (deriv_mul (A:=FieldOp S d) (f:=fun t => Z (-t)) (g:=F) (-(Z (-s)*E)) (E*F s-F s*E) hu hF) hg
    have he : (-(Z (-s)*E)* F s + Z (-s)*(E*F s-F s*E)) * Z s + (Z (-s)*F s) * (E*Z s)=0 := by
      have hb {T : Type} [Ring T] (e f u v : T) : (-(e*f) * v + e * (f*v-v*f))* u + e*v*(f*u)=0 := by
        simp only [mul_sub,add_mul,sub_mul,mul_assoc, neg_mul]; abel
      exact hb (Z (-s)) E (Z s) (F s)
    rwa [he] at hy
  have hi := const_deriv (A:=FieldOp S d) f hf u
  change Z (-u)*F u*Z u = Z (-0)*F 0*Z 0 at hi
  have h0 : F 0=rankAction R d X := by unfold F; rw [boost, Ray.boost_start, Ad_one]
  have hz : Z 0=1 := eb_zero R d a
  rw [h0,neg_zero,hz,one_mul,mul_one] at hi
  change Z u*rankAction R d X= F u*Z u
  rw [← hi, ← mul_assoc, ← mul_assoc, show Z u * Z (-u)=1 from by
    have hw := eb_inv R d a (-u); rw [neg_neg] at hw; exact hw, one_mul]

/-- Right factor lifted velocities, localized at the point. -/
def Along (f : ℝ → Lorentz) (A : ℝ → FieldOp S d) (r : ℝ) : Prop := Matches R d (f r) (A r) ∧
  ∃ X : M4, tangent X ∧ HasDerivAt (fun t => mat (f t)) (mat (f r)*X) r ∧ HasDerivAt A (A r * rankAction R d X) r

lemma along_mul {f g : ℝ → Lorentz} {A B : ℝ → FieldOp S d} {r : ℝ}
    (h : Along R d f A r) (k : Along R d g B r) : Along R d (fun t => f t*g t) (fun t => A t * B t) r := by
  obtain ⟨hm, X, hx, hF, hA⟩ := h
  obtain ⟨hn, Y, hy, hG, hB⟩ := k
  let P := Ad (g r)⁻¹ X
  have hp : tangent P := Ad_tangent hx _
  have he := hn P hp
  rw [show Ad (g r) P=X by unfold P; rw [← Ad_mul,mul_inv_cancel,Ad_one]] at he
  refine ⟨hm.mul hn,P+Y,tangent_add hp hy,?_,?_⟩
  · simp_rw [mat_mul]; refine (hF.fun_mul hG).congr_deriv ?_
    change mat (f r)*X*mat (g r)+mat (f r)*(mat (g r)*Y)=_
    have hh : mat (g r) * P = X * mat (g r) := by
      unfold P Ad; rw [inv_inv,← mul_assoc,← mul_assoc,mat_mul_inv,one_mul]
    rw [mul_add,mul_assoc _ _ P,hh,mul_assoc,mul_assoc]
  have hh : (A r * rankAction R d X) * B r + A r * (B r * rankAction R d Y)=
      A r * B r * rankAction R d (P+Y) := by
    rw [mul_assoc _ _ (B r),← he,map_add,mul_add,mul_assoc,mul_assoc]
  have ht : HasDerivAt (fun t => A t * B t)
      ((A r * rankAction R d X) * B r + A r * (B r * rankAction R d Y)) r :=
    deriv_mul (A:=FieldOp S d) (f:=A) (g:=B) _ _ hA hB
  rw [hh] at ht; exact ht

lemma along_boost (h : Spin.Port R H) (a) (x : ℝ→ℝ) {s} (hv : DifferentiableAt ℝ x s) :
    Along R d (fun t => boost a (x t)) (fun t => eb R d a (x t)) s := by
  let u := deriv x s
  have he : HasDerivAt x u s := hv.hasDerivAt
  refine ⟨eb_matches R d h _ _, u • B a,tangent_smul (B_boostLike a).tangent _,?_,?_⟩
  · change HasDerivAt _ (mat _*(u • B a)) _
    rw [mul_smul_comm]; exact (at_boost a _).scomp s he
  let Z := eb R d a
  have hw : HasDerivAt (fun t => Z (x t)) (u • (Z (x s)*rankAction R d (B a))) s :=
    HasDerivAt.scomp (F:=FieldOp S d) (𝕜:=ℝ) (g₁:=Z) (h:=x) s (eb_right R d a (x s)) he
  have hm : u • (Z (x s)*rankAction R d (B a)) = Z (x s) * rankAction R d (u • B a) := by
    rw [map_smul]
    ext v
    change u • Z (x s) (rankAction R d (B a) v) = Z (x s) (u • rankAction R d (B a) v)
    exact ((Z (x s)).restrictScalars ℝ |>.map_smul u _).symm
  rw [hm] at hw; exact hw

lemma along_space (h : Spin.Port R H) (f : ℝ→ Ortho) (hf : ∀ t, Lorentz.spatialTurn (f t)) {r : ℝ}
    (t : DifferentiableAt ℝ (fun t => (f t).val) r) :
    Along R d (fun i => .room (f i) (hf i)) (fun i => er R d (f i)) r := by
  obtain ⟨Y,hy,hY⟩ := er_path R h t d
  have he : spaceLikeGen Y.val := by
    refine ⟨Y.2,?_⟩
    have hp := hy.const_mul theta
    have ht := hy.mul_const theta
    have hK := hp.congr_of_eventuallyEq (by
      refine Eventually.of_forall (p := fun x : ℝ => (f x).val*theta=theta*(f x).val) ?_
      intro x; exact (space_parity (f x) (hf x)).symm)
    have hh := hK.unique ht
    rw [← mul_assoc,space_parity _ (hf r),mul_assoc,mul_assoc] at hh
    have hw := congr_arg (star (f r).val * ·) hh
    -- need only cancel on left
    rw [← mul_assoc _ _ (theta*Y.val),← mul_assoc _ _ (Y.val*theta), (f r).property.1, one_mul,one_mul] at hw
    exact hw
  refine ⟨matches_space R h d _ _,Y.val,he.tangent,?_,?_⟩
  · simp_rw [mat_room]; exact hy
  change HasDerivAt _ (er _ _ _ * rankAction _ _ _) _
  rw [rank_space R d he]; exact hY

def spins (g : Lorentz) := eb R d 0 (b0 g)*(eb R d 1 (b1 g)*(eb R d 2 (b2 g)*er R d (orientation g)))

lemma along_spins (h : Spin.Port R H) (g : ℝ→Lorentz) {s : ℝ} (hv : DifferentiableAt ℝ (fun t => mat (g t)) s) :
    Along R d g (fun t => spins R d (g t)) s := by
  have hb : DifferentiableAt ℝ (fun t => b0 (g t)) s := rapidity_diff 0 hv
  have hc : DifferentiableAt ℝ (fun t => b1 (g t)) s := rapidity_diff 1 (reduce_diff 0 hv)
  have hd : DifferentiableAt ℝ (fun t => b2 (g t)) s := rapidity_diff 2 (reduce_diff 1 (reduce_diff 0 hv))
  have hx := along_mul R d (along_boost R d h 0 _ hb) (along_mul R d (along_boost R d h 1 _ hc)
    (along_mul R d (along_boost R d h 2 _ hd) (along_space R d h (fun t => orientation (g t)) (fun t => oriented _) (orient_diff hv))))
  simp_rw [factors] at hx; exact hx

lemma spins_one (h : Spin.Port R H) : spins R d 1=1 := by
  simp only [spins, b0,b1,b2, reduce_one, rapidity_one,eb_zero,orientation_one,er_one R h, one_mul]

lemma spatial_right (h : Spin.Port R H) (g : Lorentz) (k : Ortho) (hk : Lorentz.spatialTurn k) :
    spins R d (g*Lorentz.room k hk) = spins R d g * er R d k := by
  simp only [spins,b0,b1,b2, reduce_right, rapidity_right, orient_right, er_mul R h, mul_assoc]

lemma boost_right (h : Spin.Port R H) (g : Lorentz) (a) (u : ℝ) :
    spins R d (g*boost a u)= spins R d g * eb R d a u := by
  let x (t : ℝ) := g*boost a t
  let Y t := spins R d (x t)
  let Z := eb R d a
  let E := rankAction R d (B a)
  have hv (t : ℝ) : HasDerivAt Y (Y t * E) t := by
    have hu : HasDerivAt (fun s => mat (x s)) (mat (x t)*B a) t := by
      simp_rw [x, mat_mul]
      rw [mul_assoc]
      exact (at_boost a t).const_mul (mat g)
    obtain ⟨_,X,_,he,hF⟩ := along_spins R d h x hu.differentiableAt
    have ht := he.unique hu
    have hh := congr_arg (mat (x t)⁻¹ * ·) ht
    rw [← mul_assoc _ _ X, ← mul_assoc _ _ (B a),mat_inv_mul,one_mul,one_mul] at hh
    rw [hh] at hF; exact hF
  let F (s : ℝ) := Y s*Z (-s)
  have hf (s : ℝ) : HasDerivAt F 0 s := by
    have he : HasDerivAt F ((Y s*E)*Z (-s) + Y s*(-(E*Z (-s)))) s :=
      deriv_mul (A:=FieldOp S d) (f:=Y) (g:=fun t => Z (-t)) _ _ (hv s)
        (neg_parameter _ _ s (eb_left R d a _))
    have hh {A : Type} [Ring A] (X Y Z : A) : X*Y*Z+X*(-(Y*Z))=0 := by rw [mul_assoc,mul_neg]; abel
    have hZ : Y s*E*Z (-s)+Y s*(-(E*Z (-s)))=0 := hh _ _ _
    rwa [hZ] at he
  have hh := const_deriv F hf u
  have hy : F 0 = spins R d g := by simp only [F,Y,Z,x, boost, Ray.boost_start,mul_one, neg_zero,eb_zero]
  change Y u=spins R d g * Z u
  rw [← hy,← hh, show F u=Y u*Z (-u) from rfl,mul_assoc, show Z (-u)*Z u=1 from eb_inv R d a u,mul_one]

lemma spins_mul (h : Spin.Port R H) (g k : Lorentz) : spins R d (g*k)=spins R d g * spins R d k := by
  conv_lhs => rw [← factors k]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, spatial_right R d h, boost_right R d h,
    boost_right R d h,boost_right R d h]
  change _ = _ * (eb _ _ _ _ * (eb _ _ _ _ * (eb _ _ _ _ * er _ _ _)))
  simp only [mul_assoc]

lemma spins_continuous (h : Spin.Port R H) : Continuous (spins R d) := by
  have hb (a) : Continuous (eb R d a) := continuous_iff_continuousAt.mpr fun x =>
    HasDerivAt.continuousAt (F:=FieldOp S d) (𝕜:=ℝ) (x:=x) (f := eb R d a) (f':= rankAction R d (B a)*eb R d a x)
      (eb_left R d a x)
  have hv : Continuous (er R d) := continuous_clm_apply.mpr (h.spin d)
  have he : Continuous b0 := rapidity_cont _
  have ht : Continuous b1 := (rapidity_cont _).comp (reduce_cont _)
  have hs : Continuous b2 := (rapidity_cont _).comp ((reduce_cont _).comp (reduce_cont _))
  exact ((hb 0).comp he).mul (((hb 1).comp ht).mul (((hb 2).comp hs).mul (hv.comp orientation_cont)))

end YM.Next.BOUNDARY.Descent
