import YM.Bid.Craft
import YM.Next.STATIONARY.Loops.UniformMatrix


set_option autoImplicit false
/-!
# Fixed radius complex contingency for an inverse. Supplies no accidental
matrix dimension. Track V1 because L2 alias norm identification uses
frequency-dependent NOT analytic weights. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {σ A a C D : ℝ}

def ground (p : Momentum) := axes fun i => (p i).re
lemma ground_real (p : Momentum) : star (ground p)=ground p := axes_real _
lemma ground_near {p : Momentum} (hp : p ∈ strip σ) : ‖p-ground p‖ < σ := by
  apply (pi_norm_lt_iff (by exact lt_of_le_of_lt (abs_nonneg _) (hp 0))).2
  intro i; have he : p i - ground p i=(p i).im * I := by
    change p i-(↑(p i).re:ℂ)=_
    linear_combination -(re_add_im (p i))
  simpa only [Pi.sub_apply,he,norm_mul,norm_real,I_mul_re,norm_I,mul_one,Real.norm_eq_abs] using hp i
lemma air_ride {p x : Momentum} (hp : star p=p) (he : x∈ball p σ) : x∈strip σ := by
  intro i; have h := norm_le_pi_norm (x-p) i
  rw [mem_ball,dist_eq_norm] at he
  have hh : ((x-p) i).im=(x i).im := by rw [Pi.sub_apply,sub_im, conj_eq_iff_im.mp (congr_fun hp i),sub_zero]
  exact hh ▸ (abs_im_le_norm _ |>.trans_lt (h.trans_lt he))

section complex
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {R C : ℝ} {x v y : X} {f : X→Y} (hR : 0 < R)
include hR
lemma chord (h : ∀ p ∈ ball x R, DifferentiableAt ℂ f p) (he : ∀ p∈ball x R, ‖f p‖≤ C) (hy : y∈ball x (R/2)) :
    ‖fderiv ℂ f y‖≤ C/(R/2) := by
  have hr : 0 < R/2 := half_pos hR
  have hC := le_trans (norm_nonneg _) (he x (mem_ball_self hR))
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC hr.le); intro u hu
  let G : ℂ→ X := fun t => y+t • u
  have hg : Differentiable ℂ G := by unfold G; fun_prop
  have hz (p : ℂ) (hp : p∈closedBall 0 (R/2)) : G p∈ ball x R := by
    rw [mem_closedBall,dist_zero_right] at hp; rw [mem_ball] at hy ⊢
    have hm : dist (G p) y=‖p‖ := by simp [G,dist_eq_norm,norm_smul,hu]
    linarith [dist_triangle (G p) y x]
  have hp (p : ℂ) (hw : p∈closedBall 0 (R/2)) : DifferentiableAt ℂ (f∘G) p := (h _ (hz p hw)).comp _ (hg p)
  have heq : G 0=y := by simp [G]
  have hd : HasDerivAt G u 0 := by simpa only [G,one_smul] using! (((hasDerivAt_id' (0:ℂ)).smul_const u).const_add y)
  have hv := (h _ (hz 0 (mem_closedBall_self hr.le))).hasFDerivAt.comp_hasDerivAt _ hd
  rw [heq] at hv; rw [← hv.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ⟨fun p hv => (hp p (ball_subset_closedBall hv)).differentiableWithinAt, fun p hv => (hp p (closure_ball_subset_closedBall hv)).continuousAt.continuousWithinAt⟩
    fun i hv => he _ (hz _ (sphere_subset_closedBall hv))
lemma contour_cost (hf : ∀ p∈ball x R,DifferentiableAt ℂ f p) (h : ∀ p∈ball x R, ‖f p‖ ≤ C) (hy : y∈ ball x (R/2)) :
    ‖f y-f x‖≤ C/(R/2) * ‖y-x‖ := by
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ ℂ X
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s:=ball x (R/2)) (fun i hi => hf i (ball_subset_ball (by linarith) hi))
    (fun i hi => chord hR hf h hi) (convex_ball ..) (mem_ball_self (half_pos hR)) hy

lemma contour_matrix {U : X → CompM α β} (hu : ∀ p ∈ ball x R,BillD U p) (H : ∀ p∈ ball x R,vflux (U p) ≤ A) (hp : y∈ball x (R/2)) :
    vflux (U y-U x)≤ A/(R/2)*‖y-x‖ := by
  have hz := (flux_nonneg _).trans (H x (mem_ball_self hR))
  apply flux_price (by positivity); intro a b
  rw [Matrix.sub_mulVec,dotProduct_sub]
  let G := fun p => dotProduct a (U p *ᵥ b)
  have he p (hp : p∈ball x R) : DifferentiableAt ℂ G p := DifferentiableAt.fun_sum fun i _ =>
    (DifferentiableAt.fun_sum fun j _ => (hu p hp i j).mul (differentiableAt_const _)).const_mul _
  have hv p (hp : p∈ball x R) : ‖G p‖≤ A*slug a*slug b := by
    exact (flux_pay ..).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (H p hp) (slug_nonneg _)) (slug_nonneg _))
  exact (contour_cost hR he hv hp).trans_eq (by ring)
end complex
end YM.Stationary
end

/-!
# Compare alias frames analytically using the REAL anchor R-tiltable templates.

`Height X` must equal X on the same real part, for horizontal movements it
compares Slug both ways (may cost up to σ-order but L-uniform). Take inverse
λ pricing with exact order thresholds. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators
variable {ι α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {σ η C A B D a : ℝ} {p q r : Momentum}
section simple
-- gap in row op. Also suffices for free inversion on center.
variable {U V : CompM α α}
def Stable (X : CompM α α) (b : ℝ) := ∀ i : Phase α,b*slug i ≤ slug (X*ᵥ i)
lemma Stable.mono (h : Stable U A) (he : a≤A) : Stable U a := fun i => (mul_le_mul_of_nonneg_right he (slug_nonneg i)).trans (h i)
lemma Stable.safe (h : Stable U a) (he : 0<a) : IsUnit U.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]; intro v w hp
  have hx := h (v-w); rw [mulVec_sub,hp,sub_self,slug_zero] at hx
  by_contra! hn; exact (not_lt_of_ge hx) (mul_pos he (slug_pos (sub_ne_zero_of_ne hn)))
lemma Stable.bill (h : Stable U a) (he : 0<a) : vflux U⁻¹≤ a⁻¹ := by
  apply flux_take (by positivity) _
  intro i; have H := h (U⁻¹ *ᵥ i); rw [mulVec_mulVec,mul_nonsing_inv _ (h.safe he), one_mulVec] at H
  rw [← div_eq_inv_mul]; exact (le_div_iff₀ he).2 ((mul_comm ..).trans_le H)
lemma Stable.cove (h : Stable U A) (he : vflux (V-U)≤C) : Stable V (A-C) := by
  intro i; have hp := flux_tester he i
  have hh := slug_neg ((V-U)*ᵥ i)
  have hx : slug (U*ᵥ i)≤ slug (V*ᵥ i)+slug ((V-U)*ᵥ i) := by
    rw [← hh]; refine (Eq.trans_le ?_ (slug_plus ..)); congr 1; rw [Matrix.sub_mulVec]; abel
  rw [sub_mul]; linarith [h i]
lemma stable_real (h : ∀ i : Phase α, A*slug i^2 ≤ (dotProduct (star i) (U*ᵥ i)).re) : Stable U A := by
  intro i; by_cases hp : i=0
  · rw [hp,mulVec_zero,slug_zero,mul_zero]
  have ht := slug_pos hp; have he := (h i).trans ((re_le_norm _).trans (slug_dot _ _)); rw [slug_star] at he; nlinarith
end simple

namespace Slab
/-- Tiltable analytic neighborhood via anchors. `lab x` fixed x works at
anchor and at vertical out above anchor, for comparison at other values in
ball it FITS with uniform charge. -/
structure Height (X : Slab α) (σ C : ℝ) : Prop where
  feel (x : Momentum) (he : star x=x) : ∃ Y : Slab α,
    (∀ i∈ball x σ,BillD Y.tile i) ∧ (∀ i, ground i=x → Y.tile i=X.tile i) ∧ ∀ p ∈ball x σ,
      serial X Y p p 1 C ∧ serial Y X p p 1 C
lemma Height.mono {X : Slab α} (h : Height X σ C) (he : η≤σ) (hp : C≤A) : Height X η A := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨Y,h1,h2,h3⟩ := h.feel x hx
  exact ⟨Y,fun _ hi => h1 _ (ball_subset_ball he hi), h2, fun _ hi =>
    ⟨(h3 _ (ball_subset_ball he hi)).1.mono hp,(h3 _ (ball_subset_ball he hi)).2.mono hp⟩⟩
lemma Height.basic : Height (Slab.basic α) σ 1 := ⟨fun x hx => ⟨_, fun _ _ => BillD.park _ (1:CompM α α),fun _ _ => rfl,fun _ _ => ⟨serial.free,serial.free⟩⟩⟩
lemma Height.dual {X : Slab α} (h : Height X σ C) : Height X.dual σ C := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨Y,h1,h2,h3⟩ := h.feel (-x) (by rw [star_neg,hx])
  have he (p) (hp : p∈ball x σ) : -p ∈ ball (-x) σ := by simpa using hp
  refine ⟨Y.dual,fun p hp => ?_,fun p hp => ?_,fun p hp => ?_⟩
  · exact BillD.take ((BillD.enter (f:=fun p => -p) (h1 (-p) (he _ hp)) (by fun_prop)).spot) (by change IsUnit ((Y.tile (-p))ᵀ).det; rw [det_transpose]; exact Y.whole _)
  · have hh : ground (-p)=-x := by rw [← hp]; funext j; simp [ground,axes]
    simp only [Slab.dual, h2 _ hh]
  have hp' := h3 _ (he p hp)
  simpa only [neg_neg, Matrix.transpose_one] using And.intro (hp'.2.slide) (hp'.1.slide)
end Slab

section budget
variable (σ A C a : ℝ) (hs : 0<σ) (he : 0≤A) (hp : 0≤C) (ha : 0<a)
include hs hp he ha
lemma shelter :
    ∃ η D : ℝ, 0<η ∧ η≤σ ∧ 0≤D ∧ ∀ (α : Type) [Fintype α] [DecidableEq α]
    (X Y : Slab α) (HX : X.Height σ C) (HY : Y.Height σ C)
    (K : Momentum→CompM α α), Poster σ K → (∀ p∈strip σ, serial X Y p p (K p) A) →
      (∀ p : Momentum, star p=p → Stable (carryM X Y p p (K p)) a) → Freezer X Y K η D := by
  let k := C*A*C/(σ/2)
  have hk : 0 ≤ k := by unfold k; positivity
  let i := σ/2
  let j := a/2 / (1+k)
  have hv : 0 < a/2 := half_pos ha
  have hh : 0 < 1+k := by linarith
  refine ⟨min i j,(a/2)⁻¹,lt_min (half_pos hs) (div_pos hv hh),(min_le_left ..).trans (half_le_self hs.le),inv_nonneg.mpr hv.le, ?_⟩
  intro α _ _ X Y HX HY K hz hg hl
  have hq p (hq : p∈strip (min i j)) : Stable (carryM X Y p p (K p)) (a/2) := by
    let x := ground p
    have hp' := ground_near hq
    have hr : p∈ ball x i := by rw [mem_ball,dist_eq_norm]; exact hp'.trans_le (min_le_left ..)
    have hx := ground_real p
    obtain ⟨P,h1,h2,h3⟩ := HX.feel x hx
    obtain ⟨T,g1,g2,g3⟩ := HY.feel x hx
    let Q := fun z => carryM P T z z (K z)
    have hw z (hw : z∈ ball x σ) : vflux (Q z)≤ C*A*C := by
      have hi := ((h3 z hw).2.bond (hg z (air_ride hx hw))).bond (g3 z hw).1
      rwa [Matrix.one_mul, Matrix.mul_one] at hi
    have hL z (hW : z∈ball x σ) : BillD Q z := ((BillD.take (h1 z hW) (P.whole z)).bond (hz.shape (air_ride hx hW))).bond (g1 z hW)
    have hU : Q x=carryM X Y x x (K x) := by
      unfold Q carryM; rw [h2 x (axes_of_real hx), g2 x (axes_of_real hx)]
    have hV : Q p=carryM X Y p p (K p) := by unfold Q carryM; rw [h2 p rfl, g2 p rfl]
    rw [← hV]; apply Stable.mono (Stable.cove (U:=Q x) (hU.symm ▸ hl x hx) (contour_matrix hs hL hw hr))
    have hh' : k * ‖p-x‖ ≤ a/2 := calc
      _ ≤ (1+k)*j := mul_le_mul (by linarith) (hp'.trans_le (min_le_right ..)).le (norm_nonneg _) hh.le
      _ = _ := by unfold j; field_simp
    change a/2 ≤ a-k*_; linarith
  refine ⟨fun p hx=> (carryM_solid _).1 ((hq p hx).safe hv), fun p hx => ?_⟩
  unfold serial; rw [carryM_back']; exact (hq p hx).bill hv
end budget
end YM.Stationary
end

/-!
# Tiltable alias weight. Slope stone is analytic symbol d*d; `shadeK` also
works on complex contours but is NOT analytic. Explicit Bravais side μ.
Momentum arc-budget respects period jumps (including tilt at face endpoints). -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {L : Side} {σ A : ℝ} {p q r : Momentum}

def inch (L : Side) := (L.val:ℝ)⁻¹
theorem inch_pos (L : Side) : 0< inch L := by unfold inch; positivity
lemma inch_unit (L : Side) : inch L*(L.val:ℝ)=1 := inv_mul_cancel₀ (by exact_mod_cast L.property.ne')
lemma inch_le (L : Side) : inch L ≤ 1 := by unfold inch; exact inv_le_one_of_one_le₀ (by exact_mod_cast L.property)
lemma strip_unit {p : Momentum} (hp : star p=p) (i : Axis) : (((p i).re:ℂ))=p i := congr_fun (axes_of_real hp) i

def stone (p : Momentum) : ℂ := dotProduct (Exterior.q (-p)) (Exterior.q p)
def shadeK (p : Momentum) := slug (Exterior.q (ground p))
def pebWeight (p : Momentum) (μ : ℝ) := (shadeK p)^2+μ^2

theorem peb_pos (p) {μ : ℝ} (h : 0<μ) : 0<pebWeight p μ := by unfold pebWeight; positivity
lemma quanta (hp : star p=p) : Exterior.q (-p)=star (Exterior.q p) := by
  funext i
  have he := mode_adjoint p (step i)
  rw [hp,mode_opposite] at he
  have ht i k : Exterior.q i k= mode i (step k)-1 := by unfold Exterior.q; rw [factor]
  rw [ht,Pi.star_apply,ht,star_sub,he,mode_inverse,star_one]
lemma stone_real (hp : star p=p) : stone p=((shadeK p)^2:ℝ) := by unfold stone shadeK; rw [quanta hp, slug_self, show ground p=p from axes_of_real hp]
lemma roll_ground (hp : rolls p q) : rolls (ground p) (ground q) := by
  obtain ⟨k,rfl⟩ := hp; refine ⟨k,?_⟩; funext i; simp [ground,axes,reciprocal]
lemma ground_neg_at (p : Momentum) : ground (-p)=-ground p := by funext; simp [ground,axes]
lemma ground_same_re (p : Momentum) (i : Axis) : (ground p i).re=(p i).re := rfl
lemma shadeK_round (hp : rolls p q) : shadeK p=shadeK q := by
  unfold shadeK; congr 1; ext1 i; unfold Exterior.q; rw [← factor,← factor,(roll_ground hp).exp]
lemma shadeK_neg : shadeK (-p)=shadeK p := by unfold shadeK; rw [ground_neg_at,quanta (ground_real p), slug_star]

lemma alias_discount (p : Momentum) (l : Site L) : aliasAt p l=(inch L:ℂ) • (p+reciprocal (lift l)) := by simp [inch,aliasAt,mon, smul_add]
lemma alias_re (p : Momentum) (l : Site L) (i) : (aliasAt p l i).re=inch L*((p i).re+ 2*Real.pi*lift l i) := by
  rw [alias_discount]; simp [reciprocal]
lemma alias_ground (p : Momentum) (l : Site L) : ground (aliasAt p l)=aliasAt (ground p) l := by
  funext i; rw [← strip_unit (p:=aliasAt (ground p) l) (by rw [← alias_conj,ground_real])]
  change (((aliasAt p l i).re:ℂ))=_; rw [alias_re,alias_re,ground_same_re]
lemma alias_roll (p : Momentum) (k : Cover) (l : Site L) : rolls (aliasAt (p+reciprocal k) l) (aliasAt p (l+wrap _ k)) := by
  apply rolls_of_mode; intro x
  have he x : mode ((L.val:ℂ)⁻¹ • reciprocal k) x = mode (mon (wrap L k)) x := by
    obtain ⟨i,hi⟩ := Bloch.cover_of_eq (lift (wrap L k)) k (wrap_lift _)
    rw [show (L.val:ℂ)⁻¹ • reciprocal k=mon (wrap L k)+reciprocal i by
      ext1 j; conv_lhs => rw [hi]
      simp only [mon,reciprocal,Pi.smul_apply,Pi.add_apply,smul_eq_mul,Pi.mul_apply,Pi.natCast_apply,nsmul_eq_mul,Int.cast_add,Int.cast_mul, Int.cast_natCast]
      field_simp [side_ne],mode_phase,mode_periodic,mul_one]
  simp only [aliasAt,smul_add,mode_phase,he]; rw [← cell_wrap (l+_),cell_duality (_+_),cell_add]
  rw [cell_duality _ l,cell_duality (wrap L x),cell_wrap, cell_wrap]; ring
lemma alias_counter (p : Momentum) (l : Site L) : rolls (aliasAt (-p) (-l)) (-aliasAt p l) := by
  unfold aliasAt; rw [smul_neg,neg_add]; refine (rolls.plus (rolls.refl _) ((rolls.refl _).flip_sign))

lemma q_le_real (h : star p=p) (i) : ‖Exterior.q p i‖ ≤ |(p i).re| := by have he := Real.norm_exp_I_mul_ofReal_sub_one_le (x:=(p i).re); rw [strip_unit h] at he; exact he
lemma real_q_lower (h : star p=p) (i) (he : |(p i).re| ≤ Real.pi) : (2:ℝ)/Real.pi*|(p i).re| ≤ ‖Exterior.q p i‖ := by
  let x := (p i).re
  unfold Exterior.q; nth_rewrite 2 [← strip_unit h i]; rw [Complex.norm_exp_I_mul_ofReal_sub_one]; norm_num
  have hd : |x/2|=|x|/2 := by norm_num [abs_div]
  have hh := Real.mul_abs_le_abs_sin (x:=x/2) (hd.trans_le (div_le_div_of_nonneg_right he (by norm_num : (0:ℝ) ≤ 2)))
  rw [hd] at hh
  change 2/Real.pi* |x| ≤ _; unfold x at *; linarith
end YM.Stationary
end

/-!
# Principal vs high aliases. Includes reflected points at faces.
`ground` projection only in analytic bounds. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {L : Side} {p q : Momentum}
def Nave (p : Momentum) : Prop := ∀ i, |(p i).re|≤ Real.pi
lemma Nave.roll (p : Momentum) : ∃ x, Nave x ∧ rolls x p := by
  let v : Cover := fun i => ⌊((p i).re + Real.pi)/(2*Real.pi)⌋
  refine ⟨p-reciprocal v, fun i => ?_,⟨v,by rw [sub_add_cancel]⟩⟩
  let x := (p i).re
  have he : 0<2*Real.pi := by positivity
  have hp : (v i:ℝ)≤(x+Real.pi)/(2*Real.pi) := Int.floor_le _
  have hx : (x+Real.pi)/(2*Real.pi)<(v i:ℝ)+1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ he] at hp; rw [div_lt_iff₀ he] at hx
  rw [Pi.sub_apply,Complex.sub_re,reciprocal]; norm_num
  unfold x at *; rw [abs_le]; constructor <;> linarith
lemma plank (l : Site L) (h : Odd L.val) (i) : (2:ℝ)*|((lift l i:ℤ):ℝ)| ≤ L.val-1 := by
  obtain ⟨k,hk⟩ := h
  have he := lift_centers l i
  rw [← Int.cast_abs]; exact_mod_cast (show 2*|lift l i| ≤ (L.val:ℤ)-1 by cases le_total (0:ℤ) (lift l i) <;> rename_i u <;> first | rw [abs_of_nonneg u]; omega | rw [abs_of_nonpos u]; omega)

lemma Nave.alias (h : Nave p) (l : Site L) (hp : Odd L.val) : Nave (aliasAt p l) := by
  intro i; rw [alias_re,abs_mul,abs_of_pos (inch_pos _)]
  calc
   _ ≤ inch L*(Real.pi+|(2:ℝ)*Real.pi*lift l i|) := by apply mul_le_mul_of_nonneg_left _ (inch_pos _).le; exact (abs_add_le ..).trans (add_le_add_left (h i) _)
   _ ≤ inch L*(Real.pi+Real.pi*(L.val-1:ℝ)) := by
     simp only [abs_mul,Nat.abs_ofNat,abs_of_pos Real.pi_pos]; apply mul_le_mul_of_nonneg_left _ (inch_pos _).le; have h := plank l hp i; nlinarith [Real.pi_pos]
   _ = _ := by rw [show Real.pi+Real.pi*(L.val-1:ℝ)=(L.val:ℝ)*Real.pi by ring,← mul_assoc,inch_unit,one_mul]
lemma Nave.preview (h : Nave p) : shadeK (aliasAt p (0:Site L)) ≤ 2*Real.pi*inch L := by
  let x := aliasAt p (0:Site L)
  have hh (i : Axis) : ‖Exterior.q (ground x) i‖ ≤ Real.pi*inch L := by
    trans |(x i).re|
    · exact q_le_real (ground_real _) i
    unfold x; simp only [alias_re]; rw [show lift (0: Site L) i=0 by simp [Lattice.lift]]; simp [abs_of_pos (inch_pos L),mul_comm _ (inch L)]
    exact mul_le_mul_of_nonneg_left (h i) (inch_pos L).le
  have hz : shadeK x^2≤ ∑ _ : Axis, (Real.pi*inch L)^2 := by unfold shadeK; rw [slug_sq]; exact sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hh i) _
  apply (pow_le_pow_iff_left₀ (slug_nonneg _) (mul_nonneg (by positivity) (inch_pos _).le) (by decide : 2≠0)).1
  exact hz.trans (by simp; linarith)

lemma pdist_pos {l : Site L} (hl : l≠0) : 0 < pdist l := by
  apply Nat.pos_of_ne_zero; intro hp
  apply hl
  rw [← wrap_lift l]; apply Eq.trans ?_ (map_zero (wrap L)); apply congr_arg _
  ext1 i; have he := component_le l i; rw [hp,Nat.le_zero] at he; exact Int.natAbs_eq_zero.mp he
lemma Nave.heights (h : Nave p) {l : Site L} (hl : l≠0) (hp : Odd L.val) : 2*inch L * pdist l ≤ shadeK (aliasAt p l) := by
  obtain ⟨i,hi,H⟩ := Finset.exists_mem_eq_sup _ univ_nonempty (fun i => (lift l i).natAbs)
  have He : pdist l=(lift l i).natAbs := H
  let K := aliasAt p l
  have hv := real_q_lower (ground_real K) i (h.alias l hp i)
  have hz : (1:ℝ) ≤ pdist l := by exact_mod_cast pdist_pos hl
  apply le_trans ?_ (hv.trans (slug_atom ..))
  rw [ground_same_re]; unfold K; rw [alias_re, abs_mul,abs_of_pos (inch_pos _)]
  have hh : |((lift l i:ℤ) : ℝ)|=pdist l := by simp [He,← Int.cast_abs]
  have hx : -(Real.pi)+(2*Real.pi)*pdist l ≤ |(p i).re+2*Real.pi*lift l i| := by
    have ha := abs_add_le (- (p i).re) ((p i).re+2*Real.pi*lift l i)
    rw [neg_add_cancel_left,abs_mul,hh,abs_of_pos (by positivity : 0<2*Real.pi),abs_neg] at ha
    linarith [h i]
  have hb : Real.pi*(pdist l)≤|(p i).re+2*Real.pi*lift l i| := le_trans (by nlinarith [Real.pi_pos]) hx
  calc
   _ = (2:ℝ)/Real.pi * (inch L*(Real.pi*(pdist l))) := by field_simp
   _ ≤ _ := by have he := inch_pos L; gcongr
end YM.Stationary
end

/-!
# Coarse horizontal and imaginary budgets on alias square. Link+site form
uses slope W; lift as analytic family at real anchor later. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex Metric
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {L : Side} {p r : Momentum} {μ η : ℝ}
lemma q_seat (h : star p=p) (i : Axis) :
    Exterior.q r i - Exterior.q p i = mode p (step i) * (exp (Complex.I * (r-p) i)-1) := by
  rw [factor]; unfold Exterior.q; rw [sub_sub_sub_cancel_right, mul_sub,mul_one, ← Complex.exp_add]; simp [mul_sub]
lemma q_drift (h : star p=p) (he : ‖r-p‖ ≤ 1) (i : Axis) : ‖Exterior.q r i - Exterior.q p i‖ ≤ 2 * ‖r-p‖ := by
  let v := r-p
  have hv := norm_le_pi_norm v i
  rw [q_seat h,norm_mul, mode_real p (step i) h,one_mul]
  have hp : ‖I*v i‖=‖v i‖ := by rw [norm_mul,norm_I,one_mul]
  exact (norm_exp_sub_one_le (x:=I*v i) (hp.trans_le (hv.trans he))).trans (by rw [hp]; exact mul_le_mul_of_nonneg_left hv zero_le_two)
lemma qCost (h : star p=p) (hr : ‖r-p‖≤1) : slug (Exterior.q r-Exterior.q p) ≤ 4* ‖r-p‖ := by
  apply (pow_le_pow_iff_left₀ (slug_nonneg _) (by positivity : 0≤4*‖r-p‖) (by decide : 2 ≠ 0)).mp
  rw [slug_sq]; calc
    _ ≤ ∑ _ : Axis, (2*‖r-p‖)^2 := sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (q_drift h hr i) _
    _ = _ := by simp; ring
lemma ground_distance (p r : Momentum) : ‖ground p-ground r‖≤ ‖p-r‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]; intro i
  have hp : ((ground p-ground r) i)=↑(((p-r) i).re) := by simp [ground,axes]
  rw [hp,norm_real, Real.norm_eq_abs]; exact (abs_re_le_norm _).trans (norm_le_pi_norm _ _)
lemma ground_up (p : Momentum) : ground (ground p)=ground p := axes_of_real (ground_real p)

private lemma walk_party (p r : Momentum) (l : Site L) :
    ‖aliasAt p l-aliasAt r l‖=inch L* ‖p-r‖ := by
  simp only [alias_discount, ← smul_sub, add_sub_add_right_eq_sub]; rw [norm_smul,norm_real,Real.norm_eq_abs,abs_of_pos (inch_pos _)]

lemma tilt_feet (l : Site L) (h : ‖p-r‖≤1) : shadeK (aliasAt p l) ≤ shadeK (aliasAt r l)+4*inch L := by
  let a := ground (aliasAt r l)
  let b := ground (aliasAt p l)
  have he : ‖b-a‖≤ inch L := by
    unfold b a; rw [alias_ground,alias_ground,walk_party]; exact mul_le_of_le_one_right (inch_pos L).le ((ground_distance _ _).trans h)
  have hh := qCost (p:=a) (r:=b) (ground_real _) (he.trans (inch_le L))
  have ht : Exterior.q b = Exterior.q a+(Exterior.q b-Exterior.q a) := by rw [add_sub_cancel]
  change slug (Exterior.q b)≤ slug (Exterior.q a)+_
  rw [ht]
  exact (slug_plus ..).trans (by linarith)

/-- budget uses sqrt directly. -/
def hill (p : Momentum) (l : Site L) := Real.sqrt (pebWeight (aliasAt p l) (inch L))
lemma hill_pos (p : Momentum) (l : Site L) : 0<hill p l := Real.sqrt_pos.2 (peb_pos _ (inch_pos L))
lemma hill_sq (p : Momentum) (l : Site L) : hill p l^2= shadeK (aliasAt p l)^2+inch L^2 := Real.sq_sqrt (peb_pos _ (inch_pos _)).le
lemma hill_inch (p : Momentum) (l : Site L) : inch L≤hill p l := by nlinarith only [inch_pos L,hill_sq p l,hill_pos p l,sq_nonneg (shadeK (aliasAt p l))]
lemma hill_q (p : Momentum) (l : Site L) : shadeK (aliasAt p l)≤hill p l := by nlinarith only [hill_pos p l,hill_sq p l,sq_nonneg (inch L)]
lemma hill_move (l : Site L) (h : ‖p-r‖ ≤ 1) : hill p l≤6*hill r l := by
  have ht : 0≤shadeK (aliasAt p l) := slug_nonneg _
  have hx : hill p l ≤ shadeK (aliasAt p l)+inch L := by nlinarith only [ht,hill_sq p l,hill_pos p l,inch_pos L]
  have H := tilt_feet l h; linarith [hill_inch r l,hill_q r l]
lemma hill_rel p (l : Site L) : hill (ground p) l=hill p l := by unfold hill pebWeight shadeK; rw [← alias_ground,ground_up]
lemma hill_turn p (l : Site L) : hill (-p) (-l)=hill p l := by unfold hill pebWeight; rw [shadeK_round (alias_counter p l),shadeK_neg]
lemma hill_wrap p (x : Cover) (l : Site L) : hill (p+reciprocal x) l=hill p (l+wrap _ x) := by unfold hill pebWeight; rw [shadeK_round (alias_roll p x l)]
-- complex q: budget tilt
lemma hill_tilt (l : Site L) (h : p∈strip 1) : slug (Exterior.q (aliasAt p l)) ≤ 5*hill p l := by
  let K := aliasAt p l
  have hz : ‖K-ground K‖≤ inch L := by unfold K; rw [alias_ground,walk_party]; exact mul_le_of_le_one_right (inch_pos _).le (ground_near h).le
  have hm : slug (Exterior.q K)≤slug (Exterior.q (ground K))+slug (Exterior.q K-Exterior.q (ground K)) := by
    simpa only [add_sub_cancel] using slug_plus (Exterior.q (ground K)) (Exterior.q K-Exterior.q (ground K))
  have hu := qCost (ground_real K) (hz.trans (inch_le L)); have hp : slug (Exterior.q (ground K))≤hill p l := hill_q p l
  change slug (Exterior.q K) ≤ _; linarith [hill_inch p l]
end YM.Stationary
end

/-!
# Tiler frames on physical-cell reads. Unit depth gauge in alias coords;
orientation pair P and P^dual, `-q` not conflated with conjugate.
-/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {L : Side} {p r : Momentum} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {σ C D : ℝ}

section unit
structure Skates (U : CompM α α) : Prop where
  slides : Uᴴ * U=1
namespace Skates
variable {U V : CompM α α}
lemma is_unit (h : Skates U) : IsUnit U.det := by rw [← Matrix.isUnit_iff_isUnit_det]; exact ⟨⟨U,_,mul_eq_one_comm.mp h.slides,h.slides⟩,rfl⟩
lemma reverse (h : Skates U) : U⁻¹=Uᴴ := by
  rw [show Uᴴ=Uᴴ*(U*U⁻¹) by rw [mul_nonsing_inv U h.is_unit,mul_one], ← mul_assoc,h.slides,one_mul]
lemma back (h : Skates U) : Skates U⁻¹ := by
  rw [h.reverse]; constructor; rw [conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp h.slides
lemma bond (h : Skates U) (hp : Skates V) : Skates (U*V) := by constructor; rw [conjTranspose_mul,mul_assoc, ← mul_assoc Uᴴ,h.slides,one_mul,hp.slides]
lemma lives (h : Skates U) (x : Phase α) : slug (U*ᵥ x)=slug x := by
  refine (sq_eq_sq₀ (slug_nonneg _) (slug_nonneg _)).mp (Complex.ofReal_injective ?_)
  rw [← slug_self,← slug_self,star_mulVec,dotProduct_mulVec]
  rw [Matrix.vecMul_vecMul,h.slides,Matrix.vecMul_one]
lemma pays (h : Skates U) : vflux U≤1 := flux_take zero_le_one _ fun x => by rw [h.lives,one_mul]
lemma slide_u (h : Skates U) (W : CompM α β) : vflux (U*W)=vflux W := by
  apply le_antisymm ((flux_power ..).trans ((mul_le_mul_of_nonneg_right h.pays (flux_nonneg _)).trans_eq (one_mul _)))
  have hp := flux_power U⁻¹ (U*W)
  rw [← Matrix.mul_assoc,nonsing_inv_mul _ h.is_unit,Matrix.one_mul] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_right h.back.pays (flux_nonneg _)).trans_eq (one_mul _))
lemma slide_v (h : Skates U) (W : CompM β α) : vflux (W*U)=vflux W := by
  apply le_antisymm ((flux_power ..).trans ((mul_le_mul_of_nonneg_left h.pays (flux_nonneg _)).trans_eq (mul_one _)))
  have hp := flux_power (W*U) U⁻¹; rw [Matrix.mul_assoc,mul_nonsing_inv _ h.is_unit,Matrix.mul_one] at hp
  exact hp.trans ((mul_le_mul_of_nonneg_left h.back.pays (flux_nonneg _)).trans_eq (mul_one _))
end Skates
end unit

def plankTile (L : Side) (α : Type) [DecidableEq α] (p : Momentum) : CompM (Co L α) (Co L α) := (inch L:ℂ)^2 • aliasBlock L α p
def counterTile (L : Side) (α : Type) [DecidableEq α] (p : Momentum) := (inch L:ℂ)^2 • returned (aliasBlock L α) p
lemma alias_palm (p : Momentum) : counterTile L α p*plankTile L α p=1 := by
  unfold counterTile plankTile; rw [Matrix.smul_mul,Matrix.mul_smul,straightens, smul_smul,smul_smul]
  rw [mul_assoc,show (inch L:ℂ)^2 * ((inch L:ℂ)^2 * (L.val:ℂ)^4)=1 by
    unfold inch; push_cast; field_simp [side_ne L],one_smul]
lemma tile_solid (p : Momentum) : IsUnit (plankTile L α p).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]; exact ⟨⟨_,_,mul_eq_one_comm.mp (alias_palm p),alias_palm p⟩,rfl⟩
lemma tile_back (p : Momentum) : (plankTile L α p)⁻¹=counterTile L α p := by
  rw [show counterTile L α p=counterTile L α p*(plankTile L α p *(plankTile L α p)⁻¹) by rw [mul_nonsing_inv _ (tile_solid p),mul_one], ← mul_assoc,alias_palm,one_mul]
lemma tile_ice (h : star p=p) : Skates (plankTile L α p) := by
  have ht := alias_palm (L:=L) (α:=α) p
  constructor; conv_lhs => lhs; simp only [plankTile,conjTranspose_smul,star_pow, Complex.star_def, conj_ofReal]
  simpa only [counterTile, returned, h] using ht
lemma tile_lit (p : Momentum) : BillD (plankTile L α) p := by
  intro i j
  change DifferentiableAt ℂ (fun p => (inch L:ℂ)^2 * (if i.2=j.2 then mode (aliasAt p j.1) (lift i.1) else 0)) _
  split; · unfold mode aliasAt; fun_prop
  exact differentiableAt_const _
section weights
variable (L α)
def spice (p : Momentum) (a : Co L α) := ((hill p a.1):ℂ)⁻¹
lemma spice_ne (p : Momentum) (a : Co L α) : spice L α p a ≠ 0 := inv_ne_zero (by exact_mod_cast (hill_pos p a.1).ne')

def contour (Y : Momentum→Momentum) : Slab (Co L α) where
  tile p := (plankTile L α p*diagonal (spice L α (Y p)))*(plankTile L α 0)⁻¹
  whole p := by
    simp only [Matrix.det_mul,Matrix.det_diagonal,Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact ((tile_solid _).mul ((prod_ne_zero_iff.mpr (fun i _ => spice_ne _ _ _ i)).isUnit)).mul (tile_solid _ |>.inv)

def altarTile := contour L α id
lemma winders (j : Momentum→Momentum) (p : Momentum) : ((contour L α j).tile p)⁻¹=(plankTile L α 0*diagonal ((spice L α (j p))⁻¹))*(plankTile L α p)⁻¹ := by
  let T := spice L α (j p)
  have hp : (diagonal T)⁻¹=diagonal (T⁻¹) := by
    have hz : diagonal T*diagonal (T⁻¹)=1 := by ext i k; by_cases h : i=k <;> simp [Matrix.diagonal_mul_diagonal,Matrix.diagonal_apply,Matrix.one_apply,h,T,spice_ne]
    exact inv_eq_right_inv hz
  change ((plankTile L α p * diagonal T) * (plankTile L α 0)⁻¹)⁻¹=_
  rw [Matrix.mul_inv_rev,Matrix.mul_inv_rev,Matrix.nonsing_inv_nonsing_inv _ (tile_solid _),hp,Matrix.mul_assoc]
lemma altar_range : Slab.Height (altarTile L α) 1 6 := by
  refine ⟨fun x hx => ?_⟩
  let P := fun _ : Momentum => x
  let G := contour L α P
  refine ⟨G,fun p hp => ?_,fun p hp => ?_,fun p hp => ?_⟩
  · exact BillD.bond (BillD.bond (tile_lit _) (BillD.park p (diagonal (spice L α x)))) (BillD.park p ((plankTile L α 0)⁻¹))
  · have hv : spice L α x=spice L α p := by funext a; unfold spice; rw [← hp,hill_rel]
    rw [show G.tile p=(plankTile L α p*diagonal (spice L α x))*(plankTile L α 0)⁻¹ from rfl,hv]; rfl
  have h0 := tile_ice (L:=L) (α:=α) (p:=0) (by simp)
  rw [Metric.mem_ball,dist_eq_norm] at hp
  have he (u v : Momentum→Momentum) (hv : ‖u p-v p‖ ≤ 1) : serial (contour L α u) (contour L α v) p p 1 6 := by
    unfold serial carryM; rw [Matrix.mul_one,winders]
    let U := plankTile L α p
    let T := plankTile L α 0
    let i := spice L α (u p); let j := spice L α (v p)
    change vflux (T*diagonal (i⁻¹)*U⁻¹*((U*diagonal j)*T⁻¹))≤6
    rw [← Matrix.mul_assoc (_*U⁻¹), ← Matrix.mul_assoc (_*U⁻¹), Matrix.mul_assoc (T*_), Matrix.nonsing_inv_mul U (tile_solid _),mul_one, h0.back.slide_v,Matrix.mul_assoc, h0.slide_u,diagonal_mul_diagonal, flux_diagonal]
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro b; have hh := hill_move b.1 hv
    have ht := hill_pos (u p) b.1; have hb := hill_pos (v p) b.1
    simp only [i,j,Pi.mul_apply,Pi.inv_apply,spice,inv_inv,norm_mul,norm_inv,norm_real,Real.norm_eq_abs,abs_of_pos ht, abs_of_pos hb]
    rw [← div_eq_mul_inv]; exact (div_le_iff₀ hb).2 hh
  exact ⟨he id P hp.le, he P id (by simpa [P,norm_sub_rev] using hp.le)⟩
end weights
end YM.Stationary
end

/-!
# Weights respect roll resets (all raw weights keep *same* convention)
and real dual for bilinear (not Hermitian outside real slice). Tilted tile
may be completed to V on real part; no volume factors. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Matrix Finset Complex
open scoped Matrix Topology ContDiff BigOperators ComplexConjugate
variable {L : Side} {p r u v : Momentum} {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {σ C D : ℝ}

structure Sheets (U V : CompM α α) : Prop where
  -- V relates U via Skater
  flee : ∃ Z : CompM α α, Skates Z ∧ U*Z=V
lemma Sheets.inv_rear {U V : CompM α α} (h : Sheets U V) : Sheets Uᵀ⁻¹ Vᵀ⁻¹ := by
  obtain ⟨Z,hZ,rfl⟩ := h.flee
  refine ⟨Zᵀ⁻¹,?_,?_⟩
  · apply Skates.back; constructor
    have hh := congr_arg Matrix.transpose (mul_eq_one_comm.mp hZ.slides)
    rw [transpose_mul,transpose_one] at hh; exact hh
  rw [transpose_mul,Matrix.mul_inv_rev]
lemma Sheets.contrast {U V P Q : CompM α α} (h : Sheets U V) (hv : Sheets P Q) {Y : CompM α α} (he : Stable (U⁻¹ *Y*P) C) : Stable (V⁻¹ *Y*Q) C := by
  obtain ⟨Z,hZ,rfl⟩ := h.flee; obtain ⟨W,hW,rfl⟩ := hv.flee
  intro i
  have hm := he (W *ᵥ i)
  rw [hW.lives] at hm
  rw [Matrix.mul_inv_rev,show Z⁻¹*U⁻¹*Y*(P*W)=Z⁻¹*((U⁻¹ *Y*P)*W) by simp only [Matrix.mul_assoc], ← Matrix.mulVec_mulVec, hZ.back.lives, ← Matrix.mulVec_mulVec]; exact hm
lemma Sheets.bill {X : Slab α} {Z : Slab β} (h : Sheets (X.tile p) (X.tile u)) (hv : Sheets (Z.tile r) (Z.tile v))
    (K : CompM α β) (he : serial X Z p r K C) : serial X Z u v K C := by
  obtain ⟨V,hV,hb⟩ := h.flee; obtain ⟨W,hW,ht⟩ := hv.flee
  unfold serial carryM; rw [← hb, ← ht,Matrix.mul_inv_rev,show V⁻¹ * _ * K* (Z.tile r*W) = V⁻¹*((X.tile p)⁻¹*K*Z.tile r)*W by simp only [Matrix.mul_assoc], hW.slide_v,hV.back.slide_u]; exact he

namespace Slab
structure Bright (X : Slab α) : Prop where
  pose {p q : Momentum} : rolls p q → Sheets (X.tile p) (X.tile q)
lemma Bright.basic : Bright (Slab.basic α) := ⟨fun h => ⟨1,⟨by simp⟩,by simp [Slab.basic]⟩⟩
lemma Bright.dual {X : Slab α} (h : Bright X) : Bright X.dual := ⟨fun hp => (h.pose hp.neg).inv_rear⟩
lemma Bright.stable {X Q : Slab α} (h : Bright X) (hq : Bright Q) (hv : rolls p u) {F : CompM α α} (he : Stable (carryM X Q p p F) C) : Stable (carryM X Q u u F) C := (h.pose hv).contrast (hq.pose hv) he
end Slab

lemma tile_perm (x : Cover) : Sheets ((altarTile L α).tile p) ((altarTile L α).tile (p+reciprocal x)) := by
  let t (p) := plankTile L α p * diagonal (spice L α p)
  let T := plankTile L α 0
  have hh : Skates T := tile_ice (by simp)
  let z := wrap L x
  let f : Equiv.Perm (Co L α) := Equiv.prodCongr (Equiv.addRight z) (Equiv.refl α)
  let M : CompM (Co L α) (Co L α) := submatrix 1 id f
  have hm : Skates M := by
    constructor; ext i j
    simp only [mul_apply,M,Matrix.submatrix_apply,conjTranspose_apply,id_eq]
    simp [Matrix.one_apply,ite_mul,mul_ite,apply_ite star]; simp only [eq_comm (a:=j) (b:=i)]
  have ht : t (p+reciprocal x)=t p*M := by
    ext i j; conv_rhs => rw [mul_apply]
    have he (a : Co L α) : M a j=(Pi.single (f j) 1:Phase (Co L α)) a := by simp [M,Pi.single_apply,Matrix.one_apply]
    simp_rw [he]; simp only [Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, t, Matrix.mul_diagonal, spice, plankTile,aliasBlock, Matrix.of_apply, Matrix.smul_apply, Equiv.prodCongr_apply,f,Equiv.refl_apply,id_eq,Prod.map_apply]
    rw [(alias_roll p x _).exp, hill_wrap]; rfl
  refine ⟨T*M*T⁻¹,(hh.bond hm).bond hh.back,?_⟩
  change t p*T⁻¹*(T*M*T⁻¹)=t _*T⁻¹
  rw [ht]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc T⁻¹,Matrix.nonsing_inv_mul T hh.is_unit,one_mul]

lemma altar_bright : Slab.Bright (altarTile L α) := ⟨by intro p q h; obtain ⟨x,rfl⟩ := h; exact tile_perm _⟩

private lemma pin_slot (h : star p=p) (x : Co L α) (l : Site L) (a : α) : plankTile L α (-p) x (-l,a) = star (plankTile L α p x (l,a)) := by
  unfold plankTile; simp only [aliasBlock, Matrix.smul_apply, of_apply]; split <;> rename_i he
  · rw [smul_eq_mul,smul_eq_mul, (alias_counter p l).exp,mode_inverse,star_mul,star_pow]
    have hi := mode_adjoint (aliasAt p l) (lift x.1); rw [← alias_conj, h, mode_opposite] at hi
    rw [hi, Complex.star_def, conj_ofReal,mul_comm]
  simp

lemma tiles_pair (h : star p=p) : ((altarTile L α).tile (-p))ᵀ=((altarTile L α).tile p)ᴴ := by
  let T := plankTile L α 0
  have ht : Skates T := tile_ice (by simp)
  have hx (l : Site L) (a : α) (x : Co L α) : T x (-l,a)=star (T x (l,a)) := by unfold T; simpa using pin_slot (by simp : star (0:Momentum)=0) x l a
  unfold altarTile contour; ext b c
  simp only [transpose_apply,conjTranspose_apply]
  change ((plankTile L α (-p) * diagonal (spice L α (-p))) * T⁻¹) c b=star (((plankTile L α p * diagonal (spice L α p))* T⁻¹) c b)
  rw [mul_apply, mul_apply,ht.reverse]; simp only [Matrix.mul_diagonal,star_sum,Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (Equiv.neg (Site L))]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [Equiv.neg_apply,id_eq, spice,pin_slot h,hill_turn,Matrix.conjTranspose_apply,hx,star_mul]
  rw [star_inv₀]; simp only [star_star,Complex.star_def, conj_ofReal]; ring
end YM.Stationary
end
