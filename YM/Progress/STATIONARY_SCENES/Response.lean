import YM.Next.BOUNDARY.Coordinates
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.FREE_KERNELS.Traffic
import YM.Next.SCHEDULE.Postal
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# Quantitative spending of the stationary scene

Show uniform localization of the TRUE linear
response of the nonlinear critical branches supplied here (every tree),
beyond the F04 ticket. Important because coming from a finite-period IFT
by itself would not even price the linear tangent uniformly in the period. A discrepancy from a coarse source at scaled distance kept in the row
weights (torus native fine-site max-distance over L). Pre-L price (including
the tree and rooted `psi` part for which this proof pays $C_J$, not $C_J/L$). Use accepted estimates on the concrete free horizons. Doesn't price higher
jet derivatives, claim measure influence or price every Laurent/higher admin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Progress.StationaryScenes

open Filter Lattice RG RG.Supply Wilson Precision Bid Tree Function Matrix Exterior Bloch Laurent
open YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

namespace Response
variable {G : Gauge} {c f : Side}

/-- Uniform geometric payments in the *fine* lattice. -/
lemma by_one (z : Site f) (b : Step) :
    separation z (z+b.vec) ≤ 1 ∧ separation z (b.used z).1 ≤ 1 := by
  have h : separation z (z+b.vec) ≤ 1 := by
    rw [separation_comm,separation, add_comm,add_sub_cancel_right, Step.vec]; split
    · rw [pdist_neg]; exact pdist_step _
    exact pdist_step _
  refine ⟨h,?_⟩
  unfold Step.used; split
  · next he => simpa [Step.vec,he,sub_eq_add_neg] using h
  simp

/-- Local integralLink bill on physical reads, increments counted in fine
units even if winding. Also usable for arbitrary tree hikes. -/
lemma integral_near (v : form 1 f) (x y : Site f) (w : Walk) (r : ℕ) (C : ℝ)
    (h : ∀ z : Body 1 f, separation x z.1 ≤ r → |v z| ≤ C)
    (hw : separation x y + w.length ≤ r) : |integralLink y w v| ≤ w.length*C := by
  induction w generalizing y with
  | nil => simp [integralLink,linkSum]
  | cons b l ih =>
    obtain ⟨hh,hg⟩ := by_one y b
    have hr := separation_triangle x y (y+b.vec)
    have ht := separation_triangle x y (b.used y).1
    have he := h ((b.used y).1,coord (b.used y).2) (show separation x (b.used y).1 ≤ r by
      rw [List.length_cons] at hw; omega)
    have hi := ih (y+b.vec) (show separation x (y+b.vec)+l.length ≤ r by
      rw [List.length_cons] at hw; omega)
    rw [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm (l.length*C) C]
    change |(if _ then _ else _) + integralLink _ l v| ≤ _
    refine (abs_add_le ..).trans (add_le_add ?_ hi); split
    · rw [abs_neg]; exact he
    exact he

section tree
variable (S : StepData c f)
local notation "L" => S.ratio.count.val
local notation "r₀" => S.patch.radius

lemma lengths (a b : S.patch.Points) (o : Lattice.Order) :
    (route a.val b.val o).length ≤ 8*r₀ := by
  have hf (l : List Axis) : (axisRoute a.val b.val l).length ≤ l.length*(2*r₀) := by
    induction l with
    | nil => simp [axisRoute]
    | cons x l ih =>
      rw [show axisRoute a.val b.val (x::l) = straight x (b.val x - a.val x) ++ axisRoute a.val b.val l from rfl,
        List.length_append,List.length_cons,Nat.add_mul, one_mul]
      obtain ⟨hl,hu⟩ := box_test.mp a.property
      obtain ⟨hl',hu'⟩ := box_test.mp b.property
      specialize hl x; specialize hu x; specialize hl' x; specialize hu' x
      rw [add_comm]
      refine Nat.add_le_add ih ?_
      unfold straight; rw [List.length_replicate]; omega
  apply le_trans (hf (allAxes o))
  simp [allAxes]; omega

/-- Footprint bound for `atPoint` paths. -/
lemma at_point (y : Site c) (z : S.patch.Points) :
    separation (S.ratio.embed y) (atPoint S y z) ≤ 4*r₀ := by
  rw [separation_comm,separation,atPoint,add_sub_cancel_right]
  apply le_trans (within_size z.val f)
  unfold size
  refine le_trans (b := ∑ _i : Axis, r₀) (Finset.sum_le_sum ?_) ?_
  · intro i _
    obtain ⟨hl,hr⟩ := box_test.mp z.property
    specialize hl i; specialize hr i; omega
  simp [Axis]

private lemma average {X : Type} [Fintype X] [Nonempty X] (a : X → ℝ) (C : ℝ)
    (h : ∀ i, |a i| ≤ C) : |(Fintype.card X : ℝ)⁻¹ * ∑ i, a i| ≤ C := by
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  have he : |∑ i, a i| ≤ Fintype.card X*C := by
    refine le_trans ((Finset.abs_sum_le_sum_abs ..).trans
      (Finset.sum_le_sum (g := fun _ => C) (fun i _ => h i))) ?_
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hf : 0 < (Fintype.card X : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (inv_mul_cancel_left₀ hf.ne' _)

/-- `ψ` bill (root of the actual Q). -/
lemma psi (v : form 1 f) (x : Site f) (y : Site c) (t : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ z : Body 1 f, separation x z.1 ≤ t → |v z| ≤ B)
    (hh : separation x (S.ratio.embed y) + 12*r₀ ≤ t) :
    |(fixRoot S *ᵥ v) (y,vac)| ≤ 16*r₀*B := by
  let M : ℝ := 8*r₀*B
  have ha (a : S.patch.Points) : |tau S y a v| ≤ M := by
    unfold tau
    simp only [LinearMap.smul_apply, LinearMap.neg_apply, LinearMap.sum_apply, smul_eq_mul, abs_neg]
    refine average _ _ fun b => average _ _ fun i => ?_
    have hf := at_point S y a
    have hl := lengths S a b i
    have hx := separation_triangle x (S.ratio.embed y) (atPoint S y a)
    refine (integral_near v x (atPoint S y a) _ t _ h (by omega)).trans ?_
    apply mul_le_mul_of_nonneg_right _ hB
    exact_mod_cast hl
  have he : |∑ b, S.patch.weight b * tau S y b v| ≤ M := by
    calc
      _ ≤ ∑ b, |S.patch.weight b * tau S y b v| := Finset.abs_sum_le_sum_abs ..
      _ ≤ ∑ b : S.patch.Points, S.patch.weight b * M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [abs_mul, abs_of_nonneg (S.patch.weight_nonneg b)]
        exact mul_le_mul_of_nonneg_left (ha b) (S.patch.weight_nonneg b)
      _ = M := by rw [← Finset.sum_mul,S.patch.weight_sum,one_mul]
  simp only [fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted,LinearMap.sub_apply,
    LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  refine le_trans ((abs_sub ..).trans (add_le_add (ha _) he)) (le_of_eq ?_)
  unfold M; ring

/-- Moving the fine origin of a cross-row weight. -/
lemma radius_cost {η : ℝ} (h : 0 ≤ η) (x z : Site f) (y : Site c) (t : ℕ)
    (hx : separation x z ≤ t*L) :
    crossW S.ratio η x y ≤ Real.exp (η*t)*crossW S.ratio η z y := by
  unfold crossW; rw [← Real.exp_add]; apply Real.exp_monotone
  have hh := (div_le_iff₀ (side_pos S.ratio.count)).2 (show (separation x z:ℝ) ≤ (t:ℝ)*L by exact_mod_cast hx)
  rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ h
  calc
    _ ≤ ((separation x z:ℝ)+ (separation z (S.ratio.embed y):ℝ))/(L:ℝ) := by
      refine div_le_div_of_nonneg_right ?_ (side_pos S.ratio.count).le
      exact_mod_cast separation_triangle x z (S.ratio.embed y)
    _ = _ := add_div ..
    _ ≤ _ := add_le_add hh le_rfl

/-- Use on sup-fields. Sign-field test below recovers AN ABSOLUTE row sum. -/
lemma start {η C : ℝ} {W : Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
    (h : 0 ≤ η) (hW : W.strip η (C/L)) (t : ℕ) (x : Site f) (v : form 1 c)
    (hv : ∀ y : Body 1 c, |v y| ≤ crossW S.ratio η x y.1) (z : Body 1 f) (ht : separation x z.1 ≤ t*L) :
    |(installed S.ratio W *ᵥ v) z| ≤ (Real.exp (η*t)*Real.exp η*(Fintype.card (TypeFace 1):ℝ)*C)/L := by
  unfold mulVec dotProduct
  apply le_trans (Finset.abs_sum_le_sum_abs ..)
  let B := Real.exp (η*t)
  calc
    _ ≤ ∑ y : Body 1 c, B*(crossW S.ratio η z.1 y.1*‖installed S.ratio W z y‖) := by
      refine Finset.sum_le_sum fun y _ => ?_
      rw [abs_mul, ← mul_assoc, Real.norm_eq_abs, mul_comm |installed S.ratio W z y|]
      exact mul_le_mul_of_nonneg_right ((hv y).trans (radius_cost S h x z.1 _ _ ht)) (abs_nonneg _)
    _ ≤ B*(Real.exp η*(Fintype.card (TypeFace 1)*(C/L))) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (cross_sprawl S.ratio h hW z) (Real.exp_pos _).le
    _ = _ := by unfold B; ring

/-- *Pre-L* straightening bill. -/
def steps (j : ℕ) : ℕ := 12*(j+3)+5

def advance (j : ℕ) (η C : ℝ) : ℝ :=
  Real.exp (η*(steps j))*Real.exp η*(Fintype.card (TypeFace 1):ℝ)*(max C 1)

def correction (j : ℕ) (η C : ℝ) : ℝ := (4+16*(j+3:ℝ))*advance j η C

def total (j : ℕ) (η C : ℝ) : ℝ := advance j η C + 2*correction j η C

lemma nonneg (j : ℕ) (η C : ℝ) : 0 ≤ advance j η C := by
  have h : 0 ≤ max C 1 := le_max_of_le_right (by norm_num)
  unfold advance; positivity

lemma local_pose {η C : ℝ} {W : Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
    (h : 0 ≤ η) (hW : W.strip η (C/L)) (x : Site f) (v : form 1 c)
    (hv : ∀ y : Body 1 c, |v y| ≤ crossW S.ratio η x y.1) (z : Body 1 f)
    (ht : separation x z.1 ≤ steps S.patch.J * L) :
    |(installed S.ratio W *ᵥ v) z| ≤ advance S.patch.J η C / L := by
  refine (start S h hW _ x _ hv z ht).trans ?_
  unfold advance; gcongr; exact le_max_left ..

/-- Uniform in the tree. Price in-arbor nodes near a probe; don't infer
that the A0 widths on mixed kernels persist on *fine lattice* units. -/
lemma straighten_price {η C : ℝ} {W : Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
    (h : 0 ≤ η) (hW : W.strip η (C/L)) (F : Forest S.ratio) (x z : Site f) (hx : separation x z ≤ 1)
    (v : form 1 c) (hv : ∀ y : Body 1 c, |v y| ≤ crossW S.ratio η x y.1) :
    |(straighten S F (installed S.ratio W) *ᵥ v) (z,vac)| ≤ correction S.patch.J η C := by
  let j := S.patch.J
  let V := installed S.ratio W *ᵥ v
  let B : ℝ := advance j η C / L
  let t := steps j * L
  have hL : 1 ≤ L := S.ratio.count.property
  have hR := side_pos S.ratio.count
  have hB : 0 ≤ B := div_nonneg (nonneg ..) hR.le
  have Hl : t = 12*r₀+5*L := by
    unfold t j steps RG.Patch.radius; rw [Nat.add_mul, Nat.mul_assoc]; rfl
  have HH z hz : |V z| ≤ B := local_pose S h hW x v hv z hz
  have hh : (F.hike z).length ≤ 4*L := (F.hike_lower _).trans (F.bound z)
  have hs := Corona.near S.ratio z
  have hz := separation_triangle x z (S.ratio.embed (S.ratio.parent z))
  have hg := psi S V x (S.ratio.parent z) t B hB HH (by omega)
  have he : |integralLink z (F.hike z) V| ≤ (4*L:ℝ)*B := by
    refine (integral_near V x z _ t B HH (by omega)).trans (mul_le_mul_of_nonneg_right ?_ hB)
    exact_mod_cast hh
  rw [books]
  apply le_trans ((abs_sub _ _).trans (add_le_add he hg)) (le_of_eq ?_)
  unfold B t V j at *
  unfold correction Patch.radius
  push_cast
  change (4* (L:ℝ) * _ + 16*(((S.patch.J:ℝ)+3)*(L:ℝ))*_) = _
  field_simp

lemma action_price {η C : ℝ} {W : Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
    (h : 0 ≤ η) (hW : W.strip η (C/L)) (F : Forest S.ratio) (x : Body 1 f) (v : form 1 c)
    (hv : ∀ y : Body 1 c, |v y| ≤ crossW S.ratio η x.1 y.1) :
    |(extracted S F (installed S.ratio W) *ᵥ v) x| ≤ total S.patch.J η C := by
  let j := S.patch.J
  obtain ⟨x,i⟩ := x
  obtain ⟨i,rfl⟩ := axisEquiv.surjective i
  have hG : |(installed S.ratio W *ᵥ v) (x,coord i)| ≤ advance j η C := by
    refine (local_pose S h hW x v hv (x,coord i) (by simp)).trans ?_
    have hu : 1 ≤ (L:ℝ) := by exact_mod_cast S.ratio.count.property
    exact div_le_self (nonneg ..) hu
  rw [extracted,Matrix.add_mulVec,Pi.add_apply,← Matrix.mulVec_mulVec]
  change |_ + (d 0 f *ᵥ _) (x,coord i)| ≤ _
  rw [d_sites]
  have ha := straighten_price S h hW F x (x+step i) (by_one x (posDir i)).1 v hv
  have hb := straighten_price S h hW F x x (by simp) v hv
  apply le_trans ((abs_add_le ..).trans (add_le_add hG ((abs_sub ..).trans (add_le_add ha hb))))
  rw [total,two_mul]

/-- Weighted *absolute* kernel rows at the unaltered periodization,
pre-L rate/payment. -/
theorem response_price {η C : ℝ} {W : Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
    (h : 0 ≤ η) (hW : W.strip η (C/L)) (F : Forest S.ratio) (x : Body 1 f) :
    ∑ y : Body 1 c, crossW S.ratio η x.1 y.1 * ‖extracted S F (installed S.ratio W) x y‖ ≤ total S.patch.J η C := by
  let w y := crossW S.ratio η x.1 y
  let A := extracted S F (installed S.ratio W)
  let v (y : Body 1 c) := if 0 ≤ A x y then w y.1 else -w y.1
  have hv (y : Body 1 c) : |v y| ≤ w y.1 := by
    have h : 0 ≤ w y.1 := (Real.exp_pos _).le
    unfold v; split
    · rw [abs_of_nonneg h]
    · rw [abs_neg,abs_of_nonneg h]
  have hh := action_price S h hW F x v hv
  have he : (A *ᵥ v) x = ∑ y : Body 1 c, w y.1*‖A x y‖ := by
    apply Finset.sum_congr rfl; intro y _
    unfold v; split
    · rename_i hi; rw [Real.norm_eq_abs, abs_of_nonneg hi, mul_comm]
    rename_i hi; rw [Real.norm_eq_abs, abs_of_neg (not_le.mp hi), mul_neg, mul_neg,mul_comm]
  rw [← he]; exact (le_abs_self _).trans hh

/-- Costs a copy subtraction: measure vertical motion in **relative**
coordinates. Weight in coarse distances at the root scales. -/
lemma tangent_apply {η C : ℝ} {W : Cross S.ratio.count (TypeFace 1) (TypeFace 1)}
    (h : 0 ≤ η) (hW : W.strip η (C/L)) (F : Forest S.ratio)
    (e : F.Free) (i : G.ColorIndex) (v : Dir G c)
    (hv : ∀ z : Body 1 c, |v z i| ≤ crossW S.ratio η e.val.1 z.1) :
    |relative F (installed S.ratio W) v e i| ≤ total S.patch.J η C + Real.exp η := by
  let x := e.val.1; let j := e.val.2
  let y := S.ratio.parent x
  have he := Corona.near S.ratio x
  have hs : separation x (S.ratio.embed y) ≤ L := by unfold y; omega
  have hp : crossW S.ratio η x y ≤ Real.exp η := by
    refine Real.exp_monotone (le_trans
      (mul_le_mul_of_nonneg_left (show (separation x (S.ratio.embed y):ℝ)/(L:ℝ) ≤ 1 from ?_) h) (mul_one _).le)
    apply (div_le_one (side_pos S.ratio.count)).2; exact_mod_cast hs
  have hh := action_price S h hW F (x,coord j) (parts G 1 v i) (fun k => hv k)
  change |_ - linearCopy S.ratio (collect G v) _ i| ≤ _
  refine le_trans (abs_sub ..) (add_le_add hh ?_)
  unfold linearCopy; split
  · rw [PiLp.zero_apply, abs_zero]; exact (Real.exp_pos _).le
  exact (hv (y,coord j)).trans hp

end tree

abbrev InputKey (G : Gauge) (c : Side) := Body 1 c × G.ColorIndex

def source (t : InputKey G c) : Dir G c :=
  Pi.single t.1 (EuclideanSpace.basisFun G.ColorIndex ℝ t.2)



variable {S : StepData c f}




end Response

variable {G : Gauge} {a : Levels G} {H : Horizon a} {K : MapPrices} {N m : ℕ} {P : PathData G} {η : ℝ}



end YM.Progress.StationaryScenes
