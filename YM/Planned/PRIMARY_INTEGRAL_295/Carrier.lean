import YM.Next.FREE_KERNELS.Curl
import YM.Planned.PRIMARY_INTEGRAL_295.Route


/-!
# Full stationary rows on the cover: accounts

Using `Flight` and the allocated `meshBook` coefficients. Polynomially
growing inputs on ALL of the cover, actual Laurent mass, incl count of
residue and true displacement. Not paying for a sum over fine origins.
The step queries these rows on the cover (including when receiving the
prescribed *periodically lifted* local arrays); not evaluating log modes
by removing momenta on a particular torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Carrier
open Function Filter Lattice Labels Laurent RG Precision Bloch Exterior Work.F08 Next.Free Place
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : Side} {j t : ℕ}

def liftCost (n : ℕ) (x : Cover) := (1+(size x:ℝ))^n
lemma liftCost_ge (n : ℕ) (x) : 1 ≤ liftCost n x := one_le_pow₀ (by simp)
lemma liftCost_pos (n : ℕ) (x) : 0 ≤ liftCost n x := zero_le_one.trans (liftCost_ge n x)
@[simp] lemma origin_lift (L : Side) : lift (0 : Site L)=0 := by ext; simp [lift]
lemma liftCost_add (n : ℕ) (x y : Cover) : liftCost n (x+y) ≤ liftCost n x * liftCost n y := by
  have he : (size (x+y) : ℝ) ≤ size x + size y := by exact_mod_cast size_add x y
  unfold liftCost; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) (size x)) (Nat.cast_nonneg (α:=ℝ) (size y))]
lemma shade_seat (x : Cover) : ‖seat x‖ ≤ (size x:ℝ) := by
  have hu : ∑ i : Axis, seat x i • basis i = seat x := by ext; simp
  conv_lhs => rw [← hu]
  unfold size; rw [Nat.cast_sum]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul,show ‖basis i‖=1 by simp [basis],mul_one,seat_apply]; rw [← norm_natAbs, Real.norm_natCast] -- rfl

/-- Threshold-independent filter spending for one order. A deliberately
moderate (not optimized) exact polynomial cost. -/
def widthCost (σ : ℝ) (n : ℕ) := (1+((n+1:ℕ):ℝ)/σ)^n
lemma widthCost_ge {σ : ℝ} (hp : 0 < σ) (n : ℕ) : 1 ≤ widthCost σ n := one_le_pow₀ (by linarith [div_nonneg (Nat.cast_nonneg (α:=ℝ) (n+1)) hp.le])
lemma widthBill (σ : ℝ) (hp : 0 < σ) (n : ℕ) (r : ℝ) (hr : 0≤r) : (1+r)^n ≤ widthCost σ n * Real.exp (σ*r) := by
  let m : ℝ := ((n+1:ℕ):ℝ)
  have hm : m > 0 := by unfold m; positivity
  let s := σ/m
  have hs : s>0 := by unfold s; positivity
  have he : 1+r ≤ (1+m/σ)*Real.exp (s*r) := calc
    1+r ≤ (1+m/σ)*(s*r+1) := by
      have hx : m/σ*(s*r)=r := by unfold s; field_simp
      have ht := div_nonneg hm.le hp.le
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)
  unfold widthCost
  refine (pow_le_pow_left₀ (by linarith) he _).trans ?_; rw [mul_pow,← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hr
  unfold s; rw [← mul_div_assoc,div_le_iff₀ hm, mul_comm σ]; gcongr; unfold m; simp

lemma width_income {σ C : ℝ} (hσ : 0<σ) {q : Cover→ℝ} (hq : Width σ C q) (n : ℕ) :
    SumBudget (fun i : Cover => ‖q i‖ * liftCost n i) (widthCost σ n*C) := by
  let g (x : Cover) := Real.exp (σ*size x)*‖q x‖
  let p := widthCost σ n
  have hp : 0 ≤ p := zero_le_one.trans (widthCost_ge hσ n)
  have he : SumBudget (fun i => p*g i) (p*C) := ⟨fun i => mul_nonneg hp (hq.1 _),hq.2.1.mul_left _,by
    rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hq.2.2 hp⟩
  apply budget_minor he (fun _ => mul_nonneg (norm_nonneg _) (liftCost_pos ..)); intro i
  rw [mul_comm ‖q i‖]; refine (mul_le_mul_of_nonneg_right (widthBill σ hσ n _ (Nat.cast_nonneg (size i))) (norm_nonneg _)).trans_eq ?_
  exact mul_assoc ..

abbrev Window (E : Type*) := Cover → Axis → E

def Carries (b : Window E) (n : ℕ) (C : ℝ) : Prop := 0 ≤ C ∧ ∀ (x : Cover) (a : Axis), ‖b x a‖ ≤ C*liftCost n x

def verdict (f : E4 → (Axis → E)) : Window E := fun x i => f (seat x) i
lemma royalties (n : ℕ) (f : E4 → Axis → E) (h : f ∈ rangeLt (Axis → E) n) : ∃ M : ℝ, Carries (verdict f) n M := by
  obtain ⟨M,hM,H⟩ := Place.band_growth h
  exact ⟨M,hM,fun x a => (norm_le_pi_norm ..).trans ((H (seat x)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (add_le_add_right (shade_seat x) _) n) hM))⟩

/-- Lifts to cover block centers. -/
def cellar (L : Side) (x : Cover) := Work.F08.carry (0:Site L) x
lemma balance (L : Side) (x) : x=lift (wrap L x)+L.val • cellar L x := by
  simpa only [origin_lift, zero_add,arrives,cellar] using carry_spec (0:Site L) x
lemma liftCost_cellar (L : Side) (n : ℕ) (x : Cover) : liftCost n (cellar L x) ≤ liftCost n x := by
  unfold liftCost; gcongr; exact carry_size _ _
lemma zero_cellar (L : Side) : cellar L 0 = 0 := stays_here (0:Site L)

/-- Per-residue 1-form row. Do not confuse with the two-form Ψ. -/
abbrev Lines (L : Side) := Cross L (TypeFace 1) (TypeFace 1)

def stream (q : Cover → ℝ) (x : Cover) (b : Cover → E) := ∑' z, q z • b (x+z)

def member (A : Lines L) (x : Cover) (i j : Axis) : Cover → ℝ := A (wrap L x,Exterior.coord i) (Exterior.coord j)

def applyLine (A : Lines L) (b : Window E) : Window E := fun x i =>
    ∑ j : Axis, stream (member A x i j) (cellar L x) (fun z => b z j)

lemma stream_income {σ C M : ℝ} {q : Cover→ℝ} (hσ : 0<σ) (hq : Width σ C q)
    (x : Cover) (n : ℕ) (hM : 0≤M) {b : Cover → E} (hb : ∀ i, ‖b i‖ ≤ M*liftCost n i) :
    SumBudget (fun z : Cover => ‖q z • b (x+z)‖) (M*liftCost n x*widthCost σ n*C) := by
  let f i := ‖q i‖*liftCost n i
  let p := M*liftCost n x
  have H := width_income hσ hq n
  have he : 0≤p := by exact mul_nonneg hM (liftCost_pos ..)
  have hy : SumBudget (fun i => p*f i) (M*liftCost n x*widthCost σ n*C) := by
    refine ⟨fun i => mul_nonneg he (H.1 _),H.2.1.mul_left _,?_⟩
    rw [tsum_mul_left,mul_assoc (M * liftCost n x)]; exact mul_le_mul_of_nonneg_left H.2.2 he
  apply budget_minor hy (fun _ => norm_nonneg _); intro i
  rw [norm_smul]
  apply (mul_le_mul_of_nonneg_left ((hb (x+i)).trans (mul_le_mul_of_nonneg_left (liftCost_add ..) hM))
    (norm_nonneg _)).trans_eq
  unfold p f; ring

lemma field_cost {σ C M : ℝ} (hσ : 0 < σ) (hC : 0≤C) {A : Lines L} (ha : A.strip σ C)
    (n : ℕ) {b : Window E} (hb : Carries b n M) : Carries (applyLine A b) n (4*M*widthCost σ n * C) := by
  have hm := hb.1
  have hg := widthCost_ge hσ n
  refine ⟨by positivity,fun x i => ?_⟩
  refine (norm_sum_le ..).trans ?_
  have he j : ‖stream (member A x i j) (cellar L x) (fun z => b z j)‖ ≤ M*widthCost σ n*C*liftCost n x := by
    let w := cellar L x
    have hc := stream_income hσ (ha (wrap L x, Exterior.coord i) (Exterior.coord j)) w n hm (fun z => hb.2 z j)
    refine ((norm_tsum_le_tsum_norm hc.2.1).trans hc.2.2).trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (liftCost_cellar ..) hm) (zero_le_one.trans hg)) hC).trans_eq ?_; ring
  calc
    _ ≤ ∑ j : Axis,M*widthCost σ n*C*liftCost n x := Finset.sum_le_sum fun j _ => he j
    _ = _ := by simp [Axis]; ring

/-- Source-faithful unmodified one-form. -/
def linesOf (P : Flight j t) (k : ℝ) : Lines P.L := (Flight.duo k P).A0

lemma priced (k : ℝ) (hk : 0 < k) (hj : 4 ≤ j) (ht : 4 ≤ t) :
    ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ (P : Flight j t) (u : List Axis), u.length ≤ j-2 →
      (advanceC P.L (linesOf P k) u).strip σ (C/(P.L.val:ℝ)^(1+u.length)) :=
    (secure_both k hk hj ht).1.honored hj 1

lemma stored (P : Flight j t) (k : ℝ) (hk : 0 < k) (ht : 4 ≤ t) :
    Whole (linesOf P k) := by
  obtain ⟨σ,C,hσ,hC,h⟩ := priced k hk P.legal ht
  exact ⟨σ,_,hσ,h P [] (by simp)⟩

section
variable [CompleteSpace E]
lemma addLine {A : Lines L} (hA : Whole A) (b c : Window E) {m n : ℕ} {M N : ℝ} (hb : Carries b m M) (hc : Carries c n N) :
    applyLine A (b+c)=applyLine A b+applyLine A c := by
  obtain ⟨σ,C,h,hA⟩ := hA
  ext1 x; ext1 i; unfold applyLine stream
  simp only [Pi.add_apply,smul_add,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun j _ => ?_
  let v := cellar L x
  let q := member A x i j
  exact (stream_income h (hA _ _) v _ hb.1 (fun z => hb.2 z j)).2.1.of_norm.tsum_add
    (g:=fun z => q z • c (v+z) j) (stream_income h (hA _ _) v _ hc.1 (fun z=> hc.2 z j)).2.1.of_norm
end
end YM.Planned.PrimaryIntegral295.Carrier
