import YM.WilsonBulk.Grid.Blind

/-! Annihilator calculus. Includes numerical moment prices *before iteration*.
Use only on `Width` with explicit summability. `composeRows` sign/order as in the
actual flat API.
-/
namespace YM.WilsonBulk
noncomputable section
open Lattice Laurent Filter Function Bloch
open MultiNext.SignedSource MultiNext.SignedSource.Newt
open Push.AbsoluteSums RG Finset Work.F08
open scoped Topology BigOperators Classical

lemma span_add (x y : Cover) : span (x+y) ≤ span x + span y := by
  exact_mod_cast size_add x y
lemma span_neg (x : Cover) : span (-x) = span x := by simp [span, size_neg]
lemma span_nonneg (x : Cover) : 0 ≤ span x := by positivity

abbrev momentWeight (σ : ℝ) (d : ℕ) : ℝ := (σ⁻¹ ^ d * d.factorial * Real.exp σ)
lemma momentWeight_nonneg {σ : ℝ} (h : 0 ≤ σ) (d : ℕ) : 0 ≤ momentWeight σ d := by
  unfold momentWeight; positivity
lemma width_moment {a σ : ℝ} {p : Cover → ℝ} (hp : Width σ a p) (hσ : 0 < σ) (d : ℕ) :
    SumBudget (fun x => ‖p x‖ * (1+span x)^d) (momentWeight σ d*a) := by
  refine budget_minor (budget_scale (momentWeight_nonneg hσ.le d) hp) (fun _ => by positivity)
    (fun x => ?_)
  exact (mul_le_mul_of_nonneg_left (test_budget x hσ) (norm_nonneg (p x))).trans_eq (by ring)

lemma growth_joint (d : ℕ) (a b : Cover) : (1+span (a+b))^d ≤ (1+span a)^d*(1+span b)^d := by
  rw [← mul_pow]
  have h := span_add a b
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [span_nonneg a, span_nonneg b]

lemma jump_shift (p : Cover → ℝ) (z : Cover) (i : Axis) : jump (fun v => p (v+z)) i =
    fun v => jump p i (v+z) := funext fun v => by simp only [jump]; rw [add_right_comm]

lemma DegLess.shift {p k} (h : DegLess k p) (z : Cover) : DegLess k (fun v => p (v+z)) := by
  induction k generalizing p with
  | zero => simp [degLess_zero.mp h, degLess_zero]; rfl
  | succ k ih =>
    apply degLess_succ.mpr; intro i; rw [jump_shift]; exact ih (degLess_succ.mp h i)

-- annihilator multiplication (all-orders), real row signature
variable {i j : ℕ} {K L p : Cover → ℝ}

/-- Unperiodized read. -/
def applied (K : Cover → ℝ) (p : Cover → ℝ) (x : Cover) := ∑' b, K b * p (b+x)
lemma jump_applied {σ a : ℝ} (hσ : 0 < σ) (hk : Width σ a K) (hp : DegLess i p) (b : Axis) :
    jump (applied K p) b = applied K (jump p b) := by
  funext x; unfold applied jump; rw [← (finite_pairing hσ hk (hp.shift (x+_)).power).tsum_sub
    (finite_pairing hσ hk (hp.shift x).power)]; apply tsum_congr; intro z
  rw [mul_sub, ← add_assoc]

lemma Blind.apply_decreases {σ a : ℝ} (hσ : 0 < σ) (h : Width σ a K) (he : Blind j K)
    (hp : DegLess (i+j) p) : DegLess i (applied K p) := by
  induction i generalizing p with
  | zero => apply degLess_zero.mpr; ext x; exact (he _ ((Nat.zero_add j ▸ hp).shift x)).tsum_eq
  | succ k ih =>
    apply degLess_succ.mpr; intro b; rw [jump_applied hσ h hp b]
    exact ih (degLess_succ.mp ((by rwa [show k+j+1=k+1+j by omega])) b)

lemma routed_bag {σ θ a b M : ℝ} (hσ : 0 < σ) (hθ : 0<θ) (hK : Width σ a K) (hL : Width θ b L)
    {d : ℕ} (hM : 0≤M) (hp : ∀ x, ‖p x‖ ≤ M*(1+span x)^d) :
    SumBudget (fun x : Cover×Cover => ‖K x.1 * L (x.2-x.1) * p x.2‖)
      (M * ((momentWeight σ d*a)*(momentWeight θ d*b))) := by
  let R (x : Cover×Cover) := (x.1,x.2-x.1)
  have hr : Injective R := by
    rintro ⟨x,y⟩ ⟨v,w⟩ h
    change (x, y-x) = (v,w-v) at h
    obtain ⟨rfl,hY⟩ := Prod.mk.inj h
    rw [sub_left_inj] at hY
    subst w; rfl
  refine budget_minor
    (budget_pull R hr (budget_scale hM (budget_prod (width_moment hK hσ d) (width_moment hL hθ d))))
    (fun _ => norm_nonneg _) fun x => ?_
  rw [norm_mul, norm_mul]
  dsimp only [R]
  have H := growth_joint d x.1 (x.2-x.1); rw [add_sub_cancel] at H
  exact (mul_le_mul_of_nonneg_left ((hp _).trans (mul_le_mul_of_nonneg_left H hM))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)

lemma multiply_applied {σ θ a b : ℝ} (hσ : 0 < σ) (hθ : 0<θ) (hK : Width σ a K) (hL : Width θ b L)
    {d : ℕ} (hp : PowerBound p d) :
    (∑' x, routed id K (fun _ => L) x * p x) = ∑' x, K x * applied L p x := by
  obtain ⟨M,hM,h⟩ := hp
  have hf := (routed_bag hσ hθ hK hL hM h).2.1
  let F := fun (x y : Cover) => K x * L (y-x) * p y
  have hF : Summable (Function.uncurry F) := hf.of_norm
  simp_rw [routed, id_eq, ← tsum_mul_right]
  change ∑' y, ∑' x, F x y = _
  rw [Summable.tsum_comm hF]; refine tsum_congr fun x => ?_
  rw [applied, ← tsum_mul_left, ← (Equiv.addRight x).tsum_eq (F x)]
  refine tsum_congr fun z => ?_; simp [F,mul_assoc]

lemma Blind.routed {σ θ a b : ℝ} (hσ : 0 < σ) (hθ : 0<θ) (hK : Width σ a K) (hL : Width θ b L)
    (hk : Blind i K) (hl : Blind j L) : Blind (i+j) (routed id K (fun _ => L)) := by
  intro p hp
  have hw : Width (min σ θ) (a*b) (Work.F08.routed id K (fun _ => L)) :=
    width_routed (lt_min hσ hθ).le (fun _ => le_rfl) (hK.mono (min_le_left ..) le_rfl) (fun _ => hL.mono (min_le_right ..) le_rfl)
  convert (finite_pairing (lt_min hσ hθ) hw hp.power).hasSum using 1
  exact (multiply_applied hσ hθ hK hL hp.power |>.trans (hk _ (hl.apply_decreases hθ hL hp)).tsum_eq).symm

lemma Blind.sum {α : Type*} (s : Finset α) {K : α → Cover → ℝ} (h : ∀ u ∈ s, Blind i (K u)) : Blind i (fun x => ∑ u ∈ s, K u x) := by
  intro p hp; have hg := hasSum_sum (f:=fun u x => K u x * p x) (a:=fun _ => 0) (s:=s) (fun u hu => h u hu _ hp)
  simpa only [Finset.sum_const_zero, Finset.sum_mul] using! hg

variable {α β γ : Type*}

lemma Blind.compose [Fintype β] {P : Row α β} {Q : Row β γ} {σ θ a b : ℝ} (hσ : 0 < σ) (hθ : 0<θ)
    (hP : P.strip σ a) (hQ : Q.strip θ b) (hp : ∀ x y, Blind i (P x y)) (hq : ∀ x y, Blind j (Q x y))
    (x : α) (y : γ) : Blind (i+j) (composeRows P Q x y) :=
  Blind.sum Finset.univ fun b _ => Blind.routed hσ hθ (hP x b) (hQ b y) (hp x b) (hq b y)

-- zero frequency convenience
lemma Blind.minus {K L : Cover → ℝ} (h : Blind i K) (he : Blind i L) : Blind i (fun x => K x - L x) :=
  fun p hp => by simpa only [sub_mul, Pi.sub_apply, sub_self] using! (h p hp).sub (he p hp)

lemma blind_one (h : HasSum K 0) : Blind 1 K := by
  intro p hp; rw [← hp.take_same]; unfold Newt.take Newt.piece; simpa using h.mul_right (p 0)

lemma masses_tone (P : Row α β) (x y) : P.read 0 x y = (∑' i, P x y i : ℝ) := by
  unfold Row.read Laurent.read; simp only [Matrix.of_apply, mode_constant, one_smul]
  exact (Complex.ofReal_tsum _).symm

lemma signal_one {P : Row α β} (h : P.safe) (hz : P.read 0 = 0) (x y) : Blind 1 (P x y) := by
  have hv := congrFun (congrFun hz x) y; rw [masses_tone] at hv
  apply blind_one; refine Summable.hasSum_iff ((show Summable (P x y) from ((h x y).of_norm))) |>.2 ?_
  exact (Complex.ofReal_injective hv)

lemma blind_minus {σ a θ b : ℝ} (hσ : 0≤σ) (hθ : 0≤θ) {P Q : Row α β}
    (hP : P.strip σ a) (hQ : Q.strip θ b) (h : P.read 0 = Q.read 0) (x y) : Blind 1 (minusRows P Q x y) := by
  apply blind_one; have hv := congrFun (congrFun h x) y; simp_rw [masses_tone] at hv
  simpa only [minusRows, Complex.ofReal_injective hv, sub_self] using!
    ((hP x y).summable hσ).hasSum.sub ((hQ x y).summable hθ).hasSum

lemma blind_trans_one (P : Row α β) (h : P.safe) (hz : P.read 0 = 0) (x y) : Blind 1 (transRows P x y) := by
  have hv := congrFun (congrFun hz y) x; rw [masses_tone] at hv; unfold transRows; apply blind_one
  apply (Equiv.neg Cover).hasSum_iff.mpr; exact ((show Summable (P y x) from (h y x).of_norm).hasSum_iff).2 (Complex.ofReal_injective hv)

end
end YM.WilsonBulk
