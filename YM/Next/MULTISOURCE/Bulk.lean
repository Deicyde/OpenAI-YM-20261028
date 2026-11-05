import YM.Corona.Halo
import YM.Next.MULTISOURCE.Packs
import YM.Shoot.Criteria


/-!
# Space of single (connected) variations

Regular directions are costed in the *actual* support metric, no evaluating
on all-field space instead of `Healthy`. Nevertheless the push goes through
on all-field space! Don't merge regular families by support without proving
regularity of such a sum.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Wilson Lattice Function Pack MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

variable {n : Side} {G : Gauge}

def burn (P : BudgetPoint) (r : ℝ) (X : Support n) := Real.exp ((P.supportExponent+r)*coverNumber P.B X)

@[simp] lemma burn_zero (P : BudgetPoint) (X : Support n) (t : ℝ) : burn P 0 X*t=P.mass X t := by
  simp [burn,BudgetPoint.mass]

lemma burn_pos (P : BudgetPoint) (r : ℝ) (X : Support n) : 0 < burn P r X := Real.exp_pos _
lemma burn_ge (P : BudgetPoint) {r : ℝ} (h : 0 ≤ r) (X : Support n) : 1 ≤ burn P r X :=
  Real.one_le_exp (mul_nonneg (add_nonneg P.exponent_pos.le h) (by positivity))

/-- Credit from having to carry all of `X`. -/
def fare (P : BudgetPoint) (r : ℝ) (X : Support n) := Real.exp (- r * coverNumber P.B X)

lemma cheaper (P : BudgetPoint) {r : ℝ} {X Y : Support n} (h : 0 ≤ r) (hx : X ⊆ Y) :
    burn P 0 Y ≤ fare P r X * burn P r Y := by
  unfold fare burn
  rw [← Real.exp_add]; apply Real.exp_monotone
  have he := mul_le_mul_of_nonneg_left (show (coverNumber P.B X:ℝ) ≤ coverNumber P.B Y by
    exact_mod_cast Corona.cover_mono hx _) h
  linarith

lemma permit_le {I : Type*} {f g : I → ℝ} {a b : ℝ} (hf : SumBudget f a) (h : a ≤ b)
    (hh : ∀ i,0≤g i ∧ g i≤f i) : SumBudget g b := by
  have hs := hf.2.1.of_nonneg_of_le (fun i => (hh i).1) fun i => (hh i).2
  exact ⟨fun i => (hh i).1,hs,(hs.tsum_le_tsum (fun i => (hh i).2) hf.2.1).trans
    (hf.2.2.trans h)⟩

lemma permit_mul {I : Type*} {f : I → ℝ} {a b : ℝ} (hf : SumBudget f a) (h : 0 ≤ b) :
    SumBudget (fun i => b * f i) (b*a) :=
  ⟨fun i => mul_nonneg h (hf.1 i), hf.2.1.mul_left _, (tsum_mul_left).trans_le (mul_le_mul_of_nonneg_left hf.2.2 h)⟩

lemma scaled_left (f : Config G n → ℂ) (z : ℂ) (l) (U) :
    leftDerivs (z • f) l U = z * leftDerivs f l U := by
  induction l generalizing U with
  | nil => rfl
  | cons a l ih =>
    simp only [leftDerivs,ih]; rw [deriv_const_mul_field]

lemma path_scaled {f : Config G n → ℂ} {X : Support n} {P : BudgetPoint} (z : ℂ)
    (h : P.Regular X f) : P.Regular X (z • f) := by
  refine ⟨fun U V H => by simp only [Pi.smul_apply, h.sites U V H], measurable_const.smul h.borel,
    fun t U => by simp only [Pi.smul_apply, h.symmetry t U],fun U hu => ?_,fun U hu A l hl => ?_⟩
  · exact ContDiffAt.const_smul z (h.smooth U hu)
  simp_rw [scaled_left]; exact (h.hasDerivs U hu A l hl).const_smul z

lemma null_path (P : BudgetPoint) (X : Support n) : P.Regular X (0 : Config G n → ℂ) ∧
    ∀ o, P.supBounds o X (0 : Config G n → ℂ) 0 := by
  have he (A : Config G n) (l) : leftDerivs (0 : Config G n → ℂ) l A=0 := by
    induction l generalizing A with
    | nil => rfl
    | cons _ _ h => simp [leftDerivs,h]
  refine ⟨⟨fun _ _ _ => rfl,measurable_const,fun _ _ => rfl,fun U _ => ?_,fun U hu A l hl => ?_⟩,
    fun o => ⟨le_rfl,fun U hu l hi hc => ?_⟩⟩
  · exact contDiffAt_const
  · simp_rw [he]; exact hasDerivAt_const _ _
  rw [he,norm_zero]

/-- Do not fold this sum into a single unmasked germ. -/
def Banked (P : BudgetPoint) (r : ℝ) (X : Support n) (F : Config G n → ℂ) (c : ℝ) : Prop :=
    ∃ (T : ℕ → Support n) (H : ℕ → Config G n → ℂ) (b : ℕ → ℝ),
      (∀ i, X ⊆ T i ∧ P.Regular (T i) (H i) ∧ 0 ≤ b i ∧
        ∀ j∈X,P.supBounds j (T i) (H i) (b i)) ∧
      SumBudget (fun i => burn P r (T i)*b i) c ∧
      ∀ U, F U = ∑' i, masked P.threshold (T i) (H i) U

namespace Banked
variable {P : BudgetPoint} {r : ℝ} {X : Support n} {F G' : Config G n → ℂ} {a b c : ℝ}

lemma zero (P : BudgetPoint) (r : ℝ) (X : Support n) : Banked P r X (0 : Config G n → ℂ) 0 := by
  refine ⟨fun _ => X,fun _ => 0,fun _ => 0,fun i => ⟨by rfl,(null_path P X).1,le_rfl,fun j _ => (null_path _ _).2 j⟩,
    ?_,fun U => ?_⟩
  · simp [SumBudget]
  simp [masked]

/-- One ordinary basis cylinder entry. -/
lemma term {Y : Support n} (hx : X ⊆ Y) (hb : 0 ≤ a) (hr : P.Regular Y F)
    (h : ∀ j∈X,P.supBounds j Y F a) : Banked P r X (masked P.threshold Y F) (burn P r Y*a) := by
  let H : ℕ → Config G n → ℂ := fun i => if i=0 then F else 0
  let f (i : ℕ) := if i=0 then a else 0
  refine ⟨fun _ => Y,H,f,fun i => ⟨hx,?_⟩,?_,fun U => ?_⟩
  · by_cases e : i=0 <;> simp only [H,f,e,↓reduceIte]
    · exact ⟨hr,hb,h⟩
    exact ⟨(null_path ..).1,le_rfl,fun j _ => (null_path ..).2 j⟩
  · have hs (i) : burn P r Y*f i=(Pi.single 0 (burn P r Y*a):ℕ → ℝ) i := by by_cases h : i=0 <;> simp [f,h]
    simp_rw [SumBudget,hs]
    constructor
    · intro i; rw [Pi.single_apply]; split <;> first | exact mul_nonneg (burn_pos ..).le hb | exact le_rfl
    constructor
    · apply HasSum.summable; refine hasSum_single 0 (fun i hi => ?_); exact Pi.single_eq_of_ne hi _
    simp
  rw [tsum_eq_single 0 fun i hi => by simp [H,hi,masked],show H 0=F by simp [H]]

lemma reserve {T : ℕ→ Support n} {H : ℕ→ Config G n → ℂ} {p : ℕ→ℝ} (hx : X.Nonempty)
    (hr : 0 ≤ r) (hd : ∀ i j, j∈X → P.supBounds j (T i) (H i) (p i))
    (hb : SumBudget (fun i => burn P r (T i)*p i) c) :
    Dominated fun i => masked P.threshold (T i) (H i) := by
  obtain ⟨i,hi⟩ := hx
  refine ⟨_, hb.2.1, fun j U => ?_⟩
  obtain ⟨hp,H⟩ := hd j i hi
  dsimp only
  apply le_trans (b:=p j) _ (le_mul_of_one_le_left hp (burn_ge P hr _)); by_cases he : Healthy P.threshold (T j) U
  · rw [masked_eq _ _ _ _ he]; exact H U he [] (by simp) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact hp

lemma enlarge (h : Banked P r X F a) (he : a ≤ b) : Banked P r X F b := by
  obtain ⟨T,H,f,hf,hq,ht⟩ := h
  exact ⟨T,H,f,hf,⟨hq.1,hq.2.1,hq.2.2.trans he⟩,ht⟩

lemma rebate (h : Banked P r X F c) (hr : 0 ≤ r) : Banked P 0 X F (fare P r X*c) := by
  obtain ⟨T,H,b,hb,hq,hv⟩ := h
  refine ⟨T,H,b,hb,?_,hv⟩
  refine permit_le (permit_mul hq (Real.exp_pos _).le) le_rfl fun i => ⟨?_,?_⟩
  · exact mul_nonneg (burn_pos ..).le (hb i).2.2.1
  exact (mul_le_mul_of_nonneg_right (cheaper P hr (hb i).1) (hb i).2.2.1).trans_eq (mul_assoc ..)

lemma scale (h : Banked P r X F a) (z : ℂ) : Banked P r X (z • F) (‖z‖*a) := by
  obtain ⟨T,H,b,hb,hk,hv⟩ := h
  refine ⟨T,fun i => z • H i,fun i => ‖z‖*b i,fun i => ⟨(hb i).1,path_scaled z (hb i).2.1,
    mul_nonneg (norm_nonneg _) (hb i).2.2.1,fun j hj => ?_⟩,?_,fun U => ?_⟩
  · obtain ⟨H,he⟩ := (hb i).2.2.2 j hj
    exact ⟨mul_nonneg (norm_nonneg _) H,fun U hu l hl hk => by
      rw [scaled_left,norm_mul]; exact mul_le_mul_of_nonneg_left (he _ hu l hl hk) (norm_nonneg _)⟩
  · simp_rw [mul_left_comm _ ‖z‖]; exact permit_mul hk (norm_nonneg z)
  have ht (i) : masked P.threshold (T i) (z • H i) U=z*masked P.threshold (T i) (H i) U := by
    by_cases e : Healthy P.threshold (T i) U
    · rw [masked_eq _ _ _ _ e,masked_eq _ _ _ _ e]; rfl
    rw [masked_ne _ _ _ _ e,masked_ne _ _ _ _ e,mul_zero]
  change z*F U = _
  simp_rw [ht]; rw [hv,tsum_mul_left]

lemma add (h : Banked P r X F a) (h' : Banked P r X G' b) (hx : X.Nonempty) (hr : 0 ≤ r) :
    Banked P r X (F+G') (a+b) := by
  obtain ⟨T,H,t,ht,hq,hv⟩ := h
  obtain ⟨T',H',t',ht',hq',hv'⟩ := h'
  let e := Equiv.natSumNatEquivNat.symm
  let V := Sum.elim T T'
  let R := Sum.elim H H'
  let f := Sum.elim t t'
  have he (i) : X ⊆ V i ∧ P.Regular (V i) (R i) ∧ 0 ≤ f i ∧ ∀ j∈ X,P.supBounds j (V i) (R i) (f i) := by
    cases i with
    | inl i => exact ht i
    | inr i => exact ht' i
  refine ⟨V ∘ e,R ∘ e, f ∘ e,fun i => he (e i), ?_,fun U => ?_⟩
  · let y i := burn P r (V i) * f i
    have hh := HasSum.sum (f:=y) hq.2.1.hasSum hq'.2.1.hasSum
    have hs := e.hasSum_iff.mpr hh
    change SumBudget (y ∘ e) _
    exact ⟨fun i => mul_nonneg (burn_pos ..).le (he _).2.2.1, hs.summable,
      hs.tsum_eq.trans_le (add_le_add hq.2.2 hq'.2.2)⟩
  let S i := masked P.threshold (V i) (R i) U
  have he1 := (reserve hx hr (fun i => (ht i).2.2.2) hq).summable U
  have he2 := (reserve hx hr (fun i => (ht' i).2.2.2) hq').summable U
  change F U+G' U=∑' i,S (e i)
  rw [hv,hv',e.tsum_eq S]; exact (HasSum.sum (f:=S) he1.hasSum he2.hasSum).tsum_eq.symm

lemma sums {I : Type*} (V : Finset I) (f : I → Config G n → ℂ) (g : I → ℝ)
    (hx : X.Nonempty) (hr : 0 ≤ r) (hf : ∀ i∈V, Banked P r X (f i) (g i)) :
    Banked P r X (∑ i∈V,f i) (∑ i∈V,g i) := by
  classical
  induction V using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact zero ..
  | insert i V h ih =>
    rw [Finset.sum_insert h,Finset.sum_insert h]
    exact add (hf i (Finset.mem_insert_self ..)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)) hx hr
end Banked
end YM.Multi
