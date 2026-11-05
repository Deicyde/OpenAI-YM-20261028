import YM.Push.RELAY_DIFFERENCE.RawTop

/-! Stronger bookkeeping: comparisons to arbitrary slowly growing rows, over
ALL p including the first. This filter has no late-period requirement. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Push.RelayDifference Filter Extraction Bid
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {C : Family G} {d:ℕ}

/-- Tails uniform in ALL admitted periods. -/
def mesh : Filter Cutoffs := comap Prod.fst atTop
lemma deepen : Tendsto Prod.fst mesh atTop:= tendsto_comap
lemma late {P:Cutoffs→Prop} : (∀ᶠ i in mesh, P i) ↔ ∀ᶠ N in atTop, ∀ p:ℕ,P (N,p):=by
  rw [mesh,eventually_comap]; constructor
  · intro h; exact h.mono fun N hn p=>hn (N,p) rfl
  intro h; filter_upwards [h] with i hi a ha
  subst i; exact hi a.2
instance : NeBot mesh:= by
  apply neBot_iff.mpr; intro hf
  obtain ⟨N,h⟩:= (late.mp (show ∀ᶠ _ in mesh,False from by simp [hf])).exists; exact h 0

lemma boosts {ε : ℝ} (hε : 0 < ε) : Tendsto (flight C ε) mesh atTop :=
  Real.tendsto_exp_atTop.comp ((C.S.divergent.comp deepen).const_mul_atTop hε)

lemma flown {ε : ℝ} (hε : 0 < ε) : Tendsto (flight C (-ε)) mesh (𝓝 0) := by
  have hx : flight C (-ε) = fun j => (flight C ε j)⁻¹ := by
    funext j
    rw [flight, neg_mul, Real.exp_neg]; rfl
  rw [hx]
  exact tendsto_inv_atTop_zero.comp (boosts hε)

section Sluggish
variable {X Y : Type*} [Norm X] [Norm Y]

def Sluggish (C : Family G) {X : Type*} [Norm X] (w : Cutoffs → X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j in mesh, ‖w j‖ ≤ flight C ε j

variable {w : Cutoffs → X} {v : Cutoffs → Y}

lemma Sluggish.const (x : X) : Sluggish C (fun _ => x) :=
  fun _ hε => (boosts hε).eventually_ge_atTop ‖x‖

lemma Sluggish.reduce (h : Sluggish C w) (hq : ∀ᶠ i in mesh, ‖v i‖ ≤ ‖w i‖) : Sluggish C v := by
  intro ε hε
  filter_upwards [hq,h _ hε] with i hi hv using hi.trans hv
end Sluggish

section SluggishOp
variable {X : Type*} [SeminormedAddCommGroup X] {w v : Cutoffs → X}

lemma Sluggish.norm (h : Sluggish C w) : Sluggish C fun i => ‖w i‖ := by
  exact h.reduce (Eventually.of_forall fun _ => by simp)

private lemma sum_le_flight (ε : ℝ) (he : 0 < ε) : ∀ᶠ j in mesh,
    flight C (ε/2) j + flight C (ε/2) j ≤ flight C ε j := by
  filter_upwards [(boosts (C:=C) (half_pos he)).eventually_ge_atTop 2] with i hi
  have hx : flight C (ε/2) i * flight C (ε/2) i = flight C ε i := by rw [flight_add,add_halves]
  nlinarith only [hi,hx]

lemma Sluggish.add (h : Sluggish C w) (H : Sluggish C v) : Sluggish C fun i => w i + v i := by
  intro ε hε
  filter_upwards [h _ (half_pos hε), H _ (half_pos hε), sum_le_flight ε hε] with i hi hv he using
    (norm_add_le ..).trans ((add_le_add hi hv).trans he)





lemma Sluggish.sum {ι : Type*} (s : Finset ι) (w : ι → Cutoffs → X) (h : ∀ i ∈ s, Sluggish C (w i)) :
    Sluggish C fun j => ∑ i∈s, w i j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (by simpa only [Finset.sum_empty] using Sluggish.const (C:=C) (0:X))
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self ..)).add (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

private lemma norm_product_slow {Y Z : Type*} [SeminormedAddCommGroup Y] [Norm Z]
    (h : Sluggish C w) {r : Cutoffs → Y} {p : Cutoffs → Z} (H : Sluggish C r)
    (he : ∀ᶠ i in mesh, ‖p i‖ ≤ ‖w i‖ * ‖r i‖) : Sluggish C p := by
  intro ε hε
  filter_upwards [h _ (half_pos hε), H _ (half_pos hε), he] with i hi hv hx
  apply hx.trans
  refine (mul_le_mul hi hv (norm_nonneg _) (show 0 ≤ flight _ _ _ from (Real.exp_pos _).le)).trans_eq ?_
  rw [flight_add,add_halves]

lemma Sluggish.smul {c : Cutoffs → ℂ} [NormedSpace ℂ X] (H : Sluggish C c) (h : Sluggish C w) :
    Sluggish C fun i => c i • w i :=
  norm_product_slow H h (Eventually.of_forall fun _ => norm_smul_le ..)
end SluggishOp

lemma Sluggish.mul {X : Type*} [NormedRing X] {c p : Cutoffs → X} (h : Sluggish C c) (H : Sluggish C p) :
    Sluggish C fun i => c i * p i :=
  norm_product_slow h H (Eventually.of_forall fun _ => norm_mul_le ..)

lemma Sluggish.pow {c : Cutoffs → ℝ} (h : Sluggish C c) (n : ℕ) : Sluggish C fun i => c i ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using Sluggish.const (C:=C) (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul h

lemma Sluggish.below {w v : Cutoffs → ℝ} (h : Sluggish C w) (he : ∀ᶠ i in mesh, 0 ≤ v i ∧ v i ≤ w i) :
    Sluggish C v := by
  apply h.reduce
  filter_upwards [he] with i hi
  rw [Real.norm_of_nonneg hi.1, Real.norm_of_nonneg (hi.1.trans hi.2)]
  exact hi.2

lemma Sluggish.est {w : Cutoffs → ℝ} (h : Sluggish C w) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in mesh, w i ≤ flight C ε i := by
  filter_upwards [h _ hε] with i hi using (Real.le_norm_self _).trans hi

/-- Expenditure times a rate of exponential decay in the UV: choose any
 strictly smaller decay exponent. -/
lemma Sluggish.sink {w : Cutoffs → ℝ} (h : Sluggish C w) {a b : ℝ} (he : a < b) :
    ∀ᶠ i in mesh, w i * flight C (-b) i ≤ flight C (-a) i := by
  filter_upwards [h.est (sub_pos.mpr he)] with i hi
  refine (mul_le_mul_of_nonneg_right hi (show 0 ≤ flight C (-b) i from (Real.exp_pos _).le)).trans_eq ?_
  rw [flight_add]; ring_nf

lemma borrowed {α:Type*}[Norm α]{W:ℕ→α} (h: Slow C Order.full (fun i=>W i.1)):Sluggish C (fun i=>W i.1):=by
  intro ε he
  obtain ⟨k,hk⟩:= (Order.fused Order.full _|>.1 (h ε he)).exists
  rw [late]; exact hk.mono fun i hi p=> hi

lemma pillars : Sluggish C (fun j => (C.path.levels.params j.1).columns):= borrowed (W:=fun i=>(C.path.levels.params i).columns) columns_slow
lemma thresholds (h:G.Simple): Sluggish C (fun i=> (C.path.levels.budget i.1).threshold⁻¹) := borrowed (W:=fun i=> (C.path.levels.budget i).threshold⁻¹) (threshold_price h)

lemma carding (v : Rowe C d) (h : Sluggish C v) : Sluggish C fun j => (C.labels.level d).coeffSize (v j) := by
  let K (i : Fields C d) (j) := v j i
  have he (i : Fields C d) : Sluggish C (K i) := h.reduce (Eventually.of_forall fun j => norm_le_pi_norm (v j) i)
  exact Sluggish.sum _ _ fun i _ => (he i).norm
lemma scaling (v : Rowe C d) (h : Sluggish C v) (K : G.Simple) :
    Sluggish C (fun j => (C.labels.level d).coeffSize
      ((C.labels.level d).scaled ((C.path.levels.budget j.1).threshold)⁻¹ (v j))) := by
  let B (i : Fields C d) (j) := v j i
  have he (i : Fields C d) : Sluggish C (B i) := h.reduce (Eventually.of_forall fun j => norm_le_pi_norm (v j) i)
  let t (j : Cutoffs) := (C.path.levels.budget j.1).threshold⁻¹
  let F := C.labels.level d
  have hf (i : Fields C d) : Sluggish C (fun j => F.scaled (t j) (v j) i) := by
    have ht : Sluggish C fun j => ((t j)^((F.grades i).2):ℝ) := (thresholds K).pow _
    exact (ht.reduce (Eventually.of_forall fun j => (Complex.norm_real ((t j)^((F.grades i).2))).le)).mul (he i)
  exact Sluggish.sum _ _ fun i _ => (hf i).norm

def Coin (C : Family G) {d:ℕ} (w : Rowe C d) :=
    Sluggish C (fun j => (C.factory d j.1 j.2).terminal.symm (w j))
namespace Coin
variable {p q:Rowe C d}
lemma from_bound (h:C.Makes) {A:ℝ} (hp:∀ᶠ i in mesh, ‖p i‖ ≤ A) : Coin C p:=by
  intro ε he
  filter_upwards [deepen.eventually (Work.D01.terminal_ball C h _ A ε he),hp] with i hi hu
  exact hi _ _ hu
lemma sub (h : Coin C p) (hp : Coin C q) : Coin C (p-q):= by
  intro ε he
  filter_upwards [h _ (half_pos he),hp _ (half_pos he), sum_le_flight ε he] with i hi hj hk
  rw [Pi.sub_apply,map_sub]; exact (norm_sub_le ..).trans ((add_le_add hi hj).trans hk)
lemma scaled (h:Coin C p) {k:Cutoffs→ℂ} (hp:Sluggish C k):Coin C (k • p):=by
  intro ε he
  filter_upwards [hp _ (half_pos he), h _ (half_pos he)] with i hi hj
  change ‖(C.factory d _ _).terminal.symm (k i • p i)‖ ≤ _
  rw [map_smul,norm_smul]
  exact (mul_le_mul hi hj (norm_nonneg _) (by unfold flight; positivity)).trans_eq (by rw [flight_add,add_halves])
end Coin
end YM.FullVolume
