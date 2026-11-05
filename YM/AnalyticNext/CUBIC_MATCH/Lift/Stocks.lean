import YM.AnalyticNext.CUBIC_MATCH.Lift.Count
import YM.Next.FREE_KERNELS.Lifts

set_option warningAsError false

/-!
# Passing the single-momentum stock up a leg

The single lift of verified `Next.Free` works on *all* its stipulated input
rows, not just the linear-horizon applications; costs and linearity to use it
also here. Basic (degree-zero value-zero) lift provided here alongside; acts
again in one group.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch.Lift
open Filter Function Lattice Exterior Matrix Next.Free Work.F08 Bloch Laurent RG
open scoped Topology BigOperators

variable {r : ℕ} {α β γ ι : Type*}

/-- Rows supported in one independent group. -/
abbrev Array1 (r : ℕ) := TypeFace r → Cover → ℝ
abbrev emptyPrefix (A : Array1 r) : Row Unit (TypeFace r) := fun _ => A


lemma plus_rows (R T : Row α β) : plusRows R T = R + T := by
  funext i j x
  change R _ _ _ - -1*T _ _ _=R _ _ _+T _ _ _
  ring
lemma scale_rows (l : ℝ) (R : Row α β) : scaleRows l R=l • R := rfl

lemma payout_add {m : Cover → Cover → ℝ} {η θ D} (p : Tariff m η θ D) (ht : 0 ≤ θ) (hd : 0 ≤ D)
    {u v : Cover → ℝ} {B C} (hu : Laurent.Width η B u) (hv : Laurent.Width η C v) :
    payOut m (u+v) = payOut m u+payOut m v := by
  funext i; simp only [payOut,Pi.add_apply,add_mul]
  have h (z : Cover → ℝ) (M : ℝ) (h : Laurent.Width η M z) :
      Summable fun j => z j*m j i := .of_norm ((p.freedom hd h ht).prod_symm.prod_factor i)
  exact (h u _ hu).tsum_add (h v _ hv)
lemma payout_scale (m : Cover → Cover → ℝ) (u : Cover → ℝ) (a : ℝ) : payOut m (a • u) = a • payOut m u := by
  funext i; simp [payOut,mul_assoc,tsum_mul_left]

variable {R T : Row α β}
lemma pending_linear (h : Whole R) (f : Whole T) (s : Axis) : pending s (R+T)=pending s R+pending s T := by
  obtain ⟨η,x,y,hθ,hR,hT⟩ := h.ditto f
  funext i j; exact payout_add (eval_axis η hθ.le s) hθ.le zero_le_one (hR i j) (hT i j)
lemma dash_linear (h : Whole R) (f : Whole T) (s : Axis) : dashAxis s (R+T)=dashAxis s R+dashAxis s T := by
  obtain ⟨η,x,y,hθ,hR,hT⟩ := h.ditto f
  funext i j; exact payout_add (dividend η hθ s) (by positivity) (by positivity) (hR i j) (hT i j)
lemma shed_linear {A M : Row α (TypeFace (r+1))} (h : Whole A) (f : Whole M) (s : Axis) :
    shed s r (A+M) = shed s r A + shed s r M := by
  have he := pending_linear h f s
  funext i j x; simp only [shed,Pi.add_apply]; split
  · simp only [add_zero]
  rw [he]; rfl
lemma shed_scale (R : Row α (TypeFace (r+1))) (s : Axis) (a : ℝ) :
    shed s r (a • R)=a • shed s r R := by
  funext i j x; simp only [shed,Pi.smul_apply]; split
  · rw [smul_zero]
  exact congr_fun (payout_scale _ _ _) x

private lemma compose_plus [Fintype α] [Fintype β] [Fintype γ] {P : Row β γ}
    (h : Whole R) (f : Whole T) (g : Whole P) : composeRows (R+T) P=composeRows R P+composeRows T P := by
  rw [← plus_rows,← plus_rows (composeRows R P)]
  refine bank_injective (((h.plus f).prod g).safe) (((h.prod g).plus (f.prod g)).safe) (fun i => ?_)
  rw [(h.plus f).acts g i,h.acts_plus f i,Matrix.add_mul,(h.prod g).acts_plus (f.prod g) i,h.acts g i,f.acts g i]
private lemma compose_scale [Fintype α] [Fintype β] [Fintype γ] {P : Row β γ}
    (h : Whole R) (f : Whole P) (l : ℝ) : composeRows (l • R) P=l • composeRows R P := by
  rw [← scale_rows,← scale_rows]
  refine bank_injective (((h.weight _).prod f).safe) (((h.prod f).weight _).safe) (fun i => ?_)
  rw [(h.weight _).acts f,acts_scale,Matrix.smul_mul,acts_scale,h.acts f i]
lemma fold_linear {A M : Row Unit (TypeFace (r+1))} (h : Whole A) (g : Whole M) (l : List Axis) :
    folded r (A+M) l=folded r A l+folded r M l := by
  induction l generalizing A M with
  | nil => simp [folded]
  | cons a l ih =>
    simp only [folded,shed_linear h g, relief,dash_linear h g, plus_rows]
    rw [compose_plus (dash_whole h _) (dash_whole g _) (constant_whole _), ih (shed_whole _ h) (shed_whole _ g)]
    abel
lemma fold_scale {A : Row Unit (TypeFace (r+1))} (h : Whole A) (l : List Axis) (s : ℝ) :
    folded r (s • A) l=s • folded r A l := by
  induction l generalizing A with
  | nil => simp [folded]
  | cons a l ih =>
    have he : dashAxis a (s • A) = s • dashAxis a A := funext fun i => funext fun j => payout_scale _ _ _
    simp only [folded, shed_scale, plus_rows, ih (shed_whole _ h), relief,he,
      compose_scale (dash_whole h _) (constant_whole _) s, smul_add]

/-- Scalar contraction by z_i−1. -/
def boundary (d : ℕ) (A : Array1 (d+1)) (b : TypeFace d) (x : Cover) :=
    ∑ k : TypeFace (d+1), ∑ a : Axis, Exterior.left ℝ d a k b * (A k (x-step a)-A k x)

lemma boundary_rows (A : Array1 (r+1)) : emptyPrefix (boundary r A) = composeRows (emptyPrefix A) (cobound r) := by
  funext i j x
  symm
  refine Finset.sum_congr rfl (fun k hk => ?_)
  change routed id (A k) (fun _ => cobound r k j) x = _
  let e : Equiv.Perm Cover := (Equiv.neg _).trans (Equiv.addLeft x)
  have he (i : Cover) : e i=x-i := by simp [e,sub_eq_add_neg]
  unfold routed; rw [← e.tsum_eq]
  simp_rw [he,id_eq,sub_sub_cancel]; rw [tsum_eq_sum (s:=support)]; swap
  · exact fun i hi => by rw [certified _ _ _ _ hi, mul_zero]
  simp_rw [cobound,Finset.mul_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have ht : step d ∈ support := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, Finset.mem_univ _,rfl⟩)
  have hx : (0:Cover) ∈ support := Finset.mem_insert_self ..
  simp only [mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,Finset.sum_ite_eq', ht, hx, if_true,sub_zero]
  ring

def Lifted (A : Array1 (r+1)) : Array1 (r+2) := capLift r (emptyPrefix A) ()

lemma lift_rows (A : Array1 (r+1)) : emptyPrefix (Lifted A)=capLift r (emptyPrefix A) := by
  funext i; exact congr_arg _ (Subsingleton.elim _ i)

/-- Equality on coefficients, includes the motion/shears in later use. -/
lemma single_lift {A : Array1 (r+1)} (h : Whole (emptyPrefix A)) (p : boundary r A=0) :
    boundary (r+1) (Lifted A)=A := by
  have hh : Whole (emptyPrefix (Lifted A)) := lift_rows A ▸ whole_fold h _
  have hs : emptyPrefix (boundary (r+1) (Lifted A))=emptyPrefix A := by
    rw [boundary_rows]; refine bank_injective (hh.prod (Whole.boundary _)).safe h.safe fun c => ?_
    rw [hh.acts (Whole.boundary _) _,lift_rows]
    apply dormant_right h _ c
    intro x; rw [← h.acts (Whole.boundary r), ← boundary_rows, p]
    exact barren_acts x
  exact congr_fun hs ()

section vacuum
variable {A B : Array1 0}

def partialRise (s : Axis) (R : Row α (TypeFace 0)) :=
    composeRows (dashAxis s R) (constantRows (left ℝ 0 s).transpose)
def climb (R : Row α (TypeFace 0)) : List Axis → Row α (TypeFace 1)
  | [] => 0
  | a :: l => plusRows (partialRise a R) (climb (pending a R) l)

lemma climb_stock {w : ι → ℝ} {A : ι → Row Unit (TypeFace 0)} (h : Next.Free.Stock (α:=fun _ => Unit) (β:=fun _ => TypeFace 0) w A) (l : List Axis) :
    Next.Free.Stock (α:=fun _ => Unit) (β:=fun _ => TypeFace 1) w fun i => climb (A i) l := by
  induction l generalizing A with
  | nil => exact Stock.home h.cash
  | cons a l ih =>
    have hh := (dash_stock h a).times (Stock.constant (constantRows (left ℝ 0 a).transpose) (constant_whole _))
    simp only [mul_one] at hh
    exact hh.plus (ih (pending_stock h a))

lemma pending_whole {R : Row α β} (h : Whole R) (a : Axis) : Whole (pending a R) :=
  (pending_stock (Stock.constant (ι:=Unit) R h) a).whole ()
lemma climb_whole {R : Row Unit (TypeFace 0)} (h : Whole R) (l : List Axis) : Whole (climb R l) :=
    (climb_stock (Stock.constant (ι:=Unit) R h) l).whole ()
lemma climb_linear {R T : Row Unit (TypeFace 0)} (h : Whole R) (g : Whole T) (l : List Axis) :
    climb (R+T) l=climb R l+climb T l := by
  induction l generalizing R T with
  | nil => simp [climb]
  | cons a l ih =>
    simp only [climb,pending_linear h g,partialRise, dash_linear h g, plus_rows]
    rw [compose_plus (dash_whole h _) (dash_whole g _) (constant_whole _), ih (pending_whole h a) (pending_whole g a)]; abel
lemma climb_scale {R : Row Unit (TypeFace 0)} (h : Whole R) (l : List Axis) (x : ℝ) :
    climb (x • R) l=x • climb R l := by
  induction l generalizing R with
  | nil => simp [climb]
  | cons a l ih =>
    have he : dashAxis a (x • R)=x • dashAxis a R := funext fun i => funext fun j => payout_scale _ _ _
    have hg : pending a (x • R)=x • pending a R := funext fun i => funext fun j => payout_scale _ _ _
    simp only [climb, partialRise, plus_rows,hg,ih (pending_whole h a),he,
      compose_scale (dash_whole h _) (constant_whole _) x, smul_add]

lemma weave (p : Momentum) (s : Axis) : (left ℂ 0 s).transpose*symbol 0 p=q p s • 1 := by
  ext i j
  rw [vac_only i,vac_only j,Matrix.mul_apply]
  rw [Finset.sum_eq_single (coord s)]
  · have he (a : Axis) : left ℂ 0 a (coord s) vac = if a=s then 1 else 0 := by
      simp only [left,Matrix.of_apply,coord, Finset.mem_singleton]
      split_ifs with h
      · subst a; simp [parity,pre,Finset.filter_singleton]
      · rename_i H; exact False.elim (H (vac_only _))
      rfl
    simp only [Matrix.transpose_apply,symbol,wedge,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,he]
    simp
  · intro b hb hw
    rw [Matrix.transpose_apply,left,Matrix.of_apply,dif_neg]
    · rw [zero_mul]
    intro he; obtain ⟨i,rfl⟩ := axisEquiv.surjective b
    simp only [coord_map, coord, Finset.mem_singleton] at he
    exact hw (he ▸ rfl)
  simp

def swept (p : Momentum) (l : List Axis) := fun i => if i∈l then 0 else p i
lemma swept_physical (p : Momentum) (hp : physical p) (l : List Axis) : physical (swept p l) := by
  rw [physical_iff] at *; intro i; by_cases he : i∈l <;> simp [swept,he,hp]
lemma climbed {R : Row Unit (TypeFace 0)} (h : Whole R) (l : List Axis) (p : Momentum) (hp : physical p) :
    (climb R l).read p*symbol 0 p=R.read p - R.read (swept p l) := by
  induction l generalizing R with
  | nil => rw [show swept p []=p from funext fun i => if_neg (by simp)]; simp [climb]
  | cons a l ih =>
    let K := constantRows (left ℝ 0 a).transpose; have he : Whole K := constant_whole _
    have hh : Whole (partialRise a R) := (dash_whole h _).prod he
    rw [climb,hh.read_plus (climb_whole (pending_whole h a) _) hp,Matrix.add_mul,
      ih (pending_whole h _), partialRise,(dash_whole h _).read he hp,constant_read]
    rw [show approached _ = (left ℂ 0 a).transpose from ?eq, Matrix.mul_assoc,weave,Matrix.mul_smul,
      Matrix.mul_one,read_part h a hp,read_blank h a hp,read_blank h a (swept_physical p hp l),
      show update (swept p l) a 0 = swept p (a :: l) from ?m]; abel
    case eq => rw [← left_crank]; rfl
    case m => funext i; by_cases hi : i=a <;> simp [hi,update,swept]

def fromZero (A : Array1 0) : Array1 1 := climb (emptyPrefix A) (List.finRange 4) ()
lemma empty_climb (R : Array1 0) : emptyPrefix (fromZero R)=climb (emptyPrefix R) (List.finRange 4) := by
  funext i; exact congr_arg _ (Subsingleton.elim _ i)
lemma vacuum_lift (h : Whole (emptyPrefix A)) (p : ∑' i, A vac i = 0) : boundary 0 (fromZero A)=A := by
  let R := emptyPrefix (fromZero A)
  have hr : Whole R := by unfold R; rw [empty_climb]; exact climb_whole h _
  have hh : emptyPrefix (boundary 0 (fromZero A))=emptyPrefix A := by
    rw [boundary_rows]; apply bank_injective (hr.prod (Whole.boundary _)).safe h.safe (Whole.eq_on (hr.prod (Whole.boundary _)) h ?_)
    intro z hz
    rw [hr.read (Whole.boundary _) hz.1, show R=_ from empty_climb A, reading,climbed h _ z hz.1]
    rw [show swept z (List.finRange 4)=0 from funext fun i => if_pos (List.mem_finRange _)]
    rw [show (emptyPrefix A).read 0 = 0 from ?_,sub_zero]; ext _ i
    rw [vac_only i]; simp only [emptyPrefix,Row.read,Matrix.of_apply,Laurent.read,mode_constant,one_smul]
    rw [← Complex.ofReal_tsum,p,Complex.ofReal_zero]; rfl
  exact congr_fun hh ()
end vacuum

/-- Uniformly in arbitrarily many passive indices (including additional Cover
coordinates). Use Decay there rather than summing post-width estimates first. -/
def Price1 (η C : ℝ) (A : Array1 r) := ∀ i, Decay size η C (A i)

variable {η θ C D : ℝ} {A R₁ : Array1 r}

def share η := ∑' x : Cover, wanes η (size x)
lemma share_pos (hη : 0 < η) : 0 < share η := by
  apply lt_of_lt_of_le (a:=0) (b:=wanes η (size (0:Cover))) (wanes_pos _ _) (Summable.le_tsum (wanes_summable hη) _ (fun x _ => (wanes_pos ..).le))
lemma Price1.strip (h : Price1 η C A) (hθ : θ < η) :
    (emptyPrefix A).strip θ (C*share (η-θ)) := by
  intro _ i
  let w (x : Cover) := C*wanes (η-θ) (size x)
  have he : SumBudget w (C*share (η-θ)) := by
    refine ⟨fun x => mul_nonneg (h i|>.cash) (wanes_pos ..).le, (wanes_summable (sub_pos.mpr hθ)).mul_left C,?_⟩
    unfold w share; rw [tsum_mul_left]
  unfold Width
  refine budget_minor he (fun x => by positivity) fun x => ?_
  exact (mul_le_mul_of_nonneg_left (h i x) (Real.exp_pos _).le).trans_eq (by unfold wanes w; rw [mul_left_comm,← Real.exp_add]; unfold wanes; congr 2; ring)
lemma Price1.whole (h : Price1 η C A) (hη : 0 < η) : Whole (emptyPrefix A) :=
  ⟨η/2,_,half_pos hη,h.strip (half_lt_self hη)⟩
lemma strip_gives {η C : ℝ} (h : (emptyPrefix A).strip η C) : Price1 η C A := by
  intro i x
  have he := h () i
  have hh : Real.exp (η*size x)*‖A i x‖ ≤ C := (he.2.1.le_tsum x (fun t _ => he.1 _)).trans he.2.2
  unfold wanes
  rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).2 (by rwa [mul_comm])

/-- Package a cost lemma from the single-row Stock. *Before* any A or cap. -/
lemma upright {n : ℕ} (u : Row Unit (TypeFace r) → Row Unit (TypeFace n))
    (h : ∀ (ι : Type) (w : ι → ℝ) (a : ι → Row Unit (TypeFace r)),
      Next.Free.Stock (α:=fun _ => Unit) (β:=fun _ => TypeFace r) w a →
      Next.Free.Stock (α:=fun _ => Unit) (β:=fun _ => TypeFace n) w (fun i => u (a i))) (hη : 0 < η) :
    ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ A : Array1 r, ∀ C ≥ 0, Price1 η C A → Price1 θ (F*C) (u (emptyPrefix A) ()) := by
  let ι := {i : (Array1 r × ℝ) // 0 ≤ i.2 ∧ Price1 η i.2 i.1}
  let a (i : ι) := emptyPrefix i.val.1
  let w (i : ι) := i.val.2
  obtain ⟨θ,F,hp,hF,H⟩ := (h ι w a ⟨fun i => i.property.1,η/2,share (η-η/2),half_pos hη,
    share_pos (sub_pos.mpr (half_lt_self hη)), fun i => mul_comm (w i) _ ▸ Price1.strip i.property.2 (half_lt_self hη)⟩).uniform
  refine ⟨θ,F,hp,hF,fun R C hv hy => ?_⟩
  apply strip_gives
  rintro x j; exact H ⟨(R,C),hv,hy⟩ () j
lemma preRise {r} (hη : 0 < η) :
    ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ A : Array1 (r+1), ∀ C ≥ 0, Price1 η C A → Price1 θ (F*C) (Lifted A) :=
  upright (capLift r) (fun _ _ _ h => folded_stock h _) hη
lemma preEmpty (hη : 0 < η) : ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ A : Array1 0, ∀ C ≥ 0,
    Price1 η C A → Price1 θ (F*C) (fromZero A) := upright (fun x => climb x (List.finRange 4)) (fun _ _ _ h => climb_stock h _) hη

/-- Both lifts linear on all funded sums. The cycle hypothesis will be used only
to prove the right-inverse property. -/
structure Single (r s : ℕ) (U : Array1 r → Array1 s) : Prop where
  price : ∀ η : ℝ, 0<η → ∃ θ F : ℝ, 0<θ ∧ 0<F ∧ ∀ A : Array1 r, ∀ C ≥ 0,
      Price1 η C A → Price1 θ (F*C) (U A)
  add : ∀ (f g : Array1 r), Whole (emptyPrefix f) → Whole (emptyPrefix g) → U (f+g)=U f+U g
  smul : ∀ (f : Array1 r) (x : ℝ), Whole (emptyPrefix f) → U (x • f)=x • U f

theorem lifted_single (r) : Single (r+1) (r+2) Lifted := by
  refine ⟨fun _ => preRise,fun P Q h g => ?_,fun P a h => ?_⟩
  · exact congr_fun (fold_linear h g (List.finRange 4)) ()
  exact congr_fun (fold_scale h (List.finRange 4) _) ()
theorem empty_single : Single 0 1 fromZero := by
  refine ⟨fun _ => preEmpty,fun P Q h g => ?_,fun P a h => ?_⟩
  · exact congr_fun (climb_linear h g (List.finRange 4)) ()
  exact congr_fun (climb_scale h (List.finRange 4) _) ()
end YM.CubicMatch.Lift
