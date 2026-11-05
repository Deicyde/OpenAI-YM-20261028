import YM.Next.FREE_KERNELS.Sprout
import YM.Work.F06.Stencil
import YM.Work.F08.Rows



/-!
# Row-space arithmetic across varying shapes

All counting Width budgets require positive widths in use, so may also use
underlying absolute summability. Reuse F08 operations evaluated on EVERY
physical c/f site. Supply counterpart `read` identities on real p (keeping
stars convention). No `HasSum` from real fiber budgets alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate

variable {m n k : Type*}

lemma real_series {a : Cover → ℝ} (h : Summable fun i => ‖a i‖) {p : Momentum} (hp : physical p) :
    Summable fun i => mode p i*(a i:ℂ) := by apply Summable.of_norm; simpa only [norm_mul,mode_real p _ hp,one_mul,Complex.norm_real] using h
lemma real_sum {a : m → Cover → ℝ} (s : Finset m) (h : ∀ i∈s, Summable fun j => ‖a i j‖) {p : Momentum} (hp : physical p) :
    RRead (fun j => ∑ i∈s, a i j) p=∑ i∈s,RRead (a i) p := by
  unfold RRead Laurent.read; simp_rw [Complex.ofReal_sum,smul_eq_mul,Finset.mul_sum]; rw [Summable.tsum_finsetSum]; exact fun i hi => real_series (h i hi) hp
lemma real_join {a b : Cover → ℝ} {η C B : ℝ} (he : 0≤η) (ha : Width η C a) (hb : Width η B b) {p : Momentum} (hp : physical p) :
    RRead (routed id a fun _ => b) p=RRead a p*RRead b p := by
  let f := fun x y : Cover => mode p y*((a x*b (y-x):ℝ):ℂ)
  have hs := paths_safe he (d:=id) (fun a => le_rfl) ha (g:=fun _ => b) (fun _ => hb)
  have hm : Summable (Function.uncurry f) := by
    apply Summable.of_norm
    simpa only [Function.uncurry,f,norm_mul,mode_real p _ hp,one_mul,id_eq,Complex.norm_real,← Complex.ofReal_mul] using hs
  calc
    _ = ∑' y, ∑' x, f x y := by unfold RRead Laurent.read routed; simp_rw [f,Complex.ofReal_tsum,smul_eq_mul,id_eq,tsum_mul_left]
    _ = ∑' x, ∑' y, f x y := hm.tsum_comm
    _ = _ := by
      unfold RRead Laurent.read; rw [← tsum_mul_right]
      refine tsum_congr fun x => ?_; rw [← (Equiv.addRight x).tsum_eq,← tsum_mul_left]; refine tsum_congr fun i => ?_; unfold f; simp [mul_assoc,mul_comm,mul_left_comm]
lemma read_mul {A : Row m n} {B : Row n k} [Fintype n] {η x y : ℝ} (he : 0≤η) (ha : A.strip η x) (hb : B.strip η y)
    {p : Momentum} (hp : physical p) : (composeRows A B).read p=A.read p*B.read p := by
  ext i j
  change RRead (fun z => ∑ y, routed id _ _ z) p=_; rw [real_sum _ _ hp, Matrix.mul_apply]; swap
  · intro a ha'
    exact (((width_routed (d:=id) he (fun _ => le_rfl) (ha i a) (fun _ => hb a j)).unweighted he).2.1)
  exact Finset.sum_congr rfl fun a _ => real_join he (ha i a) (hb a j) hp
lemma read_opposite (A : Row m n) {p : Momentum} (hp : physical p) : (transRows A).read p=(A.read p)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  change RRead _ p=star (RRead _ p)
  unfold RRead transRows Laurent.read; rw [tsum_star, ← (Equiv.neg Cover).tsum_eq]; refine tsum_congr fun x => ?_
  have hh := mode_adjoint p x; rw [show star p=p from hp] at hh
  simp [hh,mul_comm]
lemma read_less {A B : Row m n} (ha : A.safe) (hb : B.safe) {p : Momentum} (hp : physical p) : (minusRows A B).read p=A.read p - B.read p := by ext i j; exact market_sub (ha i j) (hb i j) _ hp
lemma read_weight (A : Row m n) (c : ℝ) (p : Momentum) : (scaleRows c A).read p=(c:ℂ) • A.read p := by
  ext i j; simp only [scaleRows,Row.read,of_apply,Laurent.read,Complex.ofReal_mul, Matrix.smul_apply,smul_eq_mul]
  rw [← tsum_mul_left]; exact tsum_congr fun i => by ring
lemma read_unit (m : Type*) [DecidableEq m] (p : Momentum) : (unitRow m).read p=1 := by
  ext i j; by_cases h : i=j
  · subst j; unfold unitRow Row.read Laurent.read
    rw [Matrix.of_apply,tsum_eq_single 0]; simp
    intro x h; simp [h]
  simp [unitRow,Row.read,Laurent.read,h]

lemma delta_budget (r : ℕ) (η : ℝ) : ∃ C : ℝ, 0<C ∧ (cobound r).strip η C := by
  obtain ⟨C,-,h⟩ := Work.F06.strip_of_fin support (cobound r) (certified r) η
  exact ⟨max C 1, lt_max_of_lt_right one_pos, fun i j => (h i j).mono le_rfl (le_max_left ..)⟩

/-- One Row without varying scale. -/
def Whole (A : Row m n) := ∃ σ C : ℝ, 0<σ ∧ A.strip σ C
namespace Whole
variable {A B : Row m n} {D : Row n k}
lemma safe (h : Whole A) : A.safe := by obtain ⟨σ,C,hp,h⟩ := h; exact Row.rights _ _ h hp.le
lemma pass (ha : Whole A) (hb : Whole D) : ∃ σ x y : ℝ, 0<σ ∧ A.strip σ x ∧ D.strip σ y := by
  obtain ⟨σ,C,hp,h⟩ := ha; obtain ⟨θ,B,hθ,g⟩ := hb
  exact ⟨min σ θ,C,B,lt_min hp hθ,fun i j => (h i j).mono (min_le_left ..) le_rfl,fun i j => (g i j).mono (min_le_right ..) le_rfl⟩
lemma ditto (ha : Whole A) (hb : Whole B) : ∃ σ x y : ℝ, 0<σ ∧ A.strip σ x ∧ B.strip σ y := by
  obtain ⟨σ,C,hp,h⟩ := ha; obtain ⟨θ,B,hθ,g⟩ := hb
  exact ⟨min σ θ,C,B,lt_min hp hθ,fun i j => (h i j).mono (min_le_left ..) le_rfl,fun i j => (g i j).mono (min_le_right ..) le_rfl⟩
lemma prod [Fintype n] (ha : Whole A) (hb : Whole D) : Whole (composeRows A D) := by obtain ⟨σ,x,y,hp,h,g⟩ := ha.pass hb; exact ⟨σ,_,hp,strip_compose hp.le h g⟩
lemma read [Fintype n] (ha : Whole A) (hb : Whole D) {p : Momentum} (hp : physical p) :
    (composeRows A D).read p=A.read p*D.read p := by obtain ⟨σ,x,y,hp',h,g⟩ := ha.pass hb; exact read_mul hp'.le h g hp
lemma acts [Fintype n] (ha : Whole A) (hb : Whole D) (L : Side) : (composeRows A D).acts L=A.acts L*D.acts L := by obtain ⟨σ,x,y,hp,h,g⟩ := ha.pass hb; exact acts_compose hp.le h g _
lemma minus (ha : Whole A) (hb : Whole B) : Whole (minusRows A B) := by obtain ⟨σ,x,y,hp,h,g⟩ := ha.ditto hb; exact ⟨σ,_,hp,strip_minus h g⟩
lemma less (ha : Whole A) (hb : Whole B) (L : Side) : (minusRows A B).acts L=A.acts L-B.acts L := by obtain ⟨σ,x,y,hp,h,g⟩ := ha.ditto hb; exact acts_minus hp.le h g _
lemma flipped (ha : Whole A) : Whole (transRows A) := by obtain ⟨σ,C,hp,h⟩ := ha; exact ⟨_,_,hp,strip_trans h⟩
lemma weight (ha : Whole A) (r : ℝ) : Whole (scaleRows r A) := by obtain ⟨σ,C,hp,h⟩ := ha; exact ⟨_,_,hp,strip_scale h _⟩
lemma boundary (r : ℕ) : Whole (cobound r) := by obtain ⟨C,_,h⟩ := delta_budget r 1; exact ⟨1,C,one_pos,h⟩
lemma coin (m : Type*) [DecidableEq m] : Whole (unitRow m) := ⟨1,1,one_pos,strip_unit⟩
lemma eq_on {A B : Row m n} [Fintype m] [Fintype n] (ha : Whole A) (hb : Whole B)
    (h : ∀ p∈baseCube,A.read p=B.read p) (c : Side) : A.acts c=B.acts c := acts_of_cube ha.safe hb.safe h c
lemma read_ident {A B : Row m n} (ha : Whole A) (hb : Whole B)
    (h : ∀ c,A.acts c=B.acts c) (p : Momentum) : A.read p=B.read p := congr_arg (fun A => A.read p) (bank_injective ha.safe hb.safe h)
end Whole

variable {ι : Type*}
/-- Uniform width with variable type count. -/
structure Stock (w : ι → ℝ) {α β : ι → Type*} (A : ∀ i, Row (α i) (β i)) : Prop where
  cash i : 0 ≤ w i
  uniform : ∃ σ C : ℝ, 0<σ ∧ 0<C ∧ ∀ i, (A i).strip σ (C*w i)
namespace Stock
variable {w v x : ι → ℝ} {α β γ : ι → Type*} {A B : ∀ i, Row (α i) (β i)} {D : ∀ i, Row (β i) (γ i)}
lemma whole (h : Stock w A) (i : ι) : Whole (A i) := by obtain ⟨σ,C,hp,hC,h⟩ := h.uniform; exact ⟨_,_,hp,h i⟩
lemma raise (h : Stock w A) {c : ℝ} (hc : 0<c) (hw : ∀ i, w i ≤ c*x i) : Stock x A := by
  refine ⟨fun i => nonneg_of_mul_nonneg_right ((h.cash i).trans (hw i)) hc,?_⟩
  obtain ⟨σ,C,hp,hC,h⟩ := h.uniform
  exact ⟨σ,C*c,hp,mul_pos hC hc,fun i a b => (h i a b).mono le_rfl (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hw i) hC.le)⟩
lemma minus (ha : Stock w A) (hb : Stock w B) : Stock w fun i => minusRows (A i) (B i) := by
  refine ⟨ha.cash,?_⟩; obtain ⟨σ,C,hp,hC,h⟩ := ha.uniform; obtain ⟨θ,B,hθ,hB,g⟩ := hb.uniform
  exact ⟨min σ θ,C+B,lt_min hp hθ,by linarith,fun i a b => (strip_minus
    (strip_mono (h i) (min_le_left σ θ) le_rfl) (strip_mono (g i) (min_le_right σ θ) le_rfl) _ _).mono le_rfl (le_of_eq (add_mul ..).symm)⟩
lemma flipped (h : Stock w A) : Stock w fun i => transRows (A i) := by refine ⟨h.cash,?_⟩; obtain ⟨σ,C,hp,hC,h⟩ := h.uniform; exact ⟨σ,C,hp,hC,fun i => strip_trans (h i)⟩
lemma weight (h : Stock w A) (r : ℝ) : Stock w fun i => scaleRows r (A i) := by
  refine ⟨h.cash,?_⟩; obtain ⟨σ,C,hp,hC,g⟩ := h.uniform
  exact ⟨σ,(1+‖r‖)*C,hp,by positivity,fun i a b => ((strip_scale (g i) _) a b).mono le_rfl (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hC.le (h.cash i)))⟩
lemma prod [∀ i,Fintype (β i)] (ha : Stock w A) (hg : Stock v D) :
    Stock (fun i => (Fintype.card (β i):ℝ)*(w i*v i)) fun i => composeRows (A i) (D i) := by
  refine ⟨fun i => mul_nonneg (by positivity) (mul_nonneg (ha.cash i) (hg.cash i)),?_⟩
  obtain ⟨σ,C,hp,hC,h⟩ := ha.uniform; obtain ⟨θ,B,hθ,hB,g⟩ := hg.uniform
  exact ⟨min σ θ,C*B,lt_min hp hθ,mul_pos hC hB,fun i a b => (strip_compose (lt_min hp hθ).le (strip_mono (h i) (min_le_left σ θ) le_rfl) (strip_mono (g i) (min_le_right σ θ) le_rfl) a b).mono le_rfl (le_of_eq (by ring))⟩
lemma times {β : Type*} [Fintype β] {A : ∀ i, Row (α i) β} {D : ∀ i, Row β (γ i)} (ha : Stock (α:=α) (β:=fun _ => β) w A) (hg : Stock (α:=fun _ => β) (β:=γ) v D) : Stock (fun i => w i*v i) (fun i => composeRows (A i) (D i)) := by
  apply (ha.prod hg).raise (c:=Fintype.card β + 1) (by positivity)
  intro i; exact mul_le_mul_of_nonneg_right (by simp) (mul_nonneg (ha.cash i) (hg.cash i))
lemma constant (A : Row m n) (h : Whole A) : Stock (α:=fun _ => m) (β:=fun _ => n) (fun _ : ι => 1) fun _ => A := by
  obtain ⟨σ,C,hp,h⟩ := h; exact ⟨fun _ => zero_le_one,σ,max 1 C,hp,lt_max_of_lt_left one_pos,fun _ => strip_mono h le_rfl (by rw [mul_one]; exact le_max_right ..)⟩
end Stock
end YM.Next.Free
