import YM.Next.FREE_KERNELS.Lever

/-!
# Laurent lifts for the real mesh matrices

Release only after identities on the family with same stencil across ALL c,
not closure at a single period (harmonic rank deficiency). `duplex` handles
both exterior arguments sharing the same momentum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate

variable {m n ι : Type*} {r : ℕ}

/-- F08 operations abbreviation. -/
def plusRows (A B : Row m n) := minusRows A (scaleRows (-1) B)
lemma Whole.plus {A B : Row m n} (h : Whole A) (g : Whole B) : Whole (plusRows A B) := h.minus (g.weight (-1))
lemma Whole.read_plus {A B : Row m n} (h : Whole A) (g : Whole B) {p : Momentum} (hp : physical p) :
    (plusRows A B).read p=A.read p+B.read p := by rw [plusRows,read_less h.safe (g.weight _).safe hp,read_weight]; simp
lemma Whole.acts_plus {A B : Row m n} (h : Whole A) (g : Whole B) (c : Side) :
    (plusRows A B).acts c=A.acts c+B.acts c := by unfold plusRows; rw [h.less (g.weight _) c,acts_scale]; simp
lemma Stock.plus {w : ι → ℝ} {α β : ι → Type*} {A B : ∀ i, Row (α i) (β i)} (h : Stock w A) (g : Stock w B) : Stock w fun i => plusRows (A i) (B i) := h.minus (g.weight _)
@[simp] lemma barren_read (p : Momentum) : (0 : Row m n).read p=0 := by ext i j; simp [Row.read,Laurent.read]
@[simp] lemma barren_acts (c : Side) : (0 : Row m n).acts c=0 := by ext i j; simp [Row.acts]
lemma barren_strip (η : ℝ) : (0 : Row m n).strip η 0 := by intro i j; simp [Laurent.Width,SumBudget]
lemma barren_whole : Whole (0 : Row m n) := ⟨1,0,one_pos,barren_strip _⟩
lemma Stock.home {w : ι → ℝ} {α β : ι → Type*} (h : ∀ i, 0≤w i) : Stock (α:=α) (β:=β) w fun _ => 0 := by
  refine ⟨h,1,1,one_pos,one_pos,fun i => ?_⟩
  exact strip_mono (barren_strip 1) le_rfl (by simpa only [one_mul] using h i)

/-- Total residual after a list of axis contractions. -/
def sieved (r : ℕ) (A : Row m (TypeFace (r+1))) : List Axis → Row m (TypeFace (r+1))
| [] => A
| s::l => sieved r (shed s r A) l

def folded (r : ℕ) (A : Row m (TypeFace (r+1))) : List Axis → Row m (TypeFace (r+1+1))
| [] => 0
| s::l => plusRows (relief s r A) (folded r (shed s r A) l)

lemma folded_stock {w : ι → ℝ} {α : ι → Type*} {A : ∀ i, Row (α i) (TypeFace (r+1))}
    (h : Stock (α:=α) (β:=fun _ => TypeFace (r+1)) w A) (l : List Axis) :
    Stock (α:=α) (β:=fun _ => TypeFace (r+1+1)) w fun i => folded r (A i) l := by
  induction l generalizing A with
  | nil => exact Stock.home h.cash
  | cons s l ih => exact (relief_stock h s).plus (ih (shed_stock h s))
lemma whole_fold {A : Row m (TypeFace (r+1))} (h : Whole A) (l : List Axis) : Whole (folded r A l) :=
    (folded_stock (Stock.constant (ι:=Unit) A h) l).whole ()

lemma reigned_shed {A : Row m (TypeFace (r+1))} (h : Whole A) (s : Axis) (hr : Reigned r A) : Reigned r (shed s r A) := by
  intro p hp
  have hh := congr_arg (·*symbol r p) (success h s hr p hp)
  rw [Matrix.add_mul,hr p hp, Matrix.mul_assoc,show symbol (r+1) p*symbol r p=0 from Exterior.d_d ..,Matrix.mul_zero,zero_add] at hh
  exact hh
lemma full_stride {A : Row m (TypeFace (r+1))} (h : Whole A) (l : List Axis) (hr : Reigned r A) (p : Momentum) (hp : p∈baseCube) :
    (folded r A l).read p*symbol (r+1) p+(sieved r A l).read p=A.read p := by
  induction l generalizing A with
  | nil => rw [folded,barren_read,Matrix.zero_mul,zero_add,sieved]
  | cons s l ih =>
    have hv := ih (shed_whole s h) (reigned_shed h s hr)
    rw [folded,(relief_whole s h).read_plus (whole_fold (shed_whole s h) l) hp.1,Matrix.add_mul,sieved,add_assoc,hv, success h s hr p hp]
lemma sift_exhausted (A : Row m (TypeFace (r+1))) (l : List Axis) (i : m) (j : TypeFace (r+1))
    (h : A i j = 0 ∨ ∃ x∈j.val,x∈l) : sieved r A l i j=0 := by
  induction l generalizing A with
  | nil => simpa [sieved] using h
  | cons a l ih =>
    rw [sieved]; apply ih
    by_cases hA : a∈j.val
    · left; simp [shed,hA]; rfl
    rcases h with hx|⟨v,hv,g⟩
    · left; unfold shed pending; rw [if_neg hA, hx]; funext i; simp [payOut]
    exact Or.inr ⟨v,hv,(List.mem_cons.mp g).resolve_left fun hh => hA (hh ▸ hv)⟩

def capLift (r : ℕ) (A : Row m (TypeFace (r+1))) := folded r A (List.finRange 4)
lemma single_carry {A : Row m (TypeFace (r+1))} (h : Whole A) (hr : Reigned r A) (p : Momentum) (hp : p∈baseCube) :
    (capLift r A).read p*symbol (r+1) p=A.read p := by
  have he : sieved r A (List.finRange 4)=0 := by
    funext i j
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0<j.val.card by simp [j.property])
    exact sift_exhausted A _ _ _ (Or.inr ⟨a,ha, List.mem_finRange _⟩)
  have hm := full_stride h (List.finRange 4) hr p hp; rw [he,barren_read,add_zero] at hm; exact hm

lemma dormant_right [Fintype m] {A : Row m (TypeFace (r+1))} (h : Whole A)
    (hq : ∀ c, A.acts c*d r c=0) (c : Side) : (capLift r A).acts c*d (r+1) c=A.acts c := by
  have hr : Reigned r A := by
    intro p hp
    have hm := Whole.boundary r
    have hh := (h.prod hm).read_ident (B:=0) barren_whole (fun c => by rw [h.acts hm,hq c,barren_acts]) p
    rw [h.read hm hp.1,Exterior.reading,barren_read] at hh; exact hh
  let B := capLift r A
  have hB : Whole B := whole_fold h _
  have hh := Whole.boundary (r+1)
  exact ((hB.acts hh c).symm.trans ((hB.prod hh).eq_on h (fun p hp => by rw [hB.read hh hp.1,Exterior.reading]; exact single_carry h hr p hp) c))

def supplyLift (r : ℕ) (A : Row (TypeFace (r+1)) m) := transRows (capLift r (transRows A))
lemma dormant_left [Fintype m] {A : Row (TypeFace (r+1)) m} (h : Whole A)
    (hq : ∀ c, (d r c).transpose*A.acts c=0) (c : Side) : (d (r+1) c).transpose*(supplyLift r A).acts c=A.acts c := by
  have hx := dormant_right h.flipped (fun c => show (transRows A).acts c * d r c=0 from transpose_injective (by rw [transpose_mul,acts_trans,transpose_transpose,hq c,transpose_zero])) c
  unfold supplyLift; rw [acts_trans, ← Matrix.transpose_mul,hx, acts_trans,transpose_transpose]

-- Top-degree injectivity statement, even with varying number of other axes.
lemma roof_final [Fintype m] {A : Row (TypeFace 4) m} (h : Whole A)
    (hq : ∀ c, (d 3 c).transpose*A.acts c=0) (c) : A.acts c=0 := by
  letI : IsEmpty (TypeFace 5) := ⟨fun x => by have hc := Finset.card_le_univ x.val; rw [x.property] at hc; simp [Axis] at hc⟩
  have hb := dormant_left (r:=3) h hq c; rw [← hb]; ext i j; apply Finset.sum_of_isEmpty

namespace Double
variable (A : Row (TypeFace 2) (TypeFace 2))

def wing := supplyLift 1 A
-- d1ᵀ: left from degree 2 to 1; i₂ right each lift with its current degree.
def flow := composeRows (wing A) (cobound 1)
def top := supplyLift 2 (flow A) -- degree 4,1
def X := capLift 0 (top A) -- degree 4,2
def skip := minusRows (wing A) (composeRows (transRows (cobound 3)) (X A))
def both := capLift 1 (skip A)

variable {A}
lemma duplex (h : Whole A) (hq : ∀ c : Side, A.acts c*d 1 c=0)
    (hb : ∀ c : Side,(d 1 c).transpose*A.acts c=0) (c : Side) :
    (d 2 c).transpose*(both A).acts c*d 2 c=A.acts c := by
  have hW : Whole (wing A) := (whole_fold h.flipped _).flipped
  have hF : Whole (flow A) := hW.prod (Whole.boundary 1)
  have hT : Whole (top A) := (whole_fold hF.flipped _).flipped
  have hX : Whole (X A) := whole_fold hT _
  have h3 := (Whole.boundary 3).flipped
  have hK : Whole (skip A) := hW.minus (h3.prod hX)
  have he (c : Side) : (d 2 c).transpose * (wing A).acts c=A.acts c := dormant_left h hb c
  have hf (c : Side) : (flow A).acts c=(wing A).acts c*d 1 c := hW.acts (Whole.boundary 1) c
  have ht (c : Side) : (d 3 c).transpose*(top A).acts c=(flow A).acts c := dormant_left (r:=2) hF (fun c => by rw [hf,← Matrix.mul_assoc,he,hq]) c
  have hm (c : Side) : (top A).acts c*d 0 c=0 := by
    let J := composeRows (top A) (cobound 0)
    have hJ (c : Side) : J.acts c=(top A).acts c*d 0 c := hT.acts (Whole.boundary 0) c
    rw [← hJ]
    apply roof_final (A:=J) (hT.prod (Whole.boundary 0)) _ c
    intro c; rw [hJ,← Matrix.mul_assoc,ht,hf,Matrix.mul_assoc, Exterior.closed 0 c,Matrix.mul_zero]
  have hx (c : Side) : (X A).acts c*d 1 c=(top A).acts c := dormant_right (r:=0) hT hm _
  have hk (c : Side) : (skip A).acts c=(wing A).acts c-(d 3 c).transpose*(X A).acts c := by
    rw [skip,hW.less (h3.prod hX),h3.acts hX, acts_trans]
  have hh (c) : (skip A).acts c*d 1 c=0 := by rw [hk,Matrix.sub_mul,Matrix.mul_assoc,hx,ht,hf,sub_self]
  rw [Matrix.mul_assoc, show (both A).acts c*d 2 c=_ from dormant_right (r:=1) hK hh _,hk, Matrix.mul_sub,he,← Matrix.mul_assoc _ _ ((X A).acts c),← Matrix.transpose_mul, Exterior.closed 2 c,Matrix.transpose_zero,Matrix.zero_mul,sub_zero]

lemma duplex_stock {w : ι → ℝ} {A : ι → Row (TypeFace 2) (TypeFace 2)}
    (h : Stock w (α:=fun _ => TypeFace 2) (β:=fun _ => TypeFace 2) A) :
    Stock w (α:=fun _ => TypeFace 3) (β:=fun _ => TypeFace 3) fun i => both (A i) := by
  let d (r) := Stock.constant (ι:=ι) (cobound r) (Whole.boundary r)
  have hw := (folded_stock (r:=1) h.flipped (List.finRange 4)).flipped
  have hf := hw.times (d 1); simp only [mul_one] at hf
  have ht := (folded_stock (r:=2) hf.flipped (List.finRange 4)).flipped
  have hx := folded_stock (r:=0) ht (List.finRange 4)
  have hh := (d 3).flipped.times hx; simp only [one_mul] at hh
  exact folded_stock (r:=1) (hw.minus hh) (List.finRange 4)
end Double
end YM.Next.Free
