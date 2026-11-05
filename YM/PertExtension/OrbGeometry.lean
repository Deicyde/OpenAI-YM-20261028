import YM.Lattice.Support
import YM.Lattice.Box
import YM.Gauge.MatrixGroup

/-! Inversion quotient with even side length. No fixed unoriented links.
Closed potential jets with this equivariance are gradients of even site jets.
This removes *all* harmonic one-form modes on the diagram regulator, without
an ad hoc deletion of gluon degrees at intermediate graph stages. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.Orb
open Lattice Function Set

variable {n : Side} {E : Type*}

/-- Positive edge (x,i) maps to the *inverse* of this edge. -/
def reflect (e : Edge (Site n)) : Edge (Site n) := (-e.1-step e.2, e.2)
@[simp] lemma reflect_reflect (e : Edge (Site n)) : reflect (reflect e)=e := by
  unfold reflect; ext <;> simp

lemma no_fixed_edge (h : Even n.val) (e : Edge (Site n)) : reflect e ≠ e := by
  rcases e with ⟨x,i⟩
  intro he
  have ht : 2 * (-x i)=1 := by
    replace he := congr_arg (fun (p : Edge (Site n))=>p.1 i) he
    change ((-x-step i):Site n) i=x i at he; simp only [Pi.sub_apply, Pi.neg_apply, step_apply, ite_true] at he
    rw [two_mul]
    calc
      -x i + -x i = -(x i) + x i + 1 := by nth_rw 2 [← he]; abel
      _ = _ := by abel
  let f := ZMod.castHom h.two_dvd (Per ((2:ℕ+) : Side))
  have : ∀ y : Per n, 2*y ≠ 1 := by
    intro y hy
    replace hy := congr_arg f hy
    rw [map_mul,map_ofNat,map_one] at hy
    have hz : (2 : Per ((2:ℕ+):Side)) = 0 := by decide
    rw [hz,zero_mul] at hy; exact (by decide : (0:ZMod 2) ≠ 1) (show (0:ZMod 2)=1 from hy) -- characteristic 2
  exact this _ ht

/-- Ordinary positive-direction lattice curl. -/
def Curl [AddCommGroup E] (A : Links (Per n) E) (x) (i j : Axis) :=
  A (x,i)+A (x+step i,j)-A (x+step j,i)-A (x,j)

def Closed [AddCommGroup E] (A : Links (Per n) E) : Prop := ∀ x i j, Curl A x i j=0

def arrival {n : Side} (x : Site n) : Walk := route 0 (Lattice.lift x) (Equiv.refl _)
@[simp] lemma arrival_end {n : Side} (x : Site n) : stop (0:Site n) (arrival x) = x := by
  unfold arrival
  rw [← map_zero (Lattice.wrap n), ← wrap_stop_cover,route_end,wrap_lift]

section Curl
variable [AddCommGroup E]

def cash (A : Links (Per n) E)(d : Step)(x : Site n) : E := if d.neg then -(A (d.used x)) else A (d.used x)
@[simp] lemma cash_pos (A : Links (Per n) E)(i)(x : Site n) : cash A (posDir i) x=A (x,i) := rfl
@[simp] lemma cash_neg (A : Links (Per n) E)(i)(x : Site n) : cash A (negDir i) x=-A (x-step i,i) := rfl
lemma cash_rev (A : Links (Per n) E)(d)(x : Site n) : cash A d.rev (x+d.vec)=-cash A d x := by
  rcases d with ⟨i,h|h⟩ <;> simp [cash, Step.rev,Step.vec,Step.used,sub_eq_add_neg]

private def swapAt (A : Links (Per n) E)(d f : Step) (x : Site n) : Prop := cash A d x + cash A f (x + d.vec) = cash A f x + cash A d (x + f.vec)
lemma Closed.commuting0 {A : Links (Per n) E}(hA : Closed A) (i j) : ∀ x,swapAt A (posDir i) (posDir j) x := by
  intro x
  change _=_
  specialize hA x i j; unfold Curl at hA
  rw [sub_sub, sub_eq_zero] at hA; rw [add_comm (A (x+step j,i))] at hA; exact hA
private lemma swap_symm {A : Links (Per n) E}{d f : Step} (h : ∀ x,swapAt A d f x) : ∀ x,swapAt A f d x := fun x=>(show _ from (h x).symm)
private lemma swap_rev_left {A : Links (Per n) E}{d f : Step} (h : ∀ x,swapAt A d f x) (x) : swapAt A d.rev f x := by
  specialize h (x+d.rev.vec)
  unfold swapAt at *; rw [Step.vec_rev] at *; rw [show (x+-d.vec+d.vec)=x from by rw [add_assoc,neg_add_cancel,add_zero]] at h
  have he (y : Site n) : cash A d.rev y = -cash A d (y+-d.vec) := by
    convert cash_rev A d (y+-d.vec) using 2; simp
  rw [he,he,add_assoc, add_comm (f.vec),← add_assoc]
  calc
    _ = (cash A f (x+-d.vec)+cash A d (x+-d.vec+f.vec)) - (cash A d (x+-d.vec)+cash A d (x+-d.vec+f.vec)) := by abel
    _ = _ := by rw [← h]; abel

lemma Closed.commuting {A : Links (Per n) E}(hA : Closed A) (d f) : ∀ x,swapAt A d f x := by
  obtain ⟨i,h|h⟩:=d
  · refine commuting_left_pos hA i f -- not yet
  exact swap_rev_left (commuting_left_pos hA i f)
where
  -- doesn't give field notation automatically
  commuting_left_pos {A : Links (Per n) E}(hA : Closed A) (i)(f : Step) : ∀ x,swapAt A (posDir i) f x := by
    obtain ⟨j,h|h⟩:=f
    · exact hA.commuting0 i j
    exact swap_symm (swap_rev_left (hA.commuting0 j i))

def line (A : Links (Per n) E)(x : Site n) : Walk → E
 | [] => 0
 | d::w => cash A d x + line A (x+d.vec) w

lemma line_append (A : Links (Per n) E) (x : Site n) (a b : Walk) : line A x (a++b)=line A x a+line A (stop x a) b := by
  induction a generalizing x <;> simp_all [stop,line,add_assoc]

lemma line_reverse (A : Links (Per n) E) (x : Site n) (a : Walk) :
    line A (stop x a) (reverse a) = -line A x a := by
  induction a generalizing x with
  | nil => simp [stop,line,reverse]
  | cons d a ih =>
    rw [show Lattice.reverse (d::a) = (Lattice.reverse a ++ [d.rev]) from by
      simp [Lattice.reverse,List.reverse_cons,List.map_append],line_append]
    simp only [stop,reverse_stop,ih,line,add_zero,cash_rev]; abel

lemma line_perm {A : Links (Per n) E}(hA : Closed A) {a b : Walk} (h : a.Perm b) (x : Site n) : line A x a=line A x b := by
  induction h generalizing x with
  | nil => simp
  | cons d ht ih => simp [line,ih]
  | swap d f l => have he := hA.commuting f d x; unfold swapAt at he; rw [line,line,line,line,← add_assoc,← add_assoc,he]; congr 1 <;> simp [add_right_comm] -- need syntax of rw defeq
  | trans g h ih ih' => rw [ih,ih']

def InvLink (A : Links (Per n) E) := ∀ e,cash A (negDir e.2) (-e.1)=A e
lemma inv_cash {A : Links (Per n) E} (h : InvLink A) (d : Step) (x : Site n) : cash A d.rev (-x) = cash A d x := by
  obtain ⟨i,hi|hi⟩:=d
  · exact h (x,i)
  have he := h (-x,i); rw [neg_neg] at he; exact he.symm

lemma inv_line {A : Links (Per n) E} (h : InvLink A) (a : Walk) (x : Site n) : line A (-x) (a.map Step.rev)=line A x a := by
  induction a generalizing x with
  | nil => rfl
  | cons d a ih =>
    simp only [List.map_cons,line,inv_cash h,Step.vec_rev, ← neg_add]; rw [ih]

lemma loop_zero [Module ℝ E] {A : Links (Per n) E} (h : InvLink A) (hc : Closed A) {w : Walk} (hw : stop (0:Site n) w = 0) : line A 0 w = 0 := by
  have ht := line_reverse A 0 w
  unfold reverse at ht; rw [hw,line_perm hc (List.Perm.map _ (List.reverse_perm _)), ← show - (0 : Site n)=0 from neg_zero, inv_line h] at ht
  refine smul_right_injective E (two_ne_zero : (2:ℝ) ≠ 0) (show (2:ℝ) • line A 0 w= ((2:ℝ) • (0:E)) from ?_)
  rw [two_smul,smul_zero]; simp only [neg_zero] at ht; apply Eq.trans (congrArg₂ (·+·) ht rfl) (neg_add_cancel (line A 0 w))
lemma path_eq [Module ℝ E] {A : Links (Per n) E} (h : InvLink A) (hc : Closed A) {a b : Walk}
    (ht : stop (0:Site n) a=stop (0:Site n) b) : line A 0 a=line A 0 b := by
  rw [← sub_eq_zero, sub_eq_add_neg, ← line_reverse A 0 b, ←ht, ← line_append]
  exact loop_zero h hc (by rw [stop_append,ht,reverse_stop])

lemma exact_curl [Module ℝ E] {A : Links (Per n) E} (h : InvLink A) (hc : Closed A) :
    ∃ P : Site n → E, P 0=0 ∧ ∀ x i, A (x,i)=P (x+step i)-P x := by
  let P (x : Site n):= line A 0 (arrival x)
  have hp (x : Site n) (i): stop x [posDir i]=x+step i := rfl
  have he : P 0=line A 0 [] := path_eq h hc (by simp [arrival_end,stop])
  refine ⟨P,he.trans rfl,fun x i=> ?_⟩
  have hx := path_eq h hc (a:= arrival x ++ [posDir i]) (b:=arrival (x+step i)) (by rw [stop_append,arrival_end,arrival_end,hp])
  rw [line_append,arrival_end,line,line,add_zero,cash_pos] at hx
  rw [← sub_eq_zero] at hx
  dsimp [P]; rw [← sub_eq_zero]; calc
    _ = line A 0 (arrival x) + A (x,i) - line A 0 (arrival (x+step i)) := by abel
    _ = _ := hx
end Curl
end YM.PertExtension.Orb
