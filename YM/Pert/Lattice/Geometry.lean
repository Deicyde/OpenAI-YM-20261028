import YM.Lattice.Site
import YM.Gauge.Chart
/-! Even inversion quotient for finite top Wilson diagrams; positivity after Feynman fixing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Orb
open Lattice

variable {n : Side}
abbrev Links (n : Side) := Edge (Site n)

def image (l : Links n) : Links n := (-l.1-step l.2, l.2)
@[simp] lemma image_image (l : Links n) : image (image l) = l := by apply Prod.ext <;> dsimp [image]; abel

def Admissible (n : Side) := 4 ≤ n.val ∧ 2 ∣ n.val

lemma image_ne_self (hn : Admissible n) (l : Links n) : image l ≠ l := by
  rintro e
  have h := congrArg (fun p : Links n => p.1 l.2) e
  have μ := ZMod.castHom (m:=2) (n:=n.val) hn.2 (ZMod 2)
  simp only [image, Pi.sub_apply, Pi.neg_apply, step_apply, ↓reduceIte] at h
  change -(l.1 l.2) - (1:Per n) = _ at h
  have hh := congrArg μ h
  rw [map_sub,map_neg,map_one] at hh
  have hs : ∀ p : ZMod 2, -p - 1 ≠ p := by decide
  exact hs _ hh

lemma site_induct (P : Site n → Prop) (h : ∀ x i, P x → P (x+step i)) (x : Site n) (hx : P x) (y : Site n) : P y := by
  have hc (z : Site n) (i : Axis) (k : ℕ) : P z → P (z + k • step i) := by
    induction k with
    | zero => simp
    | succ k ih => intro hz; rw [succ_nsmul,← add_assoc]; exact h _ _ (ih hz)
  let diff := y-x
  let k := fun i : Axis => (diff i).val
  have he : diff = ∑ i : Axis, k i • step i := by
    funext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp [k, Pi.smul_apply, nsmul_eq_mul]
    all_goals simp_all [Pi.smul_apply,ne_comm]
  have hq (s : Finset Axis) : P (x + ∑ i ∈ s, k i • step i) := by
    induction s using Finset.induction_on with
    | empty => simp [hx]
    | insert i s hs hh => rw [Finset.sum_insert hs,add_comm (k i • step i), ← add_assoc]; apply hc _ _ _ hh
  convert! hq Finset.univ using 1
  rw [← he]; dsimp [diff]; abel

lemma harmonic_const (f : Site n → ℝ) (hf : ∀ x, ∑ i : Axis, (f (x+step i) + f (x-step i) - (2:ℝ)*f x) = 0) (x y : Site n) :
    f x = f y := by
  obtain ⟨z,hz,H⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have eq : ∀ q : Site n, f q = f z := by
    refine site_induct _ ?_ z rfl
    intro t i ht
    have he := hf t
    have hh := (Finset.sum_eq_zero_iff_of_nonpos (fun (j : Axis) (_ : j∈Finset.univ) =>
      show f (t+step j) + f (t-step j) - 2*f t ≤ 0 by linarith [H (t+step j) (Finset.mem_univ _), H (t-step j) (Finset.mem_univ _)])).mp he i (Finset.mem_univ _)
    exact le_antisymm (H _ (Finset.mem_univ _)) (by linarith [H (t-step i) (Finset.mem_univ _)])
  simp [eq x, eq y]

section difference
variable {V : Type*} [AddCommGroup V]

def grad (f : Site n → V) (l : Links n) := f l.1 - f (l.1+step l.2)
def cur (A : Links n → V) (x : Site n) (i j : Axis) := A (x,i)+A (x+step i,j)-A (x,j)-A (x+step j,i)
def divB (A : Links n → V) (x : Site n) := ∑ i : Axis, (A (x,i)-A (x-step i,i))
def lap (f : Site n → V) (x : Site n) := ∑ i : Axis, (f (x+step i)+f (x-step i)-2 • f x)
lemma lap_eq (A : Links n → V) (hc : ∀ x i j, cur A x i j = 0) (x : Site n) (b : Axis) :
    lap (fun z => A (z,b)) x = divB A (x+step b)-divB A x := by
  unfold lap divB
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  have he1 : A (x+step b,i) = A (x,i)+A (x+step i,b)-A (x,b) := by rw [eq_comm, ← sub_eq_zero]; exact hc ..
  have he2 := hc (x-step i) i b
  rw [cur,sub_add_cancel] at he2
  have he3 : A (x+step b-step i,i) = A (x-step i,i)+A (x,b)-A (x-step i,b) := by
    rw [eq_comm,← sub_eq_zero, show x+step b-step i=x-step i+step b by abel]; exact he2
  rw [he1,he3]; abel
lemma sum_div (A : Links n → V) : ∑ x : Site n, divB A x = 0 := by
  unfold divB; rw [Finset.sum_comm]
  apply Finset.sum_eq_zero; intro i hi
  rw [Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  simpa [sub_eq_add_neg] using (Equiv.sum_comp (Equiv.addRight (-step i)) (fun z : Site n => A (z,i))).symm
lemma div_even (A : Links n → V) (e : ∀ l, A (image l) = -A l) (x) : divB A (-x) = divB A x := by
  apply Finset.sum_congr rfl; intro i hi
  rw [show ((-x-step i),i)=image (x,i) from rfl,show ((-x),i)=image ((x-step i),i) by unfold image; congr 1; change -x=-((x-step i): Site n)-(step i); simp [neg_sub],e,e,neg_sub_neg]
end difference

variable {G : Gauge}
lemma closed_div_zero (A : Links n → G.Color) (hc : ∀ x i j, cur A x i j = 0) (hd : ∀ x, divB A x = 0) (b : Axis) (x y) : A (x,b) = A (y,b) := by
  ext k
  apply harmonic_const (fun t => A (t,b) k) _ x y
  intro a
  have hl : lap (fun z => A (z,b)) a = 0 := by rw [lap_eq A hc]; simp only [hd,sub_self]
  have h := congrArg (fun (z : G.Color) => z k) hl
  rw [lap,WithLp.ofLp_sum,Finset.sum_apply] at h
  simpa only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,nsmul_eq_mul,Nat.cast_ofNat] using h

lemma kernel (A : Links n → G.Color) (he : ∀ l, A (image l)= -A l) (hc : ∀ x i j, cur A x i j=0) (hd : ∀ x, divB A x=0): A=0 := by
  ext l k
  have hh := closed_div_zero A hc hd l.2 (-l.1-step l.2) l.1
  rw [show ((-l.1-step l.2),l.2) = image l from rfl,he] at hh
  have he := congrArg (fun z : G.Color => z k) hh
  rw [PiLp.neg_apply] at he
  change A l k = (0:ℝ)
  linarith only [he]

def LinkP (G : Gauge) (n : Side) : Submodule ℝ (Links n → G.Color) where
  carrier := {A | ∀ l, A (image l) = -(A l)}
  zero_mem' l := by dsimp; rw [neg_zero]
  add_mem' {A B} ha hb l := show A (image l)+B (image l) = _ by rw [ha l,hb l,← neg_add]; rfl
  smul_mem' r A h l := show r • A (image l) = _ by rw [h, smul_neg]; rfl

def EvenSite (G : Gauge) (n : Side) : Submodule ℝ (Site n→G.Color) where
  carrier := {a | ∀ x, a (-x) = a x}
  zero_mem' _ := rfl
  add_mem' {_ _} h h' x := congrArg₂ (· + ·) (h x) (h' x)
  smul_mem' r _ h x := congrArg (r • ·) (h x)

def Zero (G : Gauge) (n : Side) : Submodule ℝ (Site n→G.Color) :=
  EvenSite G n ⊓ LinearMap.ker (LinearMap.proj (R:=ℝ) (0:Site n))
def Mean (G : Gauge) (n : Side) : Submodule ℝ (Site n→G.Color) :=
  EvenSite G n ⊓ LinearMap.ker (∑ x : Site n, LinearMap.proj (R:=ℝ) x)

abbrev Pot := ↥(LinkP G n)

end YM.Pert.Orb
