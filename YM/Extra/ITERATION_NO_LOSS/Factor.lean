import YM.Extra.ITERATION_NO_LOSS.Patterns

/-!
# Real-space two-difference lift of a loop input

Only an identity on summed **linear curvatures** (tested on a whole
period, not after indicators). No complex division by momentum. Pays
one width shrink and a true-length squared moment even for winding
labels. Used once within a step (on the fine input width).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Lift
open Lattice Wilson RG Function Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

abbrev Piece (w : Walk) := Fin w.length

def axis (w : Walk) (i : Piece w) := (w.get i).dir
def sign (w : Walk) (i : Piece w) : ℤ := if (w.get i).neg then -1 else 1
def floor (z : Cover) (w : Walk) (i : Piece w) := ((w.get i).used (stop z (w.take i))).1

lemma floor_size (z : Cover) (w : Walk) (i : Piece w) : Laurent.size (floor z w i) ≤ Laurent.size z + w.length := by
  let x := stop z (w.take i)
  have he : Laurent.size x ≤ Laurent.size z + i.val := by simpa [x,i.isLt.le] using end_size z (w.take i)
  unfold floor Step.used; split
  · change Laurent.size (x-step _) ≤ _
    rw [sub_eq_add_neg]; apply (Laurent.size_add _ _).trans
    rw [Laurent.size_neg]; have ht := step_size (posDir (axis w i)); simp only [Step.vec_pos,axis] at ht; have := i.isLt; omega
  exact he.trans (Nat.add_le_add_left i.isLt.le _)

lemma telescopes (f : Site n → ℝ) (x : Site n) (z : Cover) (w : Walk) :
    f (x+wrap n (stop z w)) - f (x+wrap n z) = ∑ i : Piece w, (sign w i : ℝ) * grad (axis w i) f (x+wrap n (floor z w i)) := by
  induction w generalizing z with
  | nil => simp [Piece,stop]
  | cons d w ih =>
    change _ = ∑ i : Fin (w.length+1), (sign (d::w) i:ℝ)*grad (axis (d::w) i) f (x+wrap n (floor z (d::w) i))
    rw [show stop z (d::w)=stop (z+d.vec) w from rfl, Fin.sum_univ_succ (n:=w.length)]
    have he (i : Piece w) : floor z (d::w) i.succ = floor (z+d.vec) w i := rfl
    simp_rw [he]; have hh := ih (z+d.vec)
    change _ = (sign (d::w) 0:ℝ) * grad d.dir f (x+wrap n (floor z (d::w) 0)) +
      ∑ i : Piece w, (sign w i:ℝ)*grad (axis w i) f (x+wrap n (floor (z+d.vec) w i))
    rw [← hh]; cases d with
    | mk dir neg =>
      cases neg <;> simp [Step.vec,Step.used,sign,grad,floor,stop, add_assoc]; abel_nf

lemma projected (l : Axis) (z : Cover) (w : Walk) : stop z w l-z l = ∑ i : Piece w, if axis w i=l then sign w i else 0 := by
  induction w generalizing z with
  | nil => simp [Piece,stop]
  | cons d w ih =>
    change _ = ∑ i : Fin (w.length+1), if axis (d::w) i=l then sign (d::w) i else 0
    rw [Fin.sum_univ_succ (n:=w.length),stop]
    change _ = (if d.dir=l then sign (d::w) 0 else 0) + ∑ i : Piece w, if axis w i=l then sign w i else 0
    rw [← ih (z+d.vec)]; by_cases he : d.dir=l <;> cases h : d.neg <;> simp [Step.vec,sign,h,he,eq_comm] <;> first | exact Ne.symm he | omega

lemma linear_term (w : Walk) (g : Site n → ℝ) (x : Site n) :
    ∑ l : Axis, (stop 0 w l:ℤ)*grad l g x = ∑ i : Piece w, (sign w i:ℝ)*grad (axis w i) g x := by
  have he (l : Axis) : stop (0:Cover) w l = ∑ i : Piece w, if axis w i=l then sign w i else 0 := by simpa using projected l 0 w
  simp_rw [he, Int.cast_sum, Int.cast_ite, Int.cast_zero,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]; simp

lemma exchange (f g : Site n → ℝ) (y : Cover) : ∑ x, f x * g (x + wrap n y) = ∑ x, f (x + wrap n (-y)) * g x := by
  rw [← Equiv.sum_comp (Equiv.addRight (wrap n y)) (fun x => f (x+wrap n (-y))*g x)]
  simp

def driver (w : Walk) (i : Piece w) := route 0 (- floor 0 w i) 1
abbrev Fragment (w : Walk) := (i : Piece w) × Piece (driver w i)
lemma driver_length (w : Walk) (i : Piece w) : (driver w i).length ≤ w.length := by
  rw [driver,route_length,sub_zero,Laurent.size_neg]; simpa [Laurent.size] using floor_size 0 w i

/- Linear order divided difference on a whole opposite pair. -/
def taylor (y : Cover) (f g : Site n → ℝ) := ∑ x, f x * (g (x+wrap n y)-g x-∑ l : Axis, (y l:ℤ)*grad l g x)

def paired (w : Walk) (p : Fragment w) (f g : Site n → ℝ) (x : Site n) :=
    ((sign (driver w p.1) p.2 : ℝ) * (sign w p.1:ℝ)) * (grad (axis (driver w p.1) p.2) f
      (x+wrap n (floor 0 (driver w p.1) p.2)) * grad (axis w p.1) g x)

lemma taylor_lift (w : Walk) (f g : Site n → ℝ) : taylor (stop 0 w) f g = ∑ p : Fragment w, ∑ x, paired w p f g x := by
  unfold taylor
  have hd (x : Site n) : _ - g x = _ := (show g (x+wrap n (stop 0 w))-g x = _ by simpa using telescopes g x 0 w)
  simp_rw [hd,linear_term, ← sum_sub_distrib, mul_sum]
  rw [sum_comm, Fintype.sum_sigma]; apply sum_congr rfl; intro i _
  let y := floor 0 w i; let a := axis w i; let s := sign w i; let v := driver w i
  change (∑ x, f x*((s:ℝ)*grad a g (x+wrap n y)-(s:ℝ)*grad a g x)) = ∑ j : Piece v, ∑ x, paired w ⟨i,j⟩ f g x
  have he : stop (0:Cover) v=-y := route_end ..
  have hv (x : Site n) := telescopes f x 0 v
  simp only [he,map_zero,add_zero] at hv
  calc
    _ = s * ((∑ x, f x * grad a g (x + wrap n y)) - ∑ x, f x * grad a g x) := by
      rw [← sum_sub_distrib, mul_sum]; apply sum_congr rfl; intros; ring
    _ = s * ∑ x,(f (x+ wrap n (-y))-f x)*grad a g x := by rw [exchange]; simp_rw [sub_mul,sum_sub_distrib]
    _ = _ := by
      rw [sum_comm,mul_sum]; apply sum_congr rfl; intro x _
      rw [hv x,sum_mul,mul_sum]; apply sum_congr rfl; intro j _
      unfold paired; dsimp only; change _ = ((sign v j:ℝ)*(s:ℝ)) * (_ * _); ring

def road (a : Atom G 2) := route 0 (delta a) 1
abbrev Pieces (a : Atom G 2) := Fragment (road a)
lemma end_road (a : Atom G 2) : stop 0 (road a) = delta a := route_end ..
lemma length_road (a : Atom G 2) : (road a).length + 8 ≤ a.length := by
  rw [road,route_length,sub_zero,delta,sub_eq_add_neg, Atom.length, Fin.sum_univ_two]
  have ht := offset_size (a.leg 0); have hh := offset_size (a.leg 1)
  apply (Nat.add_le_add_right (Laurent.size_add _ _) _).trans
  rw [Laurent.size_neg]; unfold Slot.length; omega

abbrev types (a : Atom G 2) := fun i => (a.leg i).plaq

def breakUp (a : Atom G 2) (p : Pieces a) : Pattern G 2 :=
  let w := road a
  let v := driver w p.1
  ⟨![some (axis v p.2),some (axis w p.1)], relocate a ((sign v p.2:ℝ)*sign w p.1) ![floor 0 v p.2,0] (types a)⟩

lemma break_both (a : Atom G 2) (p : Pieces a) : both (breakUp a p) := by
  intro i; fin_cases i <;> rfl
lemma break_symm (a : Atom G 2) (h : a.Invariant) (p : Pieces a) : (breakUp a p).atom.Invariant := relocated_symm a h _ _ _
lemma break_length (a : Atom G 2) (p : Pieces a) : (breakUp a p).atom.length ≤ a.length := by
  dsimp only [breakUp]; rw [relocated_length, Fin.sum_univ_two]
  have he := length_road a
  have hl := driver_length (road a) p.1; have hp := floor_size 0 (driver (road a) p.1) p.2
  have h0 : Laurent.size (0:Cover) = 0 := by simp [Laurent.size]
  rw [h0] at hp; simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one,h0]; omega
lemma break_magnitude (a : Atom G 2) (p : Pieces a) : (breakUp a p).atom.magnitude = a.magnitude := by
  have he (w : Walk) (i : Piece w) : |(sign w i:ℝ)| = 1 := by cases h : w[i.val].neg <;> simp [sign,h]
  rw [breakUp, relocated_coeff, abs_mul, he,he]; simp

lemma break_cost (a : Atom G 2) (η : ℝ) (he : 0 ≤ η) :
    SumBudget (fun i => ((breakUp a i).atom).budget η) ((1+(a.length:ℝ))^2 * a.budget η) := by
  classical
  let f := fun i => ((breakUp a i).atom).budget η
  have h1 i : 0 ≤ f i := by unfold f Atom.budget Atom.magnitude; positivity
  have h' : 0 ≤ a.budget η := by unfold Atom.budget Atom.magnitude; positivity
  have h2 (i) : f i ≤ a.budget η := by unfold f Atom.budget; rw [break_magnitude]; gcongr; exacts [by unfold Atom.magnitude; positivity,break_length a i]
  refine ⟨h1, (hasSum_fintype f).summable,?_⟩
  change ∑' i, f i ≤ _
  rw [tsum_fintype,Fintype.sum_sigma]
  have ha : ((road a).length:ℝ) ≤ 1+(a.length:ℝ) := by
    have h := length_road a
    exact_mod_cast (show (road a).length ≤ 1+a.length by omega)
  calc
    _ ≤ ∑ _ : Piece (road a), ((road a).length:ℝ) * a.budget η := Finset.sum_le_sum fun i _ => by
      have hl := driver_length (road a) i
      apply (Finset.sum_le_sum (fun j (_: j ∈ (univ : Finset (Piece (driver (road a) i)))) => h2 ⟨i,j⟩)).trans
      simpa using mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ) |>.2 hl) h'
    _ = ((road a).length:ℝ)^2 * a.budget η := by simp; ring
    _ ≤ _ := by gcongr

abbrev Field (a : Atom G 2) (V : Flux G n) (b : Fin 2 → G.ColorIndex) i := V (types a i) (b i)

def constant (a : Atom G 2) (V : Flux G n) (x : Site n) (b : Fin 2 → G.ColorIndex) := a.coeff b * (Field a V b 0 x * Field a V b 1 x)

def slope (a : Atom G 2) (V : Flux G n) (x : Site n) (b : Fin 2 → G.ColorIndex) (l : Axis) := a.coeff b * delta a l *
    (Field a V b 0 x * grad l (Field a V b 1) x)

lemma break_eq (a : Atom G 2) (p : Pieces a) (V : Flux G n) (x : Site n) :
    (breakUp a p).sample V x = ∑ b, a.coeff b * paired (road a) p (Field a V b 0) (Field a V b 1) x := by
  simp only [Pattern.sample, breakUp, relocate, Fin.prod_univ_two,slot_plaq,slot_offset, Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one, map_zero, add_zero]; unfold read paired
  apply Finset.sum_congr rfl; intros; rw [mul_comm _ (a.coeff _),mul_assoc]; rfl

lemma resolve (a : Atom G 2) (V : Flux G n) :
    ∑ x : Site n, (plain a).sample V x = (∑ x,∑ b,constant a V x b) + (∑ x, ∑ b,∑ l,slope a V x b l) +
      ∑ p : Pieces a, ∑ x, (breakUp a p).sample V x := by
  simp_rw [break_eq]; conv_lhs => simp only [Pattern.sample,plain, read, Option.elim, Fin.prod_univ_two]; rw [Finset.sum_comm]
  have hx (p : Pieces a) : ∑ x : Site n, (∑ b, a.coeff b * paired (road a) p (Field a V b 0) (Field a V b 1) x) = _ := Finset.sum_comm
  simp_rw [hx]; rw [Finset.sum_comm (f:=fun x b => constant a V x b), Finset.sum_comm (f:=fun x b => ∑ l,slope a V x b l),
    Finset.sum_comm (f:=fun p b => ∑ x, a.coeff b * paired _ p _ _ x),← sum_add_distrib, ← sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _
  let f := Field a V b 0; let g := Field a V b 1; let w := road a; let u := a.coeff b
  have he := taylor_lift w f g; rw [end_road] at he
  let y := (a.leg 0).offset; let z := (a.leg 1).offset
  calc
    ∑ x : Site n, u*(f (x+wrap n y)*g (x+wrap n z)) = ∑ x, u*(f x*g (x+wrap n (delta a))) := by
      rw [← Equiv.sum_comp (Equiv.addRight (wrap n y)) (fun x => u*(f x*g (x+wrap n (delta a))))]
      unfold delta y z; simp [add_assoc]
    _ = (∑ x,constant a V x b)+(∑ x,∑ l,slope a V x b l)+ u*taylor (delta a) f g := by
      simp_rw [taylor, mul_sum]; rw [← sum_add_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro x _
      unfold constant slope; dsimp only [u,f,g]; simp only [mul_sub, mul_sum]; ring_nf
    _ = _ := by rw [he, Finset.mul_sum]; simp only [Finset.mul_sum,u]; rfl

variable {ι : Type*} {A : ι → Atom G 2}

lemma cancel_head (h : Silent A) (V : Flux G n) (x : Site n) (b : Fin 2 → G.ColorIndex) :
    HasSum (fun i => constant (A i) V x b) 0 := by
  let F (t : Fin 2 → PlaqAxes) := V (t 0) (b 0) x * V (t 1) (b 1) x
  have ht (t : Fin 2 → PlaqAxes) := ((h t b).1).mul_right (F t)
  convert! hasSum_sum (s:=univ) (fun t _ => ht t) using 1
  · funext i; simp [charge,F,constant,ite_mul]
  simp only [zero_mul,sum_const_zero]
lemma cancel_tail (h : Silent A) (V : Flux G n) (x : Site n) (b : Fin 2 → G.ColorIndex) (l : Axis) :
    HasSum (fun i => slope (A i) V x b l) 0 := by
  let F (t : Fin 2 → PlaqAxes) := V (t 0) (b 0) x * grad l (V (t 1) (b 1)) x
  have ht (t : Fin 2 → PlaqAxes) := ((h t b).2 l).mul_right (F t)
  convert! hasSum_sum (s:=univ) (fun t _ => ht t) using 1
  · funext i; simp [charge,F,slope,ite_mul]
  simp only [zero_mul,sum_const_zero]

def strip (A : ι → Atom G 2) (p : (i : ι) × Pieces (A i)) := breakUp (A p.1) p.2

lemma strip_cost {σ η C : ℝ} (h : Charged A σ C) (hp : 0 ≤ η) (he : η < σ) :
    Charged (fun p => (strip A p).atom) η (momentPrice 2 (σ-η)*C) := by
  have ht := h.moments 2 (sub_pos.mpr he)
  rw [sub_sub_cancel] at ht
  exact Cost.sigma ht fun i => break_cost _ η hp

lemma strip_total {σ η C : ℝ} (h : Charged A σ C) (hp : 0 ≤ η) (he : η < σ) (hh : Silent A) (V : Flux G n) :
    total (strip A) V = total (plain ∘ A) V := by
  have hc : HasSum (fun i => ∑ x,∑ b, constant (A i) V x b) 0 := by
    simpa using hasSum_sum (s:=univ) (fun x _ => hasSum_sum (s:=univ) (fun b _ => cancel_head hh V x b))
  have hs : HasSum (fun i => ∑ x,∑ b, ∑ l,slope (A i) V x b l) 0 := by
    simpa using hasSum_sum (s:=univ) (fun x _ => hasSum_sum (s:=univ) (fun b _ => hasSum_sum (s:=univ) (fun l _ => cancel_tail hh V x b l)))
  let F p := ∑ x, (strip A p).sample V x
  have hf : Summable F := net_summable (strip A) V hp (strip_cost h hp he)
  have hg := (hc.add hs).add hf.sigma.hasSum
  change (∑' p, F p) = _; rw [hf.tsum_sigma]; rw [zero_add,zero_add] at hg
  exact (HasSum.congr_fun hg (fun i => by rw [Function.comp_apply,resolve,tsum_fintype]; rfl)).tsum_eq.symm

end YM.Extra.Iteration.Lift
