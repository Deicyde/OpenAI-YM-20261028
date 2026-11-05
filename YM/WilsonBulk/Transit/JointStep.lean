import YM.WilsonBulk.Transit.Meaning

/-!
# Total-degree finite differences on rank-variable Shift

E4 `Newt...` works for single leg (earlier quadratic contraction uses).
For many legs in potential basis need its version on general `Laurent.Shift
α`; generalize recursion (via MVpolynomial throughout so elementary Ward
use later). Records a polynomial of TOTAL degree, not componentwise. Local
error bound in full exponent for truly arbitrary joint test. Handles negative
position integers in `Shift` sign convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet.Taylor
open scoped Topology BigOperators Classical
open Laurent Finset Function
open MvPolynomial (X C)
variable {α : Type} [Fintype α] [DecidableEq α]
abbrev Move (α : Type) := Shift α
abbrev Law (α : Type) := Move α→ℝ
def notch (i : α) : Move α:= Pi.single i 1
def hop (i : α) (f : Law α) (x : Move α) := f (x+notch i)-f x
def chain (f : Law α) : List α→ Law α
  | [] => f
  | i::l => chain (hop i f) l
omit [Fintype α] in
lemma hop_hop (i j : α) (f : Law α) : hop i (hop j f)=hop j (hop i f) := by funext x; unfold hop; rw [add_right_comm x]; ring
abbrev lineRead (x : Move α) (f : Formula α) := MvPolynomial.eval (fun i=> (x i:ℝ)) f

-- include address shift in polynomial output; avoids needing any bound on bind/subst totalDegree.
def scribble : ℕ → Law α → Move α→ Formula α
| 0,f,_ => C (f 0)
| n+1,f,c => C (((n+1:ℕ):ℝ)⁻¹) * ∑ i : α,(X i+C ((c i:ℤ):ℝ)) * scribble n (hop i f) (c-notch i)
lemma height (p : Law α) (n : ℕ) (u : Move α) : (scribble n p u).totalDegree ≤ n := by
  induction n generalizing p u with
  | zero=> simp [scribble]
  | succ n ih=>
     rw [scribble]; apply (MvPolynomial.totalDegree_mul _ _).trans; rw [MvPolynomial.totalDegree_C,zero_add]
     apply sum_cap _; intro i _; refine (MvPolynomial.totalDegree_mul ..).trans (le_trans (Nat.add_le_add (le_trans (MvPolynomial.totalDegree_add ..) ?_) (ih ..)) (Nat.add_comm 1 n).le)
     rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]; omega
lemma scrum (p : Law α) (n : ℕ) (u x : Move α) :
    lineRead x (scribble (n+1) p u)=((n+1:ℕ):ℝ)⁻¹*∑ i:α, ((x+u) i:ℝ)*lineRead x (scribble n (hop i p) (u-notch i)) := by
  simp only [lineRead,scribble,map_mul,map_sum,map_add,MvPolynomial.eval_X,MvPolynomial.eval_C,Pi.add_apply,Int.cast_add]
lemma origin (p : Law α) (n : ℕ) (u x : Move α) :
    lineRead x (scribble n p u)=lineRead (x+u) (scribble n p 0) := by
  induction n generalizing p x u with
  | zero => simp [lineRead,scribble]
  | succ n ih =>
    rw [scrum,scrum]; congr 1
    apply sum_congr rfl fun i _=>?_; rw [ih,ih (x:=x+u) (u:=0-_)]; rw [add_zero]; rw [show x+(u-notch i)=x+u+(0-notch i) from by abel]
lemma stride (p : Law α) (n : ℕ) (i : α) (x : Move α) : lineRead (x+notch i) (scribble (n+1) p 0) - lineRead x (scribble (n+1) p 0)= lineRead x (scribble n (hop i p) 0) := by
  induction n generalizing p i x with
  | zero =>
    rw [scrum,scrum]; simp_rw [add_zero,Pi.add_apply,Int.cast_add,add_mul,sum_add_distrib]
    simp [notch,lineRead,scribble,Pi.single_apply,ite_mul,apply_ite Int.cast]
  | succ n ih =>
    let a : ℝ := ((n+2:ℕ):ℝ)
    have ha : a ≠ 0:= by unfold a; positivity
    let c j y := lineRead y (scribble (n+1) (hop j p) (0-notch j))
    let b := lineRead x (scribble (n+1) (hop i p) 0)
    have he (j:α) : c j (x+notch i)-c j x=lineRead x (scribble n (hop j (hop i p)) (0-notch j)) := by
        unfold c; rw [origin _ _ _ (x+notch i),origin _ _ _ x,origin (hop j (hop i p)) n (0-notch j) x]; rw [add_right_comm x,ih]; rw [hop_hop]
    have h0 : c i (x+notch i) =b := by unfold c b; rw [origin]; simp
    rw [scrum,scrum]; simp_rw [add_zero]
    change a⁻¹*(∑ j:α, ((x+notch i) j:ℝ)*c j (x+notch i))-a⁻¹*(∑ j:α, (x j:ℝ)*c j x) = b
    rw [← mul_sub, inv_mul_eq_iff_eq_mul₀ ha]
    have ht : (∑ j:α, ((notch i) j:ℝ)*c j (x+notch i)) = b := by simp [notch,ite_mul,apply_ite Int.cast,Pi.single_apply]; exact h0
    simp_rw [Pi.add_apply,Int.cast_add,add_mul,sum_add_distrib]; rw [ht,add_sub_right_comm,← sum_sub_distrib]; simp_rw [← mul_sub,he]
    have hh : ((n+1:ℕ):ℝ)*b=∑ j:α,(x j:ℝ)*lineRead x (scribble n (hop j (hop i p)) (0-notch j)) := by
        unfold b; rw [scrum,mul_inv_cancel_left₀ (by positivity)]; simp only [add_zero]
    rw [← hh]; unfold a; push_cast; ring

def abridge (i : ℕ) (p : Law α) := ∑ n∈range i,scribble n p 0
def rest (n : ℕ) (p : Law α) (x : Move α) := p x-lineRead x (abridge n p)
lemma total_degree (i : ℕ) (p : Law α) (hi : i≠0) : (abridge i p).totalDegree < i := by
  have h : (abridge i p).totalDegree ≤ i-1:= sum_cap _ (fun j hj=> (height ..).trans (by rw [mem_range] at hj; omega)); omega
lemma rest_origin (p : Law α) (n : ℕ) : rest (n+1) p 0=0 := by
  have h i: lineRead 0 (scribble (i+1) p 0)=0:= by rw [scrum]; simp
  unfold rest; simp only [lineRead,abridge,map_sum]; rw [sum_range_succ']
  simp_rw [show ∀ i,MvPolynomial.eval (fun i : α => ((0:Move α) i:ℝ)) (scribble (i+1) p 0)=0 from h]
  simp [scribble]
lemma rest_shrink (p : Law α) (n : ℕ) (i : α) : hop i (rest (n+1) p)=rest n (hop i p) := by
  funext x; unfold hop rest
  have ht : lineRead (x+notch i) (abridge (n+1) p)-lineRead x (abridge (n+1) p)=lineRead x (abridge n (hop i p)) := by
     unfold abridge; simp only [lineRead,map_sum]; rw [sum_range_succ' (fun j=> lineRead (x+notch i) (scribble j p 0)),sum_range_succ' (fun j=> lineRead x (scribble j p 0))]
     have hz y : lineRead y (scribble 0 p 0)=p 0:= by simp [lineRead,scribble]
     rw [hz,hz,add_sub_add_right_eq_sub,← sum_sub_distrib]; exact sum_congr rfl fun j _=> stride ..
  change _ = p (x+notch i)-p x - lineRead x (abridge n (hop i p)); rw [← ht]; ring

lemma back {x : Move α} (h : x≠0) : ∃ i y, (x=y+notch i ∨ y=x+notch i) ∧ size y+1=size x := by
  obtain ⟨i,hi⟩ : ∃ i,x i≠0:= by contrapose! h; exact funext h
  have hz (f : Move α) (s:ℕ) (h : ∀ j, j≠i→ f j=x j) (ht : (f i).natAbs+s=(x i).natAbs) : size f+s=size x := by
    unfold size
    rw [← add_sum_erase _ _ (mem_univ i),← add_sum_erase _ (fun j=> (x j).natAbs) (mem_univ i),add_right_comm ((f i).natAbs),ht]; congr 1; exact sum_congr rfl fun a ha=> by rw [h a (mem_erase.mp ha).1]
  rcases hi.lt_or_gt with he|he
  · refine ⟨i,x+notch i,Or.inr rfl,hz _ 1 (fun j hj=> by simp [notch,hj]) ?_⟩; simp only [Pi.add_apply,notch,Pi.single_eq_same]; omega
  refine ⟨i,x-notch i,Or.inl (by abel),hz _ 1 (fun j hj=> by simp [notch,hj]) ?_⟩; simp only [Pi.sub_apply,notch,Pi.single_eq_same]; omega

-- use with a (0≤) convex budget s=0, no width loss beyond the extras put in input
lemma envelope (n : ℕ) (p : Law α) (s M : ℝ) (hs : 0≤s) (hM : 0≤M)
    (hp : ∀ l:List α,l.length=n → ∀ x, |chain p l x| ≤ M*Real.exp (s*size x)) (x : Move α) :
    |rest n p x| ≤ (1+(size x:ℝ))^n*(M*Real.exp (s*size x)) := by
  induction n generalizing p x with
  | zero => simpa [rest,abridge,lineRead] using (show |p x|≤M*_ from hp [] rfl x)
  | succ n ih =>
     let f := fun (x:Move α)=>(1+(size x:ℝ))^n*(M*Real.exp (s*size x))
     have he i : ∀ x, |hop i (rest (n+1) p) x| ≤ f x:= fun x=> by
       rw [rest_shrink]; exact ih (hop i p) (fun l hl=> hp (i::l) (by simp [hl])) x
     have hb (i : ℕ) (y : Move α) (hy : size y=i) : |rest (n+1) p y| ≤ (size y:ℝ)*f y := by
        induction i using Nat.strong_induction_on generalizing y with
        | h i hind =>
          by_cases hw : y=0; · subst y; rw [rest_origin,abs_zero]; unfold f; positivity
          obtain ⟨i,z,hh,hz⟩:= back hw
          have h := hind (size z) (by omega) z rfl
          have hv : f z ≤ f y:= by unfold f; gcongr <;> omega
          have hd : |rest (n+1) p y-rest (n+1) p z| ≤ f y := by
             rcases hh with h|h
             · rw [h]; have hl : f z≤ f (z+notch i):= by rwa [← h]
               exact (he i z).trans hl
             rw [abs_sub_comm, h]; exact he i y
          calc
            _ ≤ |rest (n+1) p z| + |rest (n+1) p y-rest (n+1) p z| := by simpa using abs_add_le (rest (n+1) p z) (rest (n+1) p y-rest (n+1) p z)
            _ ≤ (size z:ℝ)*f y + f y := add_le_add (h.trans (by gcongr)) hd
            _ = _ := by rw [← hz]; push_cast; ring
     refine (hb (size x) x rfl).trans ?_; unfold f; rw [← mul_assoc,pow_succ']; gcongr; linarith
end YM.WilsonBulk.Sheet.Taylor
