import YM.Exterior.Blade
/-!
# Stencil of dᵢ and actual linked lattice

No exterior annihilation postulate. Blade 2 exactly minimal corner faces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Exterior
open Lattice Bloch Laurent Matrix Function Finset
open scoped Topology BigOperators ContDiff

abbrev TypeFace (r : ℕ) := Blade Axis r
abbrev Body (r : ℕ) (n : Side) := Co n (TypeFace r)

def vac : TypeFace 0 := ⟨∅,card_empty⟩
theorem vac_only (x : TypeFace 0) : x=vac := Subtype.ext (card_eq_zero.mp x.property)

def coord (i : Axis) : TypeFace 1 := ⟨{i},card_singleton _⟩
theorem coord_iff (i j : Axis) : coord i=coord j ↔ i=j := by simp [coord]

def axisEquiv : Axis ≃ TypeFace 1 := Equiv.ofBijective coord
    ⟨fun i j => (coord_iff i j).mp, fun i => by obtain ⟨j,h⟩ := card_eq_one.mp i.property; exact ⟨j,Subtype.ext h.symm⟩⟩
@[simp] lemma coord_map (i : Axis) : axisEquiv i=coord i := rfl

def plaquette (p : PlaqAxes) : TypeFace 2 := ⟨{p.val.1,p.val.2},by simp [p.property.ne]⟩

lemma plaq_iff (p q : PlaqAxes) : plaquette p=plaquette q ↔ p=q := by
  refine ⟨?_, fun h => congr_arg _ h⟩
  rintro h
  rcases p with ⟨⟨i,j⟩,hi⟩; rcases q with ⟨⟨a,b⟩,hb⟩
  change i < j at hi; change a<b at hb
  have he : ({i,j} : Finset Axis)={a,b} := congr_arg Subtype.val h
  have ha : a∈({i,j} : Finset Axis) := by simp [he]
  have hb' : b∈({i,j} : Finset Axis) := by simp [he]
  simp only [Finset.mem_insert,mem_singleton] at ha hb'
  rcases ha with rfl|rfl <;> rcases hb' with he|hh
  · exact (hb.ne he.symm).elim
  · subst b; rfl
  · exact ((lt_asymm hi) (he ▸ hb)).elim
  exact (hb.ne hh.symm).elim

def plaqEquiv : PlaqAxes ≃ TypeFace 2 := Equiv.ofBijective plaquette ⟨fun i j => (plaq_iff i j).mp, fun i => by
  obtain ⟨a,b,h,H⟩ := card_eq_two.mp i.property
  rcases lt_or_gt_of_ne h with ht|ht
  · exact ⟨⟨(a,b),ht⟩,Subtype.ext H.symm⟩
  refine ⟨⟨(b,a),ht⟩,Subtype.ext ?_⟩
  change ({b,a}:Finset Axis)=_
  rw [H]; ext; simp; tauto⟩

@[simp] lemma plaq_map (p : PlaqAxes) : plaqEquiv p=plaquette p := rfl

/-- forward difference stencil -/
def cobound (r : ℕ) : Row (TypeFace (r+1)) (TypeFace r) := fun i j x =>
    ∑ k : Axis, left ℝ r k i j * ((if x=step k then (1:ℝ) else 0) - if x=0 then 1 else 0)

def support : Finset Cover := insert 0 (univ.image step)

lemma certified (r : ℕ) (i j) (x) (hx : x∉ support) : cobound r i j x=0 := by
  have he : x≠0 := fun h => hx (by simp [h,support])
  have ht (k : Axis) : x≠step k := fun h => hx (mem_insert_of_mem <| mem_image.mpr ⟨k,mem_univ _,h.symm⟩)
  unfold cobound; simp only [if_neg he, if_neg (ht _),sub_zero,mul_zero, sum_const_zero]

lemma cobound_safe (r : ℕ) : (cobound r).safe := fun i j =>
    summable_of_ne_finset_zero (s:=support) (fun b hb => by rw [certified _ _ _ _ (show _ from hb)]; simp)

def q (p : Momentum) : Axis → ℂ := fun i => Complex.exp (Complex.I * p i)-1

def symbol (r : ℕ) (p : Momentum) := wedge r (q p)

lemma factor (p : Momentum) (i : Axis) : mode p (step i)=Complex.exp (Complex.I*p i) := by simp [mode,mul_ite]

lemma reading (p : Momentum) (r : ℕ) : (cobound r).read p=symbol r p := by
  ext i j
  rw [Row.read, Matrix.of_apply, Laurent.read,tsum_eq_sum (s:=support)]
  · unfold cobound symbol wedge
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,Complex.ofReal_sum, Finset.mul_sum]
    rw [Finset.sum_comm]; refine sum_congr rfl fun d _ => ?_
    have h1 : step d ∈ support := mem_insert_of_mem (mem_image.mpr ⟨d,mem_univ d,rfl⟩)
    have h2 : (0:Cover) ∈ support := mem_insert_self ..
    have hh : (↑(left ℝ r d i j):ℂ)=left ℂ r d i j := by
      unfold left; simp only [Matrix.of_apply]; split_ifs <;> simp [parity]
    simp only [Complex.ofReal_sub,apply_ite ((↑):ℝ→ℂ),hh,
      Complex.ofReal_zero,mul_sub,mul_ite,mul_one,mul_zero,sum_sub_distrib, sum_ite_eq', if_pos h1,
      if_pos h2, mode_zero,one_mul,factor,sub_mul, q]
  intro b hb; rw [certified _ _ _ _ hb]; simp

lemma acts_apply (r : ℕ) (n : Side) (u v) :
    ((cobound r).acts n) u v = ∑ i : Axis,left ℝ r i u.2 v.2 *
      ((if v.1=u.1+step i then (1:ℝ) else 0) - if v.1=u.1 then 1 else 0) := by
  rw [Row.acts, Matrix.of_apply,tsum_eq_sum (s:=support)]
  · rw [show (∑ x∈support, if v.1=u.1+wrap n x then cobound r u.2 v.2 x else 0) = ∑ i : Axis, ∑ x ∈ support, if v.1=u.1+wrap n x then left ℝ r i u.2 v.2 *
        ((if x=step i then (1:ℝ) else 0) - if x=0 then 1 else 0) else 0 by
      conv_rhs => rw [sum_comm]
      refine sum_congr rfl fun k _ => ?_; split <;> simp [*,cobound]]
    refine sum_congr rfl fun k _ => ?_
    have h₁ : step k ∈ support := mem_insert_of_mem (mem_image.mpr ⟨k,mem_univ k,rfl⟩)
    have hh (x : Cover) : (if v.1=u.1+wrap n x then left ℝ r k u.2 v.2 * ((if x=step k then 1 else 0)- if x=0 then 1 else 0) else 0) =
        (if x=step k then (if v.1=u.1+step k then left ℝ r k u.2 v.2 else 0) else 0)-
        (if x=0 then (if v.1=u.1 then left ℝ r k u.2 v.2 else 0) else 0) := by
      have hD : step k ≠ (0:Cover) := fun h => by have he := congr_fun h k; simp at he
      by_cases hS : x=step k
      · subst x; simp [hD]
      by_cases hZ : x=0
      · subst x; by_cases hv : v.1=u.1 <;> simp [*,hD.symm]
      simp [hS,hZ]
    simp_rw [hh]; simp only [Finset.sum_sub_distrib, sum_ite_eq', if_pos h₁, if_pos (show (0:Cover)∈support from mem_insert_self ..), mul_sub,mul_ite,mul_one,mul_zero]
  intro b hb; split <;> first | exact certified r _ _ _ hb | rfl

lemma discrete (r : ℕ) (n : Side) (v : Body r n → ℝ) (x : Body (r+1) n) :
    ((cobound r).acts n *ᵥ v) x = ∑ i : Axis,
      if h : i∈x.2.val then parity x.2.val i ℝ * (v (x.1+step i,remove i x.2 h) - v (x.1,remove i x.2 h)) else 0 := by
  simp_rw [Matrix.mulVec,dotProduct, acts_apply,Finset.sum_mul]; rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  split <;> rename_i h
  · simp only [left,Matrix.of_apply,dif_pos h]
    have hk (q : TypeFace r) (p T Y : ℝ) : (if remove i _ h=q then T else 0)*Y*p=(if remove i _ h=q then T*Y*p else 0) := by split_ifs <;> simp
    simp only [hk, sum_ite_eq, mem_univ, ↓reduceIte]
    simp [mul_sub,sum_sub_distrib,mul_ite,ite_mul,sub_mul]
  simp only [left,Matrix.of_apply,dif_neg h, zero_mul,sum_const_zero]
end YM.Exterior
