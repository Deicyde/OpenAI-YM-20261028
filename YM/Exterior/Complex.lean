import YM.Exterior.Initial

/-! Counted gauge DOFs on actual oriented cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Exterior
open Lattice Bloch Laurent Matrix Function Finset
open RG Gauge Wilson
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n : Side}

abbrev form (r : ℕ) (n : Side) := Body r n → ℝ
abbrev d (r : ℕ) (n : Side) := (cobound r).acts n

lemma closed (r : ℕ) (n : Side) : d (r+1) n*d r n=0 := by
  apply Bloch.prom_inj
  apply cancel_rotation n
  rw [prom_mul,Matrix.mul_assoc,circulant _ _ (cobound_safe r),← Matrix.mul_assoc,circulant _ _ (cobound_safe (r+1)),Matrix.mul_assoc]
  simp_rw [reading]
  have h : fiber (fun p : Site n => symbol (r+1) (mon p))*fiber (fun p : Site n => symbol r (mon p))=0 := by
    ext ⟨x,i⟩ ⟨y,j⟩
    by_cases H : x=y
    · subst y
      simpa [fiber, mul_apply,Fintype.sum_prod_type,ite_mul,mul_ite,symbol] using congr_fun (congr_fun (d_d r (q (mon x))) i) j
    rw [mul_apply,Fintype.sum_prod_type]
    apply sum_eq_zero; intro z _
    apply sum_eq_zero; intro k _
    by_cases h' : z=x <;> simp [fiber,h',eq_comm (a:=x)]; tauto
  rw [h,Matrix.mul_zero,show approached (_:Matrix _ _ ℝ)=0 from ?_,Matrix.zero_mul]
  ext; simp [approached]

lemma d_sites (x : Site n) (i : Axis) (a : form 0 n) : (d 0 n *ᵥ a) (x,coord i)=a (x+step i,vac)-a (x,vac) := by
  rw [discrete]
  rw [Finset.sum_eq_single i]
  · rw [dif_pos (show i ∈ (coord i).val from mem_singleton_self i)]; simp [vac_only,parity,pre,coord, Finset.filter_singleton]
  · intro b _ hb; simp only [coord,mem_singleton,dif_neg hb]
  simp

lemma d_plaquettes (x : Site n) (p : PlaqAxes) (a : form 1 n) :
    (d 1 n *ᵥ a) (x,plaquette p)=
      a (x+step p.val.1, coord p.val.2)- a (x,coord p.val.2)- (a (x+step p.val.2,coord p.val.1)-a (x,coord p.val.1)) := by
  rw [discrete]
  let y := p.val.1
  let z := p.val.2
  let T := plaquette p
  have hy : y<z := p.property
  let q (i : Axis) := if h : i∈T.val then parity T.val i ℝ * (a (x+step i,remove i T h)-a (x,remove i T h)) else 0
  change (∑ i, q i) = _
  rw [← sum_subset (subset_univ ({y,z} : Finset Axis)), sum_insert (by simp [hy.ne]), sum_singleton]
  · have hv : y∈T.val := mem_insert_self ..
    have hw : z∈T.val := mem_insert_of_mem (mem_singleton_self z)
    change y<z at hy
    have hh : T.val={y,z} := rfl
    have hz : remove y T hv=coord z := by ext; simp [remove,coord, hh]; rintro rfl; exact hy.ne'
    have ha : remove z T hw=coord y := by ext i; by_cases hx : i=z <;> simp [hx,hh,coord,remove,hy.ne']
    unfold q
    rw [dif_pos hv, dif_pos hw,hz,ha]
    have h1 : parity T.val y ℝ=1 := by simp [parity,pre,hh,Finset.filter_insert,Finset.filter_singleton,hy.not_gt]
    have h2 : parity T.val z ℝ= -1 := by simp [parity,pre,hh,Finset.filter_insert,Finset.filter_singleton,hy]
    rw [h1,h2,one_mul,neg_one_mul]; rfl
  intro j _ hj; unfold q; rw [dif_neg (show j∉T.val from hj)]

/-- Cochain link sum on cover or periodized. -/
def linkSum {R X : Type*} [AddCommGroup R] [One R] [AddCommGroup X] (u : Links R X) (x : Four R) : Walk → X
  | [] => 0
  | a::l => (if a.neg then -u (a.used x) else u (a.used x))+linkSum u (x+a.vec) l

lemma ring_plaquette (x : Site n) (p : PlaqAxes) (a : form 1 n) :
    linkSum (fun e : Edge (Site n) => a (e.1,coord e.2)) x (square p.val.1 p.val.2)=(d 1 n *ᵥ a) (x,plaquette p) := by
  rw [d_plaquettes]; let i := p.val.1; let j := p.val.2
  have he : x+step i+step j -step i=x+step j := by abel
  have h : x+step i+step j +-step i=x+step j := by abel
  simp only [square,linkSum,Step.vec,Step.used, negDir, posDir,Bool.false_eq_true,↓reduceIte,add_zero]
  rw [h, he, add_sub_cancel_right]; dsimp [i,j]; abel

/-- Embed counting lift through Lie colors. -/
abbrev fieldDir (G : Gauge) (n : Side) (r : ℕ) := Body r n → G.Color

variable (G : Gauge)

def parts (r : ℕ) (A : fieldDir G n r) (i : G.ColorIndex) : form r n := fun e => A e i

def dColor (n : Side) (r : ℕ) (x : fieldDir G n r) : fieldDir G n (r+1) := fun b => WithLp.toLp 2 (fun i => ((d r n)*ᵥ (parts _ r x i)) b)

def collect (a : fieldDir G n 1) : Directions G n := fun e => a (e.1,coord e.2)

lemma path_component (a : fieldDir G n 1) (x : Site n) (w : Walk) (i : G.ColorIndex) :
    linkSum (fun e : Edge (Site n) => (collect G a) e i) x w = (linkSum (collect G a) x w) i := by
  induction w generalizing x with
  | nil => rfl
  | cons d w ih => rw [linkSum,linkSum,ih]; split <;> simp [*]

lemma fundamental (a : fieldDir G n 1) (x : Site n) (p : PlaqAxes) :
    linkSum (collect _ a) x (square p.val.1 p.val.2) = dColor G n 1 a (x,plaquette p) := by
  ext i; rw [← path_component]; exact ring_plaquette x p (parts _ 1 a i)

/-- Actual exponential stencil along a real field line. Proof includes shifts
around reversed links. -/
theorem curvature_linear (a : fieldDir G n 1) (x : Site n) (w : Walk) :
    HasDerivAt (fun t : ℝ => G.mat (travel (increment 1 (t • collect G a)) x w)) (G.colorMat (linkSum (collect G a) x w)) 0 := by
  have hk (v : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • v))) (G.colorMat v) 0 := by
    simp only [G.mat_lieExp,map_smul]; simpa using! hasDerivAt_exp_smul_const (G.colorMat v) (0:ℝ)
  have ht (U : Site n) (l : Walk) : travel (1:Config G n) U l=1 := by
    induction l generalizing U <;> simp_all [travel,Step.read]
  have hh (d : Step) (x : Site n) :
      HasDerivAt (fun t : ℝ => G.mat (d.read (increment 1 (t • collect G a)) x))
        (G.colorMat (if d.neg then -collect G a (d.used x) else collect G a (d.used x))) 0 := by
    unfold Step.read; split <;> simp only [increment,Pi.one_apply, Pi.smul_apply,mul_one]
    · rw [map_neg,← G.colorMat_skew]; simp only [G.mat_inv]; exact (hk _).star
    exact hk _
  induction w generalizing x with
  | nil => simp only [travel,linkSum,map_zero]; exact hasDerivAt_const _ _
  | cons d l ih =>
    simp_rw [travel,G.mat_mul]
    convert! (hh d x).mul (ih (x+d.vec)) using 1
    rw [zero_smul, show (increment (1:Config G n) 0 = 1) from funext fun i => by simp only [increment,Pi.zero_apply,G.mat_lieExp_zero,one_mul],ht,show d.read (1:Config G n) x=1 from by simp [Step.read], G.mat_one,mul_one,one_mul,linkSum,map_add]
end YM.Exterior
