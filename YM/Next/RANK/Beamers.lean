import YM.Next.RANK.Keys

/-!
# Exact jet samples seen by d

Use functions ONLY on positive plaquettes and physical axes colors. Pull a real
cochain on the cover. Prove triangular sampling: degree j marks obtained from
finite rows of forward differences of orders at least j; on the actual test
subspace this inverse is exact. d slots incl weight 0/1. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Beamer
open CellsInt Function Finsupp Labels Maxwell Tensor Lattice Finset 
open scoped Classical Topology BigOperators Pointwise ContDiff

variable {G : Gauge} {d n : ℕ}

-- positive indexing over entire cover
abbrev Address (G : Gauge) := Cover × PlaqAxes × G.ColorIndex
abbrev Horizon (G : Gauge) := Address G → ℝ

def light (p : Horizon G) (a b : Axis) (x : Cover) (h : a<b) : G.Color := WithLp.toLp 2 (fun i => p (x,⟨(a,b),h⟩,i))

def polar (p : Horizon G) : C2 G.Color := fun a b z => if h : a<b then light p a b z h else if hh : b<a then -(light p b a z hh) else 0

lemma poll_at (p : Horizon G) (a b) (x : Cover) (h : a<b) (i) : polar p a b x i=p (x,⟨(a,b),h⟩,i) := by rw [polar,dif_pos h]; rfl
lemma reverse (p : Horizon G) (a b) : polar p a b= -(polar p b a) := by
  funext z; rcases lt_trichotomy a b with h|h|h
  · simp only [Pi.neg_apply,polar,h,h.not_gt,↓reduceDIte,neg_neg]
  · subst a; simp [polar]
  simp only [Pi.neg_apply,polar,h,h.not_gt,↓reduceDIte]

def shutter (p : Horizon G) := ∀ a b c, stepValue (polar p b c) a+stepValue (polar p c a) b+stepValue (polar p a b) c=0
lemma secured (p : Horizon G) (h : shutter p) : Secure (polar p) := ⟨reverse p, h⟩
lemma polar_add (f g : Horizon G) : polar (f+g)=polar f+polar g := by
  funext x y i; dsimp only [polar,Pi.add_apply]; split
  · rfl
  split; · rename_i H; exact neg_add (light f y x i H) (light g y x i H)
  simp
lemma polar_smul (r : ℝ) (f : Horizon G) : polar (r • f) = r • polar f := by
  funext x y i; dsimp only [polar,Pi.smul_apply]; split
  · rfl
  split
  · rename_i H; exact (smul_neg r (light f y x i H)).symm
  simp
lemma polar_zero : polar (G:=G) 0 = 0 := by simpa only [zero_smul] using! polar_smul 0 (fun _ : Address G => 0)
lemma step_add {V : Type*} [NormedAddCommGroup V] (x y : Cover→V) (i : Axis) : stepValue (x+y) i=stepValue x i+stepValue y i := jumps_add 1 (fun _ => i) x y

lemma shut_add (x y : Horizon G) (hx : shutter x) (hy : shutter y) : shutter (x+y) := by
  intro a b c; simp only [polar_add,Pi.add_apply,step_add]
  nth_rw 1 [show (0:Cover → G.Color)=0+0 by simp]
  nth_rw 1 [← hx a b c]; nth_rw 1 [← hy a b c]; abel
lemma shut_scale (r : ℝ) (x : Horizon G) (h : shutter x) : shutter (r • x) := by
  have he (a : Cover → G.Color) (i : Axis) : stepValue (r • a) i=r • stepValue a i := jumps_scale 1 (fun _ => i) a r
  intro a b c; simp only [polar_smul,Pi.smul_apply,he, ← smul_add]; rw [h a b c,smul_zero]

def signal (G : Gauge) : Submodule ℝ (Horizon G) where
  carrier := {p|shutter p}
  add_mem' := by intro x y;exact shut_add x y
  smul_mem' r p := shut_scale r p
  zero_mem' := by
    have he (i) : stepValue (0:Cover→G.Color) i=0 := jumps_zero 1 (fun _ => i)
    intro a b c; simp only [polar_zero,Pi.zero_apply,he,add_zero]

-- full stencil reads from positive faces. A origin coordinate over Cover (later pulled along R).

structure Degree (G : Gauge) where
  a : PlaqAxes
  paint : G.ColorIndex
  point : Cover
  degree : ℕ
  layout : Fin degree → Axis

variable (L : Degree G)

def gesture : Horizon G →ₗ[ℝ] ℝ where
  toFun x := jumps L.degree L.layout (fun z => x (z,L.a,L.paint)) L.point
  map_add' := fun x y => congr_fun (jumps_add _ _ (fun z => x (z,L.a,L.paint)) (fun z => y (z,L.a,L.paint))) L.point
  map_smul' := fun r x => congr_fun (jumps_scale _ _ (fun z => x (z,L.a,L.paint)) r) L.point

lemma gesture_hits (f : Horizon G) : gesture L f=jumps L.degree L.layout (polar f L.a.val.1 L.a.val.2) L.point L.paint := by
  let a := L.a
  have h (n : ℕ) (t) (u : Cover → G.Color) (p : Cover) (i : G.ColorIndex) : jumps n t u p i=jumps n t (fun p => u p i) p := by
    induction n generalizing u p with
    | zero => rfl
    | succ n H => rw [jumps,jumps,H]; rfl
  rw [h, show (fun p => polar f a.val.1 a.val.2 p L.paint)=fun p => f (p,L.a,L.paint) from funext fun p => poll_at f _ _ p _ _]; rfl

-- map from single Taylor level. Tested after curl, exactly discrete.

def inspect (A : Taylor G n) : Horizon G := fun q => let ⟨x,a,i⟩ := q; test A a.val.1 a.val.2 x i
lemma inspected (A : Taylor G n) : polar (inspect A)=test A := by
  have ht i j : test A i j= - test A j i := by rw [cigar A i j,cigar A j i]; abel
  ext1 i; ext1 j
  rcases lt_trichotomy i j with h|h|h
  · ext x c; exact poll_at _ _ _ _ h _
  · subst j; ext1 x; simp only [polar,lt_self_iff_false,↓reduceDIte]; rw [cigar]; simp
  rw [reverse, ht i j]; congr 1; ext x c; exact poll_at _ _ _ _ h _
lemma shutters (A : Taylor G n) : shutter (inspect A) := by intro a b c; rw [inspected]; exact stencil ..

def sweep (n : ℕ) : Taylor G n →ₗ[ℝ] Horizon G where
  toFun := inspect
  map_add' x y := by
    have he : trail (x+y) = trail x + trail y := by funext a z; exact congr_fun (east_add a (f:=x.value a) (g:=y.value a) (diag_smooth _ 1).continuous (diag_smooth _ 1).continuous) _
    have hh i j : test (x+y) i j=test x i j+test y i j := by
      rw [cigar,cigar,cigar,he]; simp only [Pi.add_apply,step_add]; abel
    funext ⟨a,b,z⟩; exact congr_arg (fun (f : Cover → G.Color) => f a z) (hh b.val.1 b.val.2)
  map_smul' a x := by
    have he i : trail (a • x) i=a • trail x i := funext fun z => congr_fun (east_scale a i (x.value i)) _
    have hh i j : test (a • x) i j=a • test x i j := by
      have h (w : Cover → G.Color) i : stepValue (a • w) i=a • stepValue w i := jumps_scale 1 (fun _ : Fin 1 => i) w a
      rw [cigar,cigar,he,he,h,h,smul_sub]
    funext ⟨k,b,z⟩; exact congr_arg (fun (f : Cover → G.Color) => f k z) (hh b.val.1 b.val.2)

-- uniqueness triangular deg>n differences vanish, globally. order n jumps exact.
lemma gesture_over (h : n < L.degree) (A : Taylor G n) : gesture L (sweep n A)=0 := by
  rw [gesture_hits, show sweep n A=inspect A from rfl, inspected]
  have hp (m : ℕ) (hz : n<m) (t : Fin m → Axis) (a b : Axis) : jumps m t (test A a b)=0 := by
    induction m with
    | zero => omega
    | succ m H =>
      rw [jumps,hopped]; by_cases h : n=m
      · have he (i) : jumps m (Fin.tail t) (test A a b) i= jumps m (Fin.tail t) (test A a b) 0 := by subst m; simp only [test_top]
        funext x; change _-_=0; exact sub_eq_zero.mpr ((he _).trans (he _).symm)
      rw [H (by omega)]; exact jumps_zero 1 (fun _ => _)
  rw [hp L.degree h]
  rfl

def tester (v : Key G) := sweep v.1 (axes G _ v.2)
end YM.Next.Rank.Beamer
