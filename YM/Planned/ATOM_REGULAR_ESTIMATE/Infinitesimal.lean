import YM.Planned.ATOM_REGULAR_ESTIMATE.Tangent
import YM.Work.B04

/-! Realization of polynomial log-link directions modulo lattice gauge on a
nonwrapping input. The radial constraints are exact, by Euler in the 4
Euclidean position components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Flat
open Function Tensor MeasureTheory Filter Lattice Wilson RG Source Labels Source.Drops Gauge Next.Foundations
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {d k : ℕ}
section Seed

def negateRad (Q : Axis → T E4 G.Color k) : T E4 G.Color (k+1) :=
    symmetrize (- (((((k+1:ℕ):ℝ)⁻¹) • ∑ i : Axis, added (Q i) (Maxwell.compAxis i))))

lemma negates (Q : Axis → T E4 G.Color k) (x : E4) :
    ((k+1:ℕ):ℝ) • diagonal (negateRad Q) x = -∑ i : Axis,x i • diagonal (Q i) x := by
  simp only [negateRad, symmetrize_diagonal]
  unfold Tensor.diagonal
  rw [neg_apply,smul_apply,sum_apply]
  simp only [smul_neg,smul_smul,mul_inv_cancel₀ (by positivity : ((k+1:ℕ):ℝ) ≠ 0), one_smul]
  exact congr_arg Neg.neg (Finset.sum_congr rfl fun i _ => added_diag _ _ _)

/-- The homogeneous Taylor packet at one nonnegative position degree after
subtracting its exact gradient. Degree zero is considered separately; it's ALL
gradient! -/
lemma radialize (Q : Axis → T E4 G.Color k) :
    ∃ R : Axis → T E4 G.Color k, (∀ i, Sym (R i)) ∧ (∀ x : E4, ∑ i : Axis,x i • diagonal (R i) x = 0) ∧
      ∀ i x, diagonal (R i) x = diagonal (Q i) x + Analysis.D (basis i) (diagonal (negateRad Q)) x := by
  let A := negateRad Q
  have hh : Sym A := symmetrize_sym _
  let L := (((k+1:ℕ):ℝ) • A.curryLeft)
  let R (i : Axis) := symmetrize (Q i + L (basis i))
  have he i (x : E4) : diagonal (R i) x = diagonal (Q i) x + Maxwell.grad i (diagonal A) x := by
    simp only [R,symmetrize_diagonal]
    unfold Maxwell.grad Analysis.D
    have he := differential_diagonal A hh x (basis i)
    rw [he]; unfold Tensor.diagonal L; rw [add_apply,smul_apply,smul_apply,Nat.cast_smul_eq_nsmul]
  refine ⟨R,fun _ => symmetrize_sym _,fun x => ?_,he⟩
  simp_rw [he,smul_add, Finset.sum_add_distrib]
  rw [Maxwell.grad_euler A hh, negates]; exact add_neg_cancel _

lemma radial_zero (R : Axis → T E4 G.Color 0) (hr : ∀ x : E4, ∑ i : Axis,x i • diagonal (R i) x = 0) (i : Axis) :
    R i=0 := by
  have he : diagonal (R i) (basis i)=0 := by simpa [ite_smul] using hr (basis i)
  ext1 v; rw [show v=fun _ => basis i from Subsingleton.elim ..]; exact he
end Seed

section Generation
variable (H : Hol G) (o : Site n) (X : Support n)

def stamps (A : T E4 G.Color (k+1)) (h : k < d) : MaskLog G d :=
  Pi.single (⟨k,h⟩:Fin d) A
lemma stamps_at (A : T E4 G.Color (k+1)) (h : k < d) (x : E4) :
    enter (stamps A h) x = diagonal A x := by
  unfold enter
  rw [Finset.sum_eq_single (⟨k,h⟩:Fin d)]
  · simp only [stamps,Pi.single_eq_same]
  · intro i _ hi; rw [stamps, Pi.single_eq_of_ne hi]; rfl
  simp
lemma stamps_end (A : T E4 G.Color (k+1)) (h : k < d) (i : Fin d) (hp : k < i.val) :
    stamps A h i=0 := Pi.single_eq_of_ne (fun he => (ne_of_gt hp) (congr_arg Fin.val he)) _

theorem restore_one (hp : Nonwrapping X o) (hn : 2 ≤ n.val)
    (Q : Axis → T E4 G.Color 0) (hd : 0 < d) : ∃ w : Perturb G d, Phase 1 w ∧
      ∀ x∈X, ∀ i, tangent H o w (x,i) = diagonal (Q i) (position (lift (x-o))) := by
  let A := negateRad Q
  obtain ⟨R,-,hr,hR⟩ := radialize Q
  refine ⟨(0,stamps A hd),⟨fun i _ => rfl,fun i hi => stamps_end A hd i (by omega)⟩,fun x hx i => ?_⟩
  have h := identify H o x X hp hn hx i ((0:Snap G d), stamps A hd)
  let v := lift (x-o)
  let l := position v
  have hZ : access (0:Snap G d) (v,i) = 0 := by simp [access,partConnection,potential,Taylor.value,Tensor.diagonal]
  change tangent _ _ _ _ = enter (stamps A hd) l + access (0:Snap G d) (v,i)-enter (stamps A hd) (l+basis i) at h
  rw [h,hZ,add_zero,stamps_at,stamps_at]
  have he := hR i l
  rw [radial_zero R hr i] at he
  have ht := Degree.diagonal_exact_one A (basis i) l
  change 0 = diagonal (Q i) l + Analysis.D _ (diagonal A) _ at he
  change _=diagonal (Q i) l
  rw [← ht] at he
  exact ((eq_neg_of_add_eq_zero_left he.symm).trans (neg_sub ..)).symm

def takeRad (R : Taylor G k) (h : k+1<d) : Snap G d := Pi.single (⟨k,by omega⟩ : Fin (d-1)) R
lemma takeRad_end (R : Taylor G k) (h : k+1<d) : Lower (k+2) (takeRad R h) := fun i hi => by
  unfold takeRad; apply Pi.single_eq_of_ne; intro he
  have ht : i.val=k := congr_arg Fin.val he; omega
lemma takeRad_field (R : Taylor G k) (h : k+1<d) (x : Cover) (i : Axis) (s : ℝ) :
    partConnection d (expand d (takeRad R h)) 1 (x,i) s = R.value i (position x + s • basis i) := by
  rw [partConnection,one_smul,one_smul]
  change potential d _ i (position x+s • basis i) = _
  rw [translates,Finset.sum_eq_single (⟨k,by omega⟩:Fin (d-1))]
  · simp only [takeRad,Pi.single_eq_same]
  · intro j _ hj; rw [takeRad,Pi.single_eq_of_ne hj]; rfl
  simp
lemma takeRad_records (R : Taylor G k) (h : k+1<d) (x : Cover) (i : Axis) :
    access (takeRad R h) (x,i) = ∫ s : ℝ in 0..1, R.value i (position x+s • basis i) := by
  unfold access; simp_rw [takeRad_field]

theorem restore (hp : Nonwrapping X o) (hn : 2 ≤ n.val)
    (Q : Axis → T E4 G.Color (k+1)) (hd : k+1 < d) :
    ∃ w : Perturb G d, Phase (k+2) w ∧ ∀ i : Axis, ∃ f : E4 → G.Color, Degree k f ∧
      ∀ x∈X, tangent H o w (x,i) = (diagonal (Q i)+f) (position (lift (x-o))) := by
  let A := negateRad Q
  obtain ⟨R,hs,hr,hR⟩ := radialize Q
  let T : Taylor G k := ⟨R,hs,hr⟩
  let w : Perturb G d := (takeRad T hd, stamps A hd)
  refine ⟨w,⟨takeRad_end T hd,fun i hi => stamps_end _ _ i (by omega)⟩,fun i => ?_⟩
  let Q' (x : E4) := (∫ s : ℝ in 0..1, T.value i (x+s • basis i)) - Tensor.diagonal (R i) x
  let P (x : E4) := diagonal A (x+basis i) - diagonal A x - Analysis.D (basis i) (diagonal A) x
  have hq : Degree k Q' := Degree.integrated_degree (R i) (basis i)
  have hP : Degree k P := Degree.diagonal_rest A (basis i)
  refine ⟨Q'-P,Degree.sub hq hP,fun x hx => ?_⟩
  let y := position (lift (x-o))
  have ht := identify H o x X hp hn hx i w
  change tangent _ _ _ _ = enter (stamps A hd) y + access (takeRad T hd) _-enter (stamps A hd) (y+basis i) at ht
  rw [ht,takeRad_records,stamps_at,stamps_at]
  let a := ∫ s : ℝ in 0..1, T.value i (y+s • basis i)
  change diagonal A y + a - _ = diagonal (Q i) y + ((a-diagonal (R i) y)- P y)
  rw [hR]
  unfold P A; abel
/-- Realization simultaneously on the whole stencil. Extra requirement
`FitsGrade` sees only internal edges; translations in this proof calculate on
that lift, not arbitrary torus arguments. -/
theorem interpolate (hp : Nonwrapping X o) (hn : 2 ≤ n.val) (v : Directions G n) (hv : FitsGrade o X k v)
    (he : k < d) : ∃ w : Perturb G d, Phase (k+1) w ∧ Agrees X v (tangent H o w) := by
  induction k generalizing v with
  | zero =>
    choose f hf hr using hv
    choose A hA using hf
    obtain ⟨w,hp,h⟩ := restore_one H o X hp hn (fun i => A i 0) he
    refine ⟨w,hp,?_⟩
    rintro ⟨x,i⟩ hx hz
    rw [hr i x hx hz,h x hx i,hA i, Nat.zero_add, Finset.sum_range_one]
  | succ k ih =>
    choose f hf hr using hv
    choose A hA using hf
    obtain ⟨w,hh,h⟩ := restore H o X hp hn (fun i => A i (k+1)) he
    choose F hF hf' using h
    let Q := v-tangent H o w
    have ht : FitsGrade o X k Q := by
      intro i; let D := ∑ j∈Finset.range (k+1), diagonal (A i j)
      have hd : Degree k D := ⟨A i,rfl⟩
      refine ⟨D - F i,Degree.sub hd (hF i), fun x hx hz => ?_⟩
      unfold Q; rw [Pi.sub_apply,hr i x hx hz,hf' i x hx,hA i, Finset.sum_range_succ]
      unfold D; simp only [Pi.add_apply,Pi.sub_apply]; abel
    obtain ⟨u,hu,hv'⟩ := ih Q ht (k.lt_succ_self.trans he)
    refine ⟨u+w,(hu.mono (Nat.le_add_right ..)).add hh,fun ⟨x,i⟩ hx hz => ?_⟩
    specialize hv' (x,i) hx hz
    dsimp only [Q,Pi.sub_apply] at hv'
    rw [map_add, Pi.add_apply,← hv',sub_add_cancel]

end Generation
end YM.Planned.AtomRegular.Flat
