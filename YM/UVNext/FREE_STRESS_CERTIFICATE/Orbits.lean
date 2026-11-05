import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube

/-! Residual permutations in the frame fixing axis zero (or zero and one).
Count both orders for the two-tail sums. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) {d : ℕ} (H : (freeTable F).RealSpin)

abbrev Wheels := Equiv.Perm Axis
def round (s : Wheels) : Signed := ⟨s,fun _ => false⟩
def ride (d : ℕ) (s : Wheels) : Module.End ℂ ((freeTable F).Field d) :=
  (freeTable F).mirror H d (round s)
lemma eps_round (s : Wheels) (i : Axis) : eps (round s) i = 1 := by
  simp [round,eps,Signed.matrix_at]

@[simp] lemma ride_link (p : Wheels) (a b c k : Axis) (h : 4 ≤ d) :
    ride F H d p (link F d h a b c k) = link F d h (p a) (p b) (p c) (p k) := by
  simp only [ride,signed_link,eps_round,one_mul,Complex.ofReal_one,one_smul]; rfl
@[simp] lemma ride_first (p : Wheels) (a b c e k : Axis) :
    ride F H 5 p (first F a b c e k) = first F (p a) (p b) (p c) (p e) (p k) := by
  simp only [ride,signed_first,eps_round,one_mul,Complex.ofReal_one,one_smul]; rfl
@[simp] lemma ride_unit (p : Wheels) : ride F H d p ((freeTable F).unit d) = (freeTable F).unit d := by simp [ride]

variable {X : Type*} [AddCommGroup X]

def singles (f : Axis → X) := ∑ a : Axis, if a=0 then 0 else f a
def pairs (f : Axis → Axis → X) := singles fun a => singles fun b => if a=b then 0 else f a b

def thirds (f : Axis → X) := ∑ a : Axis, if a=0 ∨ a=1 then 0 else f a

lemma singles_sum (f : Axis → X) (h : f 0=0) : (∑ a : Axis, f a) = singles f := by
  unfold singles; apply Finset.sum_congr rfl; intro b _; by_cases he : b=0 <;> simp [he,h]
lemma pairs_sum (f : Axis → Axis → X) (h : ∀ a, f a 0=0) (hl : ∀ a, f 0 a=0) (he : ∀ a, f a a=0) :
    (∑ a : Axis, ∑ b : Axis, f a b)=pairs f := by
  have hp (a : Axis) : (∑ b : Axis, f a b) = singles fun b => if a=b then 0 else f a b := by
    rw [singles_sum _ (h a)]; unfold singles
    congr 1; funext b; split_ifs with hh <;> simp_all
  unfold pairs; rw [singles_sum _ (by simp [hl])]; simp_rw [hp]
lemma thirds_sum (f : Axis → X) (h : f 0=0) (k : f 1=0) : (∑ a : Axis, f a) = thirds f := by
  unfold thirds; apply Finset.sum_congr rfl; intro b _; split_ifs with he
  · rcases he with rfl|rfl <;> assumption
  rfl

lemma single_change (f g : Axis → X) (h : ∀ i≠0, f i=g i) : singles f = singles g := by
  apply Finset.sum_congr rfl; intro i _; split_ifs with he
  rfl
  exact h _ he
lemma pair_change (f g : Axis → Axis → X) (h : ∀ i≠0,∀ j≠0,i≠j→f i j=g i j) : pairs f=pairs g := by
  apply single_change; intro i he; apply single_change; intro j hj
  split_ifs with hh
  rfl
  exact h _ he _ hj hh

-- axis certificate indep of fields
lemma single_eval (f : Axis → X) : singles f = f 1 + f 2 + f 3 := by
  change (∑ a : Fin (3+1), if a=(0:Axis) then (0:X) else f a) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ, Fin.sum_univ_succ,Fin.sum_univ_one]
  change (if (0:Axis)=0 then (0:X) else _) + ((if (1:Axis)=0 then 0 else f 1) +
    ((if (2:Axis)=0 then 0 else f 2)+(if (3:Axis)=0 then 0 else f 3))) = _
  simp [add_assoc]
lemma pair_eval (f : Axis→Axis→X) : pairs f = f 1 2 + f 1 3 + f 2 1 + f 2 3 + f 3 1 + f 3 2 := by
  simp only [pairs,single_eval]
  simp [add_assoc]
lemma third_eval (f : Axis → X) : thirds f = f 2 + f 3 := by
  change (∑ a : Fin (3+1), if a=0∨a=1 then (0:X) else f a) = _
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  change (if (0:Axis)=0 ∨ (0:Axis)=1 then (0:X) else _) + ((if (1:Axis)=0 ∨ (1:Axis)=1 then 0 else _) +
    ((if (2:Axis)=0 ∨ (2:Axis)=1 then 0 else f 2)+(if (3:Axis)=0 ∨ (3:Axis)=1 then 0 else f 3))) = _
  simp

-- Six orders; not relying on abstract orientation of perm group multiplication
def l12 : Wheels := Equiv.swap 1 2
def l13 : Wheels := Equiv.swap 1 3
def l23 : Wheels := Equiv.swap 2 3
def lP := l12*l23
def lM := l23*l12

def around (f : Wheels → X) := f 1 + f l12 + f l13 + f l23 + f lP + f lM

lemma tail_four : ∀ i : Axis, i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide

-- `simp` decide handles swaps on literal axes; abbreviate
set_option linter.unusedSimpArgs false in
lemma six_one (f : Axis → X) (i : Axis) (h : i≠0) :
    around (fun p => f (p i)) = singles f + singles f := by
  rw [single_eval]
  rcases tail_four i with rfl | rfl | rfl | rfl
  all_goals first | contradiction | (simp [around, l12,l13,l23,lP,lM,Equiv.swap_apply_def]; abel)
set_option linter.unusedSimpArgs false in
lemma six_two (f : Axis→Axis→X) (i j : Axis) (h : i≠0) (hj : j≠0) (ht : i≠j) :
    around (fun p => f (p i) (p j)) = pairs f := by
  rw [pair_eval]
  rcases tail_four i with rfl | rfl | rfl | rfl <;> rcases tail_four j with rfl | rfl | rfl | rfl
  all_goals first | contradiction | (simp [around, l12,l13,l23,lP,lM,Equiv.swap_apply_def]; abel)
lemma two_one (f : Axis→X) (i : Axis) (h : i≠0) (ht : i≠1) : f i + f (l23 i) = thirds f := by
  rw [third_eval]
  rcases tail_four i with rfl|rfl|rfl|rfl
  all_goals first | contradiction | simp [l23, add_comm]
lemma around_ext (f g : Wheels → X) (h : ∀ p : Wheels,p 0=0→ f p=g p) : around f=around g := by
  unfold around; rw [h 1 (by decide), h l12 (by decide), h l13 (by decide), h l23 (by decide),h lP (by decide),h lM (by decide)]

def revolving (d : ℕ) : Module.End ℂ ((freeTable F).Field d) := around (ride F H d)
def lastPair (d : ℕ) : Module.End ℂ ((freeTable F).Field d) := LinearMap.id + ride F H d l23

theorem revolve_value (v : (freeTable F).Field d) : revolving F H d v = around fun p => ride F H d p v := by
  simp only [revolving,around,LinearMap.add_apply]

theorem secure (v : (freeTable F).Field d) (h : ∀ p : Wheels,p 0=0 → ride F H d p v=v)
    (U : Submodule ℂ ((freeTable F).Field d)) (ht : v ∈ U.comap (revolving F H d)) : v∈U := by
  change revolving F H d v ∈ U at ht; rw [revolve_value, around_ext _ (fun _ : Wheels=>v) h] at ht
  have he : around (fun _ : Wheels=>v) = (6:ℂ) • v := by unfold around; module
  rw [he] at ht; have hQ := U.smul_mem ((6:ℂ)⁻¹) ht; rw [smul_smul] at hQ; norm_num at hQ; exact hQ

theorem securing (v : (freeTable F).Field d) (h : ride F H d l23 v=v)
    (U : Submodule ℂ ((freeTable F).Field d)) (ht : v ∈ U.comap (lastPair F H d)) : v∈U := by
  change v+ride F H d l23 v ∈ U at ht; rw [h,← two_smul ℂ] at ht
  have hQ := U.smul_mem ((2:ℂ)⁻¹) ht; rw [smul_smul] at hQ; norm_num at hQ; exact hQ

lemma harvest_single (f : Axis → (freeTable F).Field d) (i : Axis) (hi : i ≠ 0) (he : ∀ p : Wheels,p 0=0 → ride F H d p (f i) = f (p i))
    (U : Submodule ℂ ((freeTable F).Field d)) (hU : singles f∈U) : f i ∈ U.comap (revolving F H d) := by
  change revolving F H d (f i) ∈ U
  rw [revolve_value,around_ext _ (fun p => f (p i)) he,six_one _ _ hi]; exact U.add_mem hU hU
lemma harvest_pair (f : Axis → Axis → (freeTable F).Field d) (i j : Axis) (hi : i≠0) (hj : j≠0) (ht : i≠j)
    (he : ∀ p : Wheels,p 0=0 → ride F H d p (f i j) = f (p i) (p j))
    (U : Submodule ℂ ((freeTable F).Field d)) (hU : pairs f∈U) : f i j ∈ U.comap (revolving F H d) := by
  change revolving F H d (f i j) ∈ U
  rw [revolve_value,around_ext _ (fun p => f (p i) (p j)) he,six_two _ _ _ hi hj ht]; exact hU

end YM.UVNext.FreeStress
