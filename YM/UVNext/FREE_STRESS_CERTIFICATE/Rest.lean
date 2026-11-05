import YM.UVNext.FREE_STRESS_CERTIFICATE.Orbits

/-! Symmetric H tensor generators through degree four. The second diagonal type
uses both orders of the pairs, i.e. twice E's U2. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin)

def splitDiag (v : Axis → FourFields F) : (freeTable F).Stress := fun a b => if a=b then v a else 0
def panel (a b : Axis) : FourFields F := ∑ k, flat F a k b k
def near (a : Axis) := panel F a a
def far (a : Axis) : FourFields F := ∑ b : Axis, ∑ k : Axis, if b=a ∨ k=a then 0 else flat F b k b k
def total : FourFields F := ∑ b : Axis, ∑ k : Axis, flat F b k b k

def east := splitDiag F (near F)
def west := splitDiag F (far F)
def across : (freeTable F).Stress := fun a b => if a=b then 0 else panel F a b

lemma far_zero : far F 0 = pairs (fun i j => flat F i j i j) := by
  let f (i j : Axis) : FourFields F := if i=0 ∨ j=0 then 0 else flat F i j i j
  change (∑ i, ∑ j, f i j) = _
  have h (a : Axis) : f a a=0 := by unfold f; split_ifs <;> simp [flat]
  rw [pairs_sum f (by simp [f]) (by simp [f]) h]
  apply pair_change; intro i hi j hj _; simp [f,hi,hj]

lemma near_zero : near F 0 = singles (fun i => flat F 0 i 0 i) := by
  rw [near,panel,singles_sum _ (by simp [flat])]
lemma panel_one : panel F 0 1 = thirds (fun i => flat F 0 i 1 i) := by
  rw [panel,thirds_sum _ (by simp [flat]) (by simp [flat])]
lemma panel_flip (i j : Axis) : panel F i j = panel F j i := by
  exact Finset.sum_congr rfl (fun k _ => swap_link F _ i k j k)
lemma total_at (i : Axis) : total F = ((2:ℂ) • near F i) + far F i := by
  let f (a b : Axis) := flat F a b a b
  have h (a b : Axis) : f a b = f b a := by
    dsimp only [f,flat]; rw [left_link F _ b a,right_link F _ b a b a,neg_neg]
  have ht (a b : Axis) : f a b = (if a=i then f i b else 0) + (if b=i then f i a else 0) +
      (if a=i ∨ b=i then 0 else f a b) := by
    rcases eq_or_ne a i with ha|ha <;> rcases eq_or_ne b i with rfl|hb
    · simp_all [f,flat]
    · simp [ha,hb]
    · simp [ha]; exact h ..
    simp [ha,hb]
  change (∑ a, ∑ b, f a b)= (2:ℂ) • (∑ b, f i b) + (∑ a, ∑ b, _)
  conv_lhs => arg 2; intro a; arg 2; intro b; rw [ht a b]
  simp_rw [Finset.sum_add_distrib,Finset.sum_ite_irrel,Finset.sum_const_zero]
  simp [two_smul,f]

-- all generators eligible: centered real, symmetric and actual H tensor
lemma panel_star (a b : Axis) : (freeTable F).conj H 4 (panel F a b) = panel F a b := by simp [panel,flat]

lemma far_star (a : Axis) : (freeTable F).conj H 4 (far F a) = far F a := by
  unfold far; simp_rw [map_sum, apply_ite, flat,link_real,map_zero]

lemma square_eps (s : Signed) (i : Axis) : eps s i * eps s i = 1 := eps_self ..
lemma panel_transfer (s : Signed) (a b : Axis) :
    (freeTable F).mirror H 4 s (panel F a b) = (↑(eps s a * eps s b):ℂ) • panel F (s.perm a) (s.perm b) := by
  rw [panel,map_sum,panel, ← Equiv.sum_comp s.perm (fun k => flat F (s.perm a) k (s.perm b) k), Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i _
  dsimp only [flat]; rw [signed_link,show eps s a * eps s i * (eps s b * eps s i) = _ from
    calc
      _ = eps s a * eps s b * (eps s i * eps s i) := by ring
      _ = eps s a * eps s b := by rw [square_eps,mul_one]]
lemma total_transfer (s : Signed) : (freeTable F).mirror H 4 s (total F) = total F := by
  change (freeTable F).mirror H 4 s (∑ a, panel F a a) = _
  simp_rw [map_sum,panel_transfer,square_eps,Complex.ofReal_one,one_smul]
  exact Equiv.sum_comp s.perm (fun i => panel F i i)
lemma far_transfer (s : Signed) (a : Axis) : (freeTable F).mirror H 4 s (far F a) = far F (s.perm a) := by
  rw [show far F a = total F - (2:ℂ) • near F a by rw [total_at F a]; abel,
    map_sub,map_smul,total_transfer,near,panel_transfer,square_eps,Complex.ofReal_one,one_smul,total_at F (s.perm a)]
  unfold near; abel

lemma panel_mean (a b) : expectation (freeTable F) 4 (panel F a b)=0 := by simp [panel,flat,link,ff,mean_bond]
lemma far_mean (a) : expectation (freeTable F) 4 (far F a)=0 := by
  unfold far; simp_rw [map_sum, apply_ite,flat,link,ff,mean_bond,map_zero]; simp

lemma column_tensor (B : (freeTable F).Stress) (h : ∀ (s : Signed) (a b : Axis),
    (freeTable F).mirror H 4 s (B a b) = (↑(eps s a * eps s b):ℂ) • B (s.perm a) (s.perm b)) : RawTensor H B := by
  intro s a b
  rw [h]; simp_rw [Complex.ofReal_mul,mul_smul,← Finset.smul_sum]
  simp_rw [eps_column]

lemma diagonal_kernel (v : Axis → FourFields F)
    (h : ∀ (s : Signed) a, (freeTable F).mirror H 4 s (v a) = v (s.perm a))
    (g : ∀ a, (freeTable F).conj H 4 (v a)=v a) (m : ∀ a, expectation (freeTable F) 4 (v a)=0) :
    splitDiag F v ∈ KernelSpace H := by
  refine kernel_mem.mpr ⟨sym_mem.mpr ⟨fun i j => ?_,fun a b => ?_,column_tensor F H _ (fun s a b => ?_)⟩,
    fun a b => ?_⟩
  · unfold splitDiag; rcases eq_or_ne i j with rfl|hi
    · rfl
    simp [hi,Ne.symm hi]
  · unfold splitDiag; split <;> simp [g]
  · unfold splitDiag; rcases eq_or_ne a b with rfl|he
    · simp [square_eps,h]
    simp [he]
  · unfold splitDiag; split <;> simp [m]

lemma east_on : east F ∈ KernelSpace H :=
  diagonal_kernel F H _ (fun s a => by simp only [near,panel_transfer,square_eps,Complex.ofReal_one,one_smul])
    (fun a => panel_star F H _ _) (fun a => panel_mean F _ _)
lemma west_on : west F ∈ KernelSpace H := diagonal_kernel F H _ (far_transfer F H) (far_star F H) (far_mean F)
lemma across_on : across F ∈ KernelSpace H := by
  refine kernel_mem.mpr ⟨sym_mem.mpr ⟨fun a b => ?_,fun a b => ?_,column_tensor F H _ (fun s a b => ?_)⟩,fun a b => ?_⟩
  · unfold across; rcases eq_or_ne a b with rfl|h <;> simp_all [eq_comm]; exact panel_flip ..
  · unfold across; split <;> simp [panel_star]
  · simp only [across, apply_ite, map_zero, panel_transfer,s.perm.apply_eq_iff_eq,smul_zero]; split_ifs <;> rfl
  unfold across; split <;> simp [panel_mean]

end YM.UVNext.FreeStress
