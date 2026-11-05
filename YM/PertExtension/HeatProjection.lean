import YM.Next.RANK.Ample

/-! Finite-dimensional top Wick-symbol matrix. Separate from subsequent X and
coupling changes. Slot-count triangularity but not claiming UV stability. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.PertExtension.Heat
open Function Filter Set MvPolynomial Finset
open YM.Next.Rank YM.Next.Rank.Normal
open scoped Topology Classical BigOperators
variable {V A :Type*}(Q : Symmetric V)

-- Inductive polynomial bounds, no coefficient-norm restrictions.
private theorem equation (f : A→V)(i : A)(s : Finset A)(hi:i∈s) :
    let u:=s.erase i; let x:=glyphs f u; let w:=glyphs f s
    milk Q w=X (f i)* milk Q x+ ∑ j∈u, (Q.cov (f i) (f j)) • milk Q (glyphs f (u.erase j)) := by
  intro u x w
  have he : w=X _*x := (Finset.mul_prod_erase s (fun j => X (f j)) hi).symm
  rw [he, feeds,skims,show x=glyphs _ _ from rfl]; simp_rw [renew,map_sum,map_smul]

private def Rules (k : ℕ)(p : poly V) := totalDegree (milk Q p)≤k ∧
      (k=0 → milk Q p=p) ∧ (0<k → (milk Q p-p).totalDegree < k)

private theorem smallerLetter (k : ℕ)(s : Finset A)(f : A→V) (h:s.card≤k) : Rules Q k (glyphs f s):=by
   unfold Rules
   induction k using Nat.strong_induction_on generalizing s with
   | _ n ih=>
      let p:=glyphs f s
      obtain rfl|⟨j,hj⟩:=s.eq_empty_or_nonempty
      · simp [Normal.glyphs]
      have hpos : 0<n := (Finset.card_pos.mpr ⟨j,hj⟩).trans_le h -- adjust
      let u:=s.erase j; let x := glyphs f u
      have he := equation Q f j s hj
      let S:= ∑ r∈u, (Q.cov (f j) (f r)) • milk Q (glyphs f (u.erase r))
      have hx : p=X (f j)*x := (Finset.mul_prod_erase s (fun i => X (f i)) hj).symm
      have hu : u.card≤n-1:= by dsimp only [u];rw [card_erase_of_mem hj];omega
      have hO r (hr:r∈u):u.card-1=(u.erase r).card := (card_erase_of_mem hr).symm
      obtain ⟨hY,h0,hY'⟩ := show Rules Q (n-1) x from ih (n-1) (by omega) u hu
      have hS : S.totalDegree < n:=by
         refine (totalDegree_finsetSum _ _).trans_lt (lt_of_le_of_lt (Finset.sup_le (a:=n-1) (fun i hi=>?_)) (Nat.sub_lt hpos one_pos))
         apply le_trans (totalDegree_smul_le ..)
         exact (ih (n-1) (by omega) (u.erase i) ((Finset.card_le_card (erase_subset ..)).trans hu)).1
      refine ⟨?_,fun h=> (hpos.ne' h).elim,fun _=>?_⟩
      · change (milk Q p).totalDegree ≤ n
        change milk Q p = _ + S at he; rw [he]
        refine (totalDegree_add ..).trans (max_le ((totalDegree_mul ..).trans (by rw [totalDegree_X]; change _ ≤ _ at hY; have hyy := show totalDegree (milk Q (glyphs f (s.erase j)))≤n-1 from hY; omega)) hS.le)
      change (milk Q p-p).totalDegree < n
      rw [show milk Q p-p=X (f j)*(milk Q x-x)+S by rw [mul_sub, (he : milk Q p = _+S)]; rw [hx];abel]
      refine (totalDegree_add ..).trans_lt (max_lt ?_ hS)
      by_cases hn':n=1
      · rw [h0 (by omega),sub_self,mul_zero,totalDegree_zero];exact hpos
      exact (totalDegree_mul ..).trans_lt (by have := hY' (by omega); rw [totalDegree_X];omega)

theorem degree_decrease (p : poly V)(k)(h : p.totalDegree≤k) :
    (k=0 → milk Q p=p) ∧ (0<k → (milk Q p-p).totalDegree < k):=by
  have H (i:V→₀ℕ) (hi:i∈p.support):Rules Q k (monomial i 1 : poly V) := by
     obtain ⟨v,hv⟩ := Common.letter i
     rw [hv]; exact smallerLetter Q k _ _ (by simpa using! (le_totalDegree hi).trans h)
  have he (i : V→₀ℕ): monomial i (coeff i p)=coeff i p • monomial i 1:=by rw [← map_smul,smul_eq_mul,mul_one]
  have hsum : p=∑ i ∈ p.support, coeff i p • (monomial i 1) := by convert p.as_sum; all_goals exact (he _).symm
  constructor
  · intro hk; rw [hsum,map_sum];simp_rw [map_smul]
    exact sum_congr rfl fun i hi=> congr_arg (fun x=>coeff i p • x) ((H i hi).2.1 hk)
  intro hk
  let D := milk Q - LinearMap.id; change (D p).totalDegree < k
  nth_rw 1 [p.as_sum]; simp_rw [he,map_sum,map_smul]
  refine (totalDegree_finsetSum ..).trans_lt <| lt_of_le_of_lt (Finset.sup_le (a:=k-1) (fun i hi=> (totalDegree_smul_le ..).trans ?_)) (by omega)
  have h:= (H i hi).2.2 hk; change (D _).totalDegree < k at h; omega

variable {J : Type*}[Fintype J] [DecidableEq J]

/-- Supplied bare leading pure-slot stencils and slot-preserving joint-jet
projection (before kernel quotient); conditions on stencils, not on the
answer of an X solve. Sign hypotheses record parity. -/
structure Frame (V J : Type*) [Fintype J][DecidableEq J] where
  slots : J→ℕ
  basis : J→poly V
  joint : poly V →ₗ[ℂ] (J→ℂ)
  retr i : joint (basis i)= Pi.single i 1
  bound i : (basis i).totalDegree ≤ slots i
  drops i p : p.totalDegree < slots i → joint p i=0
  even i : LiftMark.factors (-1) (basis i) = ((-1:ℂ)^slots i) • basis i
  projects p i : joint (LiftMark.factors (-1) p) i= (-1)^slots i*joint p i

namespace Frame
variable (F : Frame V J) {Q}

def matrix (Q : Symmetric V): Module.End ℂ (J→ℂ) where
  toFun a := ∑ i, a i • F.joint (milk Q (F.basis i))
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a b:= by simp [Finset.smul_sum,smul_smul]

lemma coefficientMatrix {i j} (h:F.slots i ≤ F.slots j) : F.joint (milk Q (F.basis i)) j = (Pi.single i 1 : J→ℂ) j := by
  obtain h1|h2:=Nat.eq_zero_or_pos (F.slots i)
  · rw [(degree_decrease Q _ _ (F.bound i)).1 h1, F.retr]
  have hh:=F.drops j _ (((degree_decrease Q _ _ (F.bound i)).2 h2).trans_le h)
  rw [map_sub, Pi.sub_apply,F.retr, sub_eq_zero] at hh; exact hh

private lemma eq_left (m : ℕ)(a : J→ℂ) (ha:∃i,F.slots i≥m ∧ a i≠0): ∃ i,F.slots i≥m ∧ a i ≠ 0 ∧ F.matrix Q a i =a i := by
  let s: Finset J := Finset.univ.filter fun i=> F.slots i≥m ∧ a i≠0
  obtain ⟨i,hi,hj⟩:= s.exists_max_image F.slots (by simpa [s,Finset.Nonempty] using! ha)
  have hle:=Finset.mem_filter.mp hi |>.2
  refine ⟨i,hle.1,hle.2,?_⟩
  change (∑ j:J, a j • F.joint (milk Q _)) i=a i
  rw [Finset.sum_apply,Finset.sum_eq_single_of_mem i (mem_univ i)]
  · simp only [Pi.smul_apply, smul_eq_mul,F.coefficientMatrix le_rfl]; simp
  intro j hj' h
  by_cases hj':a j ≠ 0
  · have hk : F.slots j ≤ F.slots i:= by
      by_contra! hv
      have := hj j (by simp [s,hj',hle.1.trans hv.le]);omega
    simp only [Pi.smul_apply,smul_eq_mul,F.coefficientMatrix hk,Pi.single_eq_of_ne (Ne.symm h),mul_zero]
  simp [not_ne_iff.mp hj']

lemma injective : Injective (F.matrix Q):= LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr (by
  intro x hx; funext i
  by_contra! h
  obtain ⟨j,hj,hj',hh⟩:=F.eq_left (Q:=Q) 0 x ⟨i,Nat.zero_le _,h⟩
  exact hj' (hh ▸ congr_fun (LinearMap.mem_ker.mp hx) j)))

def conversion (Q : Symmetric V) := LinearEquiv.ofBijective (F.matrix Q) ⟨F.injective,LinearMap.injective_iff_surjective.mp F.injective⟩
def inverse (Q : Symmetric V) := (F.conversion Q).symm.toLinearMap

theorem inverse_slots (y:J→ℂ)(m:ℕ)(hy:∀ i,F.slots i≥m → y i=0) : ∀ i,F.slots i≥m → F.inverse Q y i=0 := by
  intro i hi;by_contra h
  obtain ⟨s,hs,hs',hh⟩:= F.eq_left (Q:=Q) m (F.inverse Q y) ⟨i,hi,h⟩
  rw [show (F.matrix Q (F.inverse Q y))=y from (F.conversion Q).apply_symm_apply y] at hh
  exact hs' (hh ▸ hy s hs)

-- formal change remains even in slot count
def sign (a : J→ℂ)(j : J) := (-1)^F.slots j*a j
lemma matrix_sign (x : J→ℂ) : F.matrix Q (F.sign x)= F.sign (F.matrix Q x) := by
   funext i
   simp only [matrix,sign,LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
   have H:(LiftMark.opq Q (-1))=Q:= by ext1 ;funext i j; simp [LiftMark.opq]
   have hr:= LiftMark.blend_up Q (-1) (neg_ne_zero.mpr one_ne_zero)
   rw [H] at hr
   refine Finset.sum_congr rfl fun j hj=>?_ ; rw [show (-1)^F.slots j * x j * _= x j*((-1)^F.slots j *F.joint (milk Q (F.basis j)) i) by ring, ←show F.joint (((-1:ℂ)^F.slots j) • milk Q (F.basis j)) i=(-1)^F.slots j * _ by simp,←map_smul,←F.even j, ←hr (F.basis j),F.projects]
   ring

lemma inverse_sign (y : J→ℂ) : F.inverse Q (F.sign y)=F.sign (F.inverse Q y) := by
  apply (F.conversion Q).injective
  have he (y:J→ℂ): F.conversion Q (F.inverse Q y) = y:= (F.conversion Q).apply_symm_apply ..
  rw [he,show F.conversion Q (sign F _)= sign F (F.conversion Q _) from F.matrix_sign ..,he]

lemma parityInv (i j:J)(h : Odd (F.slots i + F.slots j)): F.inverse Q (Pi.single i 1) j=0:=by
  let x : J→ℂ := Pi.single i 1
  have h₁ := F.inverse_sign x (Q:=Q)
  rw [show F.sign x = ((-1:ℂ)^F.slots i) • x by funext t;unfold sign x;by_cases ht:t=i<;> simp [Pi.single_apply,ht]] at h₁
  have hv:= congr_fun h₁ j
  rw [map_smul,Pi.smul_apply, smul_eq_mul,sign] at hv
  have he₁: Even (F.slots i*(2:ℕ)):=even_two.mul_left _
  have he : ((-1:ℂ)^F.slots i)^2 -(-1)^(F.slots i+F.slots j) = 2 := by rw [←pow_mul,he₁.neg_pow,one_pow,h.neg_pow,one_pow];norm_num
  change (F.inverse Q) x j=0; have hh : 2*(F.inverse Q x j)=0:=by rw [←he,sub_mul,pow_add]; rw [pow_two,mul_assoc,hv,mul_assoc,sub_self]
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
end Frame
end YM.PertExtension.Heat
