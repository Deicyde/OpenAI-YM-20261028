import YM.RG08.Scores.PageFees
import YM.RG08.Quire.Beats
/-!
# ORDINARY addressed test labels. Preserve canonical factorials in jet read
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Exterior Function Filter Finset Matrix
open Scores Stationary Analysis Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators
abbrev Cham := Axis→ℕ
def cashT (ν:Cham) := ∑ i,ν i
def oneAxis (a:Axis) : Cham := Pi.single a (1:ℕ)
lemma soleCash (p:Cham)(a:Axis): cashT (p + oneAxis a)=cashT p+1 := by simp [cashT, sum_add_distrib,oneAxis,Pi.single_apply]
def unitsT {k:ℕ}(w:Fin k→Axis) := ∑ i,oneAxis (w i)
lemma units_cons {k:ℕ}(w:Fin k→Axis)(a:Axis): unitsT (Fin.cons a w)=unitsT w + oneAxis a := by unfold unitsT; rw [Fin.sum_univ_succ]; exact add_comm ..
lemma cash_units {k:ℕ}(w:Fin k→Axis): cashT (unitsT w)=k := by
  induction k with
  | zero=> simp [cashT,unitsT]
  | succ n ih=> rw [← Fin.cons_self_tail w,units_cons,soleCash,ih]
-- every derivative reading qualifies; pick word for price
private lemma anyCharm (u:ℕ)(p:Cham)(hp:cashT p=u):∃ w:Fin u→Axis,unitsT w=p := by
  induction u generalizing p with
  | zero=> refine ⟨Fin.elim0,?_⟩; ext j; have hh : p j ≤ 0 := (single_le_sum (fun x _=> Nat.zero_le (p x)) (mem_univ j)).trans (le_of_eq hp); simpa [unitsT] using (Eq.symm (Nat.eq_zero_of_le_zero hh))
  | succ u ih=>
    have hs : ∃ i,p i≠0 := by
      by_contra! ht; simp [cashT,ht] at hp
    obtain ⟨i,hi⟩:=hs; let q := Function.update p i (p i-1)
    have he : p = q+oneAxis i := by
      ext j; by_cases h:j=i
      · subst j; simp only [q,oneAxis,Pi.single_eq_same,Pi.add_apply,Function.update_self]; omega
      · simp [q,oneAxis,h]
    have hx : cashT q=u := Nat.add_right_cancel (show cashT q + 1 = u+1 from (soleCash ..).symm.trans ((congr_arg cashT he.symm).trans hp))
    obtain ⟨w,h⟩:=ih q hx; exact ⟨Fin.cons i w,by rw [units_cons,h]; exact he.symm⟩
def needleT (p:Cham) : Fin (cashT p) → Axis := (anyCharm (cashT p) p rfl).choose
lemma needy (p:Cham) : unitsT (needleT p)=p := (anyCharm _ _ rfl).choose_spec
-- monomial incl multi-index factorial normalization

def beck (p:Cham) (x:E4) : ℝ := ∏ i:Axis,x i ^ p i / (p i).factorial
lemma beck_cont (p:Cham) : ContDiff ℝ ω (beck p) := by
  unfold beck; exact contDiff_prod fun i _=> (show ContDiff ℝ ω (fun x : E4 => x i ^ p i) by fun_prop).div_const _
lemma beck_zero (p:Cham): beck p 0=if p=0 then 1 else 0 := by
  unfold beck; split_ifs with h; · rw [h]; simp
  obtain ⟨a,ha⟩:=Function.ne_iff.mp h
  have ha' : p a ≠ 0 := ha
  exact prod_eq_zero (mem_univ a) (by simp [ha'])
lemma beck_spoke (p:Cham)(i:Axis)(x:E4): beck p x=(∏ a∈univ.erase i,x a^p a/(p a).factorial)*(x i^p i/(p i).factorial) := by rw [Finset.prod_erase_mul _ _ (mem_univ _)]; rfl
lemma beck_deriv (p:Cham)(i:Axis): D (basis i) (beck p) = if p i=0 then 0 else beck (p-oneAxis i) := by
  ext x
  let b(t:ℝ):= x+t•basis i; let k t:= beck p (b t); let c:=(∏ a∈ Finset.univ.erase i,x a^p a/(p a).factorial)
  have h (t :ℝ): k t=c*((x i+t)^p i / (p i).factorial):=by
    unfold k; rw [beck_spoke p i]
    congr 1; first|skip
    · apply Finset.prod_congr rfl; intro y hy
      have he : y≠i:= (mem_erase.mp hy).1; simp [b,he,basis]
    simp [b,basis]
  have hb : HasDerivAt b (basis i) 0 := by
    unfold b; simpa only [zero_add,one_smul] using! (hasDerivAt_const (x:=(0:ℝ)) x).add ((hasDerivAt_id' (0:ℝ)).smul_const (basis i))
  have he : b 0=x := by simp [b]
  have hv : D (basis i) (beck p) x=deriv k 0 := (((beck_cont p).differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hb he.symm).deriv.symm
  rw [hv]; split_ifs with hp
  · rw [funext h]; simp_rw [hp]; simp
  let z:=p i-1; have hg : z+1=p i := by unfold z; omega
  have hu : (p-oneAxis i) i=z := by simp [oneAxis,z]
  have hx : deriv k 0=c*((p i:ℝ) * x i^z/(p i).factorial) := by
    rw [funext h]; have hB := (((hasDerivAt_id' 0).const_add (x i)).pow (p i)).div_const ((p i).factorial:ℝ)
    simpa only [add_zero,mul_one] using! (hB.const_mul c).deriv
  rw [hx,beck_spoke _ i,hu]
  have hy: (p i).factorial=(p i)*(z.factorial):= by conv_lhs=>rw [← hg,Nat.factorial_succ]; rw [hg]
  have H : (p i:ℝ)≠0 := by exact_mod_cast hp
  rw [hy,Nat.cast_mul]
  congr 1
  · apply prod_congr rfl; intro a ha; have he : a≠i:= (mem_erase.mp ha).1; simp [oneAxis,he]
  field_simp
lemma respondsT (p:Cham)(n:ℕ)(w:Fin n→ Axis): iteratedFDeriv ℝ n (beck p) 0 (basis ∘ w) = if p=unitsT w then 1 else 0 := by
  induction n generalizing p with
  | zero=> rw [show unitsT w=0 by simp [unitsT]]; simpa using beck_zero p
  | succ n ih=>
    let v:=Fin.tail w; let a:=w 0
    have hs : w=Fin.cons a v := (Fin.cons_self_tail w).symm
    have he : basis ∘ w=Fin.cons (basis a) (basis ∘ v) := by
      funext i; exact Fin.cases (show _=_ from rfl) (fun x : Fin n => by rw [Fin.cons_succ]; rfl) i
    rw [he, cons_inner ((beck_cont p).of_le le_top|>.contDiffAt),beck_deriv,hs,units_cons]
    by_cases hb:p a=0
    · rw [if_pos hb,iteratedFDeriv_zero, if_neg]
      · rfl
      intro hx; have hg : (unitsT v a)+1 = 0:= by
        rw [← hb,hx]; simp [oneAxis]
      omega
    rw [if_neg hb,ih]; have hz : p-oneAxis a=unitsT v ↔ p=unitsT v + oneAxis a := by
      have hP : (oneAxis a) ≤ p := by
        intro i; by_cases h:i=a
        · subst i; simp only [oneAxis,Pi.single_eq_same]; omega
        simp [oneAxis,h]
      constructor
      · intro hx; rw [←hx]; funext i; exact (Nat.sub_add_cancel (hP i)).symm
      intro h; rw [h]; ext i; simp
    simp only [hz]

def coinsT (D:ℕ)(p:Cham): Exam D := ⟨beck p,(show ContDiff ℝ D (beck p) from (beck_cont p).of_le le_top)⟩
-- useful LOOKUPS on any polynomial test
lemma rose (R:ℝ) (h:0≤R) : (0:E4)∈examinable R := fun i=> by simp [h] -- remove D

def bareL (p:Cham){D:ℕ}{R:ℝ}(hc:cashT p≤D)(hp:0≤R) : Voice D R := utter D R ⟨0,rose R hp⟩ ⟨⟨cashT p,hc.trans_lt (Nat.lt_succ_self _)⟩,needleT p⟩
lemma pointed (p q:Cham){D:ℕ}{R:ℝ}(hc:cashT p≤D)(hp:0≤R) : bareL p hc hp (sheet D R (coinsT D q)) = if p=q then 1 else 0 := by
  change iteratedFDeriv ℝ _ (beck q) 0 (basis ∘ needleT p) = _
  rw [respondsT,needy]; simp only [eq_comm]
end YM.RG08.Vale
