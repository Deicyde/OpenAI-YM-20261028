import YM.RG08.Quire.Patch
/-!
# Polynomial heat on one mark. Arbitrary rooted kernels with tests
in the formal address spaces. Covariance unrestricted exactly as for Peals.
Keep extensive unmarked processing separate.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Quire
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths
open scoped Topology ContDiff Classical BigOperators
variable {E F α β ι : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {s : Option Side} {K : Row α α} {r e n L : ℕ} {U V : Screed E α} {S : Canticle α}
def grant (i : ℕ) (u : Rooted E α r) : Rooted E α i := if h:i=r then h ▸ u else 0
lemma grant_self (u : Rooted E α r) : grant r u=u := by simp [grant]
lemma grant_zero (i : ℕ) : grant i (0:Rooted E α r)=0 := by
  by_cases h:i=r
  · subst r; rw [grant_self]
  simp [grant,h]

def hymn (K : Row α α) (U : Spine E α) (V : Verse α) (r : ℕ) := ∑ a∈wheel r,
    grant r (clasp K (U (a.1+1)) (V (a.2+1)))

def murmur (s : Option Side) (K : Row α α) (S : Canticle α) (U : Screed E α) (n e r : ℕ) : Rooted E α r := match n with
  | 0 => U e r
  | n+1 => ((↑(n+1:ℕ)):ℝ)⁻¹ • (jib s K (murmur s K S U n e (r+2)) + ∑ b : {b:ℕ×ℕ // b∈wheel n}, ∑ a∈wheel e,
      hymn K (fun r=> murmur s K S U b.val.1 a.1 r) (Refrain K S s b.val.2 a.2) r)
termination_by n
decreasing_by
  all_goals (first|omega| (have h : b.val.1+b.val.2=n := mem_antidiagonal.mp b.property; omega))
lemma murmur_step (U : Screed E α) : murmur s K S U (n+1) e r =
    ((↑(n+1:ℕ)):ℝ)⁻¹ • (jib s K (murmur s K S U n e (r+2)) + ∑ b∈wheel n, ∑ a∈wheel e,
      hymn K (murmur s K S U b.1 a.1) (Refrain K S s b.2 a.2) r) := by
  nth_rw 1 [murmur]; rw [← Finset.sum_coe_sort (wheel n)]

lemma Tidied {u : Rooted E α r} (i : ℕ) (h : Tidy u) : Tidy (grant i u) := by
  unfold grant; split; next he=> subst i; exact h
  exact Tidy.zero ..
lemma hymn_tidy {U : Spine E α} {V : Verse α} (h : Whole K) (hU : ∀ i,Pens (U i)) (hV : ∀ i, Summable (V i)) (i): Tidy (hymn K U V i) :=
    Tidy.additions fun b _=> Tidied _ (clasp_tidy (hU _) (hV _) h)

variable [Fintype α]
lemma quiet_tidily (h : Whole K) (he : ∀ e r,Tunable (S e r)) (hU : ∀ e r,Tidy (U e r)) (s n e r): Tidy (murmur s K S U n e r) := by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero => rw [murmur]; exact hU _ _
  | ind i ih=>
    rw [murmur_step]; apply Tidy.scale; apply Tidy.plus (jib_tidy (ih i le_rfl _ _|>.pens) h s)
    exact Tidy.additions (fun b hb=> Tidy.additions fun c _=> hymn_tidy h (fun k=> (ih b.1 (by have he:=mem_antidiagonal.mp hb; omega) _ k).pens) (fun k=> (refrains_tune h he _ _ _ _).1) _)
lemma grant_leaves (v : Rooted E α r) (e : E→L[ℝ] F) (i : ℕ) : e ∘ grant i v=grant i (e ∘ v) := by
  by_cases h:i=r
  · subst r; rw [grant_self,grant_self]
  funext p; simp [grant,h]
lemma graft (e : E→L[ℝ] F) (f : ι→ Rooted E α r) (s : Finset ι) : e ∘ (∑ i∈s,f i)=(∑ i∈s,e ∘ f i) := funext fun i=>by
  simp [Finset.sum_apply]
lemma hymn_sound {U : Spine E α} {V : Verse α} (h : Whole K) (hU : ∀ i, Pens (U i)) (hV : ∀ i,Summable (V i)) (e : E→L[ℝ] F) (r) : e ∘ hymn K U V r=hymn K (fun j=> e ∘ U j) V r := by
  unfold hymn; rw [graft]; simp_rw [grant_leaves,clasp_stays e (hU _) (hV _) h]
lemma murmur_map (q : E→L[ℝ] F)(h : Whole K) (hk :∀ e r,Tunable (S e r)) (hU : ∀ e r,Tidy (U e r)) :
    q ∘ (murmur s K S U n e r)=murmur s K S (fun i j=>q ∘ U i j) n e r := by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero => rw [murmur,murmur]
  | ind n ih =>
    have hh (f : Rooted E α r) (a:ℝ) : q ∘ (a • f : Rooted E α r)=a • (q ∘ f) := funext fun i=>map_smul .. -- type
    have he (f g : Rooted E α r) : q ∘ (f+g)=q ∘ f+q ∘ g := funext fun i=>map_add ..
    rw [murmur_step, hh,he,jib_stays q s (quiet_tidily h hk hU s n _ _|>.pens) h, ih n le_rfl,graft,murmur_step]
    congr 2; apply sum_congr rfl; intro b hb
    rw [graft]; apply sum_congr rfl; intro a ha; rw [hymn_sound h (fun i=>quiet_tidily h hk hU s _ _ i|>.pens) (fun i=> (refrains_tune h hk _ _ _ _).1)]
    congr 1; exact funext fun r=> ih b.1 (by have ht:=mem_antidiagonal.mp hb; omega)

def Fits (L:ℕ) (U : Screed E α) := ∀ i r,U i r≠0 → r≤L+i
lemma murmur_degree (h : Whole K) (he : ∀ i r,Tunable (S i r)) (hS : Decked S) (hp : ∀ i r,Tidy (U i r)) (hb : Fits L U) :
    murmur s K S U n e r ≠0 → r ≤ L+e ∧ 2*n+r≤L+3*e := by
  induction n using Nat.caseStrongRecOn generalizing e r with
  | zero=> intro hg; rw [murmur] at hg; have hv := hb e r hg; omega
  | ind i ih=>
    contrapose
    intro hz; rw [murmur_step]
    rw [show murmur s K S U i e (r+2)=0 from not_ne_iff.mp (mt (ih _ le_rfl) (fun H=> hz (by omega))),jib_blank s h, sum_eq_zero,zero_add,smul_zero]
    intro b hv; refine sum_eq_zero fun a ha=> ?_
    apply sum_eq_zero; intro c hc
    have h₁ := mem_antidiagonal.mp hv; have h₂:=mem_antidiagonal.mp ha; have h₃:=mem_antidiagonal.mp hc
    by_cases hx : murmur s K S U b.1 a.1 (c.1+1)=0
    · rw [hx,clasp_zero (refrains_tune h he _ _ _ _|>.1) h,grant_zero]
    have hy := ih _ (by omega : b.1 ≤ i) hx
    rw [show Refrain K S s b.2 a.2 (c.2+1)=0 from not_ne_iff.mp (mt (treble_reel h he hS) fun ⟨⟨hE,k,hk⟩,ht⟩=>hz (by omega)),clasp_stop (quiet_tidily h he hp _ _ _ _|>.pens) h,grant_zero]
-- All heat powers needed at most `windows`.

def windows (L e : ℕ) := L+3*e

def washed (L : ℕ) (s : Option Side) (K : Row α α) (S : Canticle α) (U : Screed E α) (e r : ℕ) : Rooted E α r := ∑ i∈range (windows L e+1), murmur s K S U i e r
lemma washed_duty (h : Whole K) (he : ∀ i r,Tunable (S i r)) (hS : Decked S) (hp : ∀ i r,Tidy (U i r)) (hb : Fits L U) :
    Fits L (washed L s K S U) ∧ ∀ e r,Tidy (washed L s K S U e r) := by
  refine ⟨fun i r=> ?_,fun i r=> Tidy.additions fun j _=> quiet_tidily h he hp s j i r⟩
  intro hx; by_contra hv
  exact hx (sum_eq_zero fun b _=> not_ne_iff.mp (mt (murmur_degree h he hS hp hb) fun H=> hv H.1))
lemma wash_map (q : E→L[ℝ] F)(h : Whole K) (hk :∀ e r,Tunable (S e r)) (hU : ∀ e r,Tidy (U e r)) :
    q ∘ (washed L s K S U e r)=washed L s K S (fun i j=>q ∘ U i j) e r := by unfold washed; rw [graft]; simp_rw [murmur_map q h hk hU]
end YM.RG08.Quire
