import YM.RG08.Isles.Atoll
import YM.RG08.Isles.Accord
import YM.RG08.Steam.Ballot

/-! Thus connect the period recursion to the actual cover coefficients, in every positive
rank (whether there are cycles or not). No period property of rank zero used. For simplicity
state with one admitted width for all input valences; restrict unused e,r by replacing them with
zero first for a finite use.
-/
noncomputable section
namespace YM.RG08.Isles
open Forms Pert.Bulk Packets Laurent Finset Function Lattice Filter Steam
open scoped Topology BigOperators ENNReal Classical
set_option autoImplicit false
variable {I J:Type}[Fintype I][Fintype J]{n p q e j:ℕ}{σ B W T:ℝ}

omit [Fintype I] in
private lemma transport {f:ViewDeck p I}{F:Flake p (Market I)} (h:Study σ T f F)(he:p=n) : Study σ T (fun i=>Steam.move he (f i)) (Steam.move he F):=by subst he;exact h
variable {g:(i:ℕ)→Forms.Line (colony I i)}{Γ:Forms.Line (Market I)}
private lemma studyPair {f:ViewDeck (p+1) I}{F}{f':ViewDeck (q+1) I}{F'}(h:Study σ T f F)(H:Study σ W f' F')(hΓ:StudyLine σ B g Γ) : ∃ C,Study σ C (fun i=> pair (g i) (f i) (f' i) n) (pair Γ F F' n):=by
 by_cases he:p+q=n
 · simp only [pair,he,dif_pos]; exact ⟨_,(transport (h.join H hΓ) he).smul _⟩ -- field notation?
 simp_rw [pair,dif_neg he];exact ⟨0,Study.zero _ _ h.rate le_rfl⟩

omit [Fintype I] in
private lemma collects {M:Type}{f:M→ViewDeck n I}{F:M→Flake n (Market I)} (S:Finset M)(hs:0<σ)(h:∀ i∈S,∃ p,Study σ p (f i) (F i)) : ∃ p,Study σ p (fun j=>∑i∈S,f i j) (S.sum F):=by
 choose p hp using h
 let b(i:M):=if h:i∈S then p i h else 0
 refine ⟨_, show Study _ (S.sum b) _ _ from ?_⟩
 have he:=Study.sum S hs b f F fun i hi=>by simpa [b,hi] using hp i hi
 convert he using 1
 funext j;rw [Finset.sum_apply]

def seats (σ:ℝ)(V:(i:ℕ)→Grain (colony I i))(K:Grain (Market I)):=∀ e n, ∃ C,Study σ C (fun i=>V i e n) (K e n)

variable {V:(i:ℕ)→Grain (colony I i)}{K:Grain (Market I)}
theorem restoke (h:seats σ V K)(H:StudyLine σ B g Γ)(j:ℕ): seats σ (fun i=>burn (g i) (V i) j) (burn Γ K j):=by
 induction j using Nat.strong_induction_on with
 | h j ih=> cases j with
   | zero=>simp_rw [spark];exact h
   | succ j=>
      intro e n;simp_rw [blaze]
      have he:∃ P,Study σ P (fun i=>wheels (g i) (burn (g i) (V i)) j e n) (wheels Γ (burn Γ K) j e n):=by
        unfold wheels unilateral
        obtain ⟨P,hP⟩:=ih j (by omega) e (n+2)
        have hh(c:ℕ)(y:ℕ)(ha:y≤j)(a:ℕ): ∃ r, Study σ r (fun i=>pair (g i) (burn (g i) (V i) y a (c+1)) (burn (g i) (V i) (j-y) (e-a) (n-c+1)) n) (pair Γ (burn Γ K y a (c+1)) (burn Γ K (j-y) (e-a) (n-c+1)) n):=by
           obtain ⟨P,hv⟩:=ih y (by omega) a (c+1)
           obtain ⟨Q,hw⟩:=ih (j-y) (by omega) (e-a) (n-c+1)
           exact studyPair hv hw H
        have hf:= collects (range (n+1)) H.rate (fun c _=> collects (range (j+1)) H.rate (fun y hy=> collects (range (e+1)) H.rate (fun a _=> hh c y (by simpa [Nat.lt_succ_iff] using hy) a)))
        obtain ⟨S,hs⟩:= hf
        exact ⟨_, ((hP.trace H).smul (((n:ℝ)+2)*(n+1)/2)).add hs⟩
      obtain ⟨P,hP⟩:=he; exact ⟨_,hP.smul _⟩

omit [Fintype J] in
theorem cooling (h:seats σ V K)(H:StudyLine σ B g Γ){m:(i:ℕ)→colony I i → colony J i →ℝ}{M:Kernel I J}(ht:StudyCross I J σ T m M): seats σ (fun i=>allG (g i) (V i) (m i)) (allG Γ K M):=by
 intro e n
 obtain ⟨P,hp⟩:=h e n
 obtain ⟨Q,hq⟩:=collects (range (3*e)) H.rate (f:=fun j i=> (1:ℝ)^(j+1) • burn (g i) (V i) (j+1) e n) (F:=fun j=> (1:ℝ)^(j+1) • burn Γ K (j+1) e n) (fun j _=> by obtain ⟨u,hu⟩:=restoke h H (j+1) e n; exact ⟨_,hu.smul _⟩)
 exact ⟨_,(hp.morph (fun _:Fin n=> ht)).add (hq.morph (fun _:Fin n=>ht))⟩ -- ?

end YM.RG08.Isles
