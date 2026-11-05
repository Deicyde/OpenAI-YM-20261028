import YM.RG08.Wax.Ride
/-! # Poise Euler log. Coherence under valued arc at active root only.
Alias registration for the gauge commits with theorem tags.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset
open scoped Topology BigOperators Real Classical Matrix
variable {I X:Type}[Fintype I][DecidableEq I][Fintype X][DecidableEq X]{D s r i j : ℕ}{R:ℝ}{T V:Finset I}{p:Option Side}{K:Row X X}{M:Canticle X}
abbrev Mill (I X:Type)(D:ℕ)(R:ℝ) := (T:Finset I) → Screed (Poise T D R) X
variable {A: Mill I X D R}
-- linear footprint proof (test component evaluations many) not divided Fk factorial convention for root tests. hull
abbrev access (x:I→Sight D R)(A:Mill I X D R) : Topaz I (Screed ℝ X) := fun t i j=> sampleK t x ∘ A t i j
variable {a:I→ℕ}
lemma access_p (h:∀ t i j,Tidy (A t i j))(he:∀ t,Fits (vanes a t) (A t))(t:Finset I)(x:I→Sight D R): Sails (vanes a t) (access x A t):=
   ⟨fun i j=> Tidy.map (sampleK t x) (h t i j),fun i j hz => he t i j fun h=> hz (by unfold access;rw [h]; ext k; simp)⟩
lemma access_nil (x:I→Sight D R)(h:A ∅=0): access x A ∅=0:=by funext i j k; simp [access,h]

def orbitV (p:Option Side)(K:Row X X)(S:Canticle X)(A:Mill I X D R)(t:Finset I)(n:ℕ): Screed (Poise t D R) X:= match n with
    | 0=> A t
    | n+1=> ((↑(n+1:ℕ)):ℝ)⁻¹ • blue p K S (fun t i=> if h:i≤n then orbitV p K S A t i else 0) t n
termination_by n
lemma orbit_z (A:Mill I X D R)(p:Option Side)(K:Row X X)(S:Canticle X)(t:Finset I): orbitV p K S A t 0=A t:= by rw [orbitV]
lemma orbit_t (hp:Whole K)(hd: Gets M)(h:∀ t i j,Tidy (A t i j))(t)(n i j): Tidy (orbitV p K M A t n i j):=by
  induction n using Nat.caseStrongRecOn generalizing i j t with
  | zero=> rw [orbit_z]; exact h _ _ _
  | ind n ih=>
     rw [orbitV]; simp only [Pi.smul_apply]; apply Tidy.scale (x:=blue p K M _ t n i j);-- f param name
     apply blueQ _ hp hd
     intro b i j k; by_cases he:i≤n; · simp only [dif_pos he]; exact ih i he b j k
     simp only [dif_neg he, Pi.zero_apply]; exact Tidy.zero ..
lemma orbit_e (x:I→Sight D R)(hp:Whole K)(hd:Gets M)(h:∀ t i j,Tidy (A t i j))(hx:0≤R) :
   taps_at x (orbitV p K M A) = pulse p K M (access x A):=by
   funext t n; induction n using Nat.caseStrongRecOn generalizing t with
   | zero=> funext i j; rw [taps_at,orbit_z,pulse_z]
   | ind n ih=>
     let B (t:Finset I)(i:ℕ):= if h:i≤n then orbitV p K M A t i else 0; let P:= ((↑(n+1:ℕ)):ℝ)⁻¹
     have he: taps_at x B=fun t i=> if h:i≤n then pulse p K M (access x A) t i else 0:= by
       funext t i; by_cases hx:i≤n
       · rw [dif_pos hx,← ih i hx]; unfold taps_at; simp only [B,dif_pos hx]
       rw [dif_neg hx]; funext b j k; simp [taps_at,B,hx]
     have ht t i j k:Tidy (B t i j k):= by unfold B; split; exact orbit_t hp hd h ..; exact Tidy.zero ..
     funext i j
     rw [pulse]; unfold taps_at; rw [orbitV,Pi.smul_apply,Pi.smul_apply,samples_vany]; rw [show sampleK t x ∘ blue p K M _ _ _ _ _=(lever p K M (taps_at x B) t n i j) from congr_fun (congr_fun (congr_fun (congr_fun (blue_cash x hp hd ht hx) t) n) i) j,he]; rfl
lemma orbit_cap (hp:Whole K)(hd:Gets M)(h:∀ t i j,Tidy (A t i j))(hx:0≤R)(he:∀ t,Fits (vanes a t) (A t))(t:Finset I)(n):Fits (vanes a t) (orbitV p K M A t n):=by
   intro i j hz; by_contra hh; apply hz; refine tapUni fun x=>?_
   change taps_at x (orbitV p K M A) t n i j=_; rw [orbit_e x hp hd h hx,(pulse_ok (p:=p) (access x A) hp hd (fun i=> access_p h he i x) t n|>.thin i).budget _ (by omega)]; ext k; simp
lemma orbit_end (hp:Whole K)(hd:Gets M)(h:∀ t i j,Tidy (A t i j))(hx:0≤R)(he:∀ t,Fits (vanes a t) (A t))(hv:A ∅=0)(hK:∀ c,(K.acts c)ᵀ=K.acts c)(t:Finset I)(n i)(ht:windows (vanes a t) i<n):orbitV none K M A t n i=0:=by
   funext k; refine tapUni fun x=>?_
   change taps_at x (orbitV none K M A) t n i k=_; rw [orbit_e x hp hd h hx, maxhours (fun i=>access_p h he i x) hp hd (access_nil x hv) hK _ _ _ ht]; ext; simp

def noon (K:Row X X)(M:Canticle X)(a:I→ℕ)(A:Mill I X D R): Mill I X D R:= fun t i j=>∑ n∈ range (windows (vanes a t) i+1),orbitV none K M A t n i j
lemma noon_s (x:I→Sight D R)(hp:Whole K)(hd:Gets M)(h:∀ t i j,Tidy (A t i j))(hx:0≤R) :
   access x (noon K M a A)=fun i=>endP (vanes a i) (pulse none K M (access x A) i) := by
   funext t i j; unfold access noon; rw [graft]; rw [← orbit_e x hp hd h hx (p:=none),endP,Finset.sum_apply] ; rfl
end YM.RG08.Wax
