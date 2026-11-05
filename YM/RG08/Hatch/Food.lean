import YM.RG08.Hatch.Sieve
import YM.RG08.Atlas.Plume

/-! # Cooled, on cover. Use any payments cut to e, neighboring indices covered by consumer.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Hatch
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open scoped Topology BigOperators ENNReal Classical
variable {I J:Type} {n m k e i j t d:ℕ}{σ C B:ℝ}{h:0<σ}
variable {P:Pack (m+1) (Market I)}{Q:Span (m+1) I}{γ:Forms.Line (Market I)}{Γ:(i:ℕ)→Forms.Line (colony I i)}
lemma Reed.solo_ship {P: Pack k (Market I)}{Q:Span k I}(hp:Reed d h C P Q)(eq:k=n):Reed d h C (ship eq P) (fun i=>ship eq (Q i)):=by subst eq;exact hp
variable {S:(i:ℕ)→Grain (colony I i)}{V:Grain (Market I)}{P:GrainS (Market I)}{U:(i:ℕ)→GrainS (colony I i)}

-- conflict P binder previous
variable [Fintype I]
def formal (P:GrainS (Market I))(U:(i:ℕ)→GrainS (colony I i))(d:ℕ)(h:0<σ)(t:ℕ):Prop:=∀ e≤t,∀ n,∃ C,Reed d h C (P e n) (fun i=>U i e n)
structure shut (t:ℕ)(V:Grain (Market I))(S:(i:ℕ)→Grain (colony I i))(σ:ℝ):Prop where
 launch : seats σ (fun i=>hedge t (S i)) (hedge t V)
omit [Fintype I] in
lemma shut.light (H:shut t V S σ)(he:e≤t)(n:ℕ):∃ C, Study σ C (fun i=>S i e n) (V e n):=by
    convert H.launch e n using 1; simp_rw [hedge_hit _ _ e he]
lemma shut.glint(hs:StudyLine σ B Γ γ)(H:shut t V S σ)(he:e≤t)(j n:ℕ):∃ C, Study σ C (fun i=>burn (Γ i) (S i) j e n) (burn γ V j e n):=by
    obtain ⟨u,hu⟩:=restoke H.launch hs j e n
    refine ⟨u,?_⟩; simp_rw [spark_hedge _ _ _ _ he] at hu;exact hu
lemma stain (H:shut t V S σ)(hΓ:StudyLine σ B Γ γ)(hs:formal P U d h t)(j:ℕ):formal (skate γ V P j) (fun i=>skate (Γ i) (S i) (U i) j) d h t:=by
 induction j using Nat.strong_induction_on with
 | h j ih=>cases j with
   | zero=>simp_rw [Skiff.start];exact hs
   | succ j=>
     intro e he n
     have ht(c i a:ℕ)(ha:i≤j)(hb:a≤e): ∃ C, Reed d h C (Skiff.shift γ (skate γ V P i a (c+1)) (burn γ V (j-i) (e-a) (n-c+1)) n) (fun m=>Skiff.shift (Γ m) (skate (Γ m) (S m) (U m) i a (c+1)) (burn (Γ m) (S m) (j-i) (e-a) (n-c+1)) n):=by
       obtain ⟨p,hp⟩:=ih i (by omega) a (by omega) (c+1)
       obtain ⟨x,hx⟩:=H.glint hΓ (e:=e-a) (by omega) (j-i) (n-c+1)
       unfold Skiff.shift;split_ifs with hc
       · exact ⟨_,((hp.chalk hΓ hx).solo_ship hc).scale _⟩
       exact ⟨0,Reed.solo I h le_rfl⟩
     obtain ⟨p,hp⟩:=ih j (by omega) e he (n+2)
     have hh:= Reed.accrue (range (n+1)) (fun c (_:c∈range (n+1))=> Reed.accrue (range (j+1)) (fun i hi=> Reed.accrue (range (e+1)) (fun a ha=>ht c i a (by simpa [Nat.lt_succ_iff] using hi) (by simpa [Nat.lt_succ_iff] using ha))))
     obtain ⟨p,hP⟩:=hh
     simp_rw [climbs,rungs,shim]; exact ⟨_,(((hp.squeak hΓ).scale (((n:ℝ)+2)*(n+1)/2)).add hP).scale _⟩

lemma coils (H:shut t V S σ)(hΓ:StudyLine σ B Γ γ)(hs:formal P U d h t)(l:ℕ)(a:ℝ){m:(i:ℕ)→colony I i→colony J i→ℝ}{M:Kernel I J}{T:ℝ}(hf:StudyCross I J σ T m M):formal (Trickle.mouth M (Skiff.spin l γ V P a)) (fun i=>Trickle.mouth (m i) (Skiff.spin l (Γ i) (S i) (U i) a)) d h t:=by
 intro e he n
 obtain ⟨p,hp⟩:= Reed.accrue (range (l+3*e+1)) (P:=fun j=>a^j • skate γ V P j e n) (Q:=fun j i=>a^j • skate (Γ i) (S i) (U i) j e n) (fun j _=>by
    obtain ⟨p,hp⟩:=stain H hΓ hs j e he n; exact ⟨_,hp.scale _⟩)
 exact ⟨_, (show Reed d h p (Skiff.spin l γ V P a e n) (fun i=> Skiff.spin l (Γ i) (S i) (U i) a e n) from hp).rafts hf⟩
end YM.RG08.Hatch
