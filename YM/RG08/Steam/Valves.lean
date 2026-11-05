import YM.RG08.Steam.Gears

/-!
# Connected valence & heat-time finiteness

Each contraction consumes two fields; a primitive supplied positive g-degree e
can start with at most `e+2 ≤ 3*e`. Consequently the t-formal series at fixed order is
a polynomial, so the formal continuation all the way to heat time one is literal.
-/
noncomputable section
namespace YM.RG08.Steam
open Forms Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I:Type}{p q n j e:ℕ}{Γ:Forms.Line I}

structure Eligible (V:Grain I) : Prop where
  dark : V 0=0
  head : ∀ e n,V e n≠0→n≤e+2
  foot : ∀ e n,V e n≠0→Even (e+n)

lemma bleach_zero {n:ℕ} : bleach (0:Flake n I)=0:=bleached Sym.zero
lemma lap_zero {n:ℕ}:lap Γ (0:Flake (n+2) I)=0:=by
 rw [lap]; convert bleach_zero using 1;ext; simp [lam,run,bleach,woven,Finset.sum_apply]
lemma unilateral_zero {S:Grain I}(h:S e (n+2)=0): unilateral Γ S e n=0:=by rw [unilateral,h,lap_zero,smul_zero]
lemma pair_zero_left {G:Flake (q+1) I} : pair Γ (0:Flake (p+1) I) G n=0:=by
 have he:weld Γ (0:Flake (p+1) I) G=0:=by ext; simp [weld,seam]
 unfold pair bridge; rw [he,bleach_zero]; split_ifs<;>simp [move_zero]
lemma pair_zero_right {F:Flake (p+1) I} : pair Γ F (0:Flake (q+1) I) n=0:=by
 have he:weld Γ F (0:Flake (q+1) I)=0:=by ext; simp [weld,seam]
 unfold pair bridge; rw [he,bleach_zero]; split_ifs<;>simp [move_zero]

variable {V:Grain I}
lemma predecessors (h : burn Γ V (j+1) e n ≠ 0) :
 burn Γ V j e (n+2)≠0 ∨ ∃ c≤n, ∃ i≤j,∃ a≤e, burn Γ V i a (c+1)≠0 ∧ burn Γ V (j-i) (e-a) (n-c+1)≠0:=by
 by_contra H
 push Not at H
 apply h
 rw [blaze,wheels,unilateral_zero H.1]
 simp only [zero_add]
 convert smul_zero (A:=Flake n I) ((j+1:ℝ)⁻¹) using 2 -- ?
 apply Finset.sum_eq_zero; intro c hc
 apply Finset.sum_eq_zero; intro i hi
 apply Finset.sum_eq_zero; intro a ha
 simp only [mem_range] at hc hi ha
 by_cases he:burn Γ V i a (c+1)=0
 · rw [he]; exact pair_zero_left
 rw [H.2 c (by omega) i (by omega) a (by omega) he]; exact pair_zero_right

theorem preserves (hV:Eligible V)(j e n:ℕ)(h:burn Γ V j e n ≠ 0) : 0<e ∧ n ≤ e+2 ∧ Even (e+n) ∧ n+2*j ≤ 3*e:=by
 induction j using Nat.strong_induction_on generalizing e n with
 | h j ih=> cases j with
   | zero=>
     rw [spark] at h
     have he:e≠0:=by rintro rfl; rw [hV.dark] at h; exact h rfl
     have ha:=hV.head _ _ h
     exact ⟨by omega,ha,hV.foot _ _ h,by omega⟩
   | succ j=>
     obtain h|⟨c,hc,i,hi,a,ha,h1,h2⟩:=predecessors h
     · obtain ⟨he,hn,⟨x,hx⟩,hd⟩:=ih j (by omega) _ _ h
       refine ⟨he,by omega,⟨x-1,by omega⟩,by omega⟩
     obtain ⟨he,hn,⟨x,hx⟩,hd⟩:=ih i (by omega) _ _ h1
     obtain ⟨hz,hm,⟨y,hy⟩,hf⟩:=ih (j-i) (by omega) _ _ h2
     exact ⟨by omega, by omega, ⟨x+y-1,by omega⟩,by omega⟩

lemma live (hV:Eligible V)(j:ℕ):Eligible (burn Γ V j):=by
 refine ⟨?_,fun _ _ h=>(preserves hV _ _ _ h).2.1,fun _ _ h=> (preserves hV _ _ _ h).2.2.1⟩
 ext n u
 by_contra H
 exact Nat.lt_irrefl 0 (preserves (Γ:=Γ) hV j 0 n (fun he=> H (congrFun he u))).1

theorem off (hV:Eligible V)(j e n:ℕ)(he:3*e<n+2*j) : burn Γ V j e n=0:= Classical.not_not.mp fun h=> by have hx:= (preserves (Γ:=Γ) hV j e n h).2.2.2;omega

def ember (Γ:Forms.Line I)(V:Grain I)(t:ℝ):Grain I:=fun e n=>∑ j∈Finset.range (3*e+1), t^j • (burn Γ V j e n)
def cinder (Γ:Forms.Line I)(V:Grain I)(t:ℝ):Grain I:=fun e n=>∑ j∈Finset.range (3*e),t^(j+1) • (burn Γ V (j+1) e n)

theorem smoulder (Γ:Forms.Line I)(V:Grain I)(t:ℝ): ember Γ V t= V+cinder Γ V t:=by
 ext e n:2
 simp only [ember,Finset.sum_range_succ',spark,Pi.add_apply,cinder] -- remove Pow.pow
 simp [add_comm]

lemma appropriate (hV:Eligible V)(t:ℝ):Eligible (ember Γ V t):=by
 have he (e n)(h:ember Γ V t e n≠0):∃ j,burn Γ V j e n ≠0:=by
   by_contra! H;apply h;unfold ember;simp [H]
 refine ⟨?_,?_,?_⟩
 · ext n u
   unfold ember; simp [(live hV _).dark]
 · intro e n h; obtain ⟨j,h⟩:=he e n h;exact (preserves hV _ _ _ h).2.1
 intro e n h;obtain ⟨j,h⟩:= he e n h;exact (preserves hV _ _ _ h).2.2.1

end YM.RG08.Steam
