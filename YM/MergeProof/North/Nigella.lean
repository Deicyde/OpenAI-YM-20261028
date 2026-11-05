import YM.MergeProof.North.Lyme
import YM.MergeProof.Prism
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Festal
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus Switch
open GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V
variable (F:ι→ Config G f→Poly (Aged V))(v u:V)(E:Equiv.Perm ι)(B:Equiv.Perm V)(m:Motion)(x:Site f)
    (h:∀ i U,Harm v B m (F i (pull m.1 x U)) (F (E i) U))
include h
def Rate (i:ι)(p:(X).Mode):= ⨆ U, ‖(F i U).part p‖
lemma normEq (i:ι)(p:(X).Mode)(hp:Focused v p)(U:Config G f) : ‖(F (E i) U).part (drum B p)‖ = ‖(F i (pull m.1 x U)).part p‖:= by rw [h i U p hp,norm_scalar]
lemma equals (i:ι)(p:(X).Mode)(hp:Focused v p): Rate F i p=Rate F (E i) (drum B p):=by unfold Rate; simp_rw [normEq F v E B m x h i p hp]; exact ((pull_onto (G:=G) m x).iSup_comp _).symm
abbrev Viv (F:ι→ Config G f→Poly (Aged V)):= {s:ι×(Aged V).Mode// Vivid F s.1 s.2}
lemma both (i:ι)(p:(X).Mode)(hp:Focused v p): Vivid F i p↔ Vivid F (E i) (drum B p):=by
   constructor
   · rintro ⟨U,hU⟩; obtain ⟨U,rfl⟩:= pull_onto m x U; exact ⟨U,norm_ne_zero_iff.mp (by rw [normEq F v E B m x h i p hp]; exact norm_ne_zero_iff.mpr hU)⟩ -- lemma
   rintro ⟨U,hU⟩; exact ⟨_,norm_ne_zero_iff.mp (by rw [← normEq F v E B m x h i p hp U];exact norm_ne_zero_iff.mpr hU)⟩
lemma align (hv:B v=u):∃ b:Equiv.Perm (Viv F),(∀ i,Focused v i.val.2↔ Focused u (b i).val.2) ∧ ∀ i,Focused v i.val.2→(b i).val=Equiv.prodCongr E (drum B) i.val:=by
   let r:=fun i:Viv F=>Focused v i.val.2; let s:=fun i:Viv F=>Focused u i.val.2; let D:=Equiv.prodCongr E (drum B)
   let f:{i//r i}→{i//s i}:=fun i=> ⟨⟨D i.val.val, (both F v E B m x h _ _ i.property).1 i.val.property⟩,(hv ▸ (going B v _).mp i.property : Focused u (drum B i.val.val.2))⟩
   have he : Bijective f:=by
      refine ⟨fun i j e=> Subtype.ext (Subtype.ext (D.injective (congr_arg (fun i=> i.val.val) e))),fun i=>?_⟩
      obtain ⟨j,hj⟩:=D.surjective i.val.val; have hh: Focused u (drum B j.2):=(show Focused u (D j).2 from hj ▸ i.property); rw [← hv] at hh; have hy:= (going ..).2 hh; have hk: Vivid F (D j).1 (D j).2:=hj ▸ i.val.property
      exact ⟨⟨⟨j,(both F v E B m x h _ _ hy).2 hk⟩,hy⟩,Subtype.ext (Subtype.ext hj)⟩
   obtain ⟨d,hD,hd⟩:= extends_on he; exact ⟨d,hd,fun i hi=>congr_arg Subtype.val (hD ⟨i,hi⟩)⟩
omit h
variable {F} (w:Name V→ℝ){t d b:ℝ}{a: Name V→Site f}{X':ι→ Support f}
-- purchases Merit for quantities. from Towed. 
def table (i: Viv F):=Poly.toll w i.val.2*Rate F i.val.1 i.val.2
lemma r_ated [Nonempty (Config G f)]{s:ℕ}(hw:∀ i,0<w i)(hr:Towed w X' F s t b) : (∀ i p,0≤Rate F i p∧∀ U, ‖(F i U).part p‖ ≤ Rate F i p) ∧ Ac.Hit (fun i:Viv F=>X' i.val.1) s (table w) t b:=by
   obtain ⟨c,hc,hz,hB⟩:=hr; choose f hf hF he using hB
   have h₁ i p: BddAbove (Set.range (fun U=> ‖(F i U).part p‖)):= ⟨f i p,Set.forall_mem_range.mpr fun _=>hF ..⟩
   have hv i p U: ‖(F i U).part p‖ ≤ Rate F i p:= le_ciSup (h₁ i p) U
   have hP i p: 0≤ Rate F i p:= (norm_nonneg _).trans (hv i p 1)
   have hy i p : Rate F i p≤ f i p:= ciSup_le fun _=> hF ..
   refine ⟨fun _ _=>⟨hP ..,fun i=> hv ..⟩,fun i=>?_⟩
   let f' (j:ι× (X).Mode):= Poly.toll w j.2*Rate F j.1 j.2
   have hx j: 0≤ f' j:= mul_nonneg (Poly.worth hw _).le (hP ..)
   have hh : Ac.Hit (fun j:ι×(X).Mode=> X' j.1) s f' t b:=by
      intro i; refine ⟨fun j=>?_ ,Summable.of_finite,?_⟩
      · dsimp only; split; exact mul_nonneg (hx _) (Real.exp_pos _).le;rfl
      rw [tsum_fintype,Fintype.sum_prod_type]; apply le_trans (sum_le_sum (s:=univ) ?_) (Extra.Multi.Budget.cap (hz i) univ); intro j _; dsimp only
      by_cases h:i∈ X' j
      · simp only [h,↓reduceIte, ← sum_mul]; refine mul_le_mul_of_nonneg_right (le_trans (sum_le_sum ?_) (he j)) (Real.exp_pos _|>.le); exact fun p _=> mul_le_mul_of_nonneg_left (hy j p) (Poly.worth hw _).le
      · simp only [h,↓reduceIte,sum_const_zero]; rfl
   exact Extra.Multi.Budget.pull_le (q:=fun i:Viv F=>i.val) (p:=fun _=>True) (hh i) (fun v:Viv F=>(hh i).1 v.val) (fun _ _=>trivial) Subtype.val_injective.injOn (fun _ _=>le_rfl)
end YM.MergeProof.Ribbons
