import YM.WilsonBulk.Broadcast.Stadium

/-!
# Casting kernel lecture under march arena, log identity for `receive`
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Push FreeResolvent
open Work.F08 RG Sheet Pert.Bulk
variable {α β γ : Type} {f c Λ L n : Side} {σ θ p q : ℝ} (g : Ratio c f)
open PowerSeries (constantCoeff constantCoeff_X coeff)
-- Sector Γ and W

def corridor (β : Type) (F : Row α α) : Row (α⊕β) (α⊕β):= brace (stackRows F 0) 0
def sweep (U : Row α β) (P : Row γ β) := stackRows U P
lemma corridor_height {F : Row α α} (h : F.strip σ p) (hp : 0 ≤ p) : (corridor β F).strip σ p := brace_cost _ _ (stack_cost _ _ h (zero_cost _ hp)) (zero_cost _ hp)
lemma corridor_strip {F G : Row α α} (h : (minusRows F G).strip σ p) (hp : 0 ≤ p) : (minusRows (corridor β F) (corridor β G)).strip σ p := by
  rw [show minusRows (corridor β F) (corridor β G)= corridor β (minusRows F G) from ?_]; exact corridor_height h hp
  ext (i|i) (j|j) z <;> simp [corridor,minusRows,brace,stackRows]
lemma corridor_sees (F : Row (Co g.count α) (Co g.count α)) (G : Matrix (Co f α) (Co f α) ℝ) (h : Seen c (splitCo g α) (splitCo g α) F G) :
    ∀ i j, pair (fun x y=> (corridor β F).acts c x y) (two (promenade α β g i) (promenade α β g j)) = house G (two i j) := by
  let t:=promenade α β g; intro i j; cases i with
  | inl i=> cases j with
    | inl j=> rw [house_in,h, pays_here,pays_here]; exact rfl -- h : Seen
    | inr j=> rw [house_out, pays_here,pays_there]; simp [pair,two,corridor]
  | inr i=> rw [house_front,pays_there]; cases j with
    | inl j=> rw [pays_here]; simp [pair,two,corridor]
    | inr j=> rw [pays_there]; simp [pair,two,corridor]

abbrev jury {A B : Type} (h : A≃B) : Tape A →ₐ[ℝ] Tape B := submit (named ∘ h)
lemma jury_advance (u : α ≃ β) (A : Tape α) : jury u (advanceP _ A)=advanceP _ (jury u A) := by
  unfold jury; rw [submit_name,submit_name]; ext1 i; cases i
  · rw [advance_zero,coeff_parallel,advance_zero,map_zero]
  rw [advance_hr,coeff_parallel,coeff_parallel,advance_hr]
lemma jury_zoom (u : α≃β) (A : Tape α) : jury u (zoom A)=zoom (jury u A) := by
  unfold jury; rw [submit_name, submit_name]; ext1 i; rw [zoom_power, coeff_parallel, coeff_parallel, zoom_power]

variable [Fintype α] [Fintype β]
lemma jury_reflect (T : α ≃ β) {V : Page α 2} {U : Page β 2}
    (h : ∀ i j,U (two (T i) (T j))=V (two i j)) : ∀ p : Tape α, jury T (parallel (wick V) p)=parallel (wick U) (jury T p) := by
  let X i j := if T i=j then (1:ℝ) else 0
  let Y : α→ Tape β := named ∘ T
  have he : Reflects Y X V U := by
    have hz i j : player i (Y j)=algebraMap ℝ _ (X j i) := by rw [show Y j=named _ from rfl,player_name]; split <;> simp_all [X]
    exact ⟨fun i j _=>⟨hz i,hz j⟩,fun i j=> by simp [X,mul_ite,h]⟩
  intro p; exact (he.all Y p).symm
-- Ruling commutes with march if true sector W. Need for finite Scripts.
abbrev efferos (U : Cross L α β) := sweep U (unitRow β)
omit [Fintype α] [Fintype β] in
lemma effer_cost (U : Cross L α β) (h : U.strip σ p) : (efferos U).strip σ (max p 1) := strip_stack h strip_unit
omit [Fintype α] [Fintype β] in
lemma effer_delta (U V : Cross L α β) (h : (minusRows U V).strip σ p) (hp : 0 ≤ p) : (minusRows (efferos U) (efferos V)).strip σ p := by
  rw [show minusRows (efferos U) (efferos V)=stackRows (minusRows U V) (0:Row β β) from ?_]; exact stack_cost _ _ h (zero_cost _ hp)
  ext (i|i) j z <;> simp [minusRows,efferos,sweep,stackRows]
omit [Fintype α] in
lemma ruling_jury (W : Cross g.count α β) (h : Tape (Co c (Echelon α β g.count))) : ruling (installed g W) (jury (promenade α β g).symm h)=submit (quill ((efferos W).acts c) named) h := by
  unfold ruling jury; rw [submits]; congr 2; ext1 i -- expect ?
  obtain ⟨(i|i),rfl⟩:= (promenade α β g).surjective i
  · simp only [Function.comp_apply, Equiv.symm_apply_apply, submit_named,Sum.elim_inl]; exact rfl
  simp only [Function.comp_apply, Equiv.symm_apply_apply, submit_named, Sum.elim_inr]
  rw [pays_there]; change _ = ∑ _, _; simp only [efferos,sweep,stack_wage,acts_unit]; exact (congr_fun (quill_one named) i).symm
lemma varnish_lecture (I : Record (Market α)) (hp : Pamphlet I) : jury (promenade α β g).symm (volumeTape (issue c (lecture (install (varnish g.count α β)) I)))=mountain (Co f α) (Co c β) (volumeTape (issue f I)) := by
  let F:= varnish g.count α β; let M:=promenade α β g
  have hz:= issue_lecture (fun n=>installSession (n:=n) (F:=F) (varnish_cost _ _) one_pos zero_le_one) (install_gauge g F) _ (fun x y b=> install_roll F x y b) hp
  rw [← hz,lecture_tape,jury,submits]; congr 2 -- inspect
  ext1 i; change submit (named ∘ M.symm) (quill (installed g F) named i)=privateName i
  unfold quill; rw [map_sum, ← Equiv.sum_comp M]; simp only [Fintype.sum_sum_type,map_smul, M, F, Function.comp_apply,submit_named,Equiv.symm_apply_apply,varnish_not,varnish_at]; simp [ite_smul,privateName]
-- finite Scripts caller aisle
variable (K : Matrix (Co f α) (Co f α) ℝ) (X : Matrix (Co c β) (Co f α) ℝ)
variable (V : Row (Co g.count α) (Co g.count α)) (G : Matrix (Co f α) (Co f α) ℝ) (W : Cross g.count α β)
variable {H M : StageD (Co f α) (Co c β)}
lemma podium (I : Record (Co c (Echelon α β g.count))) (hi : Document I) (hp : Free I) (h : Seen c (splitCo g α) (splitCo g α) V G) (he : constantCoeff M=0) (ht : Steps 1 H (ambient K X p)) (hJ : jury (promenade α β g).symm (volumeTape I)= curtain K X p H M) :
    let C := pair (fun x y=> (corridor β V).acts c x y)
    Scripts (installed g W) G K X p H M (volumeTape (lecture (fun x y=> (efferos W).acts c x y) (receive C I false))) := by
  intro C
  let U:= receive C I false; let T:= (efferos W).acts c
  have hU : Free U:= (siteLimits _ false hi.cap hp hi.coherent).2.2
  rw [lecture_tape]
  have hf x y : house G (two ((promenade α β g).symm x) ((promenade α β g).symm y))= C (two x y) := by
    obtain ⟨u,rfl⟩:= (promenade α β g).surjective x; obtain ⟨v,rfl⟩:= (promenade α β g).surjective y; simp only [Equiv.symm_apply_apply]; exact (corridor_sees g V G h u v).symm
  refine ⟨ht,he,?_,c_empty (submit _) (by rw [submit_X,constantCoeff_X]) (tape_free hU)⟩
  rw [← hJ, ← show jury (promenade α β g).symm (tide (volumeTape I))=_ from tutor _ constantCoeff_X (tape_free hp),← jury_reflect (V:=C) (promenade α β g).symm hf, ruling_jury]
  rw [show parallel (wick C) (tide (volumeTape I)) = tide (volumeTape U) from (connected C hi.coherent hi.cap hp).symm, show submit (quill T named) (tide (volumeTape U))=tide (submit (quill T named) (volumeTape U)) from tutor _ constantCoeff_X (tape_free hU)] -- reduce let
end YM.WilsonBulk.Parapet
