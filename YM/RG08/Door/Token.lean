import YM.RG08.Needle.Cali
/-!
# Rooted wallets. Factor δ. May be called varying scales, ranks fixed.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade
open scoped BigOperators Topology Real Classical
variable {I J E : Type}{α β : I→Type}{r s D : ℕ}[NormedAddCommGroup E]
variable {y σ w v δ b c x z : I→ℝ}{F V H : ∀ i,Rooted E (α i) r}

structure Tin (y δ : I→ℝ) (F : ∀ i, Rooted E (α i) r) (σ : I→ℝ) : Prop where
    serves : ∃ B,Weighed y B ∧ ∀ i,Quire.Lit (F i) (σ i) (B i*δ i)

lemma Tin.solo (h : Tin y δ F σ)(hv : 0≤σ)(i): Pens (F i) := (h.serves.choose_spec.2 i).pens (ling_one (hv i))
lemma Tin.raise (h : Tin y δ F σ)(hv : δ ≤ v) : Tin y v F σ := ⟨_,h.serves.choose_spec.1,fun i=> (h.serves.choose_spec.2 i).raise (mul_le_mul_of_nonneg_left (hv i) (h.serves.choose_spec.1.positive i))⟩
lemma Tin.soften (h : Tin y δ F w)(hp : v ≤ w) : Tin y δ F v := by
  obtain ⟨A,hA,ha⟩:=h.serves; refine ⟨A,hA,fun i=> (ha i).shrink (show (0:Beads _ _→ℝ)≤ _ from fun z=> (ling_pos _ _).le) ?_⟩
  intro z; dsimp only [ling]; gcongr; exact hp i
lemma Tin.plus (h : Tin y δ F w)(hp : Tin y δ V w)(he : Audience y) : Tin y δ (F+V) w := by
  obtain ⟨A,hA,H⟩:=h.serves; obtain ⟨B,hB,hv⟩:=hp.serves; exact ⟨A+B,hA.plus hB he,fun i=> Ink.raise (Ink.plus (H i) (hv i) (fun i=>(ling_pos _ _).le)) (by rw [Pi.add_apply,add_mul])⟩
lemma Tin.neg (h: Tin y δ F w): Tin y δ (-F) w := ⟨_,h.serves.choose_spec.1,fun i=>(h.serves.choose_spec.2 i).neg⟩
lemma Tin.less (h : Tin y δ F w)(hp: Tin y δ V w)(he : Audience y): Tin y δ (F-V) w:= by rw [sub_eq_add_neg]; exact h.plus hp.neg he
lemma Tin.zero : Tin y δ (0:∀ i, Rooted E (α i) r) w := by refine ⟨0,Weighed.zero,fun i=>?_⟩; rw [Pi.zero_apply,Pi.zero_apply,zero_mul]; exact Quire.Ink.none ..
lemma Tin.additions (S : Finset J) {f:J→∀ i,Rooted E (α i) r}(he:Audience y)(h : ∀ i∈S,Tin y δ (f i) w): Tin y δ (fun i=>∑ j∈S,f j i) w := by
   induction S using Finset.induction_on with
   | empty=> simp only [sum_empty]; exact Tin.zero
   | insert i s hi ih=> simp_rw [sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih (fun j hj=>h j (mem_insert_of_mem hj))) he
lemma Tin.move (b:J→I)(h:Tin y δ F w): Tin (y∘b) (δ∘b) (fun j=> F (b j)) (w∘b) := ⟨_,h.serves.choose_spec.1.transfer b,fun i=> h.serves.choose_spec.2 (b i)⟩

structure Twill (y δ : I→ℝ) (F V : ∀ i,Rooted E (α i) r)(w : I→ℝ) : Prop where
  one : Tin y 1 F w
  two : Tin y 1 V w
  goes : Tin y δ (F-V) w
lemma Twill.same (h : Tin y 1 F w) : Twill y δ F F w := ⟨h,h,by rw [sub_self]; exact Tin.zero⟩
lemma Twill.plus (h : Twill y δ F H w){U:∀ i,Rooted E (α i) r}(hp:Twill y δ V U w)(he : Audience y) : Twill y δ (F+V) (H+U) w := ⟨h.1.plus hp.1 he,h.2.plus hp.2 he,by rw [show F+V-(H+U)=F-H+(V-U) by abel]; exact h.3.plus hp.3 he⟩
lemma Twill.zero : Twill y δ (0:∀ i,Rooted E (α i) r) 0 w := Twill.same Tin.zero
lemma Twill.sums {f g : J →∀ i,Rooted E (α i) r} (S : Finset J)(he : Audience y)(hp : ∀ j∈S,Twill y δ (f j) (g j) w) : Twill y δ (fun i=> ∑ j∈S,f j i) (fun i=> ∑ j∈S,g j i) w := by
  induction S using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Twill.zero
  | insert i s hi ih=> simp_rw [sum_insert hi]; exact (hp i (mem_insert_self ..)).plus (ih fun j hj=>hp j (mem_insert_of_mem hj)) he
lemma Twill.soften (h : Twill y δ F H w)(hv : v ≤ w) : Twill y δ F H v := ⟨h.one.soften hv,h.two.soften hv,h.goes.soften hv⟩
variable [NormedSpace ℝ E]
lemma Tin.scale (h : Tin y δ F w) (he : Weighed y (fun i=> ‖b i‖)): Tin y δ (fun i=> b i • F i) w := ⟨_,he.times h.serves.choose_spec.1,fun i=> by rw [Pi.mul_apply,mul_assoc]; exact Ink.scale (h.serves.choose_spec.2 i) _⟩
lemma tin_change (h : Lease y δ b c) (he : Tin y 1 F w): Tin y δ (fun i=> (b i-c i) • F i) w := by
  obtain ⟨A,hA,H⟩:=h.asset; obtain ⟨V,hV,hx⟩:= he.serves; refine ⟨A*V,hA.times hV,fun i=> Ink.raise (Ink.scale (hx i) (b i-c i)) ?_⟩
  rw [Pi.mul_apply,mul_right_comm (A i), Pi.one_apply,mul_one]; exact mul_le_mul_of_nonneg_right (H _) (hV.positive i)
lemma Twill.scales (h : Twill y δ F H w) (hp : Lease y δ b c) (he : Audience y): Twill y δ (fun i=> b i • F i) (fun i=> c i • H i) w := by
  constructor; exact h.one.scale hp.has; exact h.two.scale hp.also
  apply cast _ ((h.goes.scale hp.has).plus (tin_change hp h.two) he)
  congr 1; funext i; dsimp only [Pi.sub_apply,Pi.add_apply]; rw [smul_sub,sub_smul]; abel
lemma Twill.weight (h : Twill y δ F H w)(t:ℝ)(he:Audience y): Twill y δ (t • F) (t • H) w:= h.scales (Lease.const _ _ t) he
end YM.RG08.Door
