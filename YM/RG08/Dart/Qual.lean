import YM.RG08.Dart.Fern
/-! # Store relative to chosen first mark. Orientation at arbitrary root in budget uses its own displacement charge on mark table. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Dart
open Function Lattice Wilson Exterior Laurent Work.F08 RG Next.Free Bloch Stationary Finset Filter Work.F02
open UVExt.Paths Push.AbsoluteSums Quire Vale Matrix Analysis Planned.PrimaryIntegral295 Work.F03 Shade
open Wax Town Creek
open scoped Topology BigOperators Real ContDiff Classical Matrix Matrix.Norms.Frobenius
variable {I J E E' W X: Type}[Fintype I][DecidableEq I][NormedAddCommGroup E][NormedSpace ℝ E]
    [CompleteSpace E][NormedAddCommGroup E'][NormedSpace ℝ E'][CompleteSpace E']{r k i s t:ℕ}{G:Gauge}{m:Side}{R v w θ C B:ℝ}{T:Finset I}
structure Camp (T: Finset I)(w:ℝ)(U:Places I → Rooted E W r)(C:ℝ):Prop where
   only:Only T U
   pos:0≤C
   for_all (a:↥T) : ∃ P:Fleet T→ℝ,(∀ i,Quire.Lit (U (loose T i)) w (P i)) ∧ ∀ p:Cover, SumBudget (fun i:Held a p=> Tribe a i.val w (P i.val)) C
lemma outingsE [Fintype W] {F: Rooted E W r}{x y:Cover}(h:Pail x v F B)(hp:0≤v): Quire.Lit (roam (-y) F) v (Real.exp (v*(r*size (y-x):ℕ))*B):= by
   apply polar_ar (x:=y)
   refine budget_mono (budget_scale (Real.exp_pos _|>.le) h) (fun i=>mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _)) (?_ : ∀ i, pale y v i *‖F i‖ ≤ Real.exp _*(pale x v i * ‖F i‖))
   intro i; have hx : size (y-x)=size (x-y):= vibrate_sym ..; rw [hx,←mul_assoc,pale,pale, ← Real.exp_add, add_comm (v*↑(r*size (x-y))), ← mul_add]
   exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left (by rw [← Nat.cast_add]; exact Nat.cast_le.mpr (spans x y i)) hp)) (norm_nonneg _)
-- polar_ar needs Fintype X +DecEq; adjust
variable {U V:Places I→ Rooted E W r}
lemma camps [Fintype W] (h:Owns w T U C)(he:v*((r+1:ℕ):ℝ)≤w)(hv:0<v)(a:↥T): Camp T v (fun x=> roam (-(x a)) (U x)) C := by
   have hp:v ≤ w:= le_trans (le_mul_of_one_le_right hv.le (by exact_mod_cast show 1≤r+1 from by omega)) he
   refine ⟨fun x y hx=> congr_arg₂ (fun z: Cover=>roam (-z)) (hx a a.property) (h.1 x y hx),h.pos,fun i=>?_⟩
   obtain ⟨P,H,H'⟩:= h.2.2 i
   have hP p: 0≤ P p:= (H p).nonneg
   let Z p:= Real.exp (v*(r*size ((p:Fleet T) a - p i) : ℕ))*P p
   refine ⟨Z,fun p=>?_,fun x=> budget_mono (H' x) (fun j=> mul_nonneg (Real.exp_pos _|>.le) (mul_nonneg (Real.exp_pos _|>.le) (hP j))) fun p=>?_⟩
   · rw [show loose T p a=p a from dif_pos a.property]; exact outingsE (Ink.shrink (H p) (show 0 ≤ pale (p i) (r:=r) (X:=W) v from fun i=> Real.exp_pos _|>.le) (fun i=> Real.exp_monotone (mul_le_mul_of_nonneg_right hp (by positivity)))) hv.le
   have hx : size (p.val a - p.val i) ≤ Mounts i p.val:= single_le_sum (s:=univ) (f:=fun u=> size (p.val u - p.val i)) (fun _ _=> Nat.zero_le _) (mem_univ a)
   unfold Tribe Z; rw [← mul_assoc, ← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (hP p.val); apply Real.exp_monotone; have hy: (r:ℝ)* size (p.val a-p.val i) ≤ (r:ℝ)* Mounts i p.val:=by exact_mod_cast Nat.mul_le_mul_left r hx
   have hh:=mul_le_mul_of_nonneg_right he (show 0≤ (Mounts i p.val:ℝ) by positivity)
   push_cast at *; nlinarith only [hv, hy,hh]
lemma camp_for (h:Camp T w U C)(hv:0≤w)(hx: T.Nonempty)(p:Places I): Quire.Lit (U p) w C:= by
   let i:T:=⟨hx.choose,hx.choose_spec⟩
   obtain ⟨P,H,hx⟩:= h.for_all i; let u:=pin T p; have he:=budget_single (hx (u i)) (⟨u,rfl⟩ : Held i (u i))
   rw [only_pin h.only p]; exact Ink.raise (H u) ((le_mul_of_one_le_left ((H u).nonneg) (Real.one_le_exp (mul_nonneg hv (Nat.cast_nonneg (Mounts i u))))).trans he)
lemma camp_mono (h:Camp T w U C)(hv:v ≤ w)(hp:C ≤ B): Camp T v U B:= by
   refine ⟨h.only,h.pos.trans hp,fun i=>?_⟩; obtain ⟨P,H,he⟩:=h.for_all i; refine ⟨P,fun k=> Ink.shrink (H k) (show 0≤ ling (r:=r) (α:=W) v from fun j=> Real.exp_pos _|>.le) (fun i=> Real.exp_monotone (mul_le_mul_of_nonneg_right hv (by positivity))),fun x=>?_⟩
   exact budget_loosen (budget_mono (he x) (fun i=>mul_nonneg (Real.exp_pos _|>.le) (Ink.nonneg (H _))) (fun i=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _))) ((H _).nonneg))) hp
lemma camp_foot (h:Camp T w U C)(op:Rooted E W r→ Rooted E' X s)(he:∀ f (i:ℝ),Quire.Lit f w i→ Quire.Lit (op f) v (B*i))(hv:v ≤ w)(hp:0≤B) : Camp T v (op ∘ U) (B*C):= by
   refine ⟨fun x y k=> congr_arg op (h.only x y k),mul_nonneg hp h.pos, fun i=>?_⟩; obtain ⟨P,H,hP⟩:=h.for_all i; refine ⟨_,fun k=> he _ _ (H k),fun x=> budget_mono (budget_scale hp (hP x)) (fun i=>mul_nonneg (Real.exp_pos _|>.le) ((he _ _ (H _)).nonneg)) fun k=>?_⟩
   unfold Tribe; rw [mul_left_comm _ B]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg _))) ((H _).nonneg)) hp
lemma camp_less (h:Camp T w U B)(hp:Camp T w V C): Camp T w (U-V) (B+C):= by
    refine ⟨fun x y hp'=> congr_arg₂ (·-·) (h.only x y hp') (hp.only x y hp'),add_nonneg h.pos hp.pos,fun i=>?_⟩; obtain ⟨U,H,H'⟩:= h.for_all i; obtain ⟨W,hW,hV⟩:= hp.for_all i
    refine ⟨U+W,fun i=> Ink.less (H i) (hW i) (fun i=> Real.exp_pos _|>.le),fun x=>?_⟩; simpa only [Tribe,Pi.add_apply,mul_add] using budget_plus (H' x) (hV x)
end YM.RG08.Dart
