import YM.RG08.Wax.Lodge
/-! # Per-root heart strip. No field/test order lost beyond edges.
 Real signs kept algebraically. Lit on full fiber offsets.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Wax
open Function Filter RG Lattice Laurent Stationary Quire Analysis Shade Vale Bands Loom Next.Free Bloch Scores Finset Push.AbsoluteSums UVExt.Paths Town Work.F08
open scoped Topology BigOperators Real Classical
variable {I E X:Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {i j k r s D:ℕ}{A B w v Z K θ R:ℝ}{U V T:Finset I} {M:Row X X} {p:Option Side}
lemma sew_pail {F:Rooted E X r}{o:Cover}(h:Pail o w F A): Pail o w (sew F) A:= sewn_income _ (fun i=>(Real.exp_pos _).le) (fun i s=>by
   unfold pale; rw [show stretch o (i∘s)=stretch o i from Equiv.sum_comp s (fun j=>size ((i j).1-o))]) h
lemma span_cast (o:Cover)(F:Beads X (r+1)) : stretch o (stem1 F) ≤ stretch o F := by
   unfold stretch; rw [Fin.sum_univ_succ]; exact Nat.le_add_left ..
lemma vibrate (x y z:Cover): size (x-y) ≤ size (x-z)+size (z-y) := (le_of_eq (show size (x-y)=size (x-z+(z-y)) by rw [sub_add_sub_cancel])).trans (size_add ..)
lemma vibrate_sym (x y:Cover): size (x-y)=size (y-x):= by rw [show x-y=-(y-x) from neg_sub .. |>.symm, size_neg]
lemma spans (x y:Cover) (F:Beads X r) : stretch y F ≤ stretch x F+r*size (x-y):= by
    unfold stretch; apply le_trans (sum_le_sum (fun i _=> vibrate (F i).1 y x)) (by rw [sum_add_distrib]; simp)
lemma pale_sub (o:Cover)(b:Beads X (r+1))(i:Fin (r+1)) : size ((b i).1-o) ≤ stretch o b:= single_le_sum (f:=fun j=> size ((b j).1-o)) (fun _ _=> Nat.zero_le _) (mem_univ i)
lemma jib_pail (x:Cover){F:Rooted E X (r+2)} (h:Pail x v F A)(hv:0≤v)(hp:M.strip θ K)(he:0≤θ)(hk:0≤K) : Pail x v (jib p M F) (‖batting r‖ * (K*A)):= by
    have hb: Ink (pale x v ∘ stems) (knot p F M) (K*A):= by
       apply budget_mono (budget_scale hk h) (fun i=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)); intro i
       have he : ‖tuneS M p i‖ ≤ K:= stroke_known M hp he ..
       simp only [knot,norm_smul]; grw [he]; apply le_trans (b:=pale x v i*(K*‖F i‖)) _ (le_of_eq (mul_left_comm ..)); apply mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ hv)) (by positivity)
       exact_mod_cast ((span_cast x (stem1 i)).trans (span_cast x i))
    exact sew_pail ((hb.pour _ (pale_one x hv)).scale _)
lemma coral_span (o:Cover)(x : Coves X r s×Cover): stretch o (coral x)≤ stretch o x.1.1+girth x.1.2 +s*(stretch o x.1.1+size x.2):=by
   have hm : stretch o (shiftedBy ((x.1.1 0).1+x.2) (stem1 x.1.2)) ≤ girth x.1.2+s*(stretch o x.1.1+size x.2):= by
      let b:= x.1.1; let c:=x.1.2
      have hz : stretch ((b 0).1+x.2) (shiftedBy ((b 0).1+x.2) (stem1 c))=girth (stem1 c):= by unfold stretch girth; simp [shiftedBy]
      apply (spans ((b 0).1+x.2) o (shiftedBy _ (stem1 c))).trans; rw [hz]; refine add_le_add (stems_le _) (Nat.mul_le_mul_left _ ?_); rw [show (b 0).1+x.2-o=(b 0).1-o+x.2 by abel]; exact (size_add ..).trans (Nat.add_le_add_right (pale_sub o b 0) _)
   unfold stretch coral tide; rw [Fin.sum_univ_add]; simp only [Fin.append_left,Fin.append_right]; rw [add_assoc]; exact Nat.add_le_add (span_cast ..) hm
lemma clasp_pail {F:Rooted E X (r+1)}{Z: Shale X (s+1)}(o:Cover)(h:Pail o (((s+1:ℕ):ℝ)*w) F A)(hp:Glow Z w B)(hv:0≤w)(hg : M.strip ((s:ℝ)*w) K)(hh:0≤K): Pail o w (clasp M F Z) (‖syl r s‖*(K*(A*B))) := by
   let z:= (↑(s+1:ℕ):ℝ)*w; apply sew_pail; apply Ink.scale; unfold tie; apply Ink.pour; swap; · exact pale_one o hv
   have hu:= h.prods hp; refine Ink.sires_cost hu (pale o w ∘ coral) _ hh (fun i=>?_)
   rw [mul_comm K]; apply budget_mono (budget_scale (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (hg (i.1 0).2 (i.2 0).2)) (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)); intro a
   simp only [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
   rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
   have ht:(stretch o (coral (i,a)):ℝ) ≤ stretch o i.1 + (girth i.2:ℝ)+(s:ℝ)*(stretch o i.1+(size a:ℝ)):= by exact_mod_cast coral_span o (i,a)
   push_cast; nlinarith only [mul_le_mul_of_nonneg_left ht hv]

variable {x y o: Cover} {F:Rooted (Poise U D R) X (r+1)} {G:Rooted (Poise V D R) X (s+1)}
lemma stems_sum (a:Beads X (r+1)×Beads X (s+1))(o:Cover): stretch o (stemPair a)=stretch o (stem1 a.1)+stretch o (stem1 a.2):= by unfold stretch stemPair aboardB; rw [Fin.sum_univ_add]; simp only [Fin.append_left,Fin.append_right]
lemma pair_bound (a:Beads X (r+1) × Beads X (s+1))(x y:Cover): size (x-y) ≤ stretch x a.1+stretch y a.2+size ((a.2 0).1-(a.1 0).1):= by
   let i:=(a.2 0).1; let j:=(a.1 0).1
   rw [vibrate_sym x y]; have hu:=vibrate y x i; have he:=vibrate i x j
   have hp:= pale_sub y a.2 0; have ht:= pale_sub x a.1 0
   change size (i-y)≤_ at hp; change size (j-x)≤_ at ht; rw [vibrate_sym i y] at hp; change _ ≤ _ + size (i-j); omega
-- Input w, output v, separation $θ. Any terminal marker θ at ANY TAG ROOT. deterministic.
lemma pulses_pair (T:Finset I)(h:Pail x w F A)(hm:Pail y w G B)(hp:o=x ∨ o=y)(hv:0≤v)(hθ:0≤θ)(hw: θ+v*((r:ℝ)+s+1)≤w)(hK:M.strip w K)(hg:0≤K) :
   Pail o v (wounds none T M F G) (‖syl r s‖*(Real.exp (-θ*size (x-y))*K*(A*B))):= by
   apply sew_pail; apply Ink.scale; apply Ink.pour; swap; · exact pale_one o hv
   apply budget_mono (budget_scale (mul_nonneg (Real.exp_pos _).le hg) (budget_prod h hm)) (fun i=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _)); intro i
   let a:= (i.1 0).1; let b:=(i.2 0).1
   have hB : ‖bob none M i‖≤ Real.exp (-w*size (b-a))*K := by
      rw [neg_mul,Real.exp_neg]; refine (le_inv_mul_iff₀ (Real.exp_pos _)).mpr (budget_single (hK _ _) _)
   let X' := stretch x i.1; let Y':= stretch y i.2
   let C:= size (x-y); let D':=size (b-a)
   have he: stretch o (stemPair i) ≤ X'+Y'+ (r+s)*C := by
      rw [stems_sum]; rcases hp with hj|hj <;> rw [hj]
      · have hx:= span_cast x i.1; have hF:= spans y x (stem1 i.2); rw [vibrate_sym y x] at hF; have hT:=span_cast y i.2; dsimp only [X',Y',C] at *; rw [add_mul]; omega
      have hx:= spans x y (stem1 i.1); have hy:= span_cast y i.2; have ht:= span_cast x i.1; dsimp only [X',Y',C] at *; rw [add_mul]; omega
   have ht: (C:ℝ) ≤ X'+(Y':ℝ)+(D':ℝ):=by exact_mod_cast pair_bound i x y
   have hs: v*stretch o (stemPair i) - w*D' ≤ -θ*C+(w*X'+w*Y'):= by
      apply sub_le_iff_le_add.mpr
      calc
        _ ≤ v*(X'+(Y':ℝ)+((r:ℝ)+s)*C) := mul_le_mul_of_nonneg_left (by exact_mod_cast he) hv
        _ ≤ _ := by
           have hx:= mul_le_mul_of_nonneg_right hw (show (0:ℝ)≤ X'+(Y':ℝ)+(D':ℝ) by positivity)
           have hy:= mul_le_mul_of_nonneg_left ht (show 0≤ θ+v*((r:ℝ)+s) by positivity)
           nlinarith only [hx,hy,mul_nonneg hv (show 0≤(D':ℝ) by positivity)]
   simp only [tape_pair,norm_smul]; refine (mul_le_mul_of_nonneg_left (mul_le_mul hB (sale_cost _ _ _) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hg)) (Real.exp_pos _).le).trans ?_
   let n:=K*(‖F i.1‖*‖G i.2‖); let p:=v*stretch o (stemPair i)
   calc
     _ = Real.exp (p-w*D') * n:= by rw [sub_eq_add_neg p,Real.exp_add]; unfold p n D'; ring_nf
     _ ≤ Real.exp (-θ*C+(w*X'+w*Y')) * n:=mul_le_mul_of_nonneg_right (Real.exp_monotone hs) (mul_nonneg hg (by positivity))
     _ = _:= by simp only [Real.exp_add]; unfold n X' Y' C pale; ring
end YM.RG08.Wax
