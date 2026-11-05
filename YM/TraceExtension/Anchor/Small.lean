import YM.TraceExtension.Anchor.Lenses
import YM.Work.D01
import YM.MergeProof.North.Wicker

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Around Asymptotics
open scoped Topology ContDiff BigOperators

abbrev factor (S:Schedule) (a:ℝ) (k:ℕ):= Real.exp (S.scale k * a)
lemma shrunk (S:Schedule)(k:ℕ) : factor S (-1) k=S.a k:=by simp [factor,Schedule.scale, Real.exp_log (S.a_pos _)]
/-- Sub-exponential in scale, leading budget convention on all witnesses and shifts. -/
def Calms {X : Type*} [Norm X] (S : Schedule) (v:ℝ) (x : ℕ→X):Prop:= ∀ p:ℝ,v<p→ x=O[atTop] factor S p
def Fast {X : Type*} [Norm X] (S : Schedule) (x : ℕ→X):Prop:=∃ p:ℝ,p<0∧ x=O[atTop] factor S p
lemma factor_mul (S:Schedule)(a b:ℝ) : factor S (a+b)=factor S a*factor S b:= funext fun k=>by rw [factor, mul_add, Real.exp_add]; rfl
lemma factor_sub (S:Schedule)(a b:ℝ) : factor S (a-b)=factor S a/factor S b:= funext fun k=>by rw [factor, mul_sub, Real.exp_sub]; rfl
lemma factor_weight (S:Schedule)(a b:ℝ) (h:a<b) : factor S a=o[atTop] factor S b:=by
  apply isLittleO_of_tendsto (fun i hi=>(absurd hi (Real.exp_pos _).ne')); simp_rw [show ∀ i:ℕ, factor S a i/factor S b i= factor S (a-b) i from fun i=>by rw [factor_sub];rfl]
  exact Real.tendsto_exp_atBot.comp (by simpa [mul_comm (S.scale _) (_-_)] using! S.divergent.const_mul_atTop_of_neg (sub_neg.mpr h))
lemma factor_const {X:Type*}[Norm X](S:Schedule)(v:X)(p:ℝ)(hp:0 < p) : (fun _:ℕ=> v)=O[atTop] factor S p:=by
   refine IsBigO.trans ?_ (factor_weight S 0 p hp).isBigO; rw [show factor S 0=fun _=>1 from funext fun k=>by unfold factor; simp only [mul_zero,Real.exp_zero]]; exact isBigO_const_const _ (one_ne_zero' ℝ) _
lemma Calms.smaller {X Y : Type*}[Norm X][SeminormedAddCommGroup Y]{S:Schedule}{v:ℝ}{f:ℕ→X}{g:ℕ→Y}(h:Calms S v g)(ht:f=O[atTop]g): Calms S v f:=fun p hp=> ht.trans (h p hp)
lemma Calms.add {X : Type*}[NormedAddCommGroup X]{S:Schedule}{v:ℝ}{f g:ℕ→X}(h:Calms S v f)(ht:Calms S v g):Calms S v (f+g):=fun p hp=>(h p hp).add (ht p hp)
lemma Calms.mul {S:Schedule}{v w:ℝ}{f g:ℕ→ℝ}(h:Calms S v f)(ht:Calms S w g):Calms S (v+w) (f*g):=by
   intro p hp; let a:ℝ:= (p-(v+w))/2
   have ha:0<a:= by unfold a; linarith
   rw [show p=v+a+(w+a) by unfold a; ring, factor_mul]; exact (h (v+a) (by linarith)).mul (ht (w+a) (by linarith))
lemma factor_calms (S:Schedule)(a:ℝ): Calms S a (factor S a):=fun p hp=> (factor_weight S a p hp).isBigO
lemma Fast.add {X : Type*}[NormedAddCommGroup X]{S:Schedule}{f g:ℕ→X}(h:Fast S f)(ht:Fast S g):Fast S (f+g):=by
  obtain ⟨p,hp,h⟩:=h; obtain ⟨q,hq,hh⟩:=ht
  obtain he|he|he:= lt_trichotomy p q; · exact ⟨q,hq,(h.trans (factor_weight S p q he).isBigO).add hh⟩
  · subst p; exact ⟨q,hq,h.add hh⟩
  exact ⟨p,hp,h.add (hh.trans (factor_weight S q p he).isBigO)⟩
lemma Fast.smaller {X Y:Type*}[Norm X][SeminormedAddCommGroup Y]{S:Schedule}{f:ℕ→X}{g:ℕ→Y}(h:Fast S g)(ht:f=O[atTop]g):Fast S f:=⟨h.choose,h.choose_spec.1,ht.trans h.choose_spec.2⟩
lemma Fast.mul {S:Schedule}{f g:ℕ→ℝ}(h:Fast S f)(ht:Calms S 0 g):Fast S (f*g):= by
  obtain ⟨p,hp,h⟩:=h; refine ⟨p+-(p/2),by linarith,?_⟩; rw [factor_mul]; exact h.mul (ht _ (by linarith))
lemma Fast.money {X : Type*}[Norm X]{S:Schedule}{f:ℕ→X}(h:Fast S f):∃ p:ℝ,p<0∧∀ᶠ i:ℕ in atTop, ‖f i‖ < factor S p i:= by
  obtain ⟨p,hp,h⟩:=h; refine ⟨p/2,by linarith,?_⟩
  filter_upwards [(h.trans_isLittleO (factor_weight S p (p/2) (by linarith))).bound (show (0:ℝ)<1/2 by norm_num)] with k hk
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hk; exact hk.trans_lt (mul_lt_of_lt_one_left (Real.exp_pos _) (by norm_num))

variable {G:Gauge}
lemma curtain (s:RG.Levels G) : Calms s.S 0 (fun i=>Real.exp (Work.D01.columnLogs s i)):= by
  intro p hp
  refine isBigO_iff'.2 ⟨1,zero_lt_one,?_⟩
  filter_upwards [Work.D01.columnLogs_le s p hp] with i hi
  simp only [Real.norm_of_nonneg (Real.exp_pos _).le,one_mul,factor]
  exact Real.exp_monotone (hi.trans_eq (mul_comm ..))
lemma column_calm (s:RG.Levels G) : Calms s.S 0 (fun i => (s.params i).columns):= by
   refine (curtain s).smaller (isBigO_iff'.2 ⟨1,zero_lt_one,?_⟩); filter_upwards [eventually_gt_atTop (0:ℕ)] with i hi
   cases i with
   | zero=> omega
   | succ i=>
     let p:=(s.params (i+1)).columns; have he:0<p:=zero_lt_one.trans_le (s.params _).columns_ge
     rw [Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg he.le, one_mul, Work.D01.columnLogs_succ, Real.exp_add, Real.exp_log he]; exact le_mul_of_one_le_left he.le (Real.one_le_exp (Work.D01.columnLogs_nonneg ..))
end YM.Trace.Pull
