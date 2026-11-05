import YM.RG08.Creek.Vanes
/-! # Native unprojected root bounds. Mesh growth charged before heat. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {I E X Z:Type} [Fintype I][DecidableEq I][Fintype X][DecidableEq X][Fintype Z][NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{G:Gauge}{L:Side}{R w v A B C:ℝ}{r D j k:ℕ}{T:Finset I}{x y z: Cover}
section prices
private lemma rosenL (p:Rooted E X r) : roam x (roam y p)=roam (x+y) p:= by
   unfold roam; funext i; simp only [comp_apply]; congr 1; funext j; simp [gang,shiftedBy, add_comm, add_assoc]
lemma rest_t (U:Rooted E X r): roam 0 U=U:= by funext p; unfold roam; simp only [comp_apply]; congr 1; funext i; simp [gang,shiftedBy]
lemma rested (U:Rooted E X r)(x:Cover): roam x (roam (-x) U)=U:= by rw [rosenL, add_neg_cancel, rest_t]
lemma bowed_ar (U:Rooted E X r) (h:Quire.Lit U w C)(x:Cover): Pail x w (roam x U) C:= by
   have hv : ∀ i:Beads X r,pale x w i=ling w ((gang x).symm i):= by intro i; simp only [pale, ling]; congr 3
   simpa only [Quire.Ink,Pail,Quire.Lit,roam,hv,Function.comp_apply] using budget_pull (gang (r:=r) (α:=X) x).symm (gang (r:=r) (α:=X) x).symm.injective h
lemma polar_ar {U:Rooted E X r}(h:Pail x w U C): Quire.Lit (roam (-x) U) w C:= by
   have hv : ∀ i:Beads X r,ling w i=pale x w ((gang (-x)).symm i):= by
      intro i; unfold ling pale
      congr 3; unfold stretch girth; apply sum_congr rfl; intro j _; simp only [gang, Equiv.coe_fn_symm_mk,shiftedBy]; rw [neg_neg,add_sub_cancel_right]
   simpa only [Quire.Ink,Pail,Quire.Lit,roam,hv,Function.comp_apply] using budget_pull (gang (r:=r) (α:=X) (-x)).symm (gang (r:=r) (α:=X) (-x)).symm.injective h

-- stem conversion via Ward proof; mean applies for any Poise
lemma poles_roam {U:Rooted (Poise T D R) X r}{M:Row X Z}(he:Whole M)(h:Pens U)(x:Cover): roam x (spring U M)=spring (roam x U) M:= by
   refine tapUni fun b=>?_ ; let f:=sampleK T b
   rw [spring_echo f (pens_roam h _) he]
   change roam x (f ∘ spring U M)=spring (roam x (f ∘ U)) M; rw [spring_echo f h he,spring_space (h.shaped f) he]
lemma pole_price (M:Row X Z)(he:M.strip w B)(hB:0≤B){U:Rooted (Poise T D R) X r} (hw:0<w)(h:Pail x w U C): Pail x w (spring U M) (((Fintype.card Z:ℝ)^r*B^r)*C):= by
   nth_rw 1 [← rested U x, ← poles_roam ⟨_,_,hw,he⟩ (Ink.pens (polar_ar h) (ling_one hw.le))]; exact bowed_ar _ (spring_receipt (polar_ar h) hw.le hB he) x
lemma wand_s (p:Site L){U:Rooted (Poise T D R) (Loc G 1) r}(x:Cover)(h:Pens U):
    vines L (roam (stemA L x p) U)=roam x (spring (shiftP p U) (skylight (Co L _) (Loc G 1))):=by
    refine tapUni fun b=>?_; let f:=sampleK T b; rw [vines_e _ L (pens_roam h _)]
    change lotS 0 (roam (stemA L x p) (f ∘ U))= roam x (f ∘ spring (shiftP p U) _); rw [spring_echo _ (shifted _ h) skylight_ok,shiftP,Pens.echo_pool _ h]; exact lot_history (h.shaped _) (by rw [nil_root,zero_add]; rfl)
def wand_fee (G:Gauge)(L: Side)(v:ℝ)(r:ℕ):= ((Fintype.card (Park G L):ℝ)^r)*Real.exp (4*v)^r
lemma wand_price {U:Rooted (Poise T D R) (Loc G 1) r}(p:Site L)(he:Pail (stemA L x p) w U C)(hv:0<v)(hw:0<w)(hL:v ≤ L.val*w):
   Pail x v (vines L U) (wand_fee G L v r*C) := by
   have ht:= polar_ar he; nth_rw 1 [← rested U (stemA L x p),wand_s p x (Ink.pens ht (ling_one hw.le)),wand_fee, mul_assoc]
   exact bowed_ar _ (by simpa using! spring_receipt (Q:=skylight _ (Loc G 1)) (shift_print p ht hv.le hL) hv.le (B:=1) zero_le_one skylight_price) x
lemma wand_plus (t:Finset Z)(F:Z→Rooted (Poise T D R) (Loc G 1) r)(h:∀ i∈t, Pens (F i)): vines L (∑ i∈t,F i)=∑ i∈t,vines L (F i):=by
   induction t using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty]; exact vines_0 _
   | insert i s hi ih=>
     have hx:= h i (mem_insert_self ..); have hS j hj:=h j (mem_insert_of_mem hj); have ht:=Pens.additions hS; rw [sum_insert hi,sum_insert hi,← ih hS]; unfold vines shiftP; rw [Pens.tub_plus _ hx ht,spring_plus (hx.pours _) (ht.pours _) skylight_ok]
lemma marks_size (h:0≤v)(hp:v≤L.val*w) (x y:Cover)(p q:Site L) : v*size (x-y) ≤ w*size (stemA L x p-stemA L y q)+4*v := by
   let a:= stemA L x p-stemA L y q; have hh : Lattice.lift q + a = stemA L (x-y) p:= by unfold a stemA; rw [smul_sub]; abel
   have hx : stemA L (carry q a) (Work.F08.arrives q a)=Lattice.lift q+a:= by rw [carry_spec,stemA,add_comm]
   have hk:=congr_arg (growP L) (hx.trans hh)
   have he:carry q a=x-y:= (stemA_fit L (carry q a,Work.F08.arrives q a)|>.1).symm.trans (hk.trans (stemA_fit L (x-y,p)|>.1))
   have hC:= size_scaled q a (x-y) h hp; rw [he,sub_self] at hC; simpa [size,a] using hC
-- per held root map with preset p tuple
abbrev decorate (X: Fleet T)(p:I→Site L): Fleet T:= pin T (footT L (loose T X) p)
private lemma peak_d (X: Fleet T)(p:I→Site L)(i:T): decorate X p i= stemA L (X i) (p i):= by unfold decorate footT pin; dsimp only; rw [show loose T X i=X i from dif_pos i.property]
lemma rise_anc (h:0≤v)(hv:v≤ L.val*w)(X: Fleet T)(p:I→Site L)(i:T): v*Mounts i X ≤ w*Mounts i (decorate X p)+4*v*T.card:= by
   unfold Mounts; rw [Nat.cast_sum,Nat.cast_sum, Finset.mul_sum,Finset.mul_sum]
   have ht: (∑ _j : T,(4*v))=4*v*T.card:= by simp [mul_comm, mul_left_comm]; -- fix
   rw [← ht,← sum_add_distrib]; exact sum_le_sum fun j _=> by rw [peak_d,peak_d]; exact marks_size h hv (X j) (X i) (p j) (p i)
lemma tribe_transfer (h:0≤v)(hv:v≤L.val*w){f:Fleet T→ℝ}{i:T}(he:∀ i,0≤f i)(hU:∀ x,SumBudget (fun y: Held i x=> Tribe i y.val w (f y.val)) A)
    (x:Cover)(p:I→Site L)(hg:0≤B): SumBudget (fun y:Held i x=> Tribe i y.val v (B*f (decorate y.val p))) ((B*Real.exp (4*v*T.card))*A):=by
   let k(y:Held i x): Held i (stemA L x (p i)):= ⟨decorate y.val p,by rw [peak_d,y.property]⟩
   have hh:Injective k:= by intro v w ht; have hz : decorate v.val p=decorate w.val p:=congr_arg Subtype.val ht; refine Subtype.ext (funext fun j=>?_); have hv:=congr_fun hz j; rw [peak_d,peak_d] at hv; exact (stemA_fit L (v.val j,p j)|>.1).symm.trans ((congr_arg (growP L) hv).trans (stemA_fit L (w.val j,p j)|>.1))
   let z:=4*v*T.card; refine budget_mono (budget_scale (show 0 ≤ B*Real.exp z from by positivity) (budget_pull k hh (hU _))) (fun i=>mul_nonneg (Real.exp_pos _|>.le) (mul_nonneg hg (he _))) (fun y=>?_)
   unfold Tribe; rw [mul_left_comm _ B]; change B * (Real.exp _ * f _) ≤ B * Real.exp z * (Real.exp (w*Mounts i (decorate y.val p))* f (decorate y.val p)); rw [mul_assoc B,← mul_assoc (Real.exp z),mul_comm (Real.exp z),← Real.exp_add]
   exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (rise_anc h hv y.val p i)) (he _)) hg

def paid_shop (L:Side)(p:Finset I)(r:ℕ)(b:I→ℝ)(G:Gauge)(v:ℝ):= wand_fee G L v r* ‖∏ i∈p,b i‖
lemma shine_a (v:ℝ)(p:I→Site L){G:Gauge}{F:Layouts I G D R}(he: Owns w T (fun x=>F x T k r) C)(b:I→ℝ)(hw:0<w)(hv:0<v)(hk:v ≤ L.val*w): Owns v T (fun x=> vines L (shop p F x b T k r)) (paid_shop L T r b G v*Real.exp (4*v*T.card)*C):=by
   let W:= paid_shop L T r b G v; have hh:0≤W:= by unfold W paid_shop wand_fee; positivity
   refine ⟨fun x y h=>?_,mul_nonneg (mul_nonneg hh (Real.exp_pos _|>.le)) he.pos,fun i=>?_⟩
   · dsimp only; unfold shop; rw [show F (footT L x p) _ _ _=F (footT L y p) _ _ _ from he.1 _ _ fun i hi=>?_]; unfold footT; rw [h i hi]
   obtain ⟨V,hp,H⟩:= he.2.2 i; refine ⟨fun X=> W*V (decorate X p),fun X=> ?_,fun x=> tribe_transfer hv.le hk (fun i=>Ink.nonneg (hp i)) H x p hh⟩
   let R':= loose T X; have ht:=hp (decorate X p); dsimp only at ht; rw [peak_d,show F (loose T (decorate X p)) _ _ _=F (footT L (loose T X) p) _ _ _ from (only_pin he.1 _).symm] at ht
   unfold W paid_shop; dsimp only; rw [mul_assoc]; exact wand_price (p i) (Ink.scale (Ink.raise (Ink.some ht (shuffle p T D R) (fun i=> Real.exp_pos _|>.le)) (mul_le_of_le_one_left ht.nonneg (shuffle_cost ..))) _) hv hw hk
-- count coarse multiplicity all tags polynomial at use
lemma chanters (L : Side){F:Layouts I G D R}(he: Owns w T (fun x=>F x T k r) C){a:I→ℕ}(hp:Sense a F)(b:I→ℝ)(hw:0<w)(hv:0<v)(hk:v ≤ L.val*w):
   Owns v T (fun x=> chancel L (signet L F x b) T k r) (((Fintype.card (Site L):ℝ)^T.card * (paid_shop L T r b G v*Real.exp (4*v*T.card)))*C) := by
   let S:= paid_shop L T r b G v; let q(x:Places I)(i:subroll T (Site L)):= shop (enter T i) F x b T k r
   simp_rw [chancel,signet, Finset.sum_apply]; have hx (x:Places I): vines L (∑ i:subroll T (Site L),q x i)=∑ i:subroll T (Site L),vines L (q x i):= wand_plus _ _ fun i _=> (shop_style hp _ x b T|>.tidy k r).pens
   change Owns _ _ (fun x=>vines _ (∑ i:subroll T (Site L),q x i)) _; simp_rw [hx]
   simpa only [sum_const,card_univ,nsmul_eq_mul,Fintype.card_fun,Fintype.card_coe,Nat.cast_pow,mul_assoc] using owns_sum (univ:Finset (subroll T (Site L))) (fun p _=> shine_a v (enter T p) he b hw hv hk)
end prices
end YM.RG08.Creek
