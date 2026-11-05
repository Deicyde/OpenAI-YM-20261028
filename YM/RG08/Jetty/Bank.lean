import YM.RG08.Jetty.Dosh
import YM.RG08.Forms.Shuffle

/-! # Rooted packet score

Includes scalar vacuum WITH marker, no held slot convention. Root via
an absolute height func, max weights (before polynomial grade).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open Forms Pert.Bulk Finset Function
open scoped Topology BigOperators ENNReal Classical ContDiff
variable {I J:Type}{n m d:ℕ}{σ τ B C:ℝ}
structure Loom (I:Type) where
 height:I→ℝ
 nn : ∀ i,0≤height i
def Loom.cage (l:Loom I)(x:Tape n I):= Finset.fold max 0 (l.height ∘ x) univ
lemma Loom.cage_nn (l:Loom I)(x:Tape n I):0≤l.cage x:= (le_fold_max _).mpr (Or.inl le_rfl)
lemma Loom.float (l:Loom I)(x:Tape n I)(i:Fin n):l.height (x i)≤l.cage x:=(le_fold_max _).mpr (Or.inr ⟨i,mem_univ i,le_rfl⟩)
lemma Loom.racks (l:Loom I)(x:Tape n I){M:ℝ}(h:0≤M)(hf:∀ i,l.height (x i)≤M):l.cage x≤M:=(fold_max_le _).mpr ⟨h,fun i _=>hf i⟩
lemma Loom.picks (l:Loom I)(x:Tape n I)(e:Fin m→Fin n):l.cage (x ∘ e)≤ l.cage x:=l.racks _ (l.cage_nn x) (fun _=>l.float x _)
lemma Loom.perm (l:Loom I)(x:Tape n I)(e:Equiv.Perm (Fin n)):l.cage (x ∘ e)= l.cage x:=le_antisymm (l.picks x e) (by
 have ht:=l.picks (x ∘ e) (e.symm:Fin n→Fin n)
 rwa [show (x ∘ ⇑e) ∘ ⇑e.symm=x from funext fun i=>by simp] at ht)
lemma Loom.snoc (l:Loom I)(x:Tape m I)(y:Tape n I) : l.cage (Fin.append x y)= max (l.cage x) (l.cage y):=by
 apply le_antisymm (l.racks _ ((l.cage_nn x).trans (le_max_left ..)) (fun i=>?_))
 · apply max_le
   · exact l.racks _ (l.cage_nn _) (fun i=>by simpa using! l.float (Fin.append x y) (Fin.castAdd n i))
   exact l.racks _ (l.cage_nn _) (fun i=>by simpa using! l.float (Fin.append x y) (Fin.natAdd m i))
 exact Fin.addCases (motive:=fun i=> l.height (Fin.append x y i)≤max _ _) (fun j=>by simpa using! (l.float x j).trans (le_max_left (l.cage x) (l.cage y))) (fun j=>by simpa using! (l.float y j).trans (le_max_right (l.cage x) (l.cage y))) i

abbrev Pack (n:ℕ)(I:Type):= Tape n I→NoteX
def weft (l:Loom I)(σ:ℝ)(x:Tape n I):= ENNReal.ofReal (Real.exp (σ*l.cage x))
def gems (l:Loom I)(d:ℕ)(h:0<σ)(F:Pack n I)(x:Tape n I):= purse d h (F x) * weft l σ x
def Sings (l:Loom I)(d:ℕ)(h:0<σ)(F:Pack n I)(K:ℝ):= (∑' x:Tape n I,gems l d h F x)≤ENNReal.ofReal K
def Lyrics (F:Pack n I):Prop:=∀ x:Tape n I,Voice (F x)
def hymn (l:Loom I)(d:ℕ)(h:0<σ)(F:Pack n I):= ENNReal.toReal (∑' x:Tape n I,gems l d h F x)

variable {l l':Loom I}{h:0<σ}{F F':Pack n I}
lemma knits (x:Tape n I)(h:0≤σ): 1≤weft l σ x:=(ENNReal.one_le_ofReal).mpr (Real.one_le_exp (mul_nonneg h (l.cage_nn _)))
lemma hymn_nn : 0 ≤ hymn l d h F := ENNReal.toReal_nonneg
lemma Sings.cost (hv:Sings l d h F C):Sings l d h F (hymn l d h F):= by
 have he:=ne_top_of_le_ne_top ENNReal.ofReal_ne_top hv
 unfold hymn Sings;rw [ENNReal.ofReal_toReal he]
lemma Sings.hymn_le (hv:Sings l d h F C)(hC:0≤C):hymn l d h F ≤ C:=(ENNReal.toReal_mono ENNReal.ofReal_ne_top hv).trans_eq (ENNReal.toReal_ofReal hC)
lemma Sings.point (hv:Sings l d h F C)(x):gems l d h F x ≤ ENNReal.ofReal C:=(ENNReal.le_tsum _).trans hv
lemma plain_gems (x:Tape n I):purse d h (F x)≤gems l d h F x:=le_mul_of_one_le_right (zero_le (a:=purse d h (F x))) (knits _ h.le)
lemma Sings.plain (hv:Sings l d h F C)(x):purse d h (F x) ≤ ENNReal.ofReal C:=(plain_gems x).trans (hv.point x)
lemma Sings.quote (hv:Sings l d h F C)(hx:Lyrics F)(hC:0≤C)(x)(f): |F x f| ≤ C*beam d h f:=by
 refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (beam_nn ..))).mp ?_
 rw [ENNReal.ofReal_mul hC]; exact (purse_gives _ _ (hx _) _).trans (mul_le_mul_left (hv.plain x) _)
lemma Sings.mono (hv:Sings l d h F C){D}{ht:0<τ}(hw:τ≤σ)(hb:d≤D)(hf:∀ i,l'.height i≤l.height i)(he:C≤B):Sings l' D ht F B:=by
 apply (ENNReal.tsum_le_tsum (f:=gems l' D ht F) (g:=gems l d h F) (fun x=>mul_le_mul' (purse_up ht hw _ hb) ?_)).trans (hv.trans (ENNReal.ofReal_le_ofReal he))
 exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul hw (l'.racks _ (l.cage_nn _) fun i=>(hf _).trans (l.float x i)) (l'.cage_nn _) h.le))
lemma hush : Lyrics (0:Pack n I):=fun _=>quiet
lemma tin : Sings l d h (0:Pack n I) B:=by
 unfold Sings gems; simp [purse_zero]
lemma Lyrics.add (hv:Lyrics F)(hx:Lyrics F'):Lyrics (F+F'):=fun x=>(hv x).add (hx x)
lemma Lyrics.neg (hv:Lyrics F):Lyrics (-F):=fun x=>(hv x).neg
lemma Lyrics.sub (hv:Lyrics F)(hx:Lyrics F'):Lyrics (F-F'):=fun x=>(hv x).sub (hx x)
lemma Lyrics.smul (hv:Lyrics F)(c:ℝ):Lyrics (c • F):=fun x=>(hv x).smul c
lemma Lyrics.sum {A:Type}{f:A→Pack n I}(s:Finset A)(hf:∀ i∈s,Lyrics (f i)):Lyrics (∑ i∈s,f i):=fun x=>by rw [Finset.sum_apply];exact Voice.stage s _ fun i hi=>(hf i hi) x
lemma Sings.add (hv:Sings l d h F B)(hx:Sings l d h F' C)(hb:0≤B)(hc:0≤C): Sings l d h (F+F') (B+C):=by
 apply (ENNReal.tsum_le_tsum (g:=fun x=>gems l d h F x+gems l d h F' x) (fun x=>?_)).trans
 · rw [ENNReal.tsum_add]; exact (add_le_add hv hx).trans_eq (ENNReal.ofReal_add hb hc).symm
 unfold gems; rw [← add_mul]; exact mul_le_mul_left (purse_add ..) _
lemma Sings.neg (hv:Sings l d h F B):Sings l d h (-F) B:=by unfold Sings gems; simp only [Pi.neg_apply,purse_neg]; exact hv
lemma Sings.sub (hv:Sings l d h F B)(hx:Sings l d h F' C)(hb:0≤B)(hc:0≤C): Sings l d h (F-F') (B+C):=by rw [sub_eq_add_neg];exact hv.add hx.neg hb hc
lemma Sings.smul (hv:Sings l d h F B)(c:ℝ):Sings l d h (c • F) (|c| * B):=by
 apply (ENNReal.tsum_le_tsum (g:=fun x=>ENNReal.ofReal |c| * gems l d h F x) (fun x=>?_)).trans
 · rw [ENNReal.tsum_mul_left, ENNReal.ofReal_mul (abs_nonneg _)]; exact mul_le_mul_right hv _
 unfold gems; rw [← mul_assoc]; exact mul_le_mul_left (purse_smul ..) _
lemma Sings.sum {A:Type}{f:A→Pack n I}{a:A→ℝ}(s:Finset A)(hf:∀ i∈s,Sings l d h (f i) (a i))(hn:∀ i∈s,0≤a i):Sings l d h (∑ i∈s,f i) (∑ i∈s,a i):=by
 induction s using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty];exact tin
 | @insert j s hh ih=>
   rw [sum_insert hh,sum_insert hh]
   have he:=show ∀ i∈s,0≤a i from fun i hi=>hn _ (by simp [hi]);exact (hf j (by simp)).add (ih (fun i hi=>hf i (by simp [hi])) he) (hn j (by simp)) (sum_nonneg he)

def pattern (S:Equiv.Perm (Fin n))(F:Pack n I):Pack n I:= fun x=> F (x ∘ S)
def breeze (F:Pack n I):Pack n I:= ((Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹) • ∑ p,pattern p F
lemma Sings.pattern (hv:Sings l d h F B)(S:Equiv.Perm (Fin n)):Sings l d h (Jetty.pattern S F) B:=by
 have he(x:Tape n I): gems l d h (Jetty.pattern S F) x=gems l d h F (twist S x):=by
   unfold gems weft twist Jetty.pattern; change _=_ * ENNReal.ofReal (Real.exp (σ*l.cage (_ ∘ ↑S)))
   rw [l.perm];rfl
 unfold Sings; simp_rw [he]; rw [Equiv.tsum_eq (twist S)]; exact hv
lemma Sings.breeze (hv:Sings l d h F B)(hb:0≤B):Sings l d h (Jetty.breeze F) B:=by
 let a:ℝ:=Fintype.card (Equiv.Perm (Fin n)); have he:0<a:= Nat.cast_pos.mpr Fintype.card_pos
 have hh:= (Sings.sum univ (fun i _=> hv.pattern i) (fun _ _=> hb)).smul a⁻¹
 simp_rw [abs_of_pos (inv_pos.mpr he),sum_const,nsmul_eq_mul,card_univ] at hh
 change Sings _ _ _ (Jetty.breeze _) (a⁻¹*(a*B)) at hh; rwa [inv_mul_cancel_left₀ he.ne'] at hh
lemma Lyrics.breeze (hv:Lyrics F):Lyrics (Jetty.breeze F):=(Lyrics.sum (univ:Finset (Equiv.Perm (Fin n))) (f:=fun i=>Jetty.pattern i F) fun i _ x=> hv (x ∘ i)).smul _
end YM.RG08.Jetty
