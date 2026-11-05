import YM.RG08.Hatch.Food
import YM.RG08.Gallery.Script

/-! # All-mark periodization at every root i (scalar included), exact DCT.
No external polynomial ideal. Works prior to field-horizon projection.
No position genealogy in the vacuum-side tape beyond width (paths must be
precharged already if implementing a cylindrical selection).
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Hatch
open Jetty Skiff Lattice Isles Forms Pert.Bulk Function Finset Laurent Filter Packets Steam Mount
open scoped Topology BigOperators ENNReal Classical
variable {I J:Type} {n d:ℕ}{σ C:ℝ}{h:0<σ}{F:Pack n I}{l:Loom I}

lemma jewel(hF:Sings l d h F C):(∑' i,purse d h (F i))≠⊤:=ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((ENNReal.tsum_le_tsum (fun i=>plain_gems i)).trans hF)
lemma jewelled (hv:Lyrics F)(he:Sings l d h F C)(f:Pearl):Summable (fun i=> ‖F i f‖):=audible _ _ _ hv (jewel he) f
lemma portion (hv:Lyrics F)(he:Sings l d h F C)(f:Pearl)(p:Tape n I→Prop)[DecidablePred p]:Summable (fun i=>‖if p i then F i f else 0‖):=(jewelled hv he f).of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>by split <;> simp)

def broom (u:I→J)(F:Pack n I):Pack n J:=fun y f=>∑' i:Tape n I, if y=u∘i then F i f else 0
lemma dead (u:I→J):broom u (0:Pack n I)=0:=by ext1 _; funext _;simp [broom]
lemma cull (u:I→J)(hv:Lyrics F)(he:Sings l d h F C): Lyrics (broom u F):=by
 intro x;let D (i:Tape n I):NoteX:= if x=u∘i then F i else 0
 have ht:= jewel he
 have ho:Lyrics D:=fun i=>by unfold D; split;exact hv i;exact Jetty.quiet
 have hb:(∑' i,purse d h (D i))≠⊤:=ne_top_of_le_ne_top ht (ENNReal.tsum_le_tsum fun i=>by unfold D;split; rfl; rw [purse_zero];exact bot_le)
 have hT:broom u F x=(fun y=>∑' i,D i y):=by funext y;simp [broom,D,ite_apply]
 rw [hT];exact choir _ _ _ ho hb
lemma toolish (u:I→J)(L:Loom J)(σ':ℝ)(k:0<σ')(hp:σ' ≤ σ)(hc:∀ i,σ'*L.height (u i)≤σ*l.height i)(he:Sings l d h F C): Sings L d k (broom u F) C:=by
 calc _ ≤ ∑' y:Tape n J,∑' x,if y=u∘x then gems l d h F x else 0:= ENNReal.tsum_le_tsum (fun y=>?_)
      _ ≤ ENNReal.ofReal C:=by rw [ENNReal.tsum_comm];simp_rw [tsum_ite_eq];exact he
 unfold gems broom
 let D (x:Tape n I):NoteX:=if y=u∘x then F x else 0
 apply (mul_le_mul_left (show (Jetty.purse d k fun f=>∑' x, if y=u∘x then F x f else 0) ≤ ∑' i,Jetty.purse d k (D i) from by
    convert purse_sum d k D using 2; funext f; exact tsum_congr fun x=>by simp [D,ite_apply]) _).trans
 rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum;intro x
 unfold D; split_ifs with hy
 · subst hy; refine mul_le_mul' (purse_up _ hp _ le_rfl) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
   rw [mul_comm σ',←le_div_iff₀ k];apply L.racks _ (div_nonneg (mul_nonneg h.le (l.cage_nn _)) k.le);intro i;rw [le_div_iff₀ k,mul_comm];exact (hc (x i)).trans (mul_le_mul_of_nonneg_left (l.float x i) h.le)
 rw [purse_zero,zero_mul]
lemma bowl (u:I→J){f:Pearl}(he:Forms.Sym (during f F)):Forms.Sym (during f (broom u F)):=by
 intro e;ext y; unfold woven during broom
 rw [← (twist e).tsum_eq]
 apply tsum_congr;intro i
 change (if y ∘ ⇑e=u ∘ (i∘ ⇑e) then F (i∘ ⇑e) _ else 0)=_
 rw [show F (i ∘ ⇑e) _=F i _ from congrFun (he e) i]; apply ite_cond_congr
 apply propext
 constructor
 · intro hi; funext j
   simpa only [Function.comp_apply, e.apply_symm_apply] using congrFun hi (e.symm j)
 · rintro rfl; rfl

variable {F:Pack n (Market I)}
theorem Reed.sill (hv:Lyrics F)(he:Sings (stance I) d h F C)(hc:0≤C):Reed d h C F (fun m=>broom (port (chain m)) F):=by
 refine ⟨hc,hv,fun m=> cull (port (chain m)) hv he,he,fun m=>toolish (l:=stance I) _ _ σ h le_rfl (fun i=> mul_le_mul_of_nonneg_left (Isles.native_port _) h.le) he,fun f x=>?_⟩
 let p(i:Tape n (Market I)):= if x=i then F i f else 0
 let q(m:ℕ)(i:Tape n (Market I)):= if port (chain m) ∘ x=port (chain m) ∘ i then F i f else 0
 have hx(i):Tendsto (fun m=>q m i) atTop (𝓝 (p i)):=by
    apply EventuallyEq.tendsto
    filter_upwards [(carpetRoad I).cards n|>.growing i, (carpetRoad I).cards n|>.growing x] with m hm hn
    let N:=chain m;change Isles.reach ∘ port N ∘ i=i at hm; change Isles.reach ∘ port N ∘ x=x at hn
    unfold q p;by_cases hj:x=i; · simp [hj]
    rw [if_neg hj,if_neg]; intro ht; apply hj; rw [←hm,←hn,ht]
 have hh := tendsto_tsum_of_dominated_convergence (jewelled hv he f) hx (.of_forall (fun m i=> show ‖q m i‖≤‖F i f‖ from by unfold q; split<;>simp))
 simp only [p,tsum_ite_eq'] at hh
 unfold broom
 refine hh.congr' (Eventually.of_forall fun m=>tsum_congr fun i=>?_)
 by_cases hg:port (chain m) ∘ x=port (chain m) ∘ i
 · simp [q,hg]
   exact fun hn=>False.elim (hn hg)
 · simp [q,hg]
   exact fun hy=>False.elim (hg hy)
end YM.RG08.Hatch
