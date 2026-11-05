import YM.TraceExtension.Margin.Mallet
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
lemma rex(r:ℕ)(A:Frame G r)(s:Signed)(x:A.Coeff): Prism A (s,false) x=reflA A s x:=rfl
lemma mate(h:Cone F): Plot (Prism F) h.val=h.val:=by
    ext1 i;ext1 j; rw[plotEq]; let X(x:Motion):=(rent:ℝ) • h.val i j
    rw [sum_congr rfl (g:=X) (fun k _=> ?_),Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul,rent,mul_inv_cancel₀ (by positivity),one_smul];
    have hp(a): k.1.perm (prev k a)=a:= k.1.perm.apply_symm_apply a
    let u:=prev k i;let v:=prev k j
    have hz: Prism F k (h.val (prev k i) (prev k j))= reflA F k.1 (h.val u v):=by
        unfold Prism Motion.patch; simp only[LinearMap.coe_mk,AddHom.coe_mk]; split; swap; · rfl
        change star (F.act _ (h.val u v))=_; rw[← Motion.act_conj,show star (h.val u v)=_ from h.property.2.1 u v]; rfl
    rw[hz,h.property.2.2 k.1 u v,hp,hp]; unfold X; rw[smul_smul]; apply congr_arg (· • _); unfold hued; unfold u v; have hu:=sign_sq k.1 (prev k i); have hv:=sign_sq k.1 (prev k j);linear_combination (norm:=ring) rent*(hv+(sign k.1 (prev k j))^2*hu)
lemma lamp (w:Fin 4→ℝ): let T:Axis→Axis→F.Coeff:=fun i j=> F.coords (stress G w i j); Plot (Prism F) T=T:=by
    intro H; have ht:H∈ Cone F:= by
       refine ⟨fun i j=> congr_arg F.coords (stress_symm w i j), fun i j=> ?_, fun u i j=>?_⟩
       · let v:= H i j; change star v=v; have he :F.coords (realBar (F.coords.symm v))= star v:=funext fun i=> F.conj_basis v i; rw [← he,show F.coords.symm v=stress G w i j from F.coords.symm_apply_apply (stress G w i j),stress_real]
       exact (show F.act u.ortho (F.coords (stress G w i j))=(sign u i*sign u j) • H (u.perm i) (u.perm j) from by rw [F.act_coords,stress_tensor]; exact (F.coords.toLinearMap.restrictScalars ℝ).map_smul _ _)
    exact mate ⟨H,ht⟩
lemma ruby(n:Side)(G:Gauge)(x:ℝ)(T:Bool)(i j:Axis): Plint G n T i j 0= Toca (G:=G) T i j:=by unfold Plint; ext1 U; change Toca _ _ _ (Perfect.ride 0 U)=_; rw[show Perfect.ride 0 U=U from funext (fun e=>by simp[Perfect.ride,Lattice.translate])]
lemma astra(hG:G.Simple)(M:Bool)(hn:20*(high t+10)< n.val) (h:Club R t (Plint G n M))(hk:5 ≤ R.p.order)(he:Nonwrapping (tempQ t (n:=n)) 0) : Walt F Z H t (Plint G n M) (azure M):=by
    let V:=Plint G n M; let p:=cardX F H t V; let y:= azure M; let w: Fin 4→ℝ:= Fin.cons (α:=fun _=>ℝ) 0 y
    have ht(i j:Axis): F.coords.symm (p i j)=stress G w i j:=by
         let Y(a b c): loom G n:=⟨bornPair (G:=G) 0 a b c,(born_win ..).1⟩; let K:loom G n:=⟨V i j 0,(h.peek i j).silk⟩
         refine label_ext (fun J'=> ?_)
         let v:=Kits.ivy (0:Site n) (J' 0); let A:= ((1/2:ℝ) • anis v v); have hξ(J: loom G n): (↑(A J):ℂ)=(↑((1/2:ℝ)*sheen J.val v v):ℂ):= congr_arg _ (congr_arg ((1/2:ℝ)*·) (anum v v J))
         have hx(a b c:Axis): (↑(A (Y a b c)):ℂ)=Labels.read J' (pair G a c b c).val:=by
            rw [hξ,show sheen _ _ _=_ from (born_win (G:=G) (0:Site n) a b c).2 v v]; unfold v; rw[ivy_petal _ _ _ (by omega),ivy_petal _ _ _ (by omega),pair_value]; push_cast;ring
         have ht : JetTest H (0:Site n) (F.coords.symm (p i j)) (filmR K.val):= card_reads _ (Real_regular (h.peek i j).puff.regular) (by omega) he
         rw [vista4 K.property.1 hG ht, loom0 K,zero_add]; change (↑((1/2:ℝ)*sheen K.val v v):ℂ)=_; rw[← hξ K,stress_of]; have hh : K.val=Toca M i j:=ruby n G t M i j
         cases M <;> unfold Toca at hh <;> by_cases hg:i=j
         · rw[if_pos hg]; simp only[Bool.false_eq_true,↓reduceIte,hg] at hh; change _= Labels.read J' (( (0:ℝ) • _ + (0:ℝ) • _+(0:ℝ) • (_:Label G 4):Label G 4)).val; rw [show K=0 from Subtype.ext hh]; simp
         · simp only[Bool.false_eq_true,↓reduceIte,hg] at hh; rw[if_neg hg]; change _= Labels.read J' (( (1:ℝ) • ∑ a,pair G i a j a)).val; rw[one_smul]; let T:= fun a=>Y i j a; rw [show K=∑ a,T a from ?_,AddSubmonoidClass.coe_finsetSum,map_sum,map_sum, Complex.ofReal_sum];swap; · apply Subtype.ext; rw[hh,AddSubmonoidClass.coe_finsetSum]
           exact sum_congr rfl fun a _=> hx i j a
         · subst j; rw[if_pos rfl]; simp only[↓reduceIte] at hh; change _= Labels.read J' (((0:ℝ) • _+ (0:ℝ) • _+ (1/4:ℝ) • (_:Label G 4):Label G 4)).val; let T:= ∑ a:Axis,∑ b:Axis,Y a a b; have he : K=(1/4:ℝ) • T:=by apply Subtype.ext; simp_rw [hh,Submodule.coe_smul]; unfold T; simp only [AddSubmonoidClass.coe_finsetSum];rfl
           rw [zero_smul,zero_smul,zero_add,zero_add,he, map_smul,_root_.smul_eq_mul, Complex.ofReal_mul]; change _=Labels.read _ ((1/4:ℝ) • (∑ a:Axis,∑ b:Axis,pair G a b a b).val); rw [StressFlux.read_smul,Complex.real_smul]; unfold T; apply congr_arg; simp_rw[map_sum,AddSubmonoidClass.coe_finsetSum,map_sum,Complex.ofReal_sum,hx]
         simp only[↓reduceIte,hg] at hh; rw[if_neg hg,show K=0 from Subtype.ext hh,map_zero,Complex.ofReal_zero]; change _= Labels.read _ (((0:ℝ) • (_:Label G 4)).val);simp
    have hz:p=fun i j=> F.coords (stress G w i j):=by ext1 i;ext1 j; exact F.coords.symm.injective (by rw[ht,LinearEquiv.symm_apply_apply])
    refine scepter h hk he (by omega) hG ?_; rw[show cardX F H t (Plint G n M)=_ from hz,lamp]; intro i j;rfl
lemma Plint_sym(G:Gauge)(n:Side)(t:Bool)(i j:Axis): Plint G n t i j = Plint G n t j i:=by
    by_cases h:i=j; rw[h]; apply funext; intro x; unfold Plint; apply congr_arg; cases t; swap; · unfold Toca; simp [h, Ne.symm h]
    unfold Toca; simp only [Bool.false_eq_true, ↓reduceIte,h,Ne.symm h]; refine sum_congr rfl (fun k _=> ?_); funext U; exact real_inner_comm ..
lemma Plint_thin (G:Gauge)(n: Side): ∑ i:Axis, Plint G n false i i=0:= Finset.sum_eq_zero (fun i _=>funext fun x=>by unfold Plint Toca; simp;rfl)
end YM.Trace.Margin
