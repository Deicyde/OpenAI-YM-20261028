import YM.TraceExtension.Lamp.Cake

/-! # Regularity cost over compact index/sheet. No inverse-volume charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
    {I:Type}[Fintype I]
variable {o:Site f}
variable {W:Type*} {g:W→Side}{X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z] {F H:W→ X→Y}
structure Honor (F:W→ X→ Y)(m:ℕ): Prop where
    top:∃ C:ℝ,0≤ C ∧∀ w x,Allows m (F w) x C
lemma Honor.more (h:Honor F m)(hp:Honor H m): Honor (F+H) m:=by obtain ⟨C,hC,f⟩:=h.top; obtain ⟨D,hD,p⟩:=hp.top; exact ⟨C+D,add_nonneg hC hD,fun w i=>(f w i).add (p w i)⟩
lemma Honor.subc (h:Honor F m)(hp:Honor H m): Honor (F-H) m:=by
    have hh:Honor ((-1:ℝ) • H) m:=by
       obtain ⟨C,hC,H⟩:=hp.top; exact ⟨_,mul_nonneg (abs_nonneg _) hC,fun w i=> (H w i).smul (-1:ℝ)⟩
    rw[sub_eq_add_neg,show -H=(-1:ℝ) • H by rw[neg_smul,one_smul]]; exact h.more hh
lemma Honor.dam (h:Honor F m)(p:Z→L[ℝ] X) : Honor (fun w=>F w ∘ p) m:=by
    obtain ⟨C,hC,f⟩:= h.top; refine ⟨_,?_,fun i z=> pullAll (L:=p) (f i (p z)) (show ‖p‖ ≤ 1+‖p‖ by linarith) (le_add_of_nonneg_right (norm_nonneg _))⟩; positivity
lemma Honor.prod (L:Y→L[ℝ] Y→L[ℝ]Z)(h:Honor F m)(p: Honor H m): Honor (fun w x=> L (F w x) (H w x)) m:=by
    obtain ⟨C,hC,f⟩:=h.top;obtain ⟨D,hD,g⟩:=p.top; refine ⟨_,?_,fun w x=>Allows.bilinear L (f w x) (g w x) le_rfl⟩; positivity
lemma Honor.draw {V:Type*}(h:Honor F m)(e:V→W): Honor (F ∘ e) m:=by obtain ⟨C,hC,f⟩:=h.top; exact ⟨_,hC,fun w x=> f _ _⟩
lemma Honor.put (h:Honor F m)(Z:Y→L[ℝ]Z): Honor (fun w=> Z ∘ F w) m:=by obtain ⟨C,hC,f⟩:=h.top; exact ⟨_,mul_nonneg (norm_nonneg Z) hC, fun w x=>Allows.linear Z (f w x) le_rfl⟩
omit [Fintype I] in
lemma Honor.some {s:Finset I}{F:I→W→X→Y}(h:∀ i∈s,Honor (F i) m): Honor (fun w x=>∑ i∈s,F i w x) m:=by
    induction s using Finset.induction with
    | empty=>simp only [sum_empty]; exact ⟨0,le_rfl,fun w x=> allows_const _ (norm_zero.le)⟩
    | insert i s hi ih=> simp_rw [sum_insert hi]; exact ((h _ (mem_insert_self ..)).more (ih (fun i hi=>h i (mem_insert_of_mem hi))))
-- operations with moving arity but fees explicit
abbrev guardC (k:ℕ)(α:ℝ):= ((1+(2:ℝ)^k/(α/8))^k)*countCost (α/2) *cabD k
lemma guardC_n (h:0<α):0 ≤ guardC k α:=by unfold guardC;have hx:=count_pos (half_pos h);have hc:=cabD_n (k:=k);positivity
lemma AllowedP (F:Site f→ X × Track→ℂ)(h:0<a)(hp:0≤C)(hf:∀ i x, Allows k (F i) x (C*Decay a i o))(x:X × Track):
    Allows k (fun z:X × Track=>∑ i,F i z*mode (axes z.2) (lift (i-o))) x (guardC k a*C):=by
    let N:= ((1+(2:ℝ)^k/(a/8))^k); let B:ℝ:=C*N*cabD k; have hz:0≤B:=by unfold B N; have he:=cabD_n (k:=k); positivity
    have ht(i:Site f): Allows k (fun z:X×Track=> F i z* mode (axes z.2) (lift (i-o))) x (B*Decay (a/2) i o):=by
        let L:= ContinuousLinearMap.snd ℝ X Track
        have he:= pullAll (x:=x) (L:=L) (sea_mark (k:=k) i x.2 (show 0<a/8 by linarith) o) (show ‖L‖≤1 from L.opNorm_le_bound zero_le_one (fun x=> by rw[one_mul]; exact le_max_right ..)) le_rfl
        rw[one_pow, mul_one] at he; apply (cabin (hf i x) he).mono; apply le_of_eq
        unfold B; unfold Decay; rw [show -(a/2)*(separation i o:ℝ) = -a*(separation i o:ℝ)+4*(a/8)*separation i o by ring, Real.exp_add]; unfold N;ring
    apply Allows.mono (allows_sum (fun i (_:i∈(univ:Finset (Site f)))=> ht i)); rw[← mul_sum]; apply (mul_le_mul_of_nonneg_left (show ∑ i:Site f, Decay (a/2) i o≤countCost (a/2) from ?_) hz).trans_eq ?_
    · simp_rw [decay_comm _ _ o]; exact decay_count (half_pos h) _
    unfold B N guardC; ring

-- two-ended rooted insert W. analytic all Track variables
variable {V:WildM G f r l}
abbrev Backs (k:ℕ):=(TresF (Fin k) × Track) × Track
-- pair at tracks input/output independent, out dot uses plus (no conjugation)
def carb (o:Site f)(V:WildM G f r l)(i:Loc G r)(j:Loc G l)(p:Fin k→Loc G 1)(x:Backs k):=
    dotProduct (barca o x.2 i) ((art V k (fun w=> barca o (x.1.1 w) (p w))) *ᵥ (barca o x.1.2 j))
lemma carb_p (x:Backs k)(i:Loc G r)(j:Loc G l)(p:Fin k→ Loc G 1):
    carb o V i j p x=∑ u:Site f,(∑ v:Site f, molt o p (fun z=> V z (u,i) (v,j)) x.1.1 *mode (axes x.1.2) (lift (v-o)))* mode (axes x.2) (lift (u-o)):=by
    unfold carb; rw [barge_point o x.2,sum_dotProduct]; refine sum_congr rfl fun u _=>?_
    rw [barge_point o x.1.2,smul_dotProduct,Matrix.mulVec_sum,dotProduct_sum,smul_eq_mul,mul_comm]; congr 1; refine sum_congr rfl fun v _=>?_; rw [Matrix.mulVec_smul,dotProduct_smul,single_one_dotProduct, Matrix.mulVec_single_one, molt_be]; change mode _ _ * beat _ _ _ _ = ((beat _ _ _ _):ℂ)* _; exact mul_comm ..
lemma carb_a (i:Loc G r)(j:Loc G l)(p:Fin k→ Loc G 1)(ha:0<a)(hp:0 ≤ C)(h:PetW o V a C k)(x:Backs k):
    Allows m (carb o V i j p) x (guardC m a * (guardC m a* ramt m (Fin k) a*C)):=by
    let U(t:Site f)(x:TresF (Fin k) × Track):=∑ v:Site f,(molt o p (fun z=> V z (t,i) (v,j)) x.1)*mode (axes x.2) (lift (v-o))
    let F:=ramt m (Fin k) a; have hF: 0≤F:=ramt_n ha
    let S(t):=F*C* Decay a t o; have hS(t): 0≤S t:=mul_nonneg (mul_nonneg hF hp) (decay_pos .. |>.le)
    have ht(t:Site f)(x:TresF (Fin k) × Track): Allows m (U t) x (guardC m a * S t):=by
       apply AllowedP  (fun v x=> molt o p (fun z=> V z (t,i) (v,j)) x.1) ha (hS t) ?_ x
       intro v y; let L:= ContinuousLinearMap.fst ℝ (TresF (Fin k)) Track; have hv:= malt (x:=p) (h (t,i) (v,j)) ha (mul_nonneg (mul_nonneg hp (decay_pos .. |>.le)) (decay_pos .. |>.le)) y.1 m
       have hh:= pullAll (x:=y) (L:=L) hv (show ‖L‖ ≤ 1 from L.opNorm_le_bound zero_le_one (fun x=>by rw[one_mul]; exact le_max_left ..)) le_rfl; rw [one_pow,mul_one] at hh; apply hh.mono; dsimp only; unfold S F; rw[decay_comm a t o,decay_comm a v o]; linarith
    let L:= ContinuousLinearMap.fst ℝ (TresF (Fin k) × Track) Track; rw [show carb o V i j p=(fun z:Backs k=>∑ i,U i z.1*mode (axes z.2) (lift (i-o))) from funext fun x=> carb_p x i j p]
    have hQ:0≤guardC m a*F*C:=mul_nonneg (mul_nonneg (guardC_n ha) hF) hp
    apply AllowedP (fun t (x:Backs k)=> U t x.1) ha hQ ?_
    intro v y
    have hh:= pullAll (x:=y) (L:=L) (ht v y.1) (show ‖L‖ ≤ 1 from L.opNorm_le_bound zero_le_one (fun x=>by rw[one_mul];exact le_max_left ..)) le_rfl; rw [one_pow,mul_one] at hh; apply hh.mono; unfold S; linarith
end YM.Trace.Lamp
