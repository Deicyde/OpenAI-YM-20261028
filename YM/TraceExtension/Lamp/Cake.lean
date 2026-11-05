import YM.TraceExtension.Lamp.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
    {I:Type}[Fintype I]
omit [Fintype I] in
lemma axes_pick [DecidableEq I](i:I): Pi.single (M:=fun _=>ℂ) i 1=axes (bolt i):=by ext1 k;by_cases h:i=k<;> simp[bolt,axes,h]
lemma beat_single [DecidableEq I] (F: Corn I→ℝ) (x: Corn I) (t:Fin k→ I) : beat F x k (fun i=> (Pi.single (t i) 1))=((entry F x t:ℝ):ℂ):=by
    simp_rw [axes_pick]; exact beat_real F (fun i=> bolt (t i))
lemma barge_point {κ:Type} [Fintype κ][DecidableEq κ] (o:Site f)(x:Track)(a:κ):
    barca o x a=∑ i:Site f,(mode (axes x) (lift (i-o))) • (Pi.single (i,a) 1):=by
    ext1 ⟨i,j⟩; rw [Finset.sum_apply]; unfold barca
    by_cases h:j=a
    · subst j; simp [Pi.single_apply,Prod.ext_iff]
    simp [h]
lemma rings_set [DecidableEq I] {κ: Type}[Fintype κ] [DecidableEq κ](F:RecordM ℂ I (Co f κ))(a: I→ κ)(o:Site f)(x:I→Track):
    F (fun i=>barca o (x i) (a i))=∑ j:I→ Site f,(∏ i, mode (axes (x i)) (lift (j i-o)))* F (fun i=>Pi.single (j i,a i) 1):=by
    simp_rw [barge_point]; rw[F.map_sum]; simp only [← smul_eq_mul]; exact sum_congr rfl (fun j _=>F.map_smul_univ (fun i=>_) (fun i=>_))
-- variable momentum full spaces norm practical
abbrev TresF (I:Type) := I→ Track

def cabD (k:ℕ):ℝ:= 2^k*‖ContinuousLinearMap.mul ℝ ℂ‖
lemma cabD_n : 0≤cabD k:=mul_nonneg (by positivity) (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ))
lemma cabin {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{v:X}{F H:X→ℂ}(h: Allows k F v A)(hp:Allows k H v D): Allows k (fun z=> F z*H z) v (cabD k*A*D):= h.bilinear (f:=F) (g:=H) (ContinuousLinearMap.mul ℝ ℂ) hp le_rfl
private lemma phasesOut (k:ℕ) (ha:0<a)(s:Finset I) (x:TresF I) (o:Site f)(u:I→Site f):
    let K:= (1+(2:ℝ)^k/a)^k
    Allows k (fun z:TresF I=>∏ i∈s,mode (axes (z i)) (lift (u i-o))) x (((K*cabD k)^s.card)*Real.exp (4*a* (∑ i∈s, separation o (u i):ℕ))):=by
    let K:=(1+(2:ℝ)^k/a)^k
    induction s using Finset.induction with
    | empty => intro B; simp only [Finset.prod_empty,Finset.card_empty,sum_empty,pow_zero,Nat.cast_zero,mul_zero, Real.exp_zero,one_mul]; exact allows_const _ (norm_one.le)
    | insert i s hi h=>
       intro B; have H := sea_mark (k:=k) (u i) (x i) ha o
       let F:TresF I→L[ℝ] Track:= ContinuousLinearMap.proj i
       have he:= pullAll (x:=x) (L:=F) H (show ‖F‖ ≤ 1 from F.opNorm_le_bound zero_le_one (fun y=> by rw[one_mul];exact norm_le_pi_norm y i)) le_rfl
       rw [one_pow,mul_one] at he
       have ht:= cabin he h
       rw [separation_comm (u i)] at ht
       simp_rw [Finset.prod_insert hi]; rw [Finset.card_insert_of_notMem hi,Finset.sum_insert hi]; apply ht.mono; push_cast; unfold B; apply le_of_eq; rw [mul_add,Real.exp_add]; ring

def vase (o:Site f)(F:(I→Site f)→ℂ)(x:TresF I):ℂ:=∑ p:I→ Site f,(∏ i, mode (axes (x i)) (lift (p i-o)))*F p
def ramt (k:ℕ)(I:Type)[Fintype I](σ:ℝ):=
    (cabD k * (((1+(2:ℝ)^k/(σ/8))^k*cabD k)^(Fintype.card I)))*countCost (σ/2)^(Fintype.card I)
lemma ramt_n (ha:0<a):0 ≤ ramt k I a:=by unfold ramt; have ht:=count_pos (half_pos ha); have hf:=cabD_n (k:=k); positivity
lemma vase_pay (o:Site f)(F:(I→Site f)→ℂ)(σ:ℝ)(hσ:0<σ)(hc:0 ≤ C)(hF:∀ p, ‖F p‖≤ C*Real.exp (-σ* (∑ i,separation o (p i):ℕ)))(x:TresF I):
    Allows k (vase o F) x (ramt k I σ*C):=by
    let a:=σ/8; let K:= (1+(2:ℝ)^k/a)^k
    let B:=cabD k*(K*cabD k)^ (Fintype.card I)
    have hV: 4*a=σ/2:=by unfold a; ring
    have H(p:I→ Site f):Allows k (fun z:TresF I=> (∏ i,mode (axes (z i)) (lift (p i-o)))*F p) x ((B*C)* ∏ i, Decay (σ/2) o (p i)):=by
       refine (cabin (phasesOut k (show 0<a by unfold a; positivity) Finset.univ x o p) (allows_const x (hF p))).mono ?_
       have ht : (∏ i,Decay (σ/2) o (p i))=Real.exp ((-(σ/2))*(∑ i, separation o (p i):ℕ)):=by unfold Decay; rw [Nat.cast_sum, mul_sum, Real.exp_sum]
       rw[hV,Finset.card_univ,ht]; apply le_of_eq; let D:ℝ:= ↑(∑ i,separation o (p i))
       change cabD k*((K*cabD k)^_*Real.exp (σ/2*D))*(C*Real.exp (-σ*D))=B*C*Real.exp (_*D); rw [show -(σ/2)*D=σ/2*D+(-σ*D) by ring,Real.exp_add]; unfold B; ring
    apply Allows.mono (allows_sum (fun i (_:i∈(univ:Finset (I→ Site f)))=> H i))
    have he:0≤ K:=by unfold K a; positivity
    rw [← Finset.mul_sum]; refine le_trans (b:= B*C*∏ _i:I,countCost (σ/2)) (mul_le_mul_of_nonneg_left ?_ (show 0 ≤ B*C from mul_nonneg (by unfold B; have hx:=cabD_n (k:=k); positivity) hc)) ?_
    · rw [← Fintype.prod_sum (fun _ i=> Decay (σ/2) o i)]; exact prod_le_prod (fun i _=>sum_nonneg fun j _=>(decay_pos ..).le) (fun i _=> decay_count (half_pos hσ) o)
    apply le_of_eq; simp [ramt]; unfold B K a; ring
-- charge and shrink hull
abbrev molt (o:Site f)(a:Fin k→Loc G 1)(F: Link G f→ℝ)(z:TresF (Fin k)):= vase o (fun x:Fin k→ Site f=>↑(entry F 0 (fun i=>(x i,a i)))) z
lemma molt_be (o:Site f)(a:Fin k→Loc G 1)(F:Link G f→ℝ)(z:TresF (Fin k)): molt o a F z = beat F 0 k (fun i=> barca o (z i) (a i)):=by
    unfold molt vase; rw[rings_set]; simp_rw[show ∀ j : Fin k → Site f, beat F 0 k (fun i=> Pi.single (j i,a i) 1)=_ from fun j=> beat_single F 0 (fun i=> (j i,a i))]
    congr 2; apply Subsingleton.elim
lemma malt {F:Link G f→ℝ}{o:Site f}(h:Pet Prod.fst o F α C k)(ha:0<α)(hc:0 ≤ C)(x:Fin k→Loc G 1)(z:TresF (Fin k)) (j:ℕ): Allows j (molt o x F) z (ramt j (Fin k) α*C):=by
    refine vase_pay _ _ α ha hc ?_ z; intro p; rw[Complex.norm_real]; exact h.2 k le_rfl _
end YM.Trace.Lamp
