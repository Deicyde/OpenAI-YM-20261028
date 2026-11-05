import YM.MultipleContact.Multi.Receipt

/-! Finite multibranch comparison modulo readings, retaining cancellation. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.MultipleContact.Drama
open Function Filter MeasureTheory Table Extraction Set Script Flight Scene Ward
open scoped BigOperators Classical ComplexOrder
variable {I:Type*}[Fintype I][DecidableEq I]{n d:I→ℕ}
variable {G:Gauge}{L:Register G}(S:Table L)
local notation "Gram" => Grammar (Alpha S)
def Indist (x y:Grammar (Alpha S)):=∀ f:Gram,evaluation S (x*f)=evaluation S (y*f)
lemma reading_eq {x y:Gram}(h:Indist S x y):evaluation S x=evaluation S y:=by simpa using (h 1)
variable (hs:S.Symmetric)
omit hs in
lemma prod_indist {q:Finset I}{x y:I→ Grammar (Alpha S)}(h:∀i∈q,Indist S (x i) (y i)): Indist S (q.prod x) (q.prod y):=by
       induction q using Finset.induction_on with
       | empty=> intro; rfl
       | @insert i q hi ih=> have hq:= ih (fun i hh=>h _ (Finset.mem_insert_of_mem hh)); intro f
                             rw [Finset.prod_insert hi,Finset.prod_insert hi,mul_assoc,mul_assoc,h i (Finset.mem_insert_self ..),← mul_assoc,mul_comm (y i),mul_assoc,hq (y i * f),← mul_assoc,mul_comm (q.prod y)]; rw [mul_assoc]
include hs
private lemma cancel_here (h:ℕ)(w:ℂ){z:E4}(x:Gram)(K D B:S.Field h) {A:ℂ} (hB : A • B=K-D):Indist S (w • x-insertion S z D) ((w • x-insertion S z K) + A • insertion S z B):=by
              intro f; obtain ⟨g,hg⟩:=Scene.inline S (d:=h) hs z f
              unfold insertion; simp only [sub_mul,add_mul,smul_mul_assoc,map_add,map_sub,map_smul,hg,←g.map_smul,hB]; abel
private def replace (g:I→Mode)(b:I→Fin 2)(i:I):Mode := if b i = 0 then g i else if g i = Mode.signed then Mode.fused else g i
private def scalarCost (K:ℝ)(D:I→ℝ)(g:I→Mode)(b:I→Fin 2)(i:I):ℝ:=if b i=0 then 1 else if g i=Mode.signed then K*D i else 0
def changedCost(D P:I→ℝ)(g:I→Mode)(t:I→Mode)(i:I):ℝ:=if t i=g i then P i else D i
variable (K:ℝ)(D:I→ℝ)(g:I→Mode) (z:I→E4)(x:I→ Grammar (Alpha S))(w:I→ℝ)(v m:∀i,S.Field (d i)) (hv:∀ i,g i ≠ Mode.signed → v i=m i)

/-- A profile `r` can switch any subtracted clusters to inserted unit fields.
`u i`, `m i`, `v i` parameterize same center.
-/ -- fix
def body (g:Mode)(w:ℝ)(x:Gram){d:ℕ}(v:S.Field d)(z:E4):Gram:=match g with
 | .signed=> ((w:ℝ):ℂ) • x-insertion S z v
 | .raw=>x
 | .fused=> insertion S z v
variable (hK:0<K)(hD:∀i,0<D i)(hbound:∀i,g i=Mode.signed→‖v i-m i‖≤K*D i)(P:I→ℝ) (hP:∀ i,0≤P i)
include hK hD hbound hP hs hv
set_option maxRecDepth 100000
theorem adjust
   (reading : ∀ r:I→Mode, (∀i, r i=g i ∨ (g i=Mode.signed ∧ r i=Mode.fused))→ ∀ u:∀i,S.Field (d i),(∀i,r i≠ g i→‖u i‖≤1) →
     ‖evaluation S (∏ i:I,body S (r i) (w i) (x i) (if r i=g i then m i else u i) (z i))‖≤ ∏ i, changedCost P D g r i):
     ‖evaluation S (∏i:I,body S (g i) (w i) (x i) (v i) (z i))‖ ≤ (Fintype.card (I→Fin 2):ℝ) * (∏ i:I,max 1 (K*P i)) * (∏ i:I,D i):=by
       let B i:= ((K*D i)⁻¹:ℝ) • (m i-v i); let Z i (b:Fin 2):=if b=0 then g i else if g i=Mode.signed then Mode.fused else g i
       let c i (b:Fin 2):ℝ:=if b=0 then 1 else if g i=Mode.signed then K*D i else 0
       have hb(i): 0<K*D i:=mul_pos hK (hD i); have hc(i): ((K*D i:ℝ):ℂ) • B i=m i-v i:= by unfold B; change ((K*D i):ℝ) • (((K*D i)⁻¹:ℝ) • (m i-v i))=m i-v i; rw [smul_smul,mul_inv_cancel₀ (hb i).ne',one_smul]
       let term(i)(b:Fin 2):= let p:=if Z i b=g i then m i else B i; body S (Z i b) (w i) (x i) p (z i)
       let load(i b):= (↑(c i b):ℂ) • term i b
       have hl(i:I):Indist S (body S (g i) (w i) (x i) (v i) (z i)) (∑b,load i b):=by
          rw [Fin.sum_univ_two]
          by_cases h:g i=Mode.signed
          · simpa only [body,load,c,term,Z,h,if_neg (show (1:Fin 2)≠0 by decide),ite_true,Complex.ofReal_one,one_smul, if_neg (show Mode.fused≠Mode.signed by decide)] using (cancel_here S hs (d i) (w i) (x i) (m i) (v i) (B i) (z:=z i) (hc i))
          simpa [load,c,Z,term,h,hv i h,Indist] using! (show ∀t:Gram,evaluation S (body S (g i) (w i) (x i) (v i) (z i)*t)=evaluation S (body S (g i) (w i) (x i) (v i) (z i)*t) from fun _=>rfl)
       rw [reading_eq S (prod_indist S (q:=Finset.univ) (fun i _=>hl i)), Fintype.prod_sum, map_sum]
       let C:= (∏ i:I,max 1 (K*P i)) * (∏ i:I,D i)
       have ht(b:I→Fin 2): ‖evaluation S (∏ i:I,load i (b i))‖≤C:=by
          have hc'(i): 0≤c i (b i):=by unfold c; split_ifs <;> first | exact (hb _).le | positivity
          let r(i):=Z i (b i); let cost:= changedCost P D g r
          have hw i : 0≤cost i:= by unfold cost changedCost; split; exact hD i|>.le; exact hP i
          have hy i: c i (b i)*cost i ≤ (max 1 (K*P i))*(D i):=by
              by_cases he:r i=g i
              · change c i (b i) * changedCost P D g r i ≤ _; rw [changedCost,if_pos he]
                by_cases hh:g i=Mode.signed ∧ b i ≠ 0
                · rw [show r i = Mode.fused from by simp [r,Z,hh.1,hh.2]] at he; cases (hh.1.symm.trans he.symm) -- orientation
                exact mul_le_mul_of_nonneg_right ((show c i (b i)≤1 from (by unfold c;split_ifs <;> aesop)).trans (le_max_left ..)) (hD i).le
              obtain ⟨hv,h⟩:=show b i ≠ 0 ∧ g i=Mode.signed from ⟨fun h=>he (by simp [r,Z,h]),by_contradiction fun h=>he (by simp [r,Z,h])⟩
              change c i _ * changedCost P D g r i ≤ _; rw [changedCost,if_neg he]; unfold c;rw [if_neg hv,if_pos h]
              have heq := mul_le_mul_of_nonneg_right (le_max_right 1 (K*P i)) (hD i).le; rw [mul_right_comm]; exact heq
          have hProd: (∏ i,c i (b i)*cost i) ≤ C:=by
               apply (Finset.prod_le_prod (fun i _=>mul_nonneg (hc' i) (hw i)) (fun i _=>hy i)).trans_eq; exact Finset.prod_mul_distrib
          rw [Finset.prod_mul_distrib] at hProd
          unfold load; rw [Finset.prod_smul,map_smul,norm_smul]
          simp_rw [← Complex.ofReal_prod] -- rewrite? names
          rw [show ‖(↑((∏ i:I,c i (b i):ℝ)):ℂ)‖ = ∏ i,c i (b i) from (by rw [Complex.norm_real,Real.norm_of_nonneg (Finset.prod_nonneg (fun i _=>hc' i))])]
          refine (hProd.trans' (mul_le_mul_of_nonneg_left (reading r ?_ B ?_) (Finset.prod_nonneg (fun i _=>hc' i)))) -- need prod_mul_distrib
          · intro i; unfold r Z; split_ifs with ht' hv <;> simp [ht', hv]
          intro i he; unfold B; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (hb i).le)]
          apply (inv_mul_le_iff₀ (hb i)|>.2); rw [mul_one,norm_sub_rev]; exact hbound i (by_contradiction fun h=>he (by simp [r,Z,h]))
       exact ((norm_sum_le ..).trans (Finset.sum_le_sum fun b _=>ht b)).trans_eq (by unfold C; simp [nsmul_eq_mul,mul_assoc])

open Scene Script
end YM.MultipleContact.Drama
#print axioms YM.MultipleContact.Drama.adjust
