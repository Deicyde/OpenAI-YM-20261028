import YM.RG08.Vale.Detail
/-!
# One-root pullback by rows with EXACT evaluation. Pol or Exponential reserves
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators
variable {I E H α β: Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E] [NormedAddCommGroup H][NormedSpace ℝ H]
variable {u m L : Side} {r k:ℕ} {w: Cover × α→ℝ} {v: Cover × β→ℝ} {p: Fin r→ℝ} {C K σ:ℝ}
variable {V:Rooted E α r}{U:Shale α r}
def brocade (w : Cover×α→ℝ) (b: Beads α r):=∏ i,w (b i)
lemma fineBro (hw:1≤w) : 1 ≤ brocade (r:=r) w := fun i=> one_le_prod fun _ _=> hw _
lemma fineObs (hw:0≤w) : 0 ≤ brocade (r:=r) w := fun i=> prod_nonneg fun _ _=> hw _
lemma bro_mint (w : ℕ)(x: Beads α r) : mint w x= brocade (fun i=> dime w i.1) x:=rfl
lemma bro_lit (w:ℝ)(x: Beads α r) : ling w x=brocade (fun i=>Real.exp (w*size i.1)) x := by unfold ling brocade girth; rw [Nat.cast_sum,mul_sum,Real.exp_sum]
-- nodes from any consumed TRUE cover array
def Paper (α β:Type) := Cover×α → Cover×β→ℝ
variable {P : Fin r→ Paper α β}
-- multilinear, evaluating not sorted costs. No path cutoff

def bulb (P : Fin r→ Paper α β) (i:Beads α r×Beads β r):= ∏ j,P j (i.1 j) (i.2 j)
def revolve (V:Rooted E α r)(P:Fin r→Paper α β) (i:Beads β r):=∑' j:Beads α r,sires V (bulb P) (j,i)
lemma bulb_price (he:Quire.Ink (brocade w) V C)(hp:0≤p)(h:∀ i j,Charge v (P i j) (p i*w j)):
    Quire.Ink (fun x:Beads α r×Beads β r=> brocade v x.2) (sires V (bulb P)) ((∏ i,p i)*C) := by
  refine he.sires_cost _ _ (prod_nonneg fun i _=>hp i) fun i=> ?_
  unfold Charge brocade bulb; simp_rw [norm_prod,← prod_mul_distrib]; exact budget_fin_prod _ (fun j=> h j _)
lemma revolves (he:Quire.Ink (brocade w) V C)(hp:0≤p)(h:∀ i j,Charge v (P i j) (p i*w j))(hv:1≤v):
    Quire.Ink (brocade v) (revolve V P) ((∏ i,p i)* C) := budget_projection _ (fun i=> zero_lt_one.trans_le (fineBro hv i)) (bulb_price he hp h)
lemma revolve_eval (he:Pens (sires V (bulb P))) (g:E→L[ℝ] H) : g ∘ revolve V P=revolve (g ∘ V) P := by
  funext x
  let B:=sires V (bulb P)
  have hp: Summable (fun i=> B (i,x)):= (he.of_norm).prod_symm.prod_factor x
  rw [comp_apply,revolve,g.map_tsum hp]; exact tsum_congr fun i=> map_smul ..
lemma revolve_s (Q : Paper α β)(h:Tidy V)(hh: Pens (sires V (bulb (fun _:Fin r=>Q)))) : Tidy (revolve V (fun _=>Q)) := by
  let F:=sires V (bulb (fun _:Fin r=>Q))
  refine ⟨?_,fun i b=>?_⟩
  · let g i := ∑' j: Beads α r, ‖F (j,i)‖
    have he := (summable_prod_of_nonneg (fun x : Beads β r×Beads α r=> norm_nonneg (F (x.2,x.1)))).mp hh.prod_symm
    exact Summable.of_nonneg_of_le (fun i=> norm_nonneg (revolve V _ i)) (fun i=> norm_tsum_le_tsum_norm (he.1 i)) he.2
  let e : Beads α r≃ Beads α r := Equiv.arrowCongr b.symm (Equiv.refl _)
  change (∑' k,F (k,i∘b))= ∑' k,F (k,i); rw [← e.tsum_eq]; apply tsum_congr; intro j
  change (∏ k,Q (j (b k)) (i (b k))) • V (j ∘ b)=_
  unfold F sires bulb; rw [h.woven]; exact congr_arg (· • V j) (Equiv.prod_comp b (fun k=> Q (j k) (i k)))
-- evaluating a polynomial test on output covariantly
lemma pocket (V:Shale α r) (P:Fin r→Paper α β)(x: Beads α r×Beads β r): sires V (bulb P) x=V x.1*(∏ i,P i (x.1 i) (x.2 i)):= mul_comm ..
def pursed (P:Paper α β)(f:Cover×β→ℝ) (x:Cover×α):ℝ:=∑' j,P x j*f j
lemma divulge (h:Quire.Ink (brocade w) U C)(g:∀ i j,Charge v (P i j) (p i*w j))(hp:0≤p)(hv:1≤v)
    (F:Fin r→ Cover×β→ℝ)(A:Fin r→ℝ)(hA:0≤A)(hy:∀ i x, ‖F i x‖ ≤ A i * v x):
    wallet (revolve U P) F = wallet U (fun i=> pursed (P i) (F i)) := by
  let Q (f:Fin r→Cover×β→ℝ) (b:Beads β r):= ∏ i,f i (b i)
  let G i := sires U (bulb P) i * Q F i.2
  have ha : Pens G := by
    have hz:= budget_scale (show 0 ≤ ∏ i,A i from prod_nonneg fun i _=> hA i) (bulb_price h hp g)
    apply (Summable.of_nonneg_of_le (fun i=>norm_nonneg (G i)) _ hz.2.1); intro i
    have he: ‖Q F i.2‖≤ (∏ j,A j)*brocade v i.2 := by unfold Q brocade; rw [norm_prod,← prod_mul_distrib]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> hy j _)
    unfold G; rw [norm_mul]; apply (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq; ring
  have hf (i:Fin r) (x : Cover×α): Summable (fun j=> P i x j * F i j):= by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun j=>?_) (budget_scale (hA i) (g i x)).2.1)
    rw [norm_mul]; refine (mul_le_mul_of_nonneg_left (hy i j) (norm_nonneg (P i x j))).trans_eq ?_; ring
  unfold wallet; change (∑' i,revolve U P i* Q F i)=_
  simp_rw [revolve,← tsum_mul_right]; rw [← (show Summable (fun i: Beads β r×Beads α r=> G (i.2,i.1)) from ha.of_norm.prod_symm).tsum_prod,show (∑' i:Beads β r×Beads α r,G (i.2,i.1))=_ from (Equiv.prodComm ..).tsum_eq G,ha.of_norm.tsum_prod]
  apply tsum_congr; intro i; unfold G Q; simp_rw [pocket,mul_assoc,← prod_mul_distrib]; rw [tsum_mul_left]; congr 1
  exact tsum_fin_prod _ (fun j=> hf j _)
end YM.RG08.Vale
