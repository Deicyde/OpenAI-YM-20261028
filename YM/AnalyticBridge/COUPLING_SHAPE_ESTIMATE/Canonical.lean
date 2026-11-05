import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Existing

/-!
# Affine responses of all output path pairs sum to the claimed metric.

No claim when attempting just the nonwrapping subseries. Charge every clover,
even for row terms masked elsewhere. `narrow` is the argument with the clovers
under their common smaller support; this mask move will be paid in the gas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.CouplingShape
open Function Lattice Wilson RG Precision Finset Work
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace Classical
variable {G : Gauge} {n : Side} {σ C Λ : ℝ} {P : PathData G} {p : Clip} {b : BudgetPoint}

def squareNorm (A : Flux G) := ∑ i, ⟪A i,A i⟫_ℝ / 2

def curlValue (o : Site n) (U : Config G n) := squareNorm (needles o U)

def short (b : BudgetPoint) (U : Config G n) (o : Site n) := masked b.threshold (ringlet o) (curlValue o) U

private def mark (P : PathData G) (i : PlaqAxes) (U : Flux G) := ∑ j, P.symbol0 i j • U j
private def projected (P : PathData G) (i : PlaqAxes) (U : Flux G) (j : ℕ) := earnCoeff P i j • U (first P i j).plaq

private lemma column (hd : P.Bounds p σ C Λ) (i : PlaqAxes) (U : Flux G) :
    Summable (projected P i U) ∧ mark P i U=∑' j, projected P i U j := by
  let M (l : PlaqAxes) j := (if (P.row i j).2.plaq=l then (P.row i j).1 else 0)
  have he : projected P i U=fun j => ∑ l, M l j • U l := by funext j; simp only [M,ite_smul,zero_smul,sum_ite_eq,mem_univ,if_true]; rfl
  have hh l : Summable (fun j => M l j • U l) := by
    let L := (ContinuousLinearMap.id ℝ ℝ).smulRight (U l)
    exact (L.hasSum (hd.symTerms i l).hasSum).summable
  rw [he]; constructor
  · exact summable_sum fun i _ => hh i
  unfold mark; rw [Summable.tsum_finsetSum (fun i _ => hh i)]
  refine sum_congr rfl fun j _ => ?_; let L := (ContinuousLinearMap.id ℝ ℝ).smulRight (U j)
  exact L.map_tsum (hd.symTerms i j)

/-- The zero-symbol clause on `PathData.Bounds` for the *same* paths
installed in the step; checked in ℝ with physical color. -/
private lemma metric (hd : P.Bounds p σ C Λ) (U : Flux G) :
    p.direct*squareNorm U+squareNorm (fun i => mark P i U) = squareNorm U := by
  suffices h : ∑ i, ⟪mark P i U, mark P i U⟫_ℝ = ∑ i,(1-p.direct)* ⟪U i,U i⟫_ℝ by unfold squareNorm; rw [← sum_div,← sum_div,h, ← mul_sum]; ring
  have he i : ⟪mark P i U,mark P i U⟫_ℝ=∑ j,∑ k, P.symbol0 i j*P.symbol0 i k* ⟪U j,U k⟫_ℝ := by
    unfold mark; simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,mul_assoc]
    apply sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; rw [real_inner_comm (U k)]
  simp_rw [he]; rw [sum_comm]; refine sum_congr rfl fun j _ => ?_; rw [sum_comm]
  simp_rw [← sum_mul]; rw [sum_eq_single j]
  · have hh := hd.metric j j; simp only [if_true] at hh; congr 1; linarith
  · intro k _ hv
    have hh := hd.metric j k; rw [if_neg hv.symm,if_neg hv.symm,zero_add] at hh; rw [hh,zero_mul]
  simp

private lemma rawAccount (hd : P.Bounds p σ C Λ) (U : Config G n) (h : Summable fun i => response P p i U) :
    ∑' i,response P p i U=weight* curlValue 0 U := by
  let u := needles 0 U; let F := fun i => ⟪mark P i u,mark P i u⟫_ℝ
  have h₁ i : (∑' a:ℕ,∑' b:ℕ,response P p (i,Sum.inr (a,b)) U)=weight/2*F i := by
    have he (a b:ℕ) : response P p (i,Sum.inr (a,b)) U=weight/2* ⟪projected P i u a,projected P i u b⟫_ℝ := by
      simp only [Sum.elim_inr,response,projected,u,copper,mul_assoc, real_inner_smul_left,real_inner_smul_right]; ring
    simp_rw [he,tsum_mul_left]
    obtain ⟨hh,hx⟩:=column hd i u; rw [together hh hh,← hx]
  rw [fixedStep (fun i=>response P p i U) h]; simp_rw [h₁]
  rw [sum_add_distrib,←mul_sum]; dsimp only [response,Sum.elim]; rw [← Finset.mul_sum]
  have hx := metric hd u
  unfold squareNorm at hx; rw [←sum_div,←sum_div] at hx
  change weight*p.direct/2*(∑ i,⟪u i,u i⟫_ℝ)+weight/2*(∑ i,F i)=weight * squareNorm u
  nth_rw 1 [squareNorm]; rw [← sum_div,← hx]; unfold F; ring

private lemma conserving (s : Signed) (u : Flux G) : squareNorm (swivels G s u)=squareNorm u := by
  unfold squareNorm; refine sum_equiv (PlaqAxes.transform s) (by simp) (fun i _ => ?_)
  let v := u (PlaqAxes.transform s i)
  change ⟪parityPrice s i • v,parityPrice s i • v⟫_ℝ / 2= _
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [norm_smul, Real.norm_eq_abs, parityPrice_abs,one_mul]; rfl

lemma clover_share (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) (U : Config G n) (x : Site n) :
    ∑ s : Signed, (∑' i : Sequence, narrow P p b (x,s,i) U) = short b U x := by
  have he (s : Signed) : (∑' i : Sequence, narrow P p b (x,s,i) U)=weight*short b U x := by
    by_cases ht : Healthy b.threshold (ringlet x) U
    · have hh (i : Sequence) : narrow P p b (x,s,i) U=response P p i (pull s x U) := masked_eq _ _ _ _ ht
      simp_rw [hh]; rw [rawAccount hd,short,masked_eq _ _ _ _ ht]
      · unfold curlValue; rw [spins,conserving]; simp [affine]
      have hz := (((narrow_cost hd hg).summable U).prod_factor x).prod_factor s; exact hz.congr hh
    have hp (i : Sequence) : narrow P p b (x,s,i) U=0 := masked_ne _ _ _ _ ht
    simp_rw [hp]; rw [short,masked_ne _ _ _ _ ht, mul_zero,tsum_zero]
  simp only [he,sum_const,card_univ,nsmul_eq_mul,← mul_assoc,weight_count,one_mul]

lemma whittle (hd : P.Bounds p σ C Λ) (hg : Grace p b σ) (U : Config G n) :
    (∑' i, narrow P p b i U)=∑ x, short b U x := by
  rw [tally ((narrow_cost hd hg).summable U)]; simp_rw [clover_share hd hg]
end YM.AnalyticBridge.CouplingShape
