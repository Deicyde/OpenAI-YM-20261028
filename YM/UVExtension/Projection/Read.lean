import YM.UVExtension.Projection.Ink
import YM.UVExtension.Projection.Radial

/-! Linear observations of path bases, including fixed-mesh jets in arbitrary fields.
No run width lost in limits -- compute CLMs from (σ larger than) path width.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Exterior Precision Wilson Bloch Laurent Stationary Filter Function Finset
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {n : ℕ} [NeZero n] {m : Side} {I : Type} (e : Chip G n → I) {σ c : ℝ}
variable {X E : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma tsum_strike {P : ℕ → X → E} (h : ∀ x,Summable fun i => P i x) (hp : ∀ i,RLinear (P i)) : RLinear fun x=> ∑' i,P i x :=
    resists (U:=fun i x=> ∑ j ∈ range i,P j x) (fun _=> RLinear.sum _ P fun i _=> hp i) fun x=> (h x).hasSum.tendsto_sum_nat
lemma atom_coeff (i j) : RLinear fun x=> (issue (blend e σ c x) i).coeff j:= by
  simp_rw [blend_coeff]
  exact (RLinear.mk (lp.evalCLM ℝ (fun _ : I=>ℝ) 2 (e (i,j)))).mul _
lemma ink_poly (i) (p : Fin (n+1) → G.Color) : RLinear fun x=> (issue (blend e σ c x) i).poly p := by
  unfold Atom.poly; refine RLinear.sum _ _ fun u _ => ?_
  simp_rw [mul_comm _ (∏ i, p i (u i))]; exact (atom_coeff e i u).mul _
lemma uncut_linear (hp : 0<σ) (p : Config G m) : RLinear fun x=> uncut (issue (blend e σ c x)) p:= by
  unfold uncut; refine RLinear.sum _ _ fun i _=> tsum_strike (P:=fun j x=> (issue (blend e σ c x) j).unmasked p i) (fun x=> ?_) (fun j=> ?_)
  · have h:=budget_hyp e σ c x (τ:=σ/2) (by linarith)
    exact Summable.of_norm_bounded (h.2.1.mul_right (2^(n+1))) fun j=> ((Atom.unmasked_bound _ _ _)).trans <| mul_le_mul_of_nonneg_right (Atom.lower_budget _ _ (half_pos hp)) (by positivity)
  
  let a := issue (0 : Skin G n) j
  exact ink_poly e j (fun u => (a.leg u).atSite p i)
lemma signed_linear (hp : 0<σ) (p : Config G m) : RLinear fun x=> Patch.average fun i:Signed=> uncut (issue (blend e σ c x)) (pull i 0 p):= by
  unfold Patch.average; exact (RLinear.sum (Y:=ℝ) univ _ fun i _=> uncut_linear e hp (pull i 0 p)).mul _
lemma in_turn (hp : 0<σ) (j) (v : Fin j→Link G m) : RLinear fun x=> iteratedFDeriv ℝ j (turnSeries (issue (blend e σ c x))) 0 v :=
    RLinear.charge (F:=fun x=> turnSeries (issue (blend e σ c x))) (fun _=>turns_analytic _ (half_pos hp) (budget_hyp _ _ _ _ (half_lt_self hp))) (fun i=> signed_linear e hp (input _ _ i)) j v

def penny (p : ℕ→Atom G 2) (i : Fin 2 → PlaqAxes) (j : Ink G 2) (n : ℕ) :=
  if (fun a=> ((p n).leg a).plaq)=i then (p n).coeff j else 0
def lag (p : ℕ →Atom G 2) (l : Option Axis) (n : ℕ) : ℝ := l.elim 1 fun l=> (((((p n).leg 1).offset l-((p n).leg 0).offset l : ℤ)):ℝ)
lemma lag_bound (p : Skin G 1) (l : Option Axis) (n : ℕ) : |lag (issue p) l n| ≤ 1+furl G 1 n:= by
  unfold lag; rcases l with _|l
  · simp
  simp only [Option.elim,issue,artery,walkSlot_end,Fin.cons_zero]
  let v:= (carrierPath 1 n).2
  change |((v (0,l)- 0 : ℤ):ℝ)| ≤ _
  rw [Int.sub_zero, ← Int.cast_abs]; unfold furl; rw [issue,artery_length]; push_cast
  have he : (↑|v (0,l)|:ℝ) ≤ size v:=by
    have hh : (v (0,l)).natAbs ≤ size v := single_le_sum (f:=fun i=> (v i).natAbs) (fun i _=> Nat.zero_le _) (mem_univ _)
    rw [← Int.natCast_natAbs]; exact_mod_cast hh
  rw [Int.cast_abs] at he; apply he.trans; dsimp only [v]; linarith
lemma penny_linear (e : Chip G 1→I) (i j k l):RLinear fun x=> penny (issue (blend e σ c x)) i j k*lag (issue (blend e σ c x)) l k :=by
  let u : Skin G 1:=0
  by_cases h:(fun a=> ((issue u k).leg a).plaq)=i
  · simp only [penny,show ∀ x,(fun a=> ((issue (blend e σ c x) k).leg a).plaq)=i from fun _=> h,if_true]
    change RLinear fun x=> _* lag (issue u) l k; conv => arg 1; ext x; rw [mul_comm]; skip
    exact (atom_coeff e k j).mul _
  · have hk x : (fun a=> ((issue (blend e σ c x) k).leg a).plaq) ≠ i := h
    simp only [penny,hk,↓reduceIte,zero_mul]; exact RLinear.mk (0:Ortho I→L[ℝ] ℝ)

lemma penny_sum (e : Chip G 1→I) (h : 0<σ) (x : Ortho I) (i j l): Summable fun k=>
    penny (issue (blend e σ c x)) i j k*lag (issue (blend e σ c x)) l k :=by
  let w:= issue (blend e σ c x); let t:= σ/2; have ht : 0<t := half_pos h
  have hv:=budget_hyp e σ c x (half_lt_self h)
  apply Summable.of_norm_bounded (hv.2.1.mul_right (1+t⁻¹)) fun k=> ?_
  have hh : |penny w i j k| ≤ (w k).magnitude :=by
    unfold penny; split
    · exact single_le_sum (f:=fun t=> |(w k).coeff t|) (fun _ _=>abs_nonneg _) (mem_univ _)
    simp [Atom.magnitude]; positivity
  let a:=Real.exp (t*furl G 1 k)
  have hJ : 1 ≤ a := Real.one_le_exp (by positivity)
  have hl : (furl G 1 k:ℝ)≤ a*t⁻¹:=by rw [← div_eq_mul_inv,le_div_iff₀ ht,mul_comm]; unfold a; linarith [Real.add_one_le_exp (t*furl G 1 k)]
  rw [Real.norm_eq_abs,abs_mul]; change _ ≤ (w k).magnitude * a*(1+t⁻¹); rw [mul_assoc]
  exact mul_le_mul hh ((lag_bound _ _ _).trans (by linarith)) (abs_nonneg _) ((abs_nonneg _).trans hh)

lemma penny_price (e : Chip G 1→I) (h:0<σ) (i j l):RLinear fun x=> ∑' k,penny (issue (blend e σ c x)) i j k*lag (issue (blend e σ c x)) l k:= tsum_strike (P:=fun k x=> penny _ i j k*lag (issue (blend e σ c x)) l k) (fun x=>penny_sum e h x i j l) (fun i=>penny_linear e _ _ i _)
end YM.UVExtension.Projection
