import YM.UVExtension.Projection.Space
import YM.Next.STATIONARY.Lift.Ward

/-! Fixed countable alphabet actually used by stationary construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Exterior Precision Wilson Bloch Laurent Stationary Filter Function Finset
open scoped Classical Topology BigOperators InnerProductSpace
variable {G : Gauge}
abbrev Chip (G : Gauge) (n : ℕ) := ℕ × Ink G (n+1)
variable {I : Type} {n : ℕ} [NeZero n]

def furl (G : Gauge) (n : ℕ) [NeZero n] (i : ℕ) := (issue (0 : Skin G n) i).length
def grain (G : Gauge) (n : ℕ) [NeZero n] (σ : ℝ) (i : ℕ) := Real.exp (σ*furl G n i)

theorem longWay (P : Skin G n) (i : ℕ) : (issue P i).length=furl G n i := rfl

theorem grainSum {σ : ℝ} (h : 0 < σ) : RG.SumBudget (grain G n (-σ)) ((Real.exp (-σ*(4*(n+1):ℕ)) * (2*((1+σ)/σ))^(Fintype.card (Keys n))) * Fintype.card (CurRun (n+1))) := by
  let e:=Real.exp (-σ*↑(4*(n+1):ℕ))
  let P:= (2*((1+σ)/σ))^(Fintype.card (Keys n))
  have hp:= Width.compactPay (α:=Keys n) σ h
  let f:= fun x : CurRun (n+1)× Shift (Keys n) => e* Real.exp (-σ*size x.2)
  have hx : grain G n (-σ)=f ∘ carrierPath n := by
    funext i; unfold grain furl issue; rw [artery_length,Nat.cast_add, mul_add, Real.exp_add]; exact mul_comm ..
  rw [hx]; refine budget_copy (carrierPath n) ?_
  rw [show e*P*Fintype.card (CurRun (n+1))=∑ _ : CurRun (n+1),e*P by simp; ring]
  exact budget_prod_finite (A:=fun _=> e*P) fun _=> ⟨fun i=>mul_nonneg (Real.exp_pos _).le (hp.1 i),(hp.2.1.mul_left _),by unfold f; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hp.2.2 (Real.exp_pos _).le⟩

def coverBudget (G : Gauge) (n : ℕ) [NeZero n] (u : ℝ) := 1+(Fintype.card (Ink G (n+1)):ℝ)* ∑' i, grain G n (-u) i

lemma cover_one (u : ℝ) : 1 ≤ coverBudget G n u := by
  have hg i : 0 ≤ grain G n (-u) i := (Real.exp_pos _).le
  exact le_add_of_nonneg_right (mul_nonneg (by positivity) (tsum_nonneg hg))

def blend (e : Chip G n → I) (σ c : ℝ) (x : Ortho I) : Skin G n := fun i j k=>
    let u:= (carrierPath n).symm (i,k); c*grain G n (-σ) u * x (e (u,j))

theorem blend_coeff (e : Chip G n → I) (σ c : ℝ) (x : Ortho I) (i j) :
    (issue (blend e σ c x) i).coeff j= c * grain G n (-σ) i * x (e (i,j)) := by simp [blend, issue,artery]

theorem grain_meet (σ τ : ℝ) (i : ℕ) : grain G n σ i * grain G n τ i=grain G n (σ+τ) i:= by simp [grain, ← Real.exp_add,add_mul]

theorem strobe (e : Chip G n → I) (σ c : ℝ) (x : Ortho I) (b : ℝ) (he : ‖x‖≤b) (τ : ℝ) (i : ℕ):
    (issue (blend e σ c x) i).budget τ ≤ |c| *b*Fintype.card (Ink G (n+1))* grain G n (-(σ-τ)) i := by
  unfold Atom.budget; rw [longWay]
  let d:=grain G n (-σ) i
  have hd : 0≤ d := (Real.exp_pos _).le
  have hb : 0 ≤ b := (norm_nonneg _).trans he
  calc
    _ ≤ (∑ _ : Ink G (n+1),|c| *d*b)*grain G n τ i := by
      refine mul_le_mul_of_nonneg_right (sum_le_sum fun j _=> ?_) (Real.exp_pos _).le
      rw [blend_coeff,abs_mul,abs_mul,abs_of_nonneg hd]; exact mul_le_mul_of_nonneg_left ((lp.norm_apply_le_norm (by norm_num) _ _).trans he) (mul_nonneg (by positivity) hd)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]; rw [show -(σ-τ)= -σ+τ by ring, ← grain_meet]; unfold d; ring
                              -- robust below

theorem budget_hyp (e : Chip G n → I) (σ c : ℝ) (x : Ortho I) {τ : ℝ} (h : τ < σ):
    SumBudget (fun i=> (issue (blend e σ c x) i).budget τ) (|c| * ‖x‖ * coverBudget G n (σ-τ)) := by
  have hs := (grainSum (G:=G) (n:=n) (sub_pos.mpr h)).2.1.mul_left (|c| * ‖x‖ * (Fintype.card (Ink G (n+1)):ℝ))
  have hu i := strobe e σ c x ‖x‖ le_rfl τ i
  have hp i : 0 ≤ (issue (blend e σ c x) i).budget τ := by unfold Atom.budget Atom.magnitude; positivity
  have hk := hs.of_nonneg_of_le hp hu
  refine ⟨hp,hk,(Summable.tsum_le_tsum hu hk hs).trans ?_⟩
  rw [tsum_mul_left,coverBudget]; have hw : 0 ≤ |c| *‖x‖ := by positivity
  linarith

def unroll (f : Skin G n) (σ c : ℝ) : Chip G n → ℝ := fun p=> (issue f p.1).coeff p.2 * grain G n σ p.1 / c
lemma unroll_price {σ c B : ℝ} (hf : 0 < c) (f : Skin G n) (he : SumBudget (fun i=> (issue f i).budget σ) B) :
    SumBudget (fun i=> ‖unroll f σ c i‖) (B/c) := by
  have hu i : ∑ j : Ink G (n+1), ‖unroll f σ c (i,j)‖ =(issue f i).budget σ / c:= by
    simp only [unroll,Atom.budget,Atom.magnitude,norm_div, norm_mul, ← sum_div, ← sum_mul, Real.norm_eq_abs,longWay,abs_of_pos hf,grain,abs_of_pos (Real.exp_pos _)]
  have hx := he.2.1.div_const c
  have hh : Summable (fun i=> ‖unroll f σ c i‖) := by
    rw [summable_prod_of_nonneg (fun _=> norm_nonneg _)]
    refine ⟨fun _=> Summable.of_finite,?_⟩; simp_rw [tsum_fintype,hu]; exact hx
  refine ⟨fun i=> norm_nonneg _,hh,?_⟩
  rw [hh.tsum_prod]; simp_rw [tsum_fintype,hu,tsum_div_const]; exact div_le_div_of_nonneg_right he.2.2 hf.le

lemma fitting (e : Chip G n→I) (he : Injective e) (σ c : ℝ) (hc : 0<c) (P : Skin G n) (B : ℝ) (hp : SumBudget (fun i=> (issue P i).budget σ) B) :
    ∃ x : Ortho I, blend e σ c x=P ∧ (∀ i,i ∉ Set.range e → x i=0) ∧ ‖x‖ ≤ B/c := by
  let b:=B/c
  let v := unroll P σ c
  let f := Function.extend e v 0
  have hx i (h:i∉Set.range e): f i=0 := Function.extend_apply' _ _ _ h
  have hv : (fun i:I => ‖f i‖)∘ e=fun i=> ‖unroll P σ c i‖:= funext fun i => by simp [f,v,he]
  have ht : SumBudget (fun i=> ‖f i‖) b:= by
    have hQ:=unroll_price hc P hp; rw [← hv] at hQ
    have hk i (h:i∉Set.range e): ‖f i‖=0 := by rw [hx i h,norm_zero]
    have hz := (Function.Injective.hasSum_iff he hk).1 hQ.2.1.hasSum
    exact ⟨fun _=> norm_nonneg _,hz.summable,hz.tsum_eq.trans_le hQ.2.2⟩
  have hi i: ‖f i‖ ≤ b:= (ht.2.1.le_tsum i (fun i _=>ht.1 i)).trans ht.2.2
  have hh : 0≤ b := (tsum_nonneg ht.1).trans ht.2.2
  have hg i : ‖f i‖^(2:ENNReal).toReal ≤ ‖f i‖*b := by norm_num [sq]; simpa [← sq] using mul_le_mul_of_nonneg_left (hi i) (norm_nonneg (f i))
  have hK:= Summable.of_nonneg_of_le (fun i=> Real.rpow_nonneg (norm_nonneg _) _) hg (ht.2.1.mul_right b)
  let x : Ortho I:= ⟨(f : PreLp (fun _ : I=>ℝ)), memℓp_gen hK⟩
  refine ⟨x,?_,hx,lp.norm_le_of_tsum_le (by norm_num) hh ((hK.tsum_le_tsum hg (ht.2.1.mul_right b)).trans ?_)⟩
  · have hz i : x (e i)=v i := by change Function.extend _ _ _ _=_; simp [he,v]
    funext i j k; unfold blend; simp_rw [hz]; simp only [v, unroll, grain, issue, artery, Equiv.apply_symm_apply, neg_mul,Real.exp_neg]; field_simp
  rw [tsum_mul_right]; norm_num [sq]; exact mul_le_mul_of_nonneg_right ht.2.2 hh
end YM.UVExtension.Projection
