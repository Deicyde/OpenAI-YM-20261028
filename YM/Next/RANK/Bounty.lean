import YM.Next.RANK.Alarm

/-!
# All marks paid from the same suppression
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ : Type}
variable {ζ : V→Site n} {t : ℝ} {q : BudgetPoint}
variable (A : ι→ Lifted G ζ t) (B : κ→ Strike G ζ q.threshold) (X : Siren G n q.threshold)

-- express bills at threshold q, permit any root exponent charged according to upstream estimates
variable {r : V→ℝ}

def Taxed (i : Strike G ζ q.threshold) (r : V→ℝ) (a : ℝ) := 0 ≤ a ∧ ∀ U, Poly.toll r i.fires * ‖i.value U‖≤a

def heavy (i : Lifted G ζ t) (r : V→ℝ) (a : ℝ) := 0 ≤ a ∧ ∀ U, Poly.toll r i.fires * ‖i.value U‖≤a

def taxable (r : V→ℝ) (e u : ℝ) := ∃ P : κ→ℝ, (∀ i,Taxed (B i) r (P i)) ∧ Incur (fun i=> (B i).extent) q.B P e u
-- includes halo for licenses, not just base extent

def Burden (A : ι→ Lifted G ζ t) (q : BudgetPoint) (r : V→ℝ) (e u : ℝ) := ∃ P : ι → ℝ,(∀ i,heavy (A i) r (P i)) ∧ Incur (fun i=> halo 8 (A i).extent) q.B P e u

-- birth cost in retaining; X var type Slot, consumes certificate β

def fertile (v d e : ℝ) := ∃ f : Site n→ℝ, (∀ y, 0≤f y ∧ ∀ U, |X.value y U| ≤ Real.exp (-v)*f y) ∧ Incur X.chamber q.B f d e

def fragrant (u : ℝ) (i : Branch ι κ n) := Sum.elim (fun _=> (0:ℝ)) (fun _=> -u) i
omit [DecidableEq V] [Fintype V] in
lemma gifts (i : Finset (Branch ι κ n)) (u : ℝ) : ∑ j∈i, fragrant u j= -u* i.toRight.card := by
  rw [sum_sum_eq_sum_toLeft_add_sum_toRight]; simp [fragrant,mul_comm]

lemma cap (m : Branch ι κ n → ℝ) (h : ∀ i,0≤m i) (u : ℝ) (hu : 0≤u) (hp : ∀ U i,
      Poly.price r (fuel A B X i U) ≤ Real.exp (fragrant u i)*m i) (i : Domino A B X) (hr : ∀ i, 0<r i) :
    heavy (teat A B X i) r (Real.exp (-u)*∏ a∈i.val,m a) := by
  have hh : 0 ≤ ∏ j ∈ i.val, m j := prod_nonneg fun j _=> h _; have hy:=(Real.exp_pos (-u))
  refine ⟨mul_nonneg hy.le hh,fun U=>?_⟩
  have hx (i b : ℝ) : i * b≥0 → i*b≥0:= id
  rw [← Poly.solo]; change Poly.price r ((teat A B X i).amount U) ≤ _
  rw [teat_pay]; split
  · apply (Poly.multiple hr ..).trans; refine (prod_le_prod (fun i h => Poly.nonnegative hr _) (fun j _=> hp _ _)).trans ?_
    rw [prod_mul_distrib,← Real.exp_sum,gifts]; apply mul_le_mul_of_nonneg_right _ hh
    apply Real.exp_le_exp.mpr
    have ht : (1:ℝ) ≤ i.val.toRight.card:= by exact_mod_cast Finset.card_pos.mpr i.property.2.1
    linarith only [mul_le_mul_of_nonneg_left ht hu]
  rw [Poly.zero_price]; exact mul_nonneg hy.le hh

-- SumBudget.pay lexical
lemma sum_pay {ι : Type} [Fintype ι] (d : ℝ) (P : ι→Prop) (f : ι→ℝ) (h : ∀ i, 0 ≤ f i) : SumBudget (pay f P) d ↔ ∑ i,(if P i then f i else 0) ≤ d := by
  constructor; intro hf; simpa only [Thirst.pay,tsum_fintype] using hf.2.2
  intro he; refine ⟨fun i=>?_,(hasSum_fintype _).summable,?_⟩
  · unfold pay; split; exact h _; exact le_rfl
  simpa only [pay,tsum_fintype]

-- heavy at radius test only (before Charge)

def prepared (S : κ→Lifted G ζ q.threshold) (r : V→ℝ) (a W : ℝ) := ∃ (t : κ → ℝ), (∀ i,heavy (S i) r (t i)) ∧ Incur (fun i=> (S i).extent) q.B t a W



variable [Fintype ι] [Fintype κ]
variable {p w e d a : ℝ}
lemma rarity {u : ℝ} (hr : ∀ i,0<r i) (hp : taxable (q:=q) B r (a+1) p) (h : Burden A q r (a+1) w) (hx : fertile (q:=q) X u (a+1) e)
    (hF : (↑((q.B+q.B+1)^4:ℕ):ℝ) * d ≤ 1) (hd : p+w+e≤d) (ha : 0≤a) (hy : 0≤u) (hz : 0≤d) :
    prepared (q:=q) (teat A B X) r a (Real.exp (-u)*(Real.exp d-1)) := by
  obtain ⟨m,Hm,hm⟩:=hp; obtain ⟨W,XW,HW⟩:=h; obtain ⟨Y,Hp,hY⟩:=hx
  let f : Branch ι κ n→ℝ:= Sum.elim (Sum.elim W m) Y
  let E:=vol A B X
  have hf i:0≤f i:= by cases i with
                         | inl v => rcases v with i|i; exacts [(XW _).1,(Hm _).1]
                         | inr i=> exact (Hp _).1
  have Hx (γ : ℝ) i: 0≤f i * debt q.B γ (E i):=mul_nonneg (hf _) (Real.exp_pos _).le
  have he : Ac.Hit E q.B f (a+1) d := by
    intro x
    let P : Branch ι κ n→ℝ := pay (fun t=> f t*debt q.B (a+1) (E t)) (fun i=> x∈ E i)
    have hi (i:Branch ι κ n) : P i = if x∈ E i then f i*Real.exp ((a+1)*coverNumber q.B (E i)) else 0 := by unfold P pay; split_ifs<;>rfl
    rw [← funext hi]; refine (sum_pay d (fun i=> x∈ E i) (fun j=> f j*debt q.B (a+1) (E j)) (Hx _)).2 ?_
    rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; rw [add_comm p w] at hd; apply le_trans _ hd; apply add_le_add <;> try apply add_le_add
    · simpa only [SumBudget,tsum_fintype,pay,debt,f,E,vol] using! (HW x).2.2
    · simpa only [SumBudget,tsum_fintype,pay,debt,f,E,vol] using! (hm x).2.2
    simpa only [SumBudget,tsum_fintype,pay,debt,f,E,vol] using! (hY x).2.2
  have ht (U) (i : Branch ι κ n) : Poly.price r (fuel A B X i U) ≤ Real.exp (fragrant u i) * f i := by
    rcases i with (i|i)|i
    · simpa only [fuel,fragrant,f, Sum.elim_inl, Lifted.amount, Poly.solo,Real.exp_zero,one_mul] using! (XW i).2 U
    · simpa only [fuel,fragrant,f, Sum.elim_inl,Sum.elim_inr, Strike.occ, Poly.solo,Real.exp_zero,one_mul] using! (Hm i).2 U
    exact (Nprice r _).trans_le ((Hp _).2 U)
  have hu:=cap A B X f hf u hy ht
  let v (p : Domino A B X) := Real.exp (-u)*∏ i ∈ p.val, f i
  refine ⟨v,(fun i => hu i hr), fun x=>?_⟩
  have L (p : Domino A B X) : 0 ≤ v p * debt q.B a (teat A B X p).extent := mul_nonneg (hu p hr|>.1) (Real.exp_pos _).le
  apply (sum_pay _ _ _ L).2
  simp only
  have Hp := Ac.forest E q.B ha hf he (by exact_mod_cast hF) hz x
  let D:= (univ : Finset (Domino A B X)).image Subtype.val
  have hD := le_trans (Hp.2.1.sum_le_tsum D (fun i _=> Hp.1 i)) Hp.2.2
  apply le_trans _ (mul_le_mul_of_nonneg_left hD (Real.exp_pos _).le)
  rw [Finset.sum_image (fun _ _ _ _ H=>Subtype.ext H), Finset.mul_sum]; apply sum_le_sum; intro i _
  unfold Ac.roots; simp only [show Ac.Spark E i.val from i.property.1, true_and]; split_ifs
  · apply le_of_eq; dsimp only [v,debt,teat,Settle,E]; ring
  · contradiction
  · contradiction
  rw [mul_zero]
end YM.Next.Rank.Alarm
