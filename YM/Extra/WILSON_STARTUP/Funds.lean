import YM.Extra.WILSON_STARTUP.Gas

/-!
# Packet hit tests including the larger exponent for Buys/little

Input numerical reserve at THIS scale. Counts via full 2B balls and Ac.forest;
no volume dependence. Reusable with different cover exponent at markers.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Start
open Function Filter RG Wilson Lattice Design Work Ac Padded Ovens Ovens.Pipes
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {b : BudgetPoint} {c : Clip} {β σ κ a γ l : ℝ}

def offer (b : BudgetPoint) (σ : ℝ) (i : Foot n) := if lives b i then Real.exp (-σ*(i.val.2.card:ℝ)) else 0
def cash (n : Side) (b : BudgetPoint) (σ : ℝ) (i : ℕ) := if fixed (Foot n) i then offer b σ (name (Foot n) i) else 0

theorem cash_pos (i : ℕ) : 0 ≤ cash n b σ i := by
  unfold cash offer; split_ifs <;> first | exact le_rfl | positivity

theorem forced_money (h : Decent c b) (ho : 0 ≤ κ) (hz : 0 ≤ l) (ht : κ+σ ≤ l*gain b) (hβ : l ≤ β)
    (i : ℕ) (U : Config G n) : |(payload c b G n β).forced i U| ≤ Real.exp (-κ)*cash n b σ i := by
  have hb := cash_pos (b:=b) (σ:=σ) (n:=n) i
  dsimp only [payload]; split
  next hi =>
    unfold paid; split
    next had =>
      rw [cash,if_pos hi,offer,if_pos had.1,← Real.exp_add,abs_of_pos (Real.exp_pos _),Real.exp_le_exp]
      let D := inventory n i
      change -β * charge c b D U ≤ -κ + -σ*(D.card:ℝ)
      have he : D ⊆ flags b.threshold U := by
        change (name (Foot n) i).val.2 ⊆ _; rw [← had.2]; exact Finset.inter_subset_right
      have hp := charge_price c b h U D he
      have hD : (1:ℝ) ≤ D.card := by exact_mod_cast Finset.card_pos.mpr (name (Foot n) i).property.1
      have hh := mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ) ≤ D.card)
      have hl := mul_le_mul hβ hp (mul_nonneg (by positivity) (gain_pos _).le) (hz.trans hβ)
      nlinarith
    simp only [abs_zero]; positivity
  change |(0:ℝ)| ≤ _; simp only [abs_zero]; positivity

structure PacketCost (b : BudgetPoint) (σ a γ : ℝ) : Prop where
  exponent : 0 ≤ a
  room : ((b.B+b.B+1 : ℕ):ℝ)^4*γ ≤ 1
  bids : ((2*b.B+2*b.B+1 : ℕ):ℝ)^4*Real.exp ((a+1)*5^4-σ) ≤ γ

theorem PacketCost.gamma (h : PacketCost b σ a γ) : 0 ≤ γ := le_trans (by positivity) h.bids

theorem PacketCost.coins (h : PacketCost b σ a γ) : Ac.Hit (pad b (n:=n)) b.B (fun _ => Real.exp (-σ)) (a+1) γ := by
  intro x
  let D := pad b x
  let f (y : Site n) := if x ∈ pad b y then Real.exp (-σ) * Real.exp ((a+1)*coverNumber b.B (pad b y)) else 0
  have hf (i) : 0 ≤ f i := by unfold f; split <;> first | rfl | positivity
  refine ⟨hf, (hasSum_fintype f).summable,((hasSum_fintype f).tsum_eq).trans_le ?_⟩
  have hb : D.card ≤ (2*b.B+2*b.B+1)^4 := by simpa [D,pad] using Corona.halo_size ({x}:Support n) (2*b.B)
  apply le_trans ?_ h.bids
  calc
    ∑ y, f y = ∑ y ∈ D, Real.exp ((a+1)* coverNumber b.B (pad b y) - σ) := by
      unfold f
      simp_rw [mem_pad,separation_comm _ x, ← Real.exp_add, neg_add_eq_sub]
      rw [← Finset.sum_filter]; congr 1
      ext y; simp [D,mem_pad]
    _ ≤ ∑ _∈D,Real.exp ((a+1)*5^4-σ) := by
      apply Finset.sum_le_sum
      have ha := h.exponent
      intro y _; gcongr; exact_mod_cast pad_cost y
    _ ≤ _ := by simp only [Finset.sum_const,nsmul_eq_mul]; gcongr; exact_mod_cast hb

theorem PacketCost.hit (h : PacketCost b σ a γ) : Ac.Hit (extent n) b.B (cash n b σ) a (Real.exp γ-1) := by
  intro x
  let F (p : Foot n) := if x ∈ p.val.1 then offer b σ p * Real.exp (a*coverNumber b.B p.val.1) else 0
  refine Padded.budget (α:=Foot n) (g:=F) ?_ (fun p => ?_) ?_
  · intro i; unfold cash F; split_ifs <;> first | rfl | exact zero_mul _
  · unfold F offer; split_ifs <;> first | exact le_rfl | positivity
  let D := Finset.univ.filter (lives b (n:=n))
  let H := roots (pad b) b.B (fun _ => Real.exp (-σ)) a x
  have ht := Ac.forest (pad b) b.B h.exponent (fun _ => (Real.exp_pos _).le) h.coins h.room h.gamma x
  have he (i : Foot n) (hi : i ∈ D) : F i = H i.val.2 := by
    obtain ⟨-,hp : lives b i⟩ := Finset.mem_filter.mp hi
    unfold F offer H roots; rw [if_pos hp,hp.2]; simp only [hp.1,true_and, Finset.prod_const,← Real.exp_nat_mul,region]
    rw [mul_comm (-σ),mul_comm]
  calc
    _ = ∑ i ∈ D, F i := (Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by
      unfold F offer
      have hl : ¬ lives b p := fun he => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
      simp [hl])).symm
    _ = ∑ i ∈ D.image (fun p => p.val.2), H i := by
      rw [Finset.sum_image]; exact Finset.sum_congr rfl he
      intro i hi j hj hh; have h1 := (Finset.mem_filter.mp hi).2.2; have h2 := (Finset.mem_filter.mp hj).2.2
      exact Subtype.ext (Prod.ext (h1.trans ((congr_arg (region b) hh).trans h2.symm)) hh)
    _ ≤ _ := (ht.2.1.sum_le_tsum _ fun i _ => ht.1 i).trans ht.2.2

structure Loan (b : BudgetPoint) (l σ κ γ : ℝ) : Prop where
  slope : 0 ≤ l
  forced : 0 ≤ κ
  allows : κ+σ ≤ l*gain b
  packets : PacketCost b σ (b.supportExponent+1) γ
  margin : ((b.B+b.B+1:ℕ):ℝ)^4*(Real.exp γ-1) ≤ 1

theorem Loan.certificate (h : Loan b l σ κ γ) (hc : Decent c b) (X : Set ℝ) (hx : ∀ β∈X, l ≤ β) :
    ∃ v : Ovens.Label → ℝ,(∀ i, 0 ≤ v i) ∧ (∀ β ∈ X, ∀ i U,
      |reach (payload c b G n β) i U| ≤ i.elim (fun _ => Real.exp (-κ)) (fun _ => 1)*v i) ∧
      Ac.Hit (dictionary G n).patch b.B v (b.supportExponent+1) (Real.exp γ-1) := by
  let v := fun i : Ovens.Label => i.elim (cash n b σ) (fun _ => 0)
  have hv (i) : 0 ≤ v i := by cases i; exact cash_pos _; exact le_rfl
  refine ⟨v,hv,fun β hβ i U => ?_, fun x => ?_⟩
  · cases i
    · exact forced_money hc h.forced h.slope h.allows (hx _ hβ) _ U
    simp [payload,reach,v]
  · let f := fun i : Ovens.Label => if x∈ (dictionary G n).patch i then v i * Real.exp
          ((b.supportExponent+1) * coverNumber b.B ((dictionary G n).patch i)) else 0
    have h1 : SumBudget (f ∘ Sum.inl) (Real.exp γ-1) := h.packets.hit x
    have h2 : HasSum (f ∘ Sum.inr) 0 := by
      rw [show (f ∘ Sum.inr : ℕ → ℝ) = fun _ => 0 by funext i; simp [f,v]]
      exact hasSum_zero
    have hs := h1.2.1.hasSum.sum h2
    rw [add_zero] at hs
    exact ⟨fun i => by dsimp only; split <;> first | exact le_rfl | exact mul_nonneg (hv i) (Real.exp_pos _).le, hs.summable,hs.tsum_eq.trans_le h1.2.2⟩

theorem Loan.buys (h : Loan b l σ κ γ) (hc : Decent c b) (hb : l ≤ β) :
    (dictionary G n).Buys (payload c b G n β) b κ (Real.exp γ-1) := by
  obtain ⟨v,hv,hV,hX⟩ := h.certificate (n:=n) (G:=G) hc {β} (by simpa using hb)
  exact ⟨⟨sub_nonneg.mpr (Real.one_le_exp h.packets.gamma),h.forced,h.margin⟩,v,hv,hV β rfl,hX⟩

theorem Loan.little (h : Loan b l σ κ γ) (hc : Decent c b) (X : Set ℝ) (hx : ∀ β∈X, l ≤ β) :
    (dictionary G n).little b (payload c b G n) X := by
  obtain ⟨v,hv,hV,hX⟩ := h.certificate (n:=n) (G:=G) hc X hx
  exact ⟨κ,_,v,h.margin, sub_nonneg.mpr (Real.one_le_exp h.packets.gamma),h.forced,hv,hV,hX⟩

theorem Loan.kernel (h : Loan b l σ κ γ) (hc : Decent c b) (hb : l ≤ β) :
    (raw G n c b β).KBound b (Real.exp γ-1) := by
  refine ⟨cash n b σ,fun i => ⟨cash_pos _,fun U => ?_⟩,fun x => ?_⟩
  · exact (forced_money hc h.forced h.slope h.allows hb i U).trans <|
      mul_le_of_le_one_left (cash_pos _) (Real.exp_le_one_iff.mpr (by linarith only [h.forced]))
  let f := fun i => if x ∈ extent n i then b.mass (extent n i) (cash n b σ i) else 0
  have hf i : 0 ≤ f i := by unfold f BudgetPoint.mass; split <;> first | exact le_rfl | exact mul_nonneg (Real.exp_pos _).le (cash_pos _)
  have H := h.packets.hit (n:=n) x
  have he i : f i ≤ (if x ∈ extent n i then cash n b σ i * Real.exp ((b.supportExponent+1)*coverNumber b.B (extent n i)) else 0) := by
    unfold f; split
    · rw [BudgetPoint.mass,mul_comm]; have := cash_pos (n:=n) (b:=b) (σ:=σ) i; gcongr; linarith
    rfl
  have H' := H.2.1.of_nonneg_of_le hf he
  exact ⟨hf,H',(H'.tsum_le_tsum he H.2.1).trans H.2.2⟩
end YM.WilsonStartup.Start
