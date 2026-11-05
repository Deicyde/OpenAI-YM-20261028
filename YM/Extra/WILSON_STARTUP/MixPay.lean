import YM.Extra.WILSON_STARTUP.ExtraCover
import YM.Extra.WILSON_STARTUP.Mixture
import YM.Extra.WILSON_STARTUP.SourceInk
import YM.Next.BOUNDARY.Synchronize
import YM.Work.I01


/-! # Genuine simultaneous-source startup pays `Stubs.Holds`

No constants depending on number of markers. Their exponential multiplicities
inside a K are paid by a cover reserve bought at startup only. Suppress weights
of ALL zero entries of the overlay, including products that vanish identically
due to the domain or actual coefficients (Stubs.paid). Keep moves/vacuum on
the original dictionary. Margin required for now: at least 8 and B² separation
of marker origins under the torus convention.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup.Mixture
open Function Filter RG Lattice Wilson Ovens Marker LinearMarkers Finset Overlay Source Mix Padded Labels
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {n : Side} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {d : ℕ} {F : Frame G d}

lemma grain_from {o : Site n} {X : Support n} {b : BudgetPoint} {f : Config G n → ℂ} {C A : ℝ} (h : b.supBounds o X f C)
    (hA : ((b.order+1:ℕ):ℝ)*C ≤ A) : grain b X f o A :=
  ⟨fun _ => C,fun _ => h.1,(sum_le_sum (s:=range (b.order+1)) fun i _ => div_le_self h.1
    (by exact_mod_cast Nat.factorial_pos i)).trans (by simpa using hA),fun l hl hD U hU => h.2 U hU l hl hD⟩

def inside (o : V → Site n) (X : Support n) := univ.filter (fun i => o i∈X)

def Far (b : BudgetPoint) (o : V → Site n) := 8 ≤ b.B ∧ ∀ i j, i≠j → b.B^2 ≤ separation (o i) (o j)

omit [DecidableEq V] [Nonempty V] in
theorem card_inside {b : BudgetPoint} {o : V → Site n} (h : Far b o) (X : Support n) :
    (2:ℝ)^(inside o X).card ≤ 2*Real.exp (8 * coverNumber b.B X) := by
  by_cases hx : 2 ≤ (inside o X).card
  · have he := Work.I01.answer n V o b.B h.1 (inside o X) (fun i _ j _ hij => h.2 i j hij) hx X (fun x hx => by obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx; exact (Finset.mem_filter.mp hi).2
     )
    have hh := Nat.mul_le_mul_right (inside o X).card h.1
    calc
      _ ≤ (Real.exp 1)^ (inside o X).card := pow_le_pow_left₀ (by norm_num) (by linarith only [Real.add_one_le_exp 1]) _
      _ = Real.exp (inside o X).card := by rw [← Real.exp_nat_mul,mul_one]
      _ ≤ Real.exp (8 * coverNumber b.B X) := Real.exp_le_exp.mpr (by exact_mod_cast (by omega : (inside o X).card ≤ 8 * coverNumber b.B X))
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (by norm_num)
  calc
    _ ≤ (2:ℝ)^1 := pow_le_pow_right₀ (by norm_num) (by omega)
    _ ≤ _ := by simp

variable {R : Census V} {S : SectionData F} {o : V → Site n} {P : Rep G n} {v : V → F.Coeff} {δ C w : ℝ}

def ink (v : V → F.Coeff) (C : ℝ) (b : BudgetPoint) (i : V) := ((b.order+1:ℕ):ℝ)*(C* F.coeffSize (F.core (v i)))
def fullCost (v : V → F.Coeff) (S : SectionData F) (b : BudgetPoint) (i : V) := Mark.scale S b * F.coeffSize (F.core (v i))

def pricedK (S : SectionData F) (P : Rep G n) (v : V → F.Coeff) (f : ℕ → ℝ) (j : ℕ) (x : R.Mode) := f j * ∏ i ∈ x.val,fullCost v S P.p i

variable {f : ℕ → ℝ}
omit [Fintype V] [DecidableEq V] [Nonempty V] in
lemma full_nonneg (i : V) : 0 ≤ fullCost v S P.p i := mul_nonneg (Mark.scale_pos ..).le (Mark.coeff_nn ..)
omit [Fintype V] [Nonempty V] in
lemma pricedK_pos (hf : ∀ j, 0≤f j) (j : ℕ) (x : R.Mode) : 0 ≤ pricedK S P v f j x :=
  mul_nonneg (hf j) (prod_nonneg fun i _ => full_nonneg i)
lemma pricedK_pay (hf : ∀ j,0 ≤ f j ∧ ∀ U : Config G n, ‖P.activities.K j U‖ ≤ f j) (i j : ℕ) (U : Config G n) :
    ‖(overlay R S o P v).entries i j U‖ ≤ pricedK S P v f i ((overlay R S o P v).marks i j) := by
  let X := name (Positive R) j
  let b := P.p
  have he l : ‖measured S o P v i U l‖ ≤ fullCost v S b l := by
    unfold measured; split
    · exact Mark.whole_scaled S P.p _ _
    rw [norm_zero]; exact full_nonneg (P:=P) l
  change ‖(if fixed (Positive R) j then parcel R S o P v i X else 0) U‖ ≤ pricedK S P v f i X.val
  split
  · rw [parcel,norm_mul,Complex.norm_real,norm_prod]; exact mul_le_mul (hf i |>.2 U)
      (prod_le_prod (fun _ _ => norm_nonneg _) (fun l _ => he l)) (prod_nonneg fun _ _ => norm_nonneg _) (hf i).1
  exact (norm_zero.le.trans (pricedK_pos (fun j => (hf j).1) ..))

omit [Fintype V] [DecidableEq V] [Nonempty V] in
lemma ink_pos (h : 0≤C) (b : BudgetPoint) (v : V → F.Coeff) (i : V) : 0 ≤ ink v C b i :=
  mul_nonneg (by positivity) (mul_nonneg h (Mark.coeff_nn ..))

def tokenE (v : V → F.Coeff) (C : ℝ) (b : BudgetPoint) (i : ℕ) := if fixed V i then ink v C b (name V i) else 0
def tokenK (Q : Bands R P) (S : SectionData F) (v : V → F.Coeff) (f : ℕ → ℝ) (q : ℕ × ℕ) :=
  if Q.entries q.1 q.2 = 0 then 0 else pricedK S P v f q.1 (Q.marks q.1 q.2)

omit [DecidableEq V] in
lemma tokenE_pos (h : 0≤C) (i : ℕ) (b : BudgetPoint) : 0≤ tokenE v C b i := by unfold tokenE; split; exact ink_pos h ..; exact le_rfl
omit [Fintype V] [Nonempty V] in
lemma tokenK_pos {Q : Bands R P} (hf : ∀ j,0≤f j) (q : ℕ × ℕ) : 0 ≤ tokenK Q S v f q := by unfold tokenK; split; exact le_rfl; exact pricedK_pos hf ..

def stubs (hs : Bid.Credit S P.p.order P.p.power C) (hC : 0 ≤ C) (o : V → Site n)
    (hf : ∀ i,0 ≤ f i ∧ ∀ U, ‖P.activities.K i U‖ ≤ f i) (R : Census V) (v : V → F.Coeff) : Stubs (overlay R S o P v) where
  a := tokenE v C P.p
  k := tokenK (overlay R S o P v) S v f
  nonnegative i := tokenE_pos hC i _
  usable q := tokenK_pos (fun j => (hf j).1) q
  paid q h := fun hq => by rw [tokenK,if_pos hq] at h; linarith
  supplies i j U := by
    unfold tokenK; split
    next h => rw [h]; exact norm_zero.le
    exact pricedK_pay hf ..
  kernels i x h := by
    obtain rfl := mem_singleton.mp h; dsimp only [overlay]
    unfold tokenE; split
    · refine grain_from (C:=C*_) ?_ le_rfl
      have he := (Next.Foundations.combination_bound P.p (o (name V i)) hs (F.scaled P.p.threshold⁻¹ (F.core (v (name V i))))).2
      rwa [F.scaled_inv P.p.threshold_pos.ne'] at he
    refine grain_from (C:=0) ⟨le_rfl,fun U _ l _ _ => ?_⟩ (by simp)
    change ‖leftDerivs (fun _ => (0:ℂ)) l U‖ ≤ _; simp [Work.G07.left_const]

structure DataCost (S : SectionData F) (o : V → Site n) (b : BudgetPoint) (v : V → F.Coeff) (C w : ℝ) : Prop where
  nonempty : 0 ≤ C
  credit : Bid.Credit S b.order b.power C
  pos : 0 < w
  units i : w * ‖v i 0‖ ≤ 1
  rays i : w * b.mass (S.footprint (o i)) (ink v C b i) ≤ 1
  forced i : w * fullCost v S b i ≤ 1

omit [Fintype V] [Nonempty V] in
lemma charge_rank (h : DataCost S o P.p v C w) {i : ℕ} (hf : 0 ≤ f i) (q : R.Mode) :
    Poly.toll (fun _ => w) q * loaf P.p (P.activities.forced i).support 0 (pricedK S P v f i q) ≤ P.p.mass (P.activities.forced i).support (f i) := by
  unfold Poly.toll loaf pricedK BudgetPoint.mass; rw [add_zero];
  have he := Finset.prod_mul_distrib (s:=q.val) (f:=fun _ => w) (g:=fullCost v S P.p)
  apply le_trans (le_of_eq (show _ = (∏ l∈q.val,w*fullCost v S P.p l) * (Real.exp _ * f i) by rw [he]; ring))
  apply mul_le_of_le_one_left (by positivity); exact Finset.prod_le_one (fun l _ => mul_nonneg h.pos.le (full_nonneg l (P:=P))) (fun i _ => h.forced i)

lemma fundedK (h : DataCost S o P.p v C w) (hd : Far P.p o) (hk : (overlay R S o P v).Active) (hf : ∀ j,0≤ f j)
    (ht : ∀ x : Site n, SumBudget (fun i => if x∈(P.activities.forced i).support then (Start.expand P.p).mass (P.activities.forced i).support (f i) else 0) (1/2))
    (rank : Bool) (l : V) :
    let Q := overlay R S o P v
    SumBudget (fun q : ℕ × ℕ => if ranked (Q.marks q.1 q.2)=rank ∧ l∈ (Q.marks q.1 q.2).val then
      Poly.toll (fun _ => w) (Q.marks q.1 q.2)*loaf P.p (P.activities.forced q.1).support 0 (tokenK Q S v f q) else 0) 1 := by
  intro Q
  let A := fun q : ℕ × ℕ => if ranked (Q.marks q.1 q.2)=rank ∧ l∈ (Q.marks q.1 q.2).val then
      Poly.toll (fun _ => w) (Q.marks q.1 q.2)*loaf P.p (P.activities.forced q.1).support 0 (tokenK Q S v f q) else 0
  let X := fun i => (P.activities.forced i).support
  let t (i) := if o l ∈ X i then (Start.expand P.p).mass (X i) (f i) else 0
  have htt : SumBudget t (1/2) := ht _
  have hn q : 0 ≤ A q := by
    unfold A loaf; split
    · exact mul_nonneg (Poly.worth (fun _ => h.pos) _).le (mul_nonneg (Real.exp_pos _).le (tokenK_pos hf _))
    rfl
  have he (i j) (hA : A (i,j) ≠ 0) := by
    have H : (ranked (Q.marks i j)=rank ∧ l∈ (Q.marks i j).val) ∧ Q.entries i j ≠ 0 := by
      dsimp only [A,tokenK] at hA; split at hA
      next he => exact ⟨he,fun hh => hA (by rw [if_pos hh,loaf,mul_zero,mul_zero])⟩
      exact (hA rfl).elim
    exact H
  let F := fun i (q : Positive R) => A (i,index q)
  have hs i : HasSum (fun j => A (i,j)) (∑ x, F i x) := Padded.has (fun j => by
    split
    next hj => unfold F; rw [index_name hj]
    refine of_not_not fun hh => (he i j hh).2 ?_
    exact if_neg (by assumption))
  have hy i : ∑ q : Positive R,F i q ≤ t i * 2 := by
    let Z := univ.filter fun q => F i q ≠ 0
    rw [← Finset.sum_filter_ne_zero]
    have hi (q : Positive R) (hq : q∈Z) := he i (index q) ((mem_filter.mp hq).2)
    have hp (q : Positive R) : Q.marks i (index q) = q.val := congr_arg Subtype.val (name_index q)
    have hL (q : Positive R) (hq : q∈Z) : q.val.val ⊆ inside o (X i) := fun j hj => mem_filter.mpr ⟨mem_univ j,
      hk.retained i (index q) (hi q hq).2 _ ((hp q).symm ▸ hj)⟩
    change ∑ q∈Z, F i q ≤ _
    by_cases hz : o l ∈ X i
    · have heq := Finset.card_le_card_of_injOn (fun q : Positive R => q.val.val) (t:=(inside o (X i)).powerset) (s:=Z)
        (fun q hq => Finset.mem_powerset.mpr (hL q hq)) (fun q _ u _ h => Subtype.ext (Subtype.ext h))
      rw [Finset.card_powerset] at heq
      calc
        _ ≤ ∑ _q∈Z,P.p.mass (X i) (f i) := sum_le_sum fun q hq => by
          dsimp only [F,A,tokenK]; rw [if_pos (hi q hq).1, if_neg (hi q hq).2]
          exact charge_rank h (hf i) _
        _ ≤ (2*Real.exp (8 * coverNumber P.p.B (X i))) * P.p.mass (X i) (f i) := by
          rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.exp_pos _).le (hf i))
          exact (show (Z.card : ℝ) ≤ (2:ℝ)^(inside o (X i)).card by exact_mod_cast heq).trans (card_inside hd (X i))
        _ = _ := by unfold t BudgetPoint.mass Start.expand; rw [if_pos hz]; dsimp only; rw [add_mul, Real.exp_add]; ring
    have hZ : Z=∅ := eq_empty_iff_forall_notMem.mpr (fun q hq => hz ((mem_filter.mp (hL q hq ((hp q) ▸ (hi q hq).1.2))).2))
    unfold t;rw [hZ,sum_empty,if_neg hz,zero_mul]
  have hX : Summable A := (summable_prod_of_nonneg hn).mpr ⟨fun i => (hs i).summable,
    (htt.2.1.mul_right 2).of_nonneg_of_le (fun i => tsum_nonneg fun _ => hn _) (fun i => (hs i).tsum_eq.trans_le (hy i))⟩
  refine ⟨hn, hX, ?_⟩
  change ∑' q,A q ≤ 1; rw [hX.tsum_prod]
  apply le_trans (((summable_prod_of_nonneg hn).mp hX).2.tsum_le_tsum (fun i => (hs i).tsum_eq.trans_le (hy i)) (htt.2.1.mul_right 2))
  rw [tsum_mul_right]; linarith only [htt.2.2]

lemma fundedE (h : DataCost S o P.p v C w) (rank : Bool) (l : V) :
    let Q := overlay R S o P v
    SumBudget (fun q : ℕ => if ranked (Q.rays q)=rank ∧ l∈ (Q.rays q).val then
      Poly.toll (fun _ => w) (Q.rays q)*loaf P.p (Q.support q) 0 (tokenE v C P.p q) else 0) 1 := by
  dsimp only [overlay]; simp_rw [Poly.solo_toll,Census.fire, Finset.mem_singleton]
  let f := fun q : V => if ranked (R.fire q)=rank ∧ l=q then w*P.p.mass (S.footprint (o q)) (ink v C P.p q) else 0
  refine Padded.budget (g:=f) ?_ ?_ ?_
  · intro i; unfold f tokenE loaf BudgetPoint.mass Census.fire; split_ifs <;> simp
  · intro i; unfold f; split
    · exact mul_nonneg h.pos.le (mul_nonneg (Real.exp_pos _).le (ink_pos h.nonempty _ _ _))
    rfl
  · rw [sum_eq_single l]
    · unfold f; split <;> first | exact h.rays l | norm_num
    · intro i _ hi; simp [f,Ne.symm hi]
    simp

theorem holds {A : Hol G} (hS : S.Sound A) (hf : P.activities.ForcedFamily P.p)
    (h : DataCost S o P.p v C w) (hd : Far P.p o) (ht : P.activities.KBound (Start.expand P.p) (1/2)) :
    Stubs.Holds (overlay R S o P v) w := by
  obtain ⟨f,hf',hX⟩ := ht
  let T := stubs h.credit h.nonempty o hf' R v
  have hk := active (R:=R) (o:=o) (v:=v) hS h.credit hf
  have he (rank : Bool) : T.funded (fun _ => w) 0 rank 1 := ⟨fun l => fundedE h rank l,fun l => fundedK h hd hk (fun j => (hf' j).1) hX rank l⟩
  exact ⟨h.units,hk,fun v q hv => ⟨hd.1, by simpa only [sq,overlay] using hd.2 v q hv⟩,T,he false,Or.inl (he true)⟩
end YM.WilsonStartup.Mixture
