import YM.Next.MULTISOURCE.Collateral
import YM.Next.MULTISOURCE.Determined
import YM.Next.MULTISOURCE.First
import YM.Next.MULTISOURCE.Recenter

/-! Packs travel on the same history. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.AxisShift
open RG Wilson Lattice Function Filter Finset Pack MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} (o : Site n)

def runway (q : Pack n) : Pack n := ⟨⟨roots o q.zone,roots o q.flagsAt⟩, q.property.1.image _,
    roots_mono _ _ _ q.property.2⟩

def horse : Pack n ≃ Pack n where
  toFun := runway o
  invFun := runway (-o)
  left_inv q := Subtype.ext (Prod.ext (behind ..) (behind ..))
  right_inv q := by
    nth_rw 1 [show o= - -o from (neg_neg _).symm]; exact Subtype.ext (Prod.ext (behind ..) (behind ..))

lemma wind {F : Config G n → ℂ} {P : BudgetPoint} {X : Pack n} (h : Legible P X F) :
    Legible P (horse o X) (F ∘ translate o) := by
  refine ⟨h.borel.comp (visible o).measurable, respects _ _ h.symmetry,fun U W he hv => ?_, ?_⟩
  · change roots o X.zone ∩ _ = roots o X.zone ∩ _ at hv
    apply h.reads _ _ (agreeable o X.zone U W he)
    rw [← intersection, ← intersection] at hv; exact image_injective (add_left_injective o) hv
  intro i hi; exact (occupied o X.zone X.flagsAt _ i).mp (h.inventory _ hi)

def carry (D : Pulse G n) : Pulse G n := (D.1 ∘ translate o, fun v => D.2 ((horse o).symm v) ∘ translate o)

lemma carry_at (D : Pulse G n) (i : Pack n) (U) : (carry o D).2 (horse o i) U=D.2 i (translate o U) := by
  simp only [carry,Equiv.symm_apply_apply]; rfl

lemma funded {P : Rep G n} {r κ c : ℝ} {X : Support n} {D : Pulse G n} (h : Credit P.p r κ X D c) :
    Credit P.p r κ (roots o X) (carry o D) c := by
  obtain ⟨he,h1,h2,h3,⟨u,F,hf,hH,ht,hv⟩,f,hf',H⟩ := h
  refine ⟨he.image _,h1,h2,h3, ⟨u,F ∘ translate o, ?_, ?_, ht, recenters o hv⟩, f ∘ (horse o).symm,
    ?_,fun i => ?_⟩
  · simp only [carry,hf, comp_def]
  · rw [roots_card]; exact hH
  · rw [← (horse o).sum_comp]
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    change ∑ i, burn P.p r (roots o i.zone) * f i ≤ _
    simpa only [burn,priced] using hf'
  obtain ⟨q,rfl⟩ := (horse o).surjective i
  obtain ⟨hh,hx,hp,hq⟩ := H q
  unfold carry; simp only [Function.comp_apply, Equiv.symm_apply_apply]
  refine ⟨wind o hh, fun hz => roots_mono o X q.zone (hx fun h => hz (by simp only [h]; rfl)),hp,fun i => hq _⟩

lemma clean (p : BudgetPoint) (U : Config G n) (S : Finset (Pack n)) :
    S∈ clears (flags p.threshold (translate o U)) ↔
    (horse o).finsetCongr S ∈ clears (flags p.threshold U) := by
  have he : (horse o).finsetCongr S=S.image (horse o) := by rw [Equiv.finsetCongr_apply,Finset.map_eq_image]; rfl
  rw [he]; simp only [clears,mem_filter,mem_univ,true_and]
  have hv : (S.image (horse o)).biUnion flagsAt=roots o (S.biUnion flagsAt) := by
    rw [Finset.image_biUnion]; unfold roots
    rw [Finset.biUnion_image]; rfl
  have ht : (S : Set (Pack n)).PairwiseDisjoint zone ↔
      ((S.image (horse o):Finset (Pack n)): Set (Pack n)).PairwiseDisjoint zone := by
    constructor
    · intro h i hi j hj hn
      obtain ⟨i,hp,rfl⟩ := mem_image.mp hi; obtain ⟨j,hq,rfl⟩ := mem_image.mp hj
      exact (Finset.disjoint_image (add_left_injective o)).mpr (h hp hq (fun h => hn (h ▸ rfl)))
    intro h i hi j hj hn
    apply (Finset.disjoint_image (add_left_injective o)).mp; exact h (mem_image_of_mem _ hi)
      (mem_image_of_mem _ hj) ((horse o).injective.ne hn)
  rw [hv,← ht]
  conv_rhs => rw [← flagging o p.threshold U]
  exact and_congr_right fun _ => (Finset.image_injective (add_left_injective o)).eq_iff.symm

lemma incumbent_shifts (U : Config G n) {P : Rep G n} (q : Pack n) {δ κ : ℝ} (hh : P.activities.Valid P.p δ κ) :
    incumbent P U (horse o q)=incumbent P (translate o U) q := by
  obtain ⟨M⟩ := hh.moves 1 o
  have he (i) : Pack.ofAddress P.activities (M.kp i)=horse o (ofAddress P.activities i) := by
    apply Subtype.ext; refine Prod.ext ?_ ?_
    · apply (M.forced_support i).trans ?_; apply Finset.image_congr; intro x hx; simp [affine]
    apply (M.forced_inventory i).trans ?_
    apply Finset.image_congr; intro x hx; simp [affine]
  unfold incumbent Pack.collect; rw [← M.kp.tsum_eq]
  refine tsum_congr fun i => ?_
  simp only [he, Equiv.apply_eq_iff_eq,M.valuesK, pull_one]

lemma sum_shifts {T : Type*} [AddCommMonoid T] (f : Finset (Pack n) → T)
    (p : BudgetPoint) (U : Config G n) :
    (∑ i∈ clears (flags p.threshold U),f i) =
      ∑ i∈ clears (flags p.threshold (translate o U)), f ((horse o).finsetCongr i) := by
  symm
  refine Finset.sum_bij (fun i _ => (horse o).finsetCongr i) (fun i hi => (clean ..).mp hi)
    (fun i hi j hj h => (horse o).finsetCongr.injective h) ?_ fun i _ => rfl
  intro i hi; obtain ⟨t,rfl⟩ := (horse o).finsetCongr.surjective i; exact ⟨_,(clean ..).mpr hi,rfl⟩

lemma vacuum_shifts (U : Config G n) {P : Rep G n} {δ κ : ℝ} (h : P.activities.Valid P.p δ κ) :
    P.activities.gas P.p (translate o U)=P.activities.gas P.p U := by
  apply Complex.ofReal_injective; rw [real_book _ _ h, real_book _ _ h]; symm
  rw [sum_shifts o]; apply sum_congr rfl; intro i hi
  simp [Equiv.finsetCongr_apply,incumbent_shifts o U _ h]

-- No differentiability inference at the masks needed.
lemma currents (P : Rep G n) {δ κ : ℝ} (hd : P.activities.Valid P.p δ κ) (x : Config G n)
    (h : P.eval (translate o x)=P.eval x) (ht : 0 < P.eval x) (D : Pulse G n) :
    tangent P (carry o D) x=tangent P D (translate o x) := by
  have he i : incumbent P x (horse o i) = _ := incumbent_shifts o x i hd
  have hp : Real.exp (P.exponent (translate o x))=Real.exp (P.exponent x) := by
    apply mul_right_cancel₀ (show P.activities.gas P.p x ≠ 0 from fun he => by
      have hh : 0 < P.eval x := ht
      rw [Rep.eval,he,mul_zero] at hh; exact lt_irrefl _ hh)
    nth_rw 1 [← vacuum_shifts o x hd]; exact h
  unfold tangent; rw [hp,h]
  change (↑(P.eval x):ℂ)*D.1 (translate o x) + _ = _
  refine congrArg₂ _ rfl (congrArg₂ _ rfl ?_)
  rw [sum_shifts o]; apply sum_congr rfl; intro i _
  change _ = ∑ j∈i, _
  rw [Equiv.finsetCongr_apply, Finset.sum_map]; apply sum_congr rfl; intro j _
  simp_rw [← Finset.map_erase, Finset.prod_map, Equiv.coe_toEmbedding, carry_at, he]

lemma transported {A : History G} {N p j} (hj : j≤N) (h : A.Selected) (D : Pulse G (A.S.side j p))
    (o : Site (A.S.side j p)) : tangent (A.rep N p j) (carry o D)= tangent (A.rep N p j) D ∘ translate o := by
  let P := A.rep N p j
  funext x; exact currents o P (h.represents N p j hj).good.labels x
    (congr_fun (chosen_shift (N:=N) h hj o) x) (chosen_positive h hj x) D
end YM.Multi.AxisShift
