import YM.Push.CORRECTED_COLUMNS.Infuse
import YM.Push.CORRECTED_COLUMNS.Reprint
/-!
# Restore radii after k-to-l comparison

Regular split into assigned head values in the cubes, and arbitrary
Bond terms (intra and mixed, on exactly their masks). Quantitative
interface *before* radius change on mixed atoms. Fit larger radius on
those atoms by budget of old weights with stronger support exponent.

When subtracting on each head on its own mask, produce the extra
factor only off that mask to merge into the full K gas. This is an
identity of the polynomials pointwise, commutative/nilpotent. No
assumption of feasibility of larger radii on subsequent steps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Prepare
open MeasureTheory Marker Lattice RG Wilson Width Filter Set Function
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {n : Side} {G : Gauge} {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable {P : Rep G n} {v : A × V → Site n}

-- cube data and unsubtracted readings. Keeping extensions to global
-- cylinder functions; no derivatives used at this Value-only interface.
structure Heads (p : BudgetPoint) (v : A × V → Site n) (G : Gauge) where
  sites : A → Support n
  different i j : i≠j → Disjoint (sites i) (sites j)
  some i : (sites i).Nonempty
  covers (i : A×V) : v i ∈ sites i.1
  look : A → Config G n → Marks.Algebra V
  shape i : LocalOn (sites i) (look i)
  color i : GaugeInvariant (look i)
  reads i : Measurable (look i)
  alone i x : Marks.part (look i x) ∅=0

namespace Heads
variable {q : BudgetPoint}
variable (H : Heads q v G) (f : A → Marks.Algebra V)

-- The factor in the exponent in representation before correction.
def uncenter (i : A) U := Marks.into (masked q.threshold (H.sites i) (H.look i) U) i
def center (i : A) U := Marks.into (masked q.threshold (H.sites i) (fun U => H.look i U-f i) U) i

private lemma tiny (i U) : Marks.part (uncenter H i U) ∅=0 := by
  unfold uncenter; rw [Marks.into_empty]; by_cases h : Healthy q.threshold (H.sites i) U
  · rw [masked_eq _ _ _ _ h]; exact H.alone i U
  rw [masked_ne _ _ _ _ h]; rfl

open scoped Classical in
def fee (i : A) (U : Config G n) := if Healthy q.threshold (H.sites i) U then 0
    else Marks.into (Poly.pass (-f i)-1) i
lemma subtract (hf : ∀ i, Marks.part (f i) ∅=0) (i : A) U :
    Marks.into (Poly.pass (-f i)) i * Poly.pass (uncenter H i U)=Poly.pass (center H f i U)*(1+fee H f i U) := by
  classical
  have he : Marks.part (-f i) ∅=0 := by change -Marks.part (f i) ∅=0; rw [hf,neg_zero]
  have hG := show -Marks.into (f i) i=Marks.into (-f i) i from (map_neg (Marks.emb i) _).symm
  unfold fee; split_ifs with h
  · rw [Marks.pass_into _ _ he, ← Marks.absorb _ _ (by rw [Marks.into_empty,he]) (tiny H i U)]
    unfold uncenter center; rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h,add_zero,mul_one]
    congr 1
    rw [← hG,add_comm,← sub_eq_add_neg]
    exact (map_sub (Marks.emb i) _ _).symm
  unfold uncenter center; rw [masked_ne _ _ _ _ h, masked_ne _ _ _ _ h,
    show Marks.into (0:Marks.Algebra V) i=0 from map_zero (Marks.emb i),Marks.pass_zero,
    one_mul,mul_one,show Marks.into (_-_) _=Marks.into (Poly.pass (-f i)) i-1 from by
      change Marks.emb i _= (Marks.emb i) _ - _; rw [map_sub,map_one]]
  rw [add_sub_cancel]

/-- *With* factors on configurations failing each mask. -/
lemma scale (hf : ∀ i, Marks.part (f i) ∅=0) (U : Config G n) (Y : Marks.Algebra (A×V))
    (he : Marks.part Y ∅=0) :
    (∏ i : A,Marks.into (Poly.pass (-f i)) i)*Poly.pass (Y+∑ i, uncenter H i U)=
      Poly.pass (Y+∑ i, center H f i U)*(∏ i, (1+fee H f i U)) := by
  classical
  have hv i : Marks.part (center H f i U) ∅=0 := by
    unfold center; rw [Marks.into_empty]; by_cases h : Healthy q.threshold (H.sites i) U
    · rw [masked_eq _ _ _ _ h]; change Marks.part (H.look i U) ∅-Marks.part (f i) ∅=0
      rw [H.alone,hf,sub_zero]
    rw [masked_ne _ _ _ _ h]; rfl
  rw [Marks.absorb _ _ he,Marks.absorb _ _ he,Marks.absorbMany _ (fun i => uncenter H i U) (fun i => tiny H i U),
      Marks.absorbMany _ _ hv,mul_left_comm (∏ _,_) (Poly.pass Y), ← Finset.prod_mul_distrib, mul_assoc, ← Finset.prod_mul_distrib]
  · simp_rw [subtract H f hf _ U]
  · unfold Marks.part; rw [Poly.part_sum]; exact Finset.sum_eq_zero fun i _ => hv i
  unfold Marks.part; rw [Poly.part_sum]; exact Finset.sum_eq_zero fun i _ => tiny H i U

-- Cost for new factor: one per cube. The polynomial in the
-- ORIGINAL little algebra! A naive global `pass_budget` at radius
-- W could cost exp(W) which isn't covered by resources.
private lemma price {w : ℝ} (hw : 1≤ w) (f : Marks.Algebra V) :
    Poly.price (fun _ => w) f ≤ w^(Fintype.card V)*Poly.price (fun _ => 1) f := by
  unfold Poly.price; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
  simp only [Poly.toll, Finset.prod_const, one_pow,one_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw (Finset.card_le_univ _)) (norm_nonneg _)

lemma payable (w : ℝ) (hw : 1≤w) (D : ℝ) (H : ∀ i, Poly.price (fun _ => 1) (f i)≤D) (i : A) :
    Poly.price (fun _ => w) (Width.up (Marks.into (Poly.pass (-f i)-1) i)) ≤ w ^ Fintype.card V * (Real.exp D + 1) := by
  rw [Width.shelter_same]
  apply (Marks.into_price _ _ w (zero_lt_one.trans_le hw)).trans
  apply (price hw _).trans
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (zero_le_one.trans hw) _)
  rw [sub_eq_add_neg]; apply (Poly.addition (fun _ => zero_lt_one) _ _).trans
  refine add_le_add ((Poly.pass_budget (fun _=>zero_lt_one) _).trans (Real.exp_monotone ?_)) ?_
  · simpa only [Poly.price,Poly.part_neg,norm_neg] using H i
  simpa only [Poly.price,Poly.part_neg,norm_neg] using (le_of_eq (Poly.one_price (R:=Marks.all V) (w:=fun _ => (1:ℝ))))

-- encode failed-mask debt
def issues (H : Heads P.p v G) (hf : ∀ i, Marks.part (f i) ∅=0) : AddedHeads P v (Marks.all (A×V)) A := by
  classical
  refine ⟨H.sites,H.different,H.some,fee H f,?_,?_,?_⟩
  · intro i U
    by_cases h : Healthy P.p.threshold (H.sites i) U
    · unfold fee; rw [if_pos h]; rfl
    unfold fee; rw [if_neg h]; change Marks.part (Marks.into _ _) ∅=0; rw [Marks.into_empty]
    change Marks.part (Poly.pass (-f i)) ∅ - (1:ℂ) = 0
    rw [Marks.expo_none (-(f i)) (show -Marks.part (f i) ∅=0 by rw [hf,neg_zero]),sub_self]
  · intro i
    constructor
    · intro x U
      unfold fee Healthy; rw [gauge_flags]
    · exact Measurable.ite (healthy_closed P.p.threshold (H.sites i)).measurableSet measurable_const measurable_const
    · intro U W h he
      unfold fee Healthy
      simp_rw [Finset.disjoint_iff_inter_eq_empty,he]
    intro U z ht x hx
    unfold fee at ht; split at ht
    · exact absurd ht (by simp)
    have hh : Marks.part (Marks.into (Poly.pass (-f i)-1) i) z.val ≠ 0 := ht
    rw [Marks.belongs] at hh
    have hy : Marks.located z.val {i} := by_contra fun w => hh (if_neg w)
    rw [← Finset.mem_singleton.mp (hy _ hx)]; exact H.covers _
  intro i U h; exact if_pos h
lemma issueCost (H : Heads P.p v G) (hf) U i : Covered ((issues f H hf).value i U) (Width.up (Marks.into (Poly.pass (-f i)-1) i)) := by
  change Covered (fee H f i U) _
  unfold fee; split; exact (Width.shelter _).zero; exact Width.shelter _

/-!
Form exact regular atoms. Index by local nonempty mode, each separately to
have footprint bounds. Main fee hypothesis is the fixed-mask comparison in
G. Paper uses per-component uniform `p^{-1+o(1)}` with fixed number of
slot modes , here a uniform real C at this stage and use all
coefficients explicitly.
-/
abbrev Tags (V : Type*) [Fintype V] [DecidableEq V] := {t : Finset V // t.Nonempty}

def collect : Atoms q (Marks.all (A×V)) v G (A×Tags V) := by
  refine
    { sites x := H.sites x.1
      tag x := Marks.mode (Marks.injectSubset x.1 x.2.val)
      H z U := Marks.part (H.look z.1 U-f z.1) z.2.val
      proper z := z.2.property.image _
      pin z i hi := ?_
      borel z := (Poly.part_cont _).measurable.comp ((H.reads z.1).sub measurable_const)
      footprint z := fun U W h => ?_
      gauge z := fun t U => ?_ }
  · obtain ⟨x,hx,h⟩ := Finset.mem_image.mp hi; subst i; exact H.covers _
  · dsimp only; rw [H.shape z.1 U W h]
  dsimp only; rw [H.color z.1 t U]

lemma together (hf : ∀ i, Marks.part (f i) ∅=0) (U : Config G n) :
    (H.collect f).sum U=∑ i, center H f i U := by
  classical
  unfold Atoms.sum; rw [tsum_fintype,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro i _
  let b := H.look i U-f i
  have hx : Marks.part b ∅=0 := by change Marks.part (H.look i U) ∅- Marks.part (f i) ∅=0; rw [H.alone, hf, sub_zero]
  unfold center
  by_cases h : Healthy q.threshold (H.sites i) U
  · rw [masked_eq _ _ _ _ h,Marks.into_send]
    let l (t : Tags V) := Marks.mode t.val
    have he (t : Tags V) : (H.collect f).portion (i,t) U=Poly.send (Marks.mode (Marks.injectSubset i t.val)) (b.part (l t)) := by
      unfold Atoms.portion; rw [masked_eq _ _ _ _ (show Healthy q.threshold ((H.collect f).sites (i,t)) U from h)]; rfl
    simp_rw [he]
    let w (t : (Marks.all V).Mode) := Poly.send (Marks.mode (Marks.injectSubset i t.val)) (b.part t)
    change ∑ t,w (l t)=∑ t, w t
    rw [← Finset.sum_image (s:=Finset.univ) (f:=w) (g:=l)]
    · refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx' => ?_
      unfold w; by_cases H : x.val.Nonempty
      · exact (hx' (Finset.mem_image.mpr ⟨⟨_,H⟩,Finset.mem_univ _,Subtype.ext rfl⟩)).elim
      rw [show x=Marks.mode ∅ from Subtype.ext (Finset.not_nonempty_iff_eq_empty.mp H), show b.part (Marks.mode ∅)=0 from hx,Poly.send_zero]
    exact fun _ _ _ _ H => Subtype.ext (Marks.mode_inj.mp H)
  rw [masked_ne _ _ _ _ h, show Marks.into (0:Marks.Algebra V) i = 0 from (Marks.emb i).map_zero]
  apply Finset.sum_eq_zero; intro t _; unfold Atoms.portion
  rw [masked_ne _ _ _ _ (show ¬Healthy q.threshold ((H.collect f).sites (i,t)) U from h), Poly.send_zero]

lemma budget (b : ℝ) {w : ℝ} (hw : 1≤w) (hc : 0 ≤ b) {M : ℕ} (a : ℝ) {u : ℕ}
    (ha : 0 ≤ a) (hu : ∀ i, Lattice.coverNumber M (H.sites i)≤ u)
    (h : ∀ i U, Healthy q.threshold (H.sites i) U → ∀ t : Finset V,t.Nonempty →
      ‖Marks.part (H.look i U-f i) t‖≤ b) :
    (H.collect f).Cost (fun _ => w) M a (Fintype.card (Tags V) * (w^Fintype.card V*b*Real.exp (a*u))) := by
  let G : ℕ := Fintype.card V
  let L := H.collect f
  refine ⟨fun _ => b,fun i => ⟨hc,fun U hh => h i.1 U hh i.2.val i.2.property⟩,?_⟩
  intro v
  let Y (z : A×Tags V) := if v∈(L.tag z).val then Poly.toll (fun _=>w) (L.tag z)*b*emit M a (L.sites z) else 0
  have hx : 0<w := zero_lt_one.trans_le hw
  have hi i : 0 ≤ Y i := by unfold Y; split; exact mul_nonneg (mul_nonneg (Poly.worth (fun _ => hx) _).le hc) (emit_pos ..).le; exact le_rfl
  refine ⟨hi,(hasSum_fintype _).summable,?_⟩
  change ∑' i,Y i≤ _
  rw [tsum_fintype,Fintype.sum_prod_type,Finset.sum_eq_single v.1] -- cost
  · let E := w^G*b*Real.exp (a*u)
    refine le_trans (b:=∑ _ : Tags V,E) (Finset.sum_le_sum ?_) ?_
    · intro t _; unfold Y; split
      · apply mul_le_mul
        · apply mul_le_mul_of_nonneg_right _ hc
          rw [Poly.toll, Finset.prod_const]; apply pow_le_pow_right₀ hw
          exact Finset.card_image_le.trans (Finset.card_le_univ t.val)
        · exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hu v.1) ha)
        · exact (emit_pos ..).le
        exact mul_nonneg (pow_nonneg hx.le _) hc
      unfold E; positivity
    simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ, E]
    rfl
  · intro x _ hx; apply Finset.sum_eq_zero; intro i _; unfold Y; split; rename_i H'; swap; exact rfl
    obtain ⟨j,hj,hq⟩ := Finset.mem_image.mp H'
    exact False.elim (hx (congr_arg Prod.fst hq))
  simp
end Heads
end YM.Push.Corrected.Prepare
