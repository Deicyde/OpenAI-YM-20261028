import YM.Push.CORRECTED_COLUMNS.Centering
import YM.Push.CORRECTED_COLUMNS.Inflate
/-!
# Reweight unassigned regular atoms, splice

Needs good-mask estimate at u/W on intra terms (can get from E
K endpoint R's proposed estimates since these have at most n slots). For
multi-cell use sparse support *at the current stage* with smaller radius.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Prepare.Atoms
open Function Set Filter MeasureTheory Lattice RG Marker Width
open Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {A : Type} {V X Y : Type*} [Fintype A] [Fintype V] [DecidableEq V] [DecidableEq A]
variable {G : Gauge} {n : Side} {v : A × V → Site n} {q : BudgetPoint}

variable (F : Atoms q (Marks.all (A×V)) v G X) {w u a : ℝ} {B : ℕ}

-- Damping at w (v_s in E), possibly much smaller than W (our u here).
def across (i : X) := Finset.image Prod.fst (F.tag i).val

def mixed (i : X) := 2≤ (across F i).card

lemma sparsity (H : Heads q v G) (hh : ∀ i j : A, i≠j → ∀ x∈H.sites i,∀ y∈H.sites j,B^2≤ separation x y)
    (hp : 8 ≤ B) (i : X) (he : mixed F i) : B * (across F i).card ≤ 64*coverNumber B (F.sites i) := by
  refine UnionK.projects _ B hp (F.sites i) (across F i) ?_ (fun t _ q _ h => hh t q h) he
  intro t h
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
  exact Finset.not_disjoint_iff.mpr ⟨v x,H.covers _, F.pin _ _ hx⟩

lemma toll (hw : 0 < w) (hu : w≤u) (hv : 64*(Real.log (u/w)*Fintype.card V) ≤ B) (i : X)
    (h : B*(across F i).card ≤ 64*coverNumber B (F.sites i)) :
    Poly.toll (fun _ => u) (F.tag i) * emit B a (F.sites i) ≤ Poly.toll (fun _ => w) (F.tag i) * emit B (a+1) (F.sites i) := by
  let l := u/w
  have hh : 1 ≤ l := (one_le_div hw).2 hu
  let x := (across F i).card
  let c := Fintype.card V
  have he : (F.tag i).val.card ≤ x*c := (Finset.card_le_card (show (F.tag i).val ⊆ across F i ×ˢ Finset.univ from
    fun j hj => mem_product.mpr ⟨mem_image_of_mem _ hj,mem_univ _⟩)).trans_eq (by rw [Finset.card_product, card_univ])
  let D := coverNumber B (F.sites i)
  have ht : l^((F.tag i).val.card)≤Real.exp D := by
    apply (pow_le_pow_right₀ hh he).trans
    rw [show l^(x*c)=Real.exp (↑(x*c)*Real.log l) by rw [Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hh)]]
    apply Real.exp_monotone
    push_cast
    have hc : (B:ℝ)*x ≤ 64*D := by exact_mod_cast h
    change 64*(Real.log l*c)≤_ at hv
    linarith only [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α:=ℝ) x),hc]
  rw [UnionK.tollBoost hw]; unfold emit; rw [add_mul,one_mul,Real.exp_add]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (Poly.worth (fun _ => hw) _).le) (Real.exp_pos _).le).trans_eq (by unfold D; ring)

-- Need the fixed-intracell data; uniform in all marked sets of that type.
-- Output M can be the restarted `R.p.B`.
theorem rest (hw : 0 < w) (hu : w ≤ u) {b c : ℝ} (hV : F.Cost (fun _ => w) B (a+1) b)
    (H : Heads q v G) (hp : 8 ≤ B) (hh : ∀ i j : A, i ≠ j → ∀ x ∈ H.sites i, ∀ y ∈ H.sites j, B^2 ≤ separation x y)
    (hv : 64*(Real.log (u/w)*Fintype.card V) ≤ B)
    (hs : X → ℝ) (ht : ∀ i, ¬mixed F i → 0 ≤ hs i ∧ ∀ U : Wilson.Config G n,
      Healthy q.threshold (F.sites i) U → ‖F.H i U‖ ≤ hs i)
    (h : ∀ i, SumBudget (fun j => if i∈ (F.tag j).val ∧ (across F j).card < 2 then Poly.toll (fun _=>u) (F.tag j)*hs j*emit B a (F.sites j) else 0) c) :
    F.Cost (fun _=>u) B a (b+c) := by
  classical
  obtain ⟨t,hv',hf⟩ := hV
  let y (i : X) := if mixed F i then t i else hs i
  have he i : 0 ≤ y i ∧ ∀ U, Healthy q.threshold (F.sites i) U → ‖F.H i U‖ ≤ y i := by
    unfold y; split <;> rename_i e; exact hv' _; exact ht i e
  refine ⟨y,he,fun i => ?_⟩
  let f (j : X) := if i∈(F.tag j).val then Poly.toll (fun _=>u) (F.tag j)*y j*emit B a (F.sites j) else 0
  let k (j : X) := if i∈(F.tag j).val then Poly.toll (fun _=>w) (F.tag j)*t j*emit B (a+1) (F.sites j) else 0
  let g (j : X) := if i∈ (F.tag j).val ∧ (across F j).card < 2 then Poly.toll (fun _=>u) (F.tag j)*hs j*emit B a (F.sites j) else 0
  have hy (j) : f j ≤ k j + g j := by
    by_cases hx : i∈(F.tag j).val
    · rcases lt_or_ge (across F j|>.card) 2 with hz|hz
      · apply le_trans (b:=g j) ?_ (le_add_of_nonneg_left ((hf i).1 _))
        unfold f g y; rw [if_neg (show ¬mixed F j from not_le.mpr hz), if_pos hx, if_pos ⟨hx,hz⟩]
      apply le_trans (b:=k j) ?_ (le_add_of_nonneg_right ((h i).1 _))
      unfold f k y; rw [if_pos (show mixed F j from hz),if_pos hx,if_pos hx,mul_right_comm _ (t j), mul_right_comm _ (t j)]
      exact mul_le_mul_of_nonneg_right (toll F hw hu hv _ (sparsity F H hh hp _ hz)) (hv' j).1
    simp only [f,k,g,hx,false_and,↓reduceIte,add_zero]; exact le_rfl
  have hp j : 0 ≤ f j := by unfold f; split; exact mul_nonneg (mul_nonneg (Poly.worth (fun _=>hw.trans_le hu) _).le (he _).1) (emit_pos ..).le; exact le_rfl
  have hk : Summable k := (hf i).2.1
  have hg : Summable g := (h i).2.1
  have hb := (hk.add hg).of_nonneg_of_le hp hy
  refine ⟨hp,hb, (hb.tsum_le_tsum hy (Summable.add hk hg)).trans ?_⟩
  change ∑' j,(k j+g j) ≤ _
  rw [Summable.tsum_add hk hg]; exact add_le_add (hf _).2.2 (h _).2.2

-- merge two lists
def append (H : Atoms q (Marks.all (A×V)) v G Y) : Atoms q (Marks.all (A×V)) v G (X⊕Y) where
    sites := Sum.elim F.sites H.sites
    tag := Sum.elim F.tag H.tag
    H := Sum.elim F.H H.H
    proper i := by cases i; exacts [F.proper _,H.proper _]
    pin i l := by cases i; exacts [F.pin _ l,H.pin _ l]
    borel i := by cases i; exacts [F.borel _, H.borel _]
    footprint i := by cases i; exacts [F.footprint _, H.footprint _]
    gauge i := by cases i; exacts [F.gauge _, H.gauge _]
lemma liquidity {f g : ℝ} (H : Atoms q (Marks.all (A×V)) v G Y) (u : A×V → ℝ) (hv : F.Cost u B a f)
    (hx : H.Cost u B a g) : (F.append H).Cost u B a (f+g) := by
  obtain ⟨l,hl,h⟩ := hv
  obtain ⟨s,hs,hp⟩ := hx
  refine ⟨Sum.elim l s,(fun i => ?_),fun i => ?_⟩
  · cases i; exacts [hl _,hs _]
  let K := append F H
  let y (j : X ⊕ Y) := if i∈(K.tag j).val then Poly.toll u (K.tag j)*Sum.elim l s j*emit B a (K.sites j) else 0
  have hF : Summable (y ∘ Sum.inl) := (h i).2.1
  have hG : Summable (y ∘ Sum.inr) := (hp i).2.1
  refine ⟨fun j => ?_,Summable.sum y hF hG,(Summable.tsum_sum hF hG).trans_le (add_le_add ((h i).2.2) ((hp i).2.2))⟩
  cases j; exacts [(h i).1 _,(hp i).1 _]
lemma sum_append (H : Atoms q (Marks.all (A×V)) v G Y) (U : Wilson.Config G n)
    (hv : Summable fun j => F.portion j U) (hw : Summable fun j => H.portion j U) :
    (F.append H).sum U=F.sum U+H.sum U :=
  Summable.tsum_sum (f:=fun i => (F.append H).portion i U) hv hw
end YM.Push.Corrected.Prepare.Atoms
