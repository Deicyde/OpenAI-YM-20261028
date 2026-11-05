import YM.Extra.MULTISOURCE_BOUNDS.Layers
import YM.Extra.MULTISOURCE_BOUNDS.Rates
import YM.Next.FOUNDATIONS.TestBounds

/-!
# Paying the λ_s canonical mask adjustments on every copy at a merger

Keep all three value corrections (here combined into a single
letter per raw singleton term).

Needs exact coverage attaching to a current
forced term to use `Merge`; we prove the flag test but do not change any gas
predicates.

Wrapping uses the actual `Reads`.

Cut on the bulk BEFORE
L^{D_s} scaling in this test (all prices linear in the amplitude).

Other
retained section obligations including comparisons/readout in the invariant
vacuum and structural reindexing remain with the source producers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Function Filter Lattice RG Source Wilson Overlay Marker Labels MeasureTheory Finset LogTerms Germs Merger Repeated Next.Foundations
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {V : Type} {m p : ℕ}

def lens (H : Hol G) (F : Frames G) (d : ℕ) := (price_of_readout H (F.level d)).choose

def upper (H : Hol G) (F : Frames G) (j : ℕ) := ∑ d∈Finset.range (j+1),lens H F d

theorem lens_ge (H : Hol G) (F : Frames G) (d : ℕ) : 1 ≤ lens H F d := (price_of_readout H (F.level d)).choose_spec.1

theorem lens_le (H : Hol G) (F : Frames G) {d j : ℕ} (hd : d ≤ j) : lens H F d ≤ upper H F j :=
    single_le_sum (f:=lens H F) (fun _ _ => zero_le_one.trans (lens_ge ..)) (mem_range.mpr (by omega))

def overheadAt (H : Hol G) (F : Frames G) (S : Stage) (j μ B : ℕ) :=
    (1 + (1+S.columns)*upper H F j)*Real.exp (S.supportExponent+3)*(1+μ*siteFactor B)

structure Slit (C : Family G) (D : V→ℕ) (o : V→Site (C.side m p)) (X : Layer G V (C.side m p)) where
  pinned i v : v∈X.names i → o v ∈ X.supp i
  coord (i : X.Id) (v : V) : C.label (D v)
  reads i v : X.names i={v} → Reads C.params (o v) (X.supp i)
    ((C.labels.level (D v)).coords.symm (coord i v)) (X.value i)

namespace Slit
variable {C : Family G} {D : V→ℕ} {o : V→Site (C.side m p)} {X : Layer G V (C.side m p)} (S : Slit C D o X)
abbrev CardId (_S : Slit C D o X) := {p : X.Id × V // X.names p.1 = {p.2}}
abbrev sectionAt (_S : Slit C D o X) (v : V) := (C.localSection (D v)).footprint (o v)

abbrev test (i : S.CardId) := (C.localSection (D i.val.2)).places (S.coord i.val.1 i.val.2) (o i.val.2)

def layer : Layer G V (C.side m p) where
  Id := S.CardId
  names i := X.names i.val.1
  supp i := X.supp i.val.1 ∪ S.sectionAt i.val.2
  value i U :=
    let t := (point C m).threshold
    ((if Healthy t (S.sectionAt i.val.2) U then 0 else masked t (X.supp i.val.1) (X.value i.val.1) U) -
      (if Healthy t (X.supp i.val.1) U then 0 else masked t (S.sectionAt i.val.2) (S.test i) U)) -
      (if Healthy t (S.sectionAt i.val.2) U then 0 else (S.coord i.val.1 i.val.2) 0)

theorem inject : Injective (fun i : S.layer.Id => i.val.1) := by
  intro i j hij
  exact Subtype.ext <| Prod.ext hij (singleton_inj.mp ((i.property.symm.trans (congr_arg _ hij)).trans j.property))

theorem bad (i : S.CardId) {U : Config G (C.side m p)} (h : Healthy (point C m).threshold (S.layer.supp i) U) :
    S.layer.value i U=0  := by
  have he : Healthy _ (X.supp i.val.1) U := Finset.disjoint_of_subset_left Finset.subset_union_left h
  have ht : Healthy _ (S.sectionAt i.val.2) U := Finset.disjoint_of_subset_left Finset.subset_union_right h
  simp [layer,he,ht]



theorem expenses (H : C.Makes) (hm : ∀ v, C.ref (D v) ≤ m) (i : S.CardId) {e : ℝ} (hR : (point C m).Regular (X.supp i.val.1) (X.value i.val.1))
    (hP : (point C m).supBounds (o i.val.2) (X.supp i.val.1) (X.value i.val.1) e) (U : Config G (C.side m p)) :
    ‖S.layer.value i U‖ ≤ (1 + (1+col C m)*lens C.params C.labels (D i.val.2))*e := by
  let d := D i.val.2
  let F := C.labels.level d; let t := (point C m).threshold
  let v := S.coord i.val.1 i.val.2
  let K := lens C.params C.labels d
  obtain ⟨h1,h2⟩ := (H.stages _).2 m (hm i.val.2)
  have hu : F.coeffSize (F.scaled t v) ≤ K*e := by
    have he := (price_of_readout C.params F).choose_spec.2 _ _ _ _ _ _ (show d ≤ (point C m).order from (Nat.le_succ _).trans h1) h2 hR hP
      _ (S.reads _ _ i.property)
    rwa [LinearEquiv.apply_symm_apply] at he
  have hg := (BasisCost.analytic (C.localSection d) (point C m) (F.scaled t v) (o i.val.2) (H.priced d m p (hm _) _)).2
  have hv : 0<t := (point C m).threshold_pos
  change (point C m).supBounds _ _ ((C.localSection d).places (F.scaled t⁻¹ (F.scaled t v)) _) _ at hg
  rw [show F.scaled t⁻¹ (F.scaled t v) = v by simpa only [inv_inv] using F.scaled_inv (x:=v) (inv_pos.mpr hv).ne'] at hg
  have ht : v 0 = F.scaled t v 0 := by rw [Frame.scaled_apply,F.zero_degree]; simp
  have h3 : ‖(if Healthy t (S.sectionAt i.val.2) U then 0 else v 0)‖ ≤ K*e := by
    split; rw [norm_zero]; exact (BasisCost.coeff_nonneg _).trans hu
    rw [ht]; exact (BasisCost.coord_le _ 0).trans hu
  have h0 {X : Support (C.side m p)} {o} {f : Config G (C.side m p) → ℂ} {c : ℝ} (h : (point C m).supBounds o X f c) (p : Prop) :
      ‖if p then 0 else masked t X f U‖ ≤ c := by
    split; rw [norm_zero]; exact h.1
    by_cases hp : Healthy t X U; rw [masked_eq _ _ _ _ hp]; exact h.2 U hp [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hp,norm_zero]; exact h.1
  have h4 : ‖(if Healthy t (X.supp i.val.1) U then 0 else masked t _ (S.test i) U)‖ ≤ col C m*(K*e) :=
    (h0 (f:=S.test i) (c:=col C m*F.coeffSize (F.scaled t v)) hg _).trans
      (mul_le_mul_of_nonneg_left hu (zero_le_one.trans (col_ge ..)))
  apply (norm_sub_le ..).trans
  change ‖(if Healthy t (S.sectionAt i.val.2) U then _ else _) - _‖ + ‖(if Healthy t _ U then _ else _)‖ ≤ _
  refine (add_le_add ((norm_sub_le ..).trans (add_le_add (h0 hP _) h4)) h3).trans_eq ?_
  unfold K d; ring

-- automatic inherited hit also on the larger support
lemma invoice [Fintype V] (H : C.Makes) (hm : ∀ v, C.ref (D v) ≤ m)
    {μ : ℕ} (hμ : Occupancy o μ) (hfoot : ∀ v,BasisCost.extent (C.localSection (D v)) ≤ (point C m).B)
    (e : X.Id → ℝ) {b : ℝ} (w : V → ℝ) (hw : ∀ v,0 ≤ w v) (hb : 0 ≤ b)
    (hP : ∀ i,0 ≤ e i ∧ (point C m).Regular (X.supp i) (X.value i) ∧ ∀ p∈X.supp i,(point C m).supBounds p (X.supp i) (X.value i) (e i))
    (hq : Rooted X.names X.supp (point C m).B ((point C m).supportExponent+3) (X.weighted w e) b) :
    let B := point C m
    ∃ g, S.layer.Covers g 1 ∧ let Z := overheadAt C.params C.labels (C.path.levels.params m) (year C m) μ B.B
      Pool S.layer.names S.layer.supp B.B (B.supportExponent+2) (S.layer.weighted w g) (Z*b) (Z*b) := by
  intro B
  let a := B.supportExponent+3
  let P := 1+(1+col C m)*upper C.params C.labels (year C m)
  have ha : 0 ≤ a := by dsimp [a]; have := B.exponent_pos; linarith
  have he := sum_nonneg (fun i (_ : i ∈ Finset.range (year C m + 1)) => (zero_le_one.trans (lens_ge C.params C.labels i)))
  have hcol := col_ge C m
  have h1 : 0 ≤ P := by unfold P upper; positivity
  let g (i : S.CardId) := P*e i.val.1
  have hpin (i : S.layer.Id) := S.pinned _ _ (show i.val.2∈X.names i.val.1 from i.property.symm ▸ mem_singleton_self i.val.2)

  have hw' i : 0 ≤ S.layer.weighted w g i := mul_nonneg (prod_nonneg fun _ _ => hw _)
    (mul_nonneg h1 (hP _).1)
  refine ⟨g,fun i => ⟨mul_nonneg h1 (hP _).1, fun U => ?_⟩,?_⟩
  · rw [one_mul]; apply (S.expenses H hm i (hP _).2.1 ((hP _).2.2 _ (hpin i)) U).trans
    unfold g P; gcongr
    · exact (hP _).1
    exact lens_le _ _ (admitted C m H (hm _))
  intro Z
  have hb' := mul_nonneg (mul_nonneg h1 (Real.exp_pos a).le) hb
  have he : Rooted S.layer.names S.layer.supp B.B a (S.layer.weighted w g) ((P*Real.exp a)*b) := by
    intro v; apply Budget.pull_le (q:=fun i => i.val.1) (p:=fun _ => True) (Budget.scale (hq v) (mul_nonneg h1 (Real.exp_pos _).le))
    · intro i; split; exact mul_nonneg (Real.exp_pos _).le (hw' _); rfl
    · exact fun _ _ => trivial
    · exact S.inject.injOn
    intro i _; change (if v∈S.layer.names i then _ else _) ≤ (P*Real.exp a)*(if v∈X.names i.val.1 then _ else _)
    by_cases hvi : v∈X.names i.val.1 <;> simp only [layer, Layer.weighted,hvi,↓reduceIte,mul_zero,g]
    have Hs : coverNumber B.B (X.supp i.val.1 ∪ S.sectionAt i.val.2) ≤ coverNumber B.B (X.supp i.val.1)+1 := (Corona.meets_sum (hpin i)
      (show o i.val.2∈S.sectionAt i.val.2 from mem_image.mpr ⟨0,(H.sections _).anchored,by simp⟩) B.B).trans
        (Nat.add_le_add_left (BasisCost.small_footprint _ _ (hfoot i.val.2)) _)
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr Hs) ha)) (hw' i)
      _ = _ := by unfold a B at *; dsimp [layer, Layer.weighted,g]; push_cast; rw [mul_add,Real.exp_add]; ring_nf
    exact le_rfl
  have ht := root_hit hμ hw' hb' (fun i _ => ⟨i.val.2,i.property.symm ▸ mem_singleton_self _,mem_union_left _ (hpin i)⟩)
    (show Rooted S.layer.names S.layer.supp B.B (B.supportExponent+2+1) _ _ by norm_num [add_assoc]; exact he)
  refine ⟨hw',fun x => Budget.mono (ht x) ((ht x).1) (fun _ => le_rfl) ?_,
    he.mono hw' (fun _ => le_rfl) (by dsimp only [a]; linarith) ?_⟩
  · unfold Z overheadAt; change _ ≤ P*Real.exp a * _ * b; linarith only [hb']
  unfold Z overheadAt; change _ ≤ P*Real.exp a * _ * b
  have hx : 0 ≤ μ*siteFactor B.B := by unfold siteFactor; positivity
  nlinarith [mul_nonneg hb' hx]
end Slit
end YM.Extra.Multi
