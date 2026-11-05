import YM.Extra.MULTISOURCE_BOUNDS.Columns
import YM.Extra.MULTISOURCE_BOUNDS.Forest
import YM.Next.FOUNDATIONS.Primary
import YM.Work.B16
import YM.Work.F05.Jacobian

/-!
# Putting the singleton receipts into Overlay currency 

This implementation takes a precise common-address comparison. Each nonzero
singleton occurrence in the many-source density is matched at its physical
support to a *distinct* address of the corresponding translated origin
presentation (plus per marker canonical terms using disjoint sets of basis
components, e.g. a single precombined term).
Different markers' maps needn't be injective jointly. Active, alignment,
shipping, equality of the full signals are still separate. A variant using
only numerical single-source domination is also possible by `solo_bundle`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Set Function Filter Lattice RG Wilson Overlay Source Marker Labels Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {C : Family G} {d m N p : ℕ} {V ι : Type*} [DecidableEq V] {R : Census V}

abbrev PiecesAt (F : Labels.Frame G d) := ℕ → Finset F.Index

def partialCore (F : Labels.Frame G d) (t : Finset F.Index) (x : F.Coeff) : F.Coeff := fun i => if i∈t then F.core x i else 0

def portion (C : Family G) (N p m : ℕ) (o : Site (C.side m p)) (v : C.label d) (t : Finset (C.labels.level d).Index) :=
    let F := C.labels.level d
    (C.localSection d).places (F.scaled (point C m).threshold⁻¹ (partialCore F t (coord C N p m v).x)) o

def Issued (A : Bands R (C.path.rep N p m)) (s : V) (v : C.label d) := ∃ (slots : PiecesAt (C.labels.level d)),
    ∃ map : ℕ → ℕ ⊕ ℕ,
    let used := {j | (A.rays j).val = {s} ∧ A.H j ≠ 0}; let y := A.origins s
    let S := coord C N p m v
    Pairwise (Function.onFun Disjoint slots) ∧ InjOn map used ∧ ∀ j ∈ used, match map j with
      | .inl i => A.support j = (C.localSection d).footprint y ∧ A.H j = portion C N p m y v (slots i)
      | .inr i => A.support j = Relocate.shift y (S.support i) ∧ A.H j = S.regular i ∘ translate y

/-- Distinct-address comparison per singleton. The label lives at the very
same `Family` reference, and the term at a camp is compared to the positive
translate after any reflection/conjugation has been absorbed into that label
(up to the trajectory producer to get these presentations and actual full
signals). Zero entries can serve as padding at any valid addresses. -/
structure Copied (A : Bands R (C.path.rep N p m)) (s : V) (v : C.label d) : Prop where
  unit : A.units s = (coord C N p m v).x 0
  ex : Issued A s v
  forced : ∃ map : ℕ × ℕ → ℕ,
    let used := {j | (tags A j).val = {s} ∧ A.entries j.1 j.2 ≠ 0}; let S := coord C N p m v
    InjOn map used ∧ ∀ j ∈ used,
      Multi.forced (C.path.rep N p m) j = Relocate.shift (A.origins s) ((C.path.rep N p m).activities.forced (map j)).support ∧
      A.entries j.1 j.2 = S.forced (map j) ∘ translate (A.origins s)



lemma pieces_sum (F : Labels.Frame G d) (slots : PiecesAt F) (h : Pairwise (Function.onFun Disjoint slots))
    (t : Finset ℕ) (x : F.Coeff) : ∑ i∈t,F.coeffSize (partialCore F (slots i) x) ≤ F.coeffSize x := by
  refine le_trans ?_ (BasisCost.coeff_le x); unfold Labels.Frame.coeffSize partialCore; rw [sum_comm]; refine sum_le_sum fun i _ => ?_
  by_cases he : ∃ j∈t,i∈slots j
  · obtain ⟨j,hj,hi⟩ := he
    rw [sum_eq_single j,if_pos hi]
    · intro b _ hb; rw [if_neg (Finset.disjoint_right.mp (h hb) hi),norm_zero]
    exact fun hh => (hh hj).elim
  push Not at he
  exact (sum_eq_zero fun j hj => by simp [he j hj]).trans_le (norm_nonneg _)

section Bundle
variable {n : Side}

/-- Combine independent column majorants; no summing over the universe of
markers at a prescribed root. -/
theorem solo_bundle {q : ι → R.Mode} {X : ι → Support n} {P : BudgetPoint}
    {cap : V → ι → ℝ → Prop} {w c : V → ℝ} {K : ℝ}
    (funds : ∀ v, ∃ f : ι → ℝ, (∀ i, (q i).val = {v} → 0 ≤ f i ∧ cap v i (f i)) ∧
      SumBudget (fun i => if (q i).val = {v} then P.mass (X i) (f i) else 0) (c v))
    (hw : ∀ v, 0≤w v) (hK : ∀ v, w v*c v ≤ K) :
    ∃ f : ι → ℝ, (∀ i, 0 ≤ f i) ∧ (∀ i v, (q i).val = {v} → cap v i (f i)) ∧ Weighted q X P w 0 f K := by
  choose f hf h using funds
  let g i := if hi : ∃ v : V, (q i).val = {v} then f hi.choose i else 0
  have he i v (hi : (q i).val={v}) : g i = f v i := by
    unfold g; split
    next hh =>
      rw [show hh.choose = v from singleton_inj.mp (hh.choose_spec.symm.trans hi)]
    next hh => exact (hh ⟨_,hi⟩).elim
  have hg i : 0 ≤ g i := by
    unfold g; split
    next hh => exact (hf _ i hh.choose_spec).1
    exact le_rfl
  refine ⟨g,hg,fun i v hi => by simpa only [he i v hi] using (hf v i hi).2,fun v => ?_⟩
  refine Budget.mono (Budget.scale (h v) (hw v)) (fun i => ?_) (fun i => ?_) (hK v)
  · split
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (prod_nonneg fun v _ => hw v : 0≤Poly.toll w _) (hg i))
    exact le_rfl
  dsimp only; rw [add_zero]; split
  next hh =>
    by_cases hx : (q i).val={v}
    · simp [he i v hx, Poly.toll,hx, BudgetPoint.mass,mul_left_comm]
    have hn : ¬ ∃ u : V, (q i).val={u} := by
      rintro ⟨u,hu⟩; rw [hu] at hh; exact hx ((mem_singleton.mp hh).symm ▸ hu)
    simp [g,hn,hx]
  exact mul_nonneg (hw v) ((h v).1 i)

end Bundle

section Copy
variable (H : C.Makes) {A : Bands R (C.path.rep N p m)} {s : V} {v : C.label d} (h : Copied A s v)
  (hm : C.ref d ≤ m) (hN : m ≤ N)

abbrev allowance (C : Family G) (N p m) (v : C.label d) := col C m * (C.labels.level d).coeffSize (coord C N p m v).x

include H hm hN in
lemma rem_of_coord : (coord C N p m v).remBound 0 (C.path.rep N p m) (divisor C m) (allowance C N p m v) := by
  obtain ⟨a,b,ha,hb,he,hκ,hh,hg⟩ := (H.calibrated d N p (hm.trans hN)).cap m hm hN ((C.factory d N p).terminal.symm v)
  exact ⟨a,b,ha,hb,he.trans (mul_le_mul_of_nonneg_left (BasisCost.coeff_le _) (zero_le_one.trans (col_ge ..))),hκ,hh,hg⟩

include H hm hN h
lemma Copied.ex_budget (hx : BasisCost.extent (C.localSection d) ≤ (point C m).B) :
    let P := (C.path.rep N p m).p; let D := allowance C N p m v
    ∃ f : ℕ → ℝ, (∀ i, (A.rays i).val = {s} → 0 ≤ f i ∧ P.supBounds (A.origins s) (A.support i) (A.H i) (f i)) ∧
      SumBudget (fun i => if (A.rays i).val = {s} then P.mass (A.support i) (f i) else 0)
        ((1 + Real.exp P.supportExponent)*D) := by
  intro P D
  have hp : P = point C m := (H.wilson.represents _ p _ hN).vac
  obtain ⟨a,b,ha,hb,hd,_,⟨e,he,he'⟩,_⟩ := rem_of_coord (v:=v) H hm hN
  let S := coord C N p m v
  let F := C.labels.level d
  obtain ⟨slots,f,hf',hf,hr⟩ := h.ex
  let y := A.origins s
  let X := Sum.elim (fun _ : ℕ => (C.localSection d).footprint y) S.support
  let part i := partialCore F (slots i) S.x
  let k := Sum.elim (fun i => col C m * F.coeffSize (part i)) e
  have hcol := zero_le_one.trans (col_ge C m)
  have hD : 0≤D := (add_nonneg ha hb).trans hd
  have hk : SumBudget (fun i => P.mass (X i) (k i)) ((1+Real.exp P.supportExponent)*D) := by
    refine Budget.certify (fun i => ?_) fun t => ?_
    · cases i
      next => exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hcol (BasisCost.coeff_nonneg _))
      next i => exact he.1 i
    rw [← toLeft_disjSum_toRight (u:=t),sum_disjSum]
    have h1 : ∑ x∈t.toLeft,P.mass (X (.inl x)) (k (.inl x)) ≤ Real.exp P.supportExponent * D := by
      dsimp only [X,k,BudgetPoint.mass,Sum.elim_inl]; rw [←mul_sum,←mul_sum]
      gcongr
      · exact mul_nonneg hcol (sum_nonneg fun _ _ => BasisCost.coeff_nonneg _)
      · apply mul_le_of_le_one_right P.exponent_pos.le
        rw [hp]; exact_mod_cast BasisCost.small_footprint (C.localSection d) y hx
      · change col C m*_ ≤ D
        exact mul_le_mul_of_nonneg_left (pieces_sum F slots hf' t.toLeft S.x) hcol
    exact (add_le_add h1 (Budget.cap he t.toRight)).trans (by linarith only [hb,hd])
  let g i := if (A.rays i).val = {s} ∧ A.H i ≠ 0 then k (f i) else (0:ℝ)
  have he i (hi : (A.rays i).val = {s}) : P.supBounds y (A.support i) (A.H i) (g i) := by
    unfold g; split <;> rename_i hh
    · have hn := hr i hh
      cases hv : f i with
      | inl j => rw [hv] at hn; rw [hn.1,hn.2,hp]; exact (BasisCost.analytic _ (point C m) (part j) y (H.priced d m p hm y)).2
      | inr j => rw [hv] at hn; rw [hn.1,hn.2]
                 simpa only [P,k,y,Sum.elim_inr,zero_add] using Relocate.sup_translate (y:=y) (he' j)
    rw [show A.H i=0 by tauto]; exact supBounds_zero ..
  refine ⟨g, fun i hi => ⟨(he i hi).1,he i hi⟩, Budget.pull_le (q:=f)
    (p:=fun i => (A.rays i).val = {s} ∧ A.H i ≠ 0) hk ?_ ?_ hf ?_⟩
  · intro i; split
    next hh => exact mul_nonneg (Real.exp_pos _).le (he i hh).1
    exact le_rfl
  · intro i ht; contrapose! ht; simp [g,BudgetPoint.mass]; tauto
  intro i hh; simp only [if_pos hh.1,g,if_pos hh]
  have hn := hr i hh
  cases ht : f i with
  | inl j => rw [ht] at hn; rw [hn.1]; rfl
  | inr j =>
    rw [ht] at hn; rw [hn.1]; unfold BudgetPoint.mass
    refine mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (he' j).1
    apply mul_le_mul_of_nonneg_left _ P.exponent_pos.le
    exact_mod_cast Relocate.cover_shift ..

lemma Copied.gas_budget :
    let Q := C.path.rep N p m
    ∃ f : ℕ × ℕ → ℝ, (∀ i, (tags A i).val = {s} → 0 ≤ f i ∧ ∀ U, ‖A.entries i.1 i.2 U‖ ≤ f i) ∧
      SumBudget (fun i => if (tags A i).val = {s} then Q.p.mass (Multi.forced Q i) (f i) else 0)
        (divisor C m * allowance C N p m v) := by
  intro Q
  obtain ⟨a,b,ha,_,hd,hκ,_,⟨k,hk,he⟩⟩ := rem_of_coord (v:=v) H hm hN
  obtain ⟨f,hf,hr⟩ := h.forced
  let g i := if (tags A i).val = {s} ∧ A.entries i.1 i.2 ≠ 0 then k (f i) else 0
  have hg i : 0 ≤ g i := by unfold g; split; exact (he _).1; exact le_rfl
  have hk' := Budget.mono hk hk.1 (fun _ => le_rfl) (mul_le_mul_of_nonneg_left
    ((le_add_of_nonneg_left ha).trans hd) hκ.le)
  refine ⟨g, fun i hi => ⟨hg i,?_⟩, Budget.pull_le (q:=f)
    (p:=fun i => (tags A i).val = {s} ∧ A.entries i.1 i.2 ≠ 0) hk' ?_ ?_ hf ?_⟩
  · intro U; unfold g; split <;> rename_i hh
    · rw [(hr i hh).2]; exact (he (f i)).2 _
    rw [show A.entries i.1 i.2=0 by tauto]; simp
  · intro i; split
    next => exact mul_nonneg (Real.exp_pos _).le (hg i)
    exact le_rfl
  · intro i ht; contrapose! ht; simp [g,BudgetPoint.mass]; tauto
  intro i hh; simp only [if_pos hh.1,g,if_pos hh]
  rw [(hr i hh).1]; unfold BudgetPoint.mass
  apply mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (he (f i)).1
  apply mul_le_mul_of_nonneg_left _ Q.p.exponent_pos.le
  exact_mod_cast Relocate.cover_shift ..

end Copy

abbrev strength (F : Frames G) (d : ℕ) := BasisCost.slots (F.level d)+8
abbrev radius (C : Family G) (d : ℕ) (r : ℝ) (m : ℕ) := Mix.width C r (strength C.labels d) m

/-- This does not require separation. Prices at the designed final-or-smaller
rates at each marker; fixed family of labels can use different widths. -/
theorem copied_price {A : Bands R (C.path.rep N p m)} (H : C.Makes) {D : V → ℕ} {u : ∀ i, C.label (D i)}
    (h : ∀ i, Copied A i (u i)) (hm : ∀ i, C.ref (D i) ≤ m) (hN : m ≤ N)
    {w : V → ℝ} {c : V→ℝ} (hc : ∀ i, 0<c i) (hr : ∀ i,(C.labels.level (D i)).coeffSize (u i) ≤ c i)
    (hw : ∀ i, 0 ≤ w i) (price : ∀ i, w i ≤ radius C (D i) (c i) m)
    (room : ∀ i,BasisCost.extent (C.localSection (D i)) ≤ (point C m).B)
    (gate : (1+Real.exp (point C m).supportExponent)*gHat C m ≤ 1) :
    (∀ i, w i * ‖A.units i‖ ≤ 1) ∧ Spent single A w 0 (divisor C m) (gHat C m ^ 4) := by
  let Q := C.path.rep N p m; let g := gHat C m
  let k := fun i => strength C.labels (D i)
  have hg : 0 ≤ g := (gHat_pos C m).le
  have hp (i) : g^k i ≤ g^5 := pow_le_pow_of_le_one hg (gHat_le_one C m) (by unfold k strength; omega)
  have he (i) : w i * allowance C N p m (u i) ≤ g^k i :=
    (mul_le_mul_of_nonneg_right (price i) (mul_nonneg (zero_le_one.trans (col_ge C m)) (BasisCost.coeff_nonneg _))).trans
      (pays_coord C N p m (hc i) (k i) H (u i) (hr i) (hm i) hN)
  constructor
  · intro i; rw [(h i).unit]; exact (mul_le_mul_of_nonneg_left ((BasisCost.coord_le _ _).trans
      (le_mul_of_one_le_left (BasisCost.coeff_nonneg _) (col_ge ..))) (hw _)).trans ((he i).trans
        (pow_le_one₀ hg (gHat_le_one ..)))
  obtain ⟨f,hf,hf',hbudget⟩ := solo_bundle (fun i => (h i).ex_budget H (hm i) hN (room i)) hw (K:=g^4) fun i => (by
    let B := 1+Real.exp (point C m).supportExponent
    rw [(H.wilson.represents N p m hN).vac, mul_left_comm]
    apply (mul_le_mul_of_nonneg_left ((he i).trans (hp i)) (by unfold B; positivity : 0≤B)).trans
    calc
      B*g^5 = (B*g)*g^4 := by ring
      _ ≤ _ := mul_le_of_le_one_left (pow_nonneg hg _) gate)
  obtain ⟨F,hF,hF',hcost⟩ := solo_bundle (cap:=fun (_ : V) (i : ℕ×ℕ) b => ∀ U, ‖A.entries i.1 i.2 U‖ ≤ b) (fun i => (h i).gas_budget H (hm i) hN) hw (K:=divisor C m*g^4) fun i => (by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (((he i).trans (hp i)).trans
      (pow_le_pow_of_le_one hg (gHat_le_one C m) (by decide))) (divisor_pos ..).le)
  refine ⟨⟨f,hf,fun i hi j hj => ?_,hbudget⟩,⟨F,hF,fun i hi => ?_,hcost⟩⟩
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hi
    rw [hv] at hj; obtain rfl := mem_singleton.mp hj; exact hf' _ _ hv
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hi
  exact hF' _ v hv

end YM.Extra.Multi
