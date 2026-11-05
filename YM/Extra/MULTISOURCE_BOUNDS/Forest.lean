import YM.Extra.MULTISOURCE_BOUNDS.Bands
import YM.Work.G07.Calculus

/-!
# Budgets for distinct-address marked attachments (esp. simultaneous cutoff birth)

This is not a formula for the marked array. The hypothesis on its actual
entries is a connected-component majorant with every multiplicity assigned
an address. In `Birth` inputs to these composites may include
a list of terms at each cutoff name, and hard tests reducing the magnitude. Coverage must ensure a vacuum
factor in every charged forced component (pay one divisor). Even pure-contact
monomials and spectators at arbitrary positions count on the same terms.

This forest bound is for **nonrepeating** trees; in particular don't silently
use this count for all terms of a logarithm allowing repeats. Coefficient identities, unmarked normalization, retention of true
indicators/flags/support, vanishing on forbidden clauses etc. when constructing
such an overlay would be separate producer obligations.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Set Function Lattice RG Wilson Marker Overlay Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {ι α β V : Type*} {n : Side} {M : ℕ} {a b c γ : ℝ} {X : α → Support n} {f : α → ℝ}

lemma Hit_merge {Y : β → Support n} {g : β → ℝ} (h : Ac.Hit X M f a b) (hh : Ac.Hit Y M g a c) :
    Ac.Hit (Sum.elim X Y) M (Sum.elim f g) a (b+c) := by
  intro x; apply Budget.certify
  · rintro (i|i); exacts [(h x).1 i,(hh x).1 i]
  intro s; rw [← toLeft_disjSum_toRight (u:=s), sum_disjSum]
  exact add_le_add (Budget.cap (h x) _) (Budget.cap (hh x) _)

/-- Rooted sum of connected distinct-address composites paid by the site-hit
threshold, under explicit support and multiplicity conditions. No upper bound
on support diameter or truncation of the `tsum`. -/
theorem bundle_budget {mode : ι → Finset V} {o : V → Site n} {Y : ι → Support n}
    {packet : ι → Finset α} {g : ι → ℝ} (ha : 0 ≤ a) (hf : ∀ i, 0 ≤ f i)
    (h : Ac.Hit X M f (a+1) γ) (hc : ((M+M+1:ℕ):ℝ)^4*γ ≤ 1) (hγ : 0≤γ)
    (hb : 0≤b) (hg : ∀ i, 0≤g i) (hi : InjOn packet {i | 0<g i})
    (hp : ∀ i, 0<g i → Ac.Spark X (packet i) ∧ Y i ⊆ (packet i).biUnion X ∧
      (∀ v∈mode i, o v∈Y i) ∧ g i ≤ b*∏ j∈packet i, f j) :
    Rooted mode Y M a g (b*(Real.exp γ-1)) := by
  intro v
  refine Budget.pull_le (q:=packet) (p:=fun i => 0<g i ∧ v∈mode i)
    (Budget.scale (Ac.forest X M ha hf h hc hγ (o v)) hb) ?_ ?_ (hi.mono fun i he => he.1) ?_
  · intro i; split
    next => exact mul_nonneg (Real.exp_pos _).le (hg i)
    exact le_rfl
  · intro i he
    split at he <;> rename_i hx
    · exact ⟨(hg i).lt_of_ne (Ne.symm (right_ne_zero_of_mul he)),hx⟩
    exact (he rfl).elim
  intro i ⟨hg,hi⟩
  obtain ⟨hs,hu,hv,hy⟩ := hp i hg
  rw [if_pos hi,Ac.roots,if_pos ⟨hs,hu (hv v hi)⟩]
  apply (mul_le_mul (b := Real.exp (a*coverNumber M ((packet i).biUnion X))) ?_ hy hg.le (Real.exp_pos _).le).trans_eq
    (by ring)
  apply Real.exp_monotone; gcongr
  exact Corona.cover_mono hu M

variable [DecidableEq V] {R : Census V} {G : Gauge} {P : Rep G n} (A : Bands R P)

abbrev catalog (P : Rep G n) (Y : V → Support n) := Sum.elim (fun i => (P.activities.forced i).support) Y
abbrev composite (selected : ℕ × ℕ → Finset ℕ) (use : ℕ × ℕ → Finset α) (i : ℕ × ℕ) : Finset (ℕ ⊕ α) :=
    (selected i).disjSum (use i)
abbrev charged (ok : R.Mode → Prop) := {i : ℕ × ℕ | ok (tags A i) ∧ A.entries i.1 i.2 ≠ 0}

/-- A sufficient birth interface for higher terms (usually `ok=mixed`).
No assertion that such a simultaneous labelled support array exists with
the required exact evaluation and singleton history/calibration. `Y`
and `f` should contain/pay the complete stencils of the attaching terms;
there is no implicit absolute support bound for the output.
-/
structure Birth (ok : R.Mode → Prop) (v : α → V) (Y : α → Support n) (terms : α → Config G n → ℂ) : Prop where
  calm i : ok (A.rays i) → A.H i = 0
  forced : ∃ (selected : ℕ × ℕ → Finset ℕ) (use : ℕ × ℕ → Finset α), InjOn (composite selected use) (charged A ok) ∧
    ∀ i∈charged A ok, (tags A i).val=(use i).image v ∧ InjOn v (use i) ∧
      (selected i).Nonempty ∧ Ac.Spark (catalog P Y) (composite selected use i) ∧
      Multi.forced P i ⊆ (composite selected use i).biUnion (catalog P Y) ∧
      ∀ U, ‖A.entries i.1 i.2 U‖ ≤ (∏ j∈selected i, ‖P.activities.K j U‖) * ∏ j∈use i, ‖terms j U‖

lemma supBounds_zero (p : BudgetPoint) (X : Support n) (o) : p.supBounds o X (0 : Config G n → ℂ) 0 := by
  refine ⟨le_rfl,fun U _ l _ _ => ?_⟩
  rw [show leftDerivs (0 : Config G n → ℂ) l U = _ from Work.G07.left_const 0 l U]
  simp

variable {A}



theorem Birth.spent (ok : R.Mode → Prop) {q : α→V} {Y : α → Support n} {terms : α → Config G n → ℂ}
    (h : Birth A ok q Y terms) (H : A.Active) {w : V → ℝ} (hw : ∀ v,0 ≤ w v)
    {k : ℕ → ℝ} {K : α → ℝ} (hk : ∀ i, 0 ≤ k i ∧ ∀ U, ‖P.activities.K i U‖ ≤ k i)
    (hK : ∀ v, 0 ≤ K v ∧ ∀ U, ‖terms v U‖ ≤ K v) {κ δ : ℝ} (hκ : 0<κ) (hκ' : κ≤1)
    (ha : 0 ≤ P.p.supportExponent+δ)
    (hvac : Ac.Hit (fun i => (P.activities.forced i).support) P.p.B k (P.p.supportExponent+δ+1) (κ*a))
    (hterms : Ac.Hit Y P.p.B (fun v => w (q v) * K v) (P.p.supportExponent+δ+1) b)
    (hpos : 0 ≤ a+b) (hsmall : ((P.p.B+P.p.B+1:ℕ):ℝ)^4*(a+b) ≤ 1) :
    Spent ok A w δ κ (Real.exp (a+b) - 1) := by
  let f := Sum.elim (fun i => κ⁻¹*k i) (fun v => w (q v)*K v)
  have hf : ∀ i, 0 ≤ f i := Sum.rec (fun i => mul_nonneg (inv_pos.mpr hκ).le (hk i).1)
    (fun v => mul_nonneg (hw _) (hK v).1)
  have hb : Ac.Hit (catalog P Y) P.p.B f (P.p.supportExponent+δ+1) (a+b) := by
    refine Hit_merge ?_ hterms
    intro x
    convert Budget.scale (hvac x) (inv_pos.mpr hκ).le using 1
    · funext i; split_ifs <;> ring
    · rw [inv_mul_cancel_left₀ hκ.ne']
  obtain ⟨selected,use,hi,hh⟩ := h.forced
  let g (i : ℕ × ℕ) := if i∈charged A ok then (∏ j∈selected i, k j)* ∏ v∈use i,K v else 0
  have hg i : 0 ≤ g i := by
    unfold g; split
    next => exact mul_nonneg (prod_nonneg fun i _ => (hk i).1) (prod_nonneg fun i _ => (hK i).1)
    exact le_rfl
  have hot i (he : 0<Poly.toll w (tags A i)*g i) : i∈charged A ok := by by_contra h; rw [show g i = 0 from if_neg h,mul_zero] at he; exact (lt_irrefl _ he)
  refine ⟨⟨fun _ => 0,fun _ => le_rfl,fun i hi v _ => ?_, fun v => ?_⟩,
    ⟨g,hg,fun i he U => ?_,bundle_budget (o:=A.origins) ha hf hb hsmall hpos hκ.le
      (fun i => mul_nonneg (prod_nonneg fun v _ => hw v) (hg i)) (hi.mono fun i => hot i) ?_⟩⟩
  · rw [h.calm _ hi]; exact supBounds_zero ..
  · simpa using! Budget.zero (ι:=ℕ) (sub_nonneg.mpr (Real.one_le_exp hpos))
  · unfold g; split
    next h => exact ((hh i h).2.2.2.2.2 U).trans (mul_le_mul
      (prod_le_prod (fun i _ => norm_nonneg _) fun i _ => (hk i).2 U)
      (prod_le_prod (fun i _ => norm_nonneg _) fun i _ => (hK i).2 U) (prod_nonneg fun _ _ => norm_nonneg _)
      (prod_nonneg fun i _ => (hk i).1))
    next h => rw [show A.entries i.1 i.2=0 by by_contra ht; exact h ⟨he,ht⟩]; simp
  intro i ha; have he := hot i ha
  obtain ⟨hname,hun,hne,hs,hp,_⟩ := hh i he
  refine ⟨hs,hp,H.retained i.1 i.2 he.2, ?_⟩
  dsimp only [g]; rw [if_pos he, composite, prod_disjSum]; dsimp only [f,Sum.elim_inl,Sum.elim_inr]; rw [prod_mul_distrib]
  obtain ⟨j,hj⟩ := hne
  have h' i : k i ≤ κ⁻¹*k i := le_mul_of_one_le_left (hk i).1 ((one_le_inv₀ hκ).mpr hκ')
  have hA : (∏ j∈selected i,k j) ≤ κ*∏ j∈selected i, κ⁻¹*k j := by
    rw [← mul_prod_erase _ _ hj, ← mul_prod_erase _ _ hj,←mul_assoc, ←mul_assoc,mul_inv_cancel₀ hκ.ne',one_mul]
    exact mul_le_mul_of_nonneg_left (prod_le_prod (fun i _ => (hk i).1) fun i _ => h' i) (hk j).1
  dsimp only [Poly.toll]; rw [hname,prod_image hun,prod_mul_distrib]
  have h₁ : 0 ≤ ∏ v∈use i,w (q v) := prod_nonneg fun i _ => hw (q i)
  have h₂ : 0 ≤ ∏ v∈use i,K v := prod_nonneg fun i _ => (hK i).1
  rw [prod_mul_distrib] at hA; linarith only [mul_le_mul_of_nonneg_right hA (mul_nonneg h₁ h₂)]

end YM.Extra.Multi
