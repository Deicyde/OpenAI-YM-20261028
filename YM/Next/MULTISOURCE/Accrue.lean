import YM.Next.MULTISOURCE.Response
import YM.Next.MULTISOURCE.Swarm

/-!
# Mixed pricing *derived* from the response estimate

We do not price the Bell number of partitions by an exponential in rank.
Such a charge could sink the program. Pay by rooted input fees on one side
and by visiting length on the other. No exchanging support exponent for a
smaller exponent on every new level: `Raw` needs to have delivered an honest
exponent gain.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Marker Function Lattice Wilson MeasureTheory Filter Finset
open scoped Topology BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {G : Gauge} {c f : Side}


def current (w : ℝ) (k : Hot R → ℝ) := fun x : Hot R => w^x.sites.card*k x

structure Afield (P : BudgetPoint) (κ : ℝ) (o : V → Site c) (D : Hot R → Pulse G c) (k : Hot R → ℝ) (w : ℝ) : Prop where
  present i : Credit P 0 κ (i.sites.image o) (D i) (k i)
  paid (i : V) : (∑ t∈rootAt R i,current w k t) ≤ 1/4

lemma Afield.balance (P : BudgetPoint) (κ : ℝ) (o : V → Site c) (D : Hot R → Pulse G c) (w : ℝ)
    (p : V→ℝ) (k : Hot R→ℝ)
    (h : ∀ i, Credit P 0 κ {o i} (D (Hot.one R i)) (p i))
    (hh : ∀ i, w * p i ≤ 1/8)
    (ht : ∀ x : Hot R, 2 ≤ x.sites.card → Credit P 0 κ (x.sites.image o) (D x) (k x))
    (hx : ∀ i,(∑ t∈partners R i, current w k t) ≤ 1/8) :
    ∃ g : Hot R → ℝ, (∀ i : V, g (Hot.one R i)=p i) ∧ Afield P κ o D g w := by
  let g (x : Hot R) := if h : ∃ i, Hot.one R i=x then p h.choose else k x
  have he (i) : g (Hot.one R i)=p i := by
    unfold g; split <;> rename_i h
    · rw [(Hot.one_inj _ _).mp h.choose_spec]
    exact False.elim (h ⟨_,rfl⟩)
  have hA (x : Hot R) (hv : 2 ≤ x.sites.card) : g x = k x := by
    unfold g; split
    · rename_i h; obtain ⟨v,hv'⟩ := h; simp [← hv'] at hv
    rfl
  refine ⟨g,he,⟨fun i => ?_,fun i => ?_⟩⟩
  · by_cases H : 2 ≤ i.sites.card
    · rw [hA _ H]; exact ht i H
    have hf : 0 < i.sites.card := Finset.card_pos.mpr i.property
    obtain ⟨x,rfl⟩ := Hot.one_of_card (show i.sites.card=1 by omega)
    rw [he,Hot.sites_one,image_singleton]; exact h x
  have hs : (rootAt R i).erase (Hot.one R i)=partners R i := by
    ext p; simp only [partners,mem_erase, mem_filter,mem_rootAt]; constructor
    · rintro ⟨h,hx⟩; refine ⟨hx,?_⟩
      by_contra hh
      have hf : 0 < p.sites.card := card_pos.mpr p.property
      obtain ⟨a,rfl⟩ := Hot.one_of_card (show p.sites.card=1 by omega)
      simp only [Hot.sites_one, mem_singleton] at hx; exact h (hx ▸ rfl)
    rintro ⟨hx,h⟩; refine ⟨?_,hx⟩; intro e; rw [e] at h; simp at h
  rw [← add_sum_erase _ _ (by simp : Hot.one R i ∈ rootAt R i), hs]
  change _*g _+_≤_
  rw [Hot.sites_one, card_singleton,pow_one,he,Finset.sum_congr rfl (g:=current w k) (fun i hi => by
    unfold current; rw [hA _ (mem_filter.mp hi).2])]
  exact (add_le_add (hh i) (hx i)).trans (by norm_num)

section
variable {P : Rep G c} {L : ℝ} {w r b : ℝ}

/-! Refund enough with genuine winding costs to cover simultaneously.
     Below L is the *full price ratio contribution per marker* from engineering
     scaling; will also pay w/r. -/

def earned (P : BudgetPoint) (o : V → Site c) (L b : ℝ) (k : Hot R → ℝ) (x : Hot R) :=
    (L*b)^x.sites.card * fare P 2 (x.sites.image o) * ∑ T∈ blocksOf R x, ∏ i∈ T.sites,k i

lemma unblock (P : BudgetPoint) (o : V → Site c) (k : Hot R → ℝ) (L b r w κ : ℝ)
    (D : Hot (parts R) → Pulse G c) (hh : Spaced o P.B) (he : Spot P) (hx : 0 ≤ L) (hL : 0 ≤ b)
    (hr : 0 < r) (hw : 0 < w) (hy : 0 < κ) (hk : ∀ i, 0 ≤ k i)
    (H : ∀ i,(∑ t∈rootAt R i,current r k t) ≤ 1/4)
    (h : ∀ q : Hot (parts R),2≤ (unionOfHot q).sites.card →
      Credit P 2 κ ((unionOfHot q).sites.image o) (D q) (b^(unionOfHot q).sites.card * ∏ t∈ q.sites,k t))
    (HP : w*L*b/r ≤ Real.exp (P.B/64 : ℝ)) :
    let g := earned P o L b k
    (∀ x : Hot R, 2 ≤ x.sites.card → Credit P 0 κ (x.sites.image o) (ampl (fun _ => (L:ℂ)) (foldRows D) x) (g x)) ∧
      ∀ i,(∑ x ∈ partners R i, current w g x) ≤ 1/8 := by
  intro g
  have hs := hh.injective P.B_pos
  constructor
  · intro x hc
    have hf (i : Hot (parts R)) (hi : i ∈ blocksOf R x) :
        Credit P 0 κ (x.sites.image o) (D i) (fare P 2 (x.sites.image o) *
          (b^x.sites.card* ∏ j∈ i.sites,k j)) := by
      have he := (hu_chooses ..).mp hi
      rw [← he]; refine Credit.refund (h i (he.symm ▸ hc)) ?_
      rw [he, card_image_of_injective _ hs]; exact hc
    refine Credit.expand ((Credit.sums (blocksOf R x) D _ (x.property.image o) (le_refl (0:ℝ)) hy hf).scale
      (∏ _j∈ x.sites,(L:ℂ))) ?_
    change _ ≤ earned ..; unfold earned; simp_rw [← Finset.mul_sum,prod_const,norm_pow,Complex.norm_real, Real.norm_of_nonneg hx]; exact le_of_eq (by ring)
  intro i
  have hf (x : Hot R) (hi : x∈partners R i) : current w g x ≤ fare P 1 (x.sites.image o) := by
    let q := x.sites.card
    let d := fare P 2 (x.sites.image o)
    have hq := pays_parts (current r k) (fun i => mul_nonneg (by positivity : 0 ≤ r^i.sites.card) (hk i))
      (fun i => (H i).trans (by norm_num)) x
    have hg : r^q * (∑ i∈blocksOf R x, ∏ j∈i.sites, k j) ≤ 1 := by
      rw [Finset.mul_sum]; refine le_trans (le_of_eq (sum_congr rfl ?_)) hq
      exact fun i hi => part_cost x i hi r k
    have hW := mul_le_mul_of_nonneg_left hg (show 0 ≤ (w*L*b/r)^q * d from
      mul_nonneg (by positivity) (Real.exp_pos _).le)
    calc
      _ = ((w*L*b/r)^q * d)*(r^q * (∑ i∈blocksOf R x,∏ j∈i.sites, k j)) := by
        unfold current; dsimp only [g,earned]; change w^q*(_^q*d*_) = _
        rw [div_pow]; field_simp; ring
      _ ≤ (w*L*b/r)^q * d := by simpa using hW
      _ ≤ _ := radius_change x (mem_filter.mp hi).2 P he.1 hh _ (by positivity) HP
  exact (sum_le_sum hf).trans (root_campaign R i P hh he)
end

lemma move_book {S : StepData c f} {P : Rep G c} {Q : Rep G f}
    (o : V → Site c) (D : Hot R → Pulse G f) (k : Hot R → ℝ) (L w r b κ K : ℝ)
    (F : V → Pulse G c) (p : V→ℝ)
    {δ σ C Λ μ rho v : ℝ} (h : P.activities.Valid P.p δ rho) (hh : Q.Lawful σ C Λ μ v)
    (hb : S.IsKernel Q.beta G) (hv : P.eval=S.push Q.beta Q.eval)
    (hs : Spaced o P.p.B) (HE : Spot P.p) (hL : 0 < L) (hx : 0 ≤ b) (hr : 0 < r) (hw : 0 < w) (hy : 0 < κ)
    (HL : w*L*b/r ≤ Real.exp (P.p.B/64 : ℝ))
    (HI : ∀ i, w*p i ≤ 1/8 ∧ Credit P.p 0 κ {o i} (F i) (p i))
    (HP : Afield Q.p K (S.ratio.embed ∘ o) D k r)
    (HT : ∀ i : V,tangent P (F i)=(L:ℂ) • (S.push Q.beta (tangent Q (D (Hot.one R i)))))
    (HR : ∃ Z : Hot (parts R) → Pulse G c,
      (∀ i : V,(L:ℂ) • Z (Hot.one _ (Hot.one R i))=F i) ∧
      ∀ t : Hot (parts R), 2 ≤ (unionOfHot t).sites.card → Raw S P Q Z D b κ k o t) :
    ∃ (D' : Hot R → Pulse G c) (k' : Hot R → ℝ), (∀ i, D' (Hot.one R i)=F i ∧ k' (Hot.one R i)=p i) ∧
      Afield P.p κ o D' k' w ∧ ∀ t : R.Mode,(fun U => (many P R D' U).part t)=
        ((L:ℂ)^t.val.card) • S.push Q.beta (fun U => (many Q R D U).part t) := by
  obtain ⟨Z,H,hZ⟩ := HR
  let Y := ampl (fun _ => (L:ℂ)) (foldRows Z)
  have HJ i : Y (Hot.one R i)=F i := by
    unfold Y ampl
    rw [foldRows,Hot.sites_one, Finset.prod_singleton,singleton_blocks, sum_singleton]
    exact H _
  obtain ⟨Hq,Ht⟩ := unblock P.p o k L b r w κ Z hs HE hL.le hx hr hw hy
    (fun i => (HP.present i).2.2.2.1) HP.paid (fun i hh => (hZ i hh).2) HL
  obtain ⟨g,hg,hT⟩ := Afield.balance P.p κ o Y w p _ (fun i => by rw [HJ]; exact (HI i).2)
    (fun i => (HI i).1) Hq Ht
  refine ⟨Y,g,fun i => ⟨HJ i,hg i⟩,hT,fun t => ?_⟩
  have hV (i : V) : tangent P (Z (Hot.one _ (Hot.one R i)))=S.push Q.beta (tangent Q (D (Hot.one R i))) := by
    have ht := HT i; rw [← H, tangent_scale] at ht
    exact (smul_right_injective _ (by exact_mod_cast hL.ne')) ht
  have ht := account_lives S P Q Z D t k _ _ _ h hh HP.present hb hv hV fun i hi => (hZ i hi).1
  rw [← ht]; funext U
  unfold Y; rw [← amplify,dilation_part, prod_const]; rfl
end YM.Multi
