import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Cask
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Season


set_option warningAsError false

/-!
# Rooted cost of canonical re-description, fixed challenge

Measure all intertwined parts of that challenge (dropping the other
Poly coefficients only IN THIS TEST). For the edited output bits themselves,
use the full merge calculation. Different challenges on the same output,
can choose prices differently but cannot change *labels or allocations*.
Here need input costs at least strong enough for an extra unit of burn on
both parks (others for landing the marker hit). Rescale the trees using
the Pack inventory.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Harvest
open Filter Function MeasureTheory RG Marker Wilson Lattice Multi Multi.Couples Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {I W : Type} [Fintype I] [DecidableEq I] [DecidableEq W] [Fintype W] {R : Census W}
variable {G : Gauge} {n : Side} (P : Rep G n)
variable (D : Hot R → Pulse G n) (Y : I → Support n) (tag : I → W) (F : I → Config G n → ℂ)
variable (L : R.Mode) (f : W→ℝ) (s : Poly R) (U : Config G n) (p : Pack n)

/-- Challenge lens zeros out all keys not requested at that tag list,
through a ring hom. No need high rank factorials. -/
def lens := Poly.price f (dilation R (fun w => if w∈L.val then 1 else 0) s)

omit [Fintype W] in
lemma under (x : R.Mode) :
    Poly.toll f x*‖((dilation R (fun w => if w∈L.val then 1 else 0)) s).part x‖ =
      if x.val ⊆ L.val then Poly.toll f x*‖s.part x‖ else 0 := by
  rw [dilation_part]
  by_cases he : x.val ⊆ L.val
  · rw [if_pos he, Finset.prod_eq_one (fun i hi => if_pos (he hi)),one_mul]
  rw [if_neg he]; obtain ⟨i,hi,hf⟩ := Finset.not_subset.mp he
  rw [Finset.prod_eq_zero hi (if_neg hf),zero_mul,norm_zero,mul_zero]

variable (t : I)
omit [Fintype I] [DecidableEq I] [Fintype W] in
lemma lens_pigment :
    lens L f (pigment R tag F U t)=if tag t∈L.val then f (tag t)*‖F t U‖ else 0 := by
  unfold lens pigment; rw [dilation_send, Poly.solo]
  change (∏ i∈{tag t},f i)*‖(∏ i ∈ {tag t}, (if i∈L.val then (1:ℂ) else 0)) * F t U‖ = _
  split <;> rename_i h <;> simp [h]

omit [Fintype W] in
lemma lit_price (g : Hot R → ℂ) (h : ∀ i,0<f i) :
    lens L f (lit R g) ≤ ∑ i : Hot R, if i.sites ⊆ L.val then Poly.toll f i.val * ‖g i‖ else 0 := by
  unfold lens lit; rw [map_sum]; apply (Poly.batch h _ _).trans; apply sum_le_sum; intro i _
  by_cases he : i.sites ⊆ L.val
  · rw [if_pos he,dilation_send,show (∏ x ∈ i.sites, if x∈L.val then (1:ℂ) else 0) = 1 from Finset.prod_eq_one
      (fun x hx => if_pos (he hx)),one_mul, Poly.solo]
  obtain ⟨x,hx,h⟩:= Finset.not_subset.mp he
  rw [if_neg he,dilation_send,show (∏ x ∈ i.sites, if x∈L.val then (1:ℂ) else 0) = 0 from Finset.prod_eq_zero hx (if_neg h),
    zero_mul,Poly.send_zero, Poly.zero_price]

omit [Fintype W] in
lemma lens_pack {K : Pack n→ℝ} (h : ∀ i,0<f i) (hk : ∀ i V, ‖incumbent P V i‖≤K i) {g : Hot R →Pack n→ℝ}
    (he : ∀ x V,‖(D x).2 p V‖≤g x p) : lens L f (Alphabet.share P D U p) ≤ K p +
    (∑ x ∈ univ.filter (fun x : Hot R => x.sites ⊆ L.val), Poly.toll f x.val*g x p) := by
  unfold Alphabet.share lens; rw [map_add]; apply (Poly.addition h ..).trans
  refine add_le_add ?_ ((lit_price L f _ h).trans ?_)
  · rw [dilation_send,Poly.solo,Poly.quiet_toll,show (∏ v ∈ R.quiet.val, _)=(1:ℂ) from rfl,one_mul,one_mul]; exact hk _ U
  rw [Finset.sum_filter]; apply sum_le_sum; intro i _; split
  · exact mul_le_mul_of_nonneg_left (he i _) (Poly.worth h _).le
  exact le_rfl

omit [DecidableEq I] [Fintype W] in
lemma donors (h : ∀ i,0<f i) (g : Pack n → ℝ) (k : I → ℝ)
    (hg : ∀ p : Pack n,0 ≤ g p ∧ lens L f (Alphabet.share P D U p) ≤ g p)
    (hk : ∀ i,0 ≤ k i ∧ lens L f (pigment R tag F U i) ≤ k i) :
    lens L f (fusion R P D Y tag F U p) ≤ storage Y g k p := by
  unfold lens fusion till storage; rw [map_sum]; refine (Poly.batch h ..).trans ?_
  unfold trays
  apply sum_le_sum; intro i hi; unfold earning; split
  · rw [map_prod]; apply (Poly.multiple h ..).trans
    refine prod_le_prod (fun i _ => Poly.nonnegative h _) fun j _ => ?_
    cases j; exact (hg _).2; exact (hk _).2
  rw [map_zero,Poly.zero_price]; exact prod_nonneg (fun i _ => by cases i; exact (hg _).1; exact (hk _).1)

/-- Complete local input to query lens pricing. Crate at EACH site on Q,
stronger support prices facing mixed marks. -/
structure Apparent (X : W→Support n) (r κ : ℝ) : Prop where
  wage i : 0 < f i
  rent : 0≤r
  cap : 0<κ
  wall : (P.p.B+P.p.B+1:ℕ)^4*(κ:ℝ) ≤ 1/32
  markers : ∃ (g : Pack n→ℝ) (s : I→ℝ),
    (∀ p : Pack n,0≤g p ∧ ∀ U,lens L f (Alphabet.share P D U p) ≤ g p) ∧
    (∀ i,0≤s i ∧ ∀ U,lens L f (pigment R tag F U i) ≤ s i) ∧
    (∀ x : Site n, crate Pack.zone P.p.B (P.p.supportExponent+r+1) g x ≤ 2*κ) ∧
    ∀ x : Site n, crate Y P.p.B (P.p.supportExponent+r+1) s x ≤ 1/(2*((P.p.B+P.p.B+1:ℕ)^4:ℕ))
-- X unused

omit [DecidableEq I] [Fintype W] in
lemma reimburse {X : W→Support n} (i : Hot R) {κ σ w r : ℝ} (hc : School R P D Y tag F X)
    (he : P.activities.Valid P.p σ w) (h : Apparent P D Y tag F i.val f X r κ) (hi : ∀ v∈i.sites,(X v).Nonempty) :
    ∃ b : Pack n → ℝ,(∑ p,burn P.p r p.zone*b p)≤ κ*(128/Poly.toll f i.val) ∧
      ∀ p, Legible P.p p ((new R P D Y tag F i).2 p) ∧ ((new R P D Y tag F i).2 p≠ 0 → i.sites.biUnion X ⊆ p.zone) ∧
        0≤b p ∧ ∀ U, ‖(new R P D Y tag F i).2 p U‖≤b p := by
  obtain ⟨hf,hr,hκ,hW,g,s,hg,hs,hG,hS⟩ := h
  let c := storage Y g s
  let A := i.sites.biUnion X
  let v := Poly.toll f i.val
  let z := new R P D Y tag F i
  let b (p : Pack n) := if A⊆p.zone then c p/v else 0
  have hp (p : Pack n) : 0 ≤ c p := sum_nonneg (fun j _ => prod_nonneg (fun i _ => by cases i; exact (hg _).1; exact (hs _).1))
  have hv : 0<v := Poly.worth hf _
  obtain ⟨j,hj⟩ := (i.property : i.sites.Nonempty); obtain ⟨x,hx⟩ := hi _ hj
  have hA : x∈A := mem_biUnion.mpr ⟨j,hj,hx⟩
  obtain hh := garage Y P.p.B g s (add_nonneg P.p.exponent_pos.le hr) hκ (fun _ => (hg _).1) (fun _ => (hs _).1) hW hG hS x
  refine ⟨b,?_,fun p => ?_⟩
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hv).mpr; rw [Finset.sum_mul,mul_comm κ 128]
    rw [crate,Finset.sum_filter] at hh
    apply le_trans ?_ hh; apply sum_le_sum; intro p _
    unfold b; split <;> rename_i h
    · rw [if_pos (h hA),mul_assoc,div_mul_cancel₀ _ hv.ne']; rfl
    rw [mul_zero,zero_mul]; split; exact mul_nonneg (Real.exp_pos _).le (hp _); exact le_rfl
  obtain ⟨hl,hq⟩ := hc.legislates p he i
  have hc (h : z.2 p≠0) : A⊆p.zone := biUnion_subset.mpr (hq h)
  refine ⟨hl,hc,?_,fun U => ?_⟩
  · unfold b; split; exact div_nonneg (hp _) hv.le; exact le_rfl
  by_cases h : A⊆p.zone
  · unfold b; rw [if_pos h]; refine (le_div_iff₀ hv).mpr ?_
    let u := fusion R P D Y tag F U p
    have hz := donors P D Y tag F i.val f U p hf g s (fun p => ⟨(hg _).1,(hg p).2 _⟩) (fun j => ⟨(hs _).1,(hs j).2 _⟩)
    rw [mul_comm]; change Poly.toll f i.val*‖u.part i.val‖ ≤ _
    apply le_trans ?_ hz; unfold lens
    let l := dilation R (fun w => if w∈i.sites then (1:ℂ) else 0)
    have ht : Poly.toll f i.val*‖(l u).part i.val‖=Poly.toll f i.val*‖u.part i.val‖ :=
      (under i.val f _ i.val).trans (if_pos (subset_refl _))
    exact ht ▸ Poly.member (R:=R) hf i.val (l u)
  unfold b; rw [if_neg h,show (new ..).2 p=0 from not_not.mp (mt hc h),Pi.zero_apply,norm_zero]
end YM.AnalyticNext.GridStop.Harvest
