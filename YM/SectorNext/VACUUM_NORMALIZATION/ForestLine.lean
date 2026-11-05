import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import YM.Complex.Columns
import YM.Next.FREE_KERNELS.Lifts


/-!
# Change of tree tag, additive tangent counting

Works on the actual periodic cut Forests incl degenerate sides. Keep
true `Step.used` & root tests. Build equivalence over ℤ (one copy per
key/color), for the determinant on exponential tangents. Quantitative
stencils/gaps and identification of flat rowwise precision family with
such a restriction are separate (in particular this doesn't assume or
export that the cut win matrices are tree independent when seeds are
*not* empty). Also pays exact #nt for the exponents/ledg3.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum.FlatTree
open Lattice Tree RG Wilson Precision Matrix Filter Function
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical
variable {c f : Side} {r : Ratio c f} (F H : Forest r) {K : Type*} [AddCommGroup K] {G : Gauge}

/-- Additive orientation convention. -/
def beam {n : Side} (U : Links (Per n) K) (d : Step) (x : Site n) := if d.neg then -U (d.used x) else U (d.used x)

def cab {n : Side} (U : Links (Per n) K) (x : Site n) : Walk → K
  | [] => 0
  | d::l => beam U d x + cab U (x+d.vec) l

def climb {n : Side} (t : Site n → K) : Links (Per n) K := fun i => t i.1 - t (i.1 + step i.2)

def leafWard (U : Links (Per f) K) (x) := -cab U x (F.hike x)

def erase (U : Links (Per f) K) := U + climb (leafWard F U)

def fleet (U : Links (Per f) K) (i : F.Free) := erase F U i.val

def blank (U : F.Free → K) (i : Edge (Site f)) := if h : i∈F.trunks then (0:K) else U ⟨i,h⟩

lemma cab_gauge (t : Site f → K) (U : Links (Per f) K) (x : Site f) (l : Walk) :
    cab (U+climb t) x l = t x + cab U x l -t (stop x l) := by
  induction l generalizing x with
  | nil => simp [cab, stop]
  | cons d l ih =>
    simp only [cab, ih, stop, beam, Pi.add_apply,climb]
    cases d with | mk a b => cases b <;> simp [Step.used,Step.vec,sub_eq_add_neg] <;> abel

lemma fleet_gauge (t : Site f → K) (U : Links (Per f) K) (h : ∀ x : Site c,t (r.embed x)=0) :
    fleet F (U+climb t) = fleet F U := by
  funext i; simp only [fleet,erase,climb, Pi.add_apply,leafWard,cab_gauge,F.hike_root,h,sub_zero,neg_add_rev]; abel

lemma trunk_clear (U : Links (Per f) K) (i : Edge (Site f)) (hi : i∈F.trunks) : erase F U i=0 := by
  obtain ⟨x,hx,rfl⟩ := (F.trunk_mem_iff _).mp hi
  have he : leafWard F U x = -beam U (F.up x) x + leafWard F U (x+(F.up x).vec) := by
    unfold leafWard; nth_rw 1 [Forest.hike]; rw [dif_pos hx,cab]; abel
  unfold erase climb; rw [Pi.add_apply]
  cases h : F.up x with | mk a b => cases b <;> rw [h] at he <;> simp only [beam,Step.used,Step.vec,Bool.false_eq_true,↓reduceIte,sub_add_cancel] at he ⊢ <;> first | (rw [sub_eq_add_neg, he]; abel)
lemma root_clear (U : Links (Per f) K) (x : Site c) : leafWard F U (r.embed x) = 0 := by
  unfold leafWard; rw [Forest.hike,dif_neg ?_,cab,neg_zero]
  intro H; exact H (by rw [Ratio.embed_parent])

lemma clear (U : Links (Per f) K) : blank F (fleet F U) = erase F U := by
  funext i; unfold blank fleet
  split; exact (trunk_clear F U i ‹_›).symm; rfl
lemma cleared (U : F.Free → K) : fleet F (blank F U) = U := by
  have h i : cab (blank F U) i (F.hike i)=0 := by
    induction i using Forest.hike.induct F with
    | case1 i hi ih =>
      have he : (F.up i).used i ∈ F.trunks := (F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩
      rw [Forest.hike,dif_pos hi,cab, ih,beam]; simp [blank,he]
    | case2 i hi => rw [Forest.hike,dif_neg hi,cab]
  funext i; unfold fleet erase climb leafWard
  rw [Pi.add_apply]; simp_rw [h]; unfold blank; simp [i.property]

lemma route_home (U : F.Free → K) : fleet F (blank H (fleet H (blank F U))) = U := by
  rw [clear,erase,fleet_gauge F (leafWard H (blank F U)) _ (fun x => root_clear ..),cleared]

/-- Also for scalar additive links. Gives #nt equality even between
arbitrary admitted forests e.g. c=1 f even. -/
def express (K : Type*) [AddCommGroup K] : (F.Free → K) ≃ (H.Free → K) where
  toFun U := fleet H (blank F U)
  invFun U := fleet F (blank H U)
  left_inv := route_home F H
  right_inv U := route_home H F U

lemma cab_add (U V : Links (Per f) K) (x : Site f) (l : Walk) : cab (U+V) x l=cab U x l+cab V x l := by
  induction l generalizing x with | nil => simp [cab] | cons d b ih =>
    simp only [cab,ih,beam,Pi.add_apply]; split <;> abel
lemma cab_scalar {P : Type*} [Ring P] [Module P K] (U : Links (Per f) K) (a : P) (x : Site f) (l : Walk) : cab (a•U) x l=a•cab U x l := by
  induction l generalizing x with | nil => simp [cab] | cons d b ih =>
    simp only [cab,ih,beam,Pi.smul_apply,smul_add]; split <;> simp

def linear (P K : Type*) [Ring P] [AddCommGroup K] [Module P K] : (F.Free → K) ≃ₗ[P] (H.Free → K) := {
    express F H K with
    map_add' := by
      intro U V; funext i
      have he : blank F (U+V) = blank F U+blank F V := by funext j; unfold blank; rw [Pi.add_apply]; split <;> simp
      unfold express; change fleet H (blank F (U+V)) i=(fleet H (blank F U)+fleet H (blank F V)) i; unfold fleet erase climb leafWard; rw [he]; simp_rw [Pi.add_apply,cab_add]; abel
    map_smul' := by
      intro a U; funext i
      have he : blank F (a • U) = a • blank F U := by funext j; unfold blank; rw [Pi.smul_apply]; split <;> simp
      unfold express; change fleet H (blank F (a•U)) i=(a • fleet H (blank F U) : H.Free → K) i; unfold fleet erase climb leafWard; rw [he]; simp only [Pi.add_apply,Pi.smul_apply,cab_scalar,smul_add,smul_neg,smul_sub] }

lemma same_free_card : Fintype.card F.Free = Fintype.card H.Free := by simpa using! (linear F H ℝ ℝ).finrank_eq

def sendKey (i : {x // leaf r x}) := (F.up i.val).used i.val

lemma used_inj : Function.Injective (sendKey F) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h
  have h1 := F.rise _ hx; have h2 := F.rise _ hy
  change (F.up x).used x=(F.up y).used y at h
  cases hk : F.up x with | mk a b =>
  cases hl : F.up y with | mk d e =>
  rw [hk] at h h1; rw [hl] at h h2
  cases b <;> cases e
  all_goals simp only [Step.used,Step.vec, Bool.false_eq_true,↓reduceIte,Prod.mk.injEq, sub_eq_add_neg] at h h1 h2
  all_goals obtain ⟨he,rfl⟩ := h
  all_goals first | exact Subtype.ext (show x=y from he) | skip
  all_goals try {exact Subtype.ext (add_right_cancel he)}
  all_goals exfalso
  · -- x=y-step a
    rw [he,neg_add_cancel_right] at h1; omega
  -- x-step a = y
  rw [he] at h1
  rw [←he,neg_add_cancel_right] at h2; rw [←he] at h1; omega

lemma count_clear : Fintype.card F.Free + Fintype.card (Site f) = Fintype.card (Edge (Site f)) + Fintype.card (Site c) := by
  have h1 : Fintype.card {x // leaf r x}=Fintype.card (↥F.trunks) := Fintype.card_congr (Equiv.ofBijective
    (fun i=> (⟨sendKey F i,(F.trunk_mem_iff _).mpr ⟨i,i.property,rfl⟩⟩ : ↥F.trunks))
    ⟨fun i j h => used_inj F (congr_arg Subtype.val h),fun ⟨i,hi⟩=> by
      obtain ⟨x,hx,rfl⟩ := (F.trunk_mem_iff _).mp hi; exact ⟨⟨x,hx⟩,rfl⟩⟩)
  have h2 : Fintype.card {x // ¬leaf r x} = Fintype.card (Site c) := Fintype.card_congr {
    toFun x := r.parent x.val
    invFun x := ⟨r.embed x,fun h=> h (by simp only [r.embed_parent])⟩
    left_inv := fun ⟨x,h⟩ => Subtype.ext (Classical.not_not.mp h).symm
    right_inv x := r.embed_parent x }
  have h3 : Fintype.card {x // leaf r x}+ Fintype.card {x // ¬ leaf r x}= Fintype.card (Site f) := by
    rw [Fintype.card_subtype_compl]; exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have h4 : Fintype.card F.Free = Fintype.card (Edge (Site f))-Fintype.card (↥F.trunks) := by
    exact Fintype.card_subtype_compl (fun x => x ∈ F.trunks)
  have h5 : Fintype.card (↥F.trunks) ≤ Fintype.card (Edge (Site f)) := Fintype.card_subtype_le _
  omega


variable (I : Type*)
abbrev Page (F : Forest r) := F.Free × I
abbrev AllKeys (n : Side) := Edge (Site n) × I

/-- Side-colors (including dummy dual components, or taking real
colorMat coordinate keys directly below). -/
def fluid (P : Type*) [CommRing P] : (Page I F → P) ≃ₗ[P] (Page I H → P) where
  toFun U i := linear F H P P (fun j => U (j,i.2)) i.1
  invFun U i := (linear F H P P).symm (fun j => U (j,i.2)) i.1
  left_inv U := by funext ⟨i,k⟩; exact congr_fun ((linear F H P P).symm_apply_apply (fun j => U (j,k))) i
  right_inv U := by funext ⟨i,k⟩; exact congr_fun ((linear F H P P).apply_symm_apply (fun j => U (j,k))) i
  map_add' U V := by
    funext i; change linear F H P P ((fun j => U (j,i.2))+(fun j=>V (j,i.2))) i.1=_; rw [map_add]; rfl
  map_smul' a U := by funext i; change linear F H P P (a•(fun j=>U (j,i.2))) i.1=_; rw [map_smul]; rfl

variable [DecidableEq I] [Fintype I]
omit [DecidableEq I] in
lemma pages : Fintype.card (Page I F)=Fintype.card (Page I H) := by simp [Page,same_free_card F H]

def roll (P : Type*) [CommRing P] : Matrix (Page I H) (Page I F) P := LinearMap.toMatrix' (fluid F H I P).toLinearMap










variable {I}
-- D is common full array (before restricting to non-tree links).
def slips {X : Type*} (D : Matrix X (AllKeys I f) ℝ) : Matrix X (Page I F) ℝ := of fun i j=>D i (j.1,j.2)

def negatives {X : Type*} (D : Matrix X (AllKeys I f) ℝ) (r : Ratio c f) := ∀ i k (t : Site f → ℝ), (∀ z : Site c,t (r.embed z)=0) →
    ∑ e : Edge (Site f), D i (e,k)*climb t e=0

omit [DecidableEq I] in
lemma slip_price {X : Type*} (D : Matrix X (AllKeys I f) ℝ) (U : Page I F → ℝ) :
    slips F D *ᵥ U = D *ᵥ fun i : AllKeys I f => blank F (fun a=> U (a,i.2)) i.1 := by
  funext i
  unfold mulVec dotProduct; rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  symm
  let P := Finset.univ.filter (fun e: Edge (Site f) => e∉F.trunks)
  let g (x : Edge (Site f)) := D i (x,k)*blank F (fun j=>U (j,k)) x
  change ∑ x,g x= _
  rw [← Finset.sum_subset (s₁:=P) (s₂:=Finset.univ) (Finset.subset_univ _) (f:=g) (by intro j _ h; unfold g blank; rw [dif_pos (by simpa [P] using h),mul_zero])]
  rw [Finset.sum_subtype P (p:=fun x=>x∉F.trunks) (fun j => by simp [P])]
  apply Finset.sum_congr rfl; intro j _; unfold slips g blank; rw [dif_neg j.property]; rfl







end YM.SectorNext.Vacuum.FlatTree
