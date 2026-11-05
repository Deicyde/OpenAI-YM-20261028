import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Corona.Halo
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Forests
import YM.Work.B06



/-!
# True cover toll of joining supports along Gaussian edges

Extend existing connected covers (with any halos and path sites already in
place) across a bond. Keep the scale division: our row decay price at a
post-L fixed stage may have a VERY small rate. No difference assumption
across chosen histories; this covers on precisely the current torus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.GCC
open Function Finset Lattice Corona Grove
 
open scoped Topology BigOperators
variable {n : Side}
namespace Connector

def crossings (X Y : Support n) := (X ×ˢ Y).image (uncurry separation)
def gap (X Y : Support n) := if h : (crossings X Y).Nonempty then (crossings X Y).min' h else 0
lemma gap_le {X Y : Support n} {x y : Site n} (hx : x ∈ X) (hy : y∈Y) : gap X Y ≤ separation x y := by
  have he : separation x y ∈ crossings X Y := Finset.mem_image.mpr
    ⟨(x,y),mem_product.mpr ⟨hx,hy⟩,rfl⟩
  rw [gap,dif_pos (show (crossings X Y).Nonempty from ⟨_,he⟩)]; exact Finset.min'_le _ _ he
lemma taken {X Y : Support n} (hx : X.Nonempty) (hy : Y.Nonempty) : ∃ x∈X, ∃ y∈Y,gap X Y=separation x y := by
  have he : (crossings X Y).Nonempty := image_nonempty.mpr (hx.product hy)
  rw [gap,dif_pos he]
  obtain ⟨⟨i,j⟩,h₁,h₂⟩ := mem_image.mp (min'_mem _ he)
  exact ⟨i,(mem_product.mp h₁).1,j,(mem_product.mp h₁).2,h₂.symm⟩

def toll (B l : ℕ) := if l=0 then 0 else l/(B+1)+2

-- geometrically conservative pair charge. `line` is Corona's
-- bounded-geodesic construction with periodic endpoints (max distance).
private lemma link (x y : Site n) (B : ℕ) : coverNumber B ({x,y}:Support n) ≤ separation x y / (B+1)+2 := by
  let k := B+1; let t := separation x y/k + 1; let f b := line x y (k*b)
  let U := range (t+1); let s := U.image f
  have he (j : ℕ) (h : j≤t) : f j∈s := mem_image_of_mem _ (mem_range.mpr (by omega))
  have hh : f 0=x := by simp [f]
  have hd : f t=y := line_end x y (le_of_lt (Nat.lt_mul_div_succ (separation x y) (Nat.succ_pos B)))
  have hi : Ships s (B+B+1) := by
    have he' i (hi : i≤t) : Relation.ReflTransGen (Touch s (B+B+1)) (f 0) (f i) := by
      refine line_path _ _ (fun i h => he _ (h.trans hi)) (fun j hj => ?_)
      unfold f
      apply (line_dist x y _ _ ?_).trans
      · rw [Nat.mul_add,Nat.mul_one,Nat.add_sub_cancel_left]; unfold k; omega
      exact Nat.mul_le_mul_left _ (by omega)
    intro a ha b hb
    rcases mem_image.mp ha with ⟨i,hi,rfl⟩
    rcases mem_image.mp hb with ⟨j,hj,rfl⟩
    exact (Corona.sym (he' i (by have := mem_range.mp hi; omega))).trans (he' j (by have := mem_range.mp hj; omega))
  have hg : covers B ({x,y}:Support n) s := by
    refine ⟨?_, Corona.ship_halo B hi⟩
    refine (Finset.insert_subset ?_ (singleton_subset_iff.mpr ?_)).trans (halo_subset B s)
    · exact hh ▸ he 0 (Nat.zero_le t)
    exact hd ▸ he t le_rfl
  exact (list_cost B hg).trans (card_image_le.trans (by simp [k,t,U]))

lemma added {X Y : Support n} {x y : Site n} (hx : x∈X) (hy : y∈Y) (B : ℕ) :
    coverNumber B (X ∪ Y) ≤ coverNumber B X+coverNumber B Y+toll B (separation x y) := by
  unfold toll; split
  next he =>
    have hh := line_end x y (show separation x y ≤ 0 from he.le); rw [line_home] at hh; subst y
    rw [add_zero]; exact meets_sum hx hy B
  let Z := ({x,y}:Support n)
  have h₁ := meets_sum hx (show x∈Z from by simp [Z]) B
  have h₂ := meets_sum (show y∈X∪Z from by simp [Z]) hy B
  have hl : coverNumber B Z ≤ _ := link x y B
  have hc := cover_mono (union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right : X∪Y⊆(X∪Z)∪Y) B
  omega

lemma ratio (B u : ℕ) : (toll B u:ℝ) ≤ (u:ℝ)/(B+1)+(if u=0 then 0 else 2) := by
  rcases u.eq_zero_or_pos with he|he
  · rw [he]; simp [toll]
  simp only [toll,if_neg he.ne',Nat.cast_add,Nat.cast_ofNat,add_le_add_iff_right]
  have hx : ((u/(B+1):ℕ):ℝ)*((B:ℝ)+1) ≤ u := by exact_mod_cast (Nat.le_div_iff_mul_le (by omega : 0<B+1)).mp (le_refl (u/(B+1)))
  linarith [ (le_div_iff₀ (by positivity : (0:ℝ)< (B:ℝ)+1)).mpr hx ]

section
variable {V : Type} [DecidableEq V] (X : V → Support n)

def joins (B : ℕ) (j i : V) := toll B (gap (X i) (X j))

private lemma grow (B : ℕ) (T : Finset V) (h : ∀ i∈T,(X i).Nonempty) (m : ℕ) :
    ∀ (A : Finset V), A⊆T → ∀ f : Parent V, Good T A f → (T \ A).card=m →
      coverNumber B (T.biUnion X) ≤ coverNumber B (A.biUnion X)+
      ∑ i∈(T\A), (coverNumber B (X i) + joins X B i (f i)) := by
  induction m with
  | zero => intro A ha f hf he; obtain rfl := Finset.Subset.antisymm ha (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp he)); simp
  | succ m ih =>
    intro A ha f hf he
    obtain ⟨j,hj⟩ := hf.buds (card_pos.mp (he.symm ▸ Nat.succ_pos _))
    have hp := Buds.kids hj
    have hg := (mem_sdiff.mp hp).1
    have h₁ := Buds.roots hj
    let L := insert j A
    have ht : L ⊆ T := insert_subset hg ha
    have hs := ih L ht (cut f j) (hf.cut_at hp) (by unfold L; rw [leaves,card_erase_of_mem hp,he]; simp)
    obtain ⟨x,hx,y,hy,hb⟩ := taken (h _ (ha h₁)) (h _ hg)
    have hk := added (mem_biUnion.mpr ⟨f j,h₁,hx⟩ : x∈ A.biUnion X) hy B
    rw [← hb] at hk
    unfold L at hs; rw [leaves,biUnion_insert,union_comm] at hs
    have hu : ∑ i∈(T\A).erase j,(coverNumber B (X i)+joins X B i (cut f j i)) =
         ∑ i∈(T\A).erase j,(coverNumber B (X i)+joins X B i (f i)) := sum_congr rfl fun i hi => by
      rw [show cut f j i=f i from update_of_ne (ne_of_mem_erase hi) ..]
    rw [hu] at hs; rw [← sum_erase_add _ _ hp]; unfold joins at *; omega

/-- Charge union even if actual Z arguments omitted or lookup touches sites
other than `front`. Needs vertex supports themselves charged & nonempty (for
physical query supports retain anchors). Doesn't assert `path` support
small or replace a hard mask on reading that support. -/
lemma coverage {i : V} (B : ℕ) (T : Finset V) (h : ∀ i∈T,(X i).Nonempty) (hi : i∈T)
    (f : Parent V) (hf : Good T {i} f) :
    coverNumber B (T.biUnion X) ≤ ∑ j∈T,coverNumber B (X j)+
      ∑ j∈(T \ {i}), joins X B j (f j) := by
  have he := grow X B T h _ {i} (singleton_subset_iff.mpr hi) f hf rfl
  rw [sum_add_distrib,singleton_biUnion] at he
  have hk := sum_sdiff (f:=fun j => coverNumber B (X j)) (singleton_subset_iff.mpr hi); simp only [sum_singleton] at hk
  omega
end
end Connector
end YM.Primitives.GCC
