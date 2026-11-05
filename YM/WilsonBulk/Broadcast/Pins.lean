import YM.WilsonBulk.Web.Volume

/-!
# Translation planting stems at all coarse origins (actual addresses)

Rank zero not planted. Semantics for budget on any e+d powers, used with a finite stem letter type
housing literal path occurrences. Collisions (wrap or lifted) cost exactly sums. Applies
also locally with root/test/pivot as retained leg; e.g. one mark; future assembler.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Topology Classical ENNReal BigOperators
open Function Filter Equiv Finset Lattice Laurent Bloch Pert.Bulk
variable {α β ι ξ : Type} {n : ℕ} {Λ : Side} {σ : ℝ}
-- translate one specific pattern including all positions

def hairs (u : Legs (Market α) n) (r : ℝ) : Text α n := fun v=> if ∃ z:Cover,v=roll z α ∘ u then r else 0
def curlies (u : Legs (Co Λ α) n) (r : ℝ) : Page (Co Λ α) n := fun v=> if ∃ z:Site Λ,v=rolls z α ∘ u then r else 0
lemma Pervasive.hairs (u : Legs (Market α) n) (r : ℝ) : Pervasive (hairs u r) := by
  intro z y; unfold Sheet.hairs
  congr 1; ext
  constructor
  · rintro ⟨a,ha⟩; refine ⟨a-z,?_⟩; have he : Injective (fun f : Legs (Market α) n=> roll z α ∘ f):= fun _ _ h=> funext fun i=> (roll z α).injective (congr_fun h i); apply he
    change roll z α ∘ y=roll z α ∘ (roll (a-z) α ∘ u); rw [ha]; ext1 x; simp only [comp_apply,roll_apply]; congr 1; abel
  rintro ⟨w,rfl⟩; rw [← Function.comp_assoc]; exact ⟨w+z,by rw [roll_add]; rfl⟩

-- a clean version using a local certificate on ALL letters. Choose σ arbitrarily.
def ribs (σ : ℝ) (r : ℝ) (u : Legs (Market α) n) := ∑ i : Fin n, |r| *Real.exp (σ*run (lawn α) (u i) u)
lemma ribs_nonneg (u : Legs (Market α) n) (r : ℝ) (σ : ℝ) : 0 ≤ ribs σ r u:= sum_nonneg fun _ _=> by positivity
lemma hairs_within (u : Legs (Market α) n) (σ r : ℝ) : Within (lawn α) σ (ribs σ r u) (hairs u r) := by
  refine ⟨ribs_nonneg ..,fun i x=> ?_⟩
  unfold rent; let z:=x.1-(u i).1; rw [tsum_eq_single (roll z α ∘ u)]
  · split
    next h =>
      rw [hairs,if_pos ⟨z,rfl⟩,← h, show run (lawn α) ((roll z α ∘ u) i) (roll z α ∘ u)=_ from Pervasive.run_roll ..]; apply ENNReal.ofReal_le_ofReal; unfold ribs; exact Finset.single_le_sum (fun j _=> mul_nonneg (abs_nonneg r) (Real.exp_pos (σ*run (lawn α) (u j) u)).le) (mem_univ i)
    exact bot_le
  intro y hy; split; next h =>
    unfold hairs; split
    next hh=>
      obtain ⟨w,rfl⟩:=hh; exfalso; apply hy; rw [show z=w from by unfold z; rw [← h]; simp only [comp_apply,roll_apply,add_sub_cancel_left]]
    simp [bill]
  rfl

lemma curls_pinned (u : Legs (Co Λ α) n) (r : ℝ) (v : Legs (Co Λ α) n) (i : Fin n) : curlies u r v=
    if v=rolls ((v i).1-(u i).1) α ∘ u then r else 0 := by
  unfold curlies; congr 1; ext; refine ⟨?_,fun h=>⟨_,h⟩⟩; rintro ⟨z,rfl⟩; simp only [Function.comp_apply,rolls_apply,add_sub_cancel_left]
lemma pin_roll (u : Legs (Market α) n) (z : Cover) : small Λ α ∘ (roll z α ∘ u)=rolls (wrap Λ z) α ∘ (small Λ α ∘ u) := funext fun _=> small_roll Λ _ z _
lemma hair_pin (u : Legs (Market α) n) (r : ℝ) (v : Legs (Market α) n) (i : Fin n) : hairs u r v=
    if v=roll ((v i).1-(u i).1) α ∘ u then r else 0 := by
  unfold hairs; congr 1; ext; refine ⟨?_,fun h=>⟨_,h⟩⟩; rintro ⟨z,rfl⟩; simp only [Function.comp_apply,roll_apply,add_sub_cancel_left]
lemma hairs_orates (u : Legs (Market α) n) (r : ℝ) : Orates (small Λ α) (hairs u r) (curlies (small Λ α ∘ u) r) := by
  intro i x v hx; let z:=x.1-(u i).1
  have hp : (v i).1-((small Λ α ∘ u) i).1=wrap Λ z:= by simp only [hx,z, small,Function.comp_apply,map_sub];
  rw [page_tsum,tsum_eq_single (roll z α ∘ u),curls_pinned _ _ v i,hp]; swap -- maybe order
  · intro y hy; split
    next h=> exact Eq.trans (hair_pin u r y i) (if_neg (by rw [h.1]; exact hy))
    exact rfl
  rw [pin_roll]; by_cases he : rolls (wrap Λ z) α ∘ (small Λ α ∘ u)=v; swap
  · rw [if_neg (Ne.symm he),if_neg fun h=> he h.2]
  have hk : (v i).2=(u i).2:= by rw [← he]; rfl
  have hz : (roll z α ∘ u) i=x:= by
    simp only [Function.comp_apply,roll_apply,z,add_sub_cancel]; exact Prod.ext rfl (by rw [hx] at hk; exact hk.symm)
  rw [if_pos he.symm,if_pos ⟨hz,he⟩, hairs, if_pos ⟨z,rfl⟩]

variable (T : β→Market α) [Fintype β]
def stem (V : Page β n) : Text α n := polish (∑ x:Legs β n,hairs (T ∘ x) (V x))
def stalk (V : Page β n) : Page (Co Λ α) n := polish (∑ x:Legs β n, curlies ((small Λ α) ∘ (T ∘ x)) (V x))
def mound (V : Page β n) (σ : ℝ) := ∑ x: Legs β n,ribs σ (V x) (T ∘ x)
lemma stem_price (V : Page β n) (σ : ℝ) : Within (lawn α) σ (mound T V σ) (stem T V) := (Within.sum _ (fun x _=> hairs_within (T ∘ x) σ (V x))).clean
lemma stem_style (V : Page β n) : Pervasive (stem T V) := (Pervasive.gather fun x _=> Pervasive.hairs (T ∘ x) (V x)).polished
lemma stem_due (c : Side) (V : Page β n) : Orates (small c α) (stem T V) (stalk T V) := by
  let a (v : Legs β n) := hairs (T∘ v) (V v); have hs i (_:i∈univ) : Within (lawn α) 0 (ribs 0 (V i) (T ∘ i)) (a i):= hairs_within ..
  exact (Orates.gather univ a _ (fun i _=> hairs_orates (Λ:=c) (T∘ i) (V i)) hs le_rfl).polished (Within.sum _ hs) le_rfl
end YM.WilsonBulk.Sheet
