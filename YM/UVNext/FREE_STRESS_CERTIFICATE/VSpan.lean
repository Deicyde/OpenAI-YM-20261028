import YM.UVNext.FREE_STRESS_CERTIFICATE.Orbits
import YM.UVNext.FREE_STRESS_CERTIFICATE.Parity

/-! Signed-coordinate orbit computation for the polar weight-five space at one port. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin) (hG : G.Simple)
variable (v : Vectors H)

lemma perm_v (p : Wheels) (a : Axis) : ride F H 5 p (v.val a) = v.val (p a) := by
  have h := (show _ ∧ _ from v.property).2 (round p) a
  change ride F H 5 p (v.val a) = ∑ i : Axis, _ • v.val i at h
  rw [h,eps_column,eps_round]; simp [round]

lemma color_v (i : Axis) : swatch F H 5 (fun t => bit t i) (v.val i) := by
  intro t
  rw [v.property.2,eps_column,eps_mirror_bit]; push_cast; rfl

-- all pairs sum over both orders

def nose := singles (fun i => first F 0 i 0 i 0)
def chin := pairs (fun i k => first F i k i k 0)
def arms := pairs (fun j i => first F 0 i j i j)
def hands := pairs (fun j i => first F j i 0 i j)


include hG in
lemma original_v : v.val 0 ∈ span ℂ {nose F, chin F, arms F, hands F} := by
  let U := span ℂ ({nose F, chin F, arms F, hands F} : Set _)
  let V := U.comap (revolving F H 5)
  let χ (t : Axis) := bit t 0
  apply secure F H _ (fun p ht => by rw [perm_v,ht])
  apply align F H _ χ (binary_bit _) (color_v F H v _) V _ (spanFive hG)
  rintro _ (rfl|⟨i,k,rfl⟩|⟨i,k,c,rfl⟩)
  · rw [pin_unit]; exact ⟨fun _ => 1,binary_unit,unit_color F H 5,fun h => by
      have he := congr_fun h (0:Axis); norm_num [χ,bit] at he⟩
  · exact ⟨fun t => zob i t*zob k t,binary_compose (binary_plane i) (binary_plane k), link_color F H _ _ _ _ _,
      fun he => ((odd_format i k) fun t => congr_fun he.symm t).elim⟩
  refine ⟨fun t => zob i t*zob k t*bit t c,
    binary_compose (binary_compose (binary_plane i) (binary_plane k)) (binary_bit c),
    first_color F H _ _ _ _ c,fun h => ?_⟩
  have he (t) : zob i t*zob k t = bit t 0 * bit t c := by
    change _ = χ t * _
    rw [congr_fun h t]
    rcases binary_bit c t with hx|hx <;> simp_all
  rcases even_format i k c he with ⟨rfl,rfl⟩|⟨a,h1,h2,h3,⟨h4,h5⟩|⟨h4,h5⟩⟩
  · obtain ⟨⟨a,b⟩,hp⟩ := i
    change first F a b a b 0∈V
    change a<b at hp
    have hh : b≠0 := (lt_of_le_of_lt (Fin.zero_le _) hp).ne'
    by_cases ht : a=0
    · subst a; exact harvest_single F H (fun i => first F 0 i 0 i 0) b hh (fun p hp => by simp [hp]) U
        (subset_span (show nose F ∈ _ by simp))
    exact harvest_pair F H (fun i j => first F i j i j 0) a b ht hh hp.ne
      (fun p hw => by simp [hw]) U (subset_span (show chin F ∈ _ by simp))
  · exact click_first F i k _ _ _ _ _ h4 h5 V (harvest_pair F H (fun j i => first F 0 i j i j) c a h3 h1 h2.symm
      (fun p hw => by simp [hw]) U (subset_span (show arms F ∈ _ by simp)))
  exact click_first F i k _ _ _ _ _ h5 h4 V (harvest_pair F H (fun j i => first F j i 0 i j) c a h3 h1 h2.symm
    (fun p hw => by simp [hw]) U (subset_span (show hands F ∈ _ by simp)))

lemma realsing (f : Axis → FiveFields F) (h : ∀ i, (freeTable F).conj H _ (f i)=f i) :
    (freeTable F).conj H 5 (singles f)=singles f := by
  rw [single_eval,map_add,map_add]; simp_rw [h]
lemma realpair (f : Axis→Axis → FiveFields F) (h : ∀ i j, (freeTable F).conj H _ (f i j)=f i j) :
    (freeTable F).conj H 5 (pairs f)=pairs f := by
  rw [pair_eval]; simp_rw [map_add,h]

include hG in
lemma real_v : v.val 0 ∈ span ℝ {nose F, chin F, arms F, hands F} := by
  refine to_real F H _ ?_ _ (v.property.1 _) (original_v F H hG v)
  intro i hi; simp only [mem_insert_iff,mem_singleton_iff] at hi
  rcases hi with rfl|rfl|rfl|rfl
  refine realsing F H _ ?_; intro a; exact first_real ..
  all_goals refine realpair F H _ ?_; intro a b; exact first_real ..

end YM.UVNext.FreeStress
