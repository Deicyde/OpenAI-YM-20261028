import YM.UVNext.FREE_STRESS_CERTIFICATE.Cube

/-! Character projection on the signed axes, and real-form span recovery on
the actual quotients. Parity tests stated over integers for finite certificates
(by Lean kernel evaluation). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Submodule Climb Table Work.A01 Next.UVStress Function Set
variable {G : Gauge} (F : Frames G) {d : ℕ} (H : (freeTable F).RealSpin)

def bit (t k : Axis) : ℤ := if k=t then -1 else 1
def zob (p : Plane) (t : Axis) := bit t p.val.1 * bit t p.val.2

def click (p : Plane) (a b : Axis) : Prop := p.val=(a,b) ∨ p.val=(b,a)
local instance (p : Plane) (a b : Axis) : Decidable (click p a b) := inferInstanceAs (Decidable (_ ∨ _))

set_option maxRecDepth 10000 in
lemma even_format : ∀ (p q : Plane) (a : Axis), (∀ t : Axis, zob p t * zob q t = bit t 0 * bit t a) →
    (a=0 ∧ p=q) ∨ ∃ k : Axis, k≠0 ∧ k≠a ∧ a≠0 ∧
      (click p 0 k ∧ click q a k ∨ click q 0 k ∧ click p a k) := by decide

set_option maxRecDepth 10000 in
lemma odd_format : ∀ (p q : Plane), ¬ (∀ t : Axis, zob p t * zob q t = bit t 0) := by decide

lemma eps_mirror_bit (t i : Axis) : eps (Signed.mirror t) i = (bit t i : ℝ) := by simp [eps,Signed.mirror,Signed.matrix_at,bit,eq_comm]

def swatch (d : ℕ) (u : Axis → ℤ) (v : (freeTable F).Field d) : Prop :=
  ∀ t, (freeTable F).mirror H d (Signed.mirror t) v = ((u t : ℤ):ℂ) • v

lemma unit_color (d : ℕ) : swatch F H d (fun _ => 1) ((freeTable F).unit d) := by simp [swatch]
lemma link_color (a b i k : Axis) (h : 4 ≤ d) : swatch F H d (fun t => bit t a*bit t b*(bit t i*bit t k))
    (link F d h a b i k) := by
  intro t
  rw [signed_link]; simp [Signed.mirror, eps, Signed.matrix_at,bit,eq_comm]
lemma first_color (a b i k c : Axis) : swatch F H 5 (fun t => bit t a*bit t b*(bit t i*bit t k)*bit t c)
    (first F a b i k c) := by
  intro t
  rw [signed_first]
  have he l : (Signed.mirror t).perm l=l := rfl
  simp_rw [he, eps_mirror_bit]
  push_cast; rfl

def Binary (a : Axis → ℤ) := ∀ t, a t=1 ∨ a t= -1
lemma binary_unit : Binary (fun _ => 1) := fun _ => Or.inl rfl
lemma binary_bit (k : Axis) : Binary (fun t => bit t k) := by intro t; by_cases he : k=t <;> simp [he,bit]
lemma binary_compose {a b : Axis → ℤ} (h : Binary a) (j : Binary b) : Binary (fun t => a t*b t) := by
  intro t; rcases h t with h|h <;> rcases j t with j|j <;> simp [h,j]
lemma binary_plane (p : Plane) : Binary (zob p) := binary_compose (binary_bit _) (binary_bit _)

-- Keep even when the input quotient has kernel at d=5.
private def sift (χ : Axis → ℤ) (d : ℕ) : List Axis → Module.End ℂ ((freeTable F).Field d)
  | [] => LinearMap.id
  | b::l => (LinearMap.id + ((χ b:ℤ):ℂ) • (freeTable F).mirror H d (Signed.mirror b)).comp (sift χ d l)

private lemma sift_on (l : List Axis) (χ u : Axis → ℤ) {v : (freeTable F).Field d} (hv : swatch F H d u v) :
    sift F H χ d l v = ((↑((l.map (fun i : Axis => 1+χ i*u i)).prod):ℂ)) • v := by
  induction l with
  | nil => simp [sift]
  | cons i l ih =>
    simp only [sift, LinearMap.comp_apply,ih, LinearMap.add_apply,LinearMap.id_coe,id_eq, LinearMap.smul_apply, 
      List.map_cons,List.prod_cons,Int.cast_mul, Int.cast_add,Int.cast_one]
    simp only [map_smul,show (freeTable F).mirror H d (Signed.mirror i) v = _ from hv i, smul_smul,← add_smul]
    congr 1; ring

private def beam (χ : Axis → ℤ) (d : ℕ) := sift F H χ d ([0,1,2,3]:List Axis)

private theorem locked {χ : Axis → ℤ} (h : Binary χ) {v} (hp : swatch F H d χ v) : beam F H χ d v = (16:ℂ) • v := by
  rw [beam,sift_on F H _ χ χ hp]
  have he (i) : 1+χ i*χ i=2 := by rcases h i with h|h <;> norm_num [h]
  simp_rw [he]; norm_num

private theorem excludes {χ u : Axis → ℤ} (h : Binary χ) (k : Binary u) (he : χ ≠ u) {v} (hp : swatch F H d u v) :
    beam F H χ d v=0 := by
  rw [beam,sift_on F H _ _ _ hp]
  have hw : (List.map (fun i => 1+χ i*u i) [0,1,2,3]).prod=0 := by
    apply List.prod_eq_zero
    rw [List.mem_map]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp he
    refine ⟨i,?_,?_⟩
    · fin_cases i <;> decide
    rcases h i with H|H <;> rcases k i with V|V <;> simp_all
  rw [hw]; simp

/-- It suffices to show containment on the generators of aligned parity.
`Surjective embed` and character swatch let this work without choosing coherent
lifts through the quotient. -/
theorem align (v : (freeTable F).Field d) (χ) (hc : Binary χ) (hx : swatch F H d χ v)
    (U : Submodule ℂ ((freeTable F).Field d)) (s : Set (Label G d)) (hs : span ℂ s = ⊤)
    (check : ∀ y∈s, ∃ t : Axis → ℤ, Binary t ∧ swatch F H d t (embed F d y) ∧ (χ=t → embed F d y∈U)) : v∈U := by
  obtain ⟨y,hy⟩ := covers F v
  let M := (beam F H χ d).comp (embed F d)
  have he : y∈U.comap M := by
    have hu : span ℂ s ≤ U.comap M := span_le.mpr fun i hi => by
      obtain ⟨t,hT,hL,hx⟩ := check i hi
      change beam F H χ d _ ∈ U
      by_cases ht : χ=t
      · subst t; rw [locked F H hc hL]; exact U.smul_mem _ (hx rfl)
      rw [excludes F H hc hT ht hL]; exact U.zero_mem
    exact hu (hs.symm ▸ mem_top)
  change beam F H χ d (embed F d y)∈U at he
  rw [hy,locked F H hc hx] at he
  have hm := U.smul_mem ((16:ℂ)⁻¹) he; rw [smul_smul] at hm; norm_num at hm; exact hm

/-- Surviving planes with off-diagonal parity are oriented only up to sign. -/
lemma click_link (p q : Plane) (a b i j : Axis) (hp : click p a b) (hq : click q i j) (h : 4 ≤ d)
    (U : Submodule ℂ ((freeTable F).Field d)) (he : link F d h a b i j∈U) : embed F d (two G d h p q)∈U := by
  change link F d h p.val.1 p.val.2 q.val.1 q.val.2 ∈ _
  rcases hp with hx|hx <;> rcases hq with hw|hw <;> simp only [hx,hw]
  exact he
  · rw [right_link F h a b i j]; exact U.neg_mem he
  · rw [left_link F h a b]; exact U.neg_mem he
  rw [right_link F h b a i j,left_link F h a b,neg_neg]; exact he

lemma click_first (p q : Plane) (a b i j k : Axis) (hp : click p a b) (hq : click q i j)
    (U : Submodule ℂ (FiveFields F)) (he : first F a b i j k∈U) : embed F 5 (mixed G 5 le_rfl p q k)∈U := by
  change first F p.val.1 p.val.2 q.val.1 q.val.2 k ∈ _
  rcases hp with hx|hx <;> rcases hq with hw|hw <;> simp only [hx,hw]
  exact he
  · rw [right_first F a b i j]; exact U.neg_mem he
  · rw [left_first F a b]; exact U.neg_mem he
  rw [right_first F b a i j,left_first F a b,neg_neg]; exact he

/-- Recover **real** generators whenever all classes are real. -/
theorem to_real (s : Set ((freeTable F).Field d)) (hs : ∀ y∈s,(freeTable F).conj H d y=y) (v) (hr : (freeTable F).conj H d v=v)
    (he : v∈span ℂ s) : v∈span ℝ s := by
  let P (y : (freeTable F).Field d) (_ : y∈span ℂ s) : Prop :=
    ∀ t : ℂ, t • y + (freeTable F).conj H d (t • y) ∈ span ℝ s
  have ht : P v he := by
    apply Submodule.span_induction (p:=P) _ _ _ _ he
    · intro x hx t
      rw [map_smulₛₗ,hs x hx, ← add_smul]
      have h : t+starRingEnd ℂ t=((2*t.re:ℝ):ℂ) := by
        apply Complex.ext <;> simp [two_mul]
      rw [h, show (((2*t.re:ℝ):ℂ) • x) = (2*t.re:ℝ) • x from (RCLike.real_smul_eq_coe_smul (K:=ℂ) (2*t.re) x).symm]
      exact (span ℝ s).smul_mem _ (subset_span hx)
    · intro _; simp
    · intro a b _ _ ha hb t
      rw [smul_add,map_add, add_add_add_comm]
      exact Submodule.add_mem _ (ha t) (hb t)
    intro t x _ hx u; rw [smul_smul]; exact hx (u*t)
  have hm := ht 1; rw [one_smul,hr] at hm
  have hl := (span ℝ s).smul_mem (1/2 : ℝ) hm; rw [← two_smul ℝ,smul_smul] at hl; norm_num at hl; exact hl

end YM.UVNext.FreeStress
