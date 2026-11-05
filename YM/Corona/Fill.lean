import YM.Lattice.Support


/-!
# Cover currency

Native radius max graph.

Works at the true
period, no injectivity in halo.

Labels still use true path lengths for other tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lattice.Corona
open Relation
variable {n : Side}

abbrev Touch (D : Support n) (b : ℕ) (x y : Site n) := x ∈ D ∧ y ∈ D ∧ separation x y ≤ b

abbrev Ships (D : Support n) (b : ℕ) := ∀ x ∈ D, ∀ y ∈ D, ReflTransGen (Touch D b) x y

lemma sym {D : Support n} {b x y} (h : ReflTransGen (Touch D b) x y) : ReflTransGen (Touch D b) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hh ih => exact .head ⟨hh.2.1,hh.1,(separation_comm ..) ▸ hh.2.2⟩ ih

lemma grow {D E : Support n} (hh : D ⊆ E) {x y b} : ReflTransGen (Touch D b) x y → ReflTransGen (Touch E b) x y :=
  ReflTransGen.mono (fun _ _ h ↦ ⟨hh h.1,hh h.2.1,h.2.2⟩) _ _

lemma lap (v : Cover) (i : Axis) : (lift (wrap n v) i).natAbs ≤ (v i).natAbs := by
  let k : ℤ := v i
  change (k:ZMod n.val).valMinAbs.natAbs ≤ k.natAbs
  by_cases h : k.natAbs ≤ n.val/2
  · by_cases hh : 0≤k
    · conv_lhs => rw [show k = (k.natAbs:ℤ) by omega,Int.cast_natCast,ZMod.valMinAbs_natCast_of_le_half h,Int.natAbs_natCast]
    conv_lhs => rw [show k = -(k.natAbs:ℤ) by omega,Int.cast_neg,ZMod.natAbs_valMinAbs_neg,Int.cast_natCast,ZMod.valMinAbs_natCast_of_le_half h, Int.natAbs_natCast]
  exact (ZMod.natAbs_valMinAbs_le _).trans (le_of_lt (lt_of_not_ge h))

/-- explicit lattice line, saturated at target. -/
def line (x y : Site n) (b : ℕ) := x + wrap n (fun i => max (-(b:ℤ)) (min (b:ℤ) (lift (y-x) i)))

@[simp] lemma line_home (x y : Site n) : line x y 0=x := by
  unfold line
  rw [show (fun i => max _ (min _ (lift (y-x) i))) = (0:Cover) by ext; simp]
  simp

lemma line_end (x y : Site n) {b : ℕ} (h : separation x y ≤ b) : line x y b=y := by
  unfold line; rw [show (fun i => max _ (min _ (lift (y-x) i))) = lift (y-x) by
    ext i; have H := component_le (y-x) i |>.trans (show pdist (y-x) ≤ b from (show separation y x ≤ b from (separation_comm x y) ▸ h)); omega]
  rw [wrap_lift]; abel

lemma line_dist (x y : Site n) (i j : ℕ) (h : i≤j) : separation (line x y i) (line x y j) ≤ j-i := by
  unfold separation line; rw [add_sub_add_left_eq_sub,← map_sub]
  apply Finset.sup_le; intro k _; apply (lap ..).trans; rw [Pi.sub_apply]; omega

lemma halo_mono {X D : Support n} {a b : ℕ} (h : a≤b) (ht : X ⊆ D) : halo a X ⊆ halo b D := fun _ he ↦
  let ⟨x,h1,h2⟩ := halo_spec.mp he; halo_spec.mpr ⟨x,ht h1,h2.trans h⟩

lemma line_path {F : ℕ → Site n} {D : Support n} (b R : ℕ) (hh : ∀ i ≤ R,F i∈D) (hw : ∀ i < R,separation (F i) (F (i+1))≤ b) :
    ReflTransGen (Touch D b) (F 0) (F R) := by
  induction R with
  | zero => exact .refl
  | succ R ih =>
    exact (ih (fun i hi => hh i (by omega)) fun i hi => hw i (by omega)).tail
      ⟨hh R (by omega), hh (R+1) le_rfl, hw _ (by omega)⟩

lemma ship_halo {D : Support n} (b : ℕ) (h : Ships D (b+b+1)) : Ships (halo b D) 1 := by
  have loc (x : Site n) (hx : x ∈ D) (y) (hh : separation x y ≤ b) : ReflTransGen (Touch (halo b D) 1) x y := by
    have hg (i : ℕ) (hi : i≤b) : line x y i ∈ halo b D := halo_spec.mpr ⟨x,hx,
      (show separation x (line x y i) ≤ i by simpa only [line_home,Nat.sub_zero] using line_dist x y 0 i (Nat.zero_le _)).trans hi⟩
    simpa only [line_home,line_end x y hh] using
      line_path 1 b hg fun i _ => (line_dist x y i (i+1) (by omega)).trans (by omega)
  intro x hx y hy
  obtain ⟨a,ha,ha'⟩ := halo_spec.mp hx; obtain ⟨c,hc,hc'⟩ := halo_spec.mp hy
  apply (sym (loc a ha x ha')).trans; refine ReflTransGen.trans ?_ (loc c hc y hc')
  have H : ∀ i j,Touch D (b+b+1) i j → ReflTransGen (Touch (halo b D) 1) i j := by
    rintro i j ⟨hi,hj,hz⟩
    rw [← line_end i j hz]; nth_rewrite 1 [← line_home i j]
    apply line_path
    · intro k hk
      by_cases h : k ≤ b
      · apply halo_spec.mpr; refine ⟨i,hi,?_⟩
        have H := line_dist i j 0 k (Nat.zero_le _); rw [line_home, Nat.sub_zero] at H; exact H.trans h
      apply halo_spec.mpr; refine ⟨j,hj,?_⟩
      have H := line_dist i j k _ hk; rw [line_end i j hz, separation_comm] at H; omega
    intro k _; exact (line_dist i j k (k+1) (by omega)).trans (by omega)
  have he : ∀ a c,ReflTransGen (Touch D (b+b+1)) a c → ReflTransGen (Touch (halo b D) 1) a c := by
    intro A C hs; induction hs with
    | refl => exact .refl
    | tail _ hj IH => exact IH.trans (H _ _ hj)
  exact he _ _ (h _ ha _ hc)

lemma halo_ship {D : Support n} (b : ℕ) (h : Ships (halo b D) 1) : Ships D (b+b+1) := by
  intro x hx y hy
  have h' : ∀ u v, ReflTransGen (Touch (halo b D) 1) u v → ∀ i∈D,separation i u ≤ b →
      ∀ j∈D,separation j v ≤ b → ReflTransGen (Touch D (b+b+1)) i j := by
    intro u v hh; induction hh with
    | refl =>
      intro i hi hv j hj hw
      have hh := separation_triangle i u j; rw [separation_comm u j] at hh
      exact .single ⟨hi,hj,by omega⟩
    | @tail v w _ hh IH =>
      intro i hi hv j hj hj'
      obtain ⟨z,hz,hz'⟩ := halo_spec.mp hh.1
      refine (IH _ hi hv _ hz hz').tail ⟨hz,hj,?_⟩
      have hu := separation_triangle z v j
      have ha := separation_triangle v w j; have H := hh.2.2
      rw [separation_comm w j] at ha; omega
  exact h' x y (h x (halo_subset b D hx) y (halo_subset b D hy)) x hx (by simp) y hy (by simp)

lemma list_cost {D X : Support n} (M : ℕ) (h : covers M X D) : coverNumber M X ≤ D.card := by
  classical
  exact Nat.find_min' _ ⟨D,h,rfl⟩

lemma box_size (n : ℕ) : (box n).card = (n+n+1)^4 := by
  rw [box,Pi.card_Icc]; simp [Int.card_Icc]; omega

lemma halo_size (D : Support n) (M : ℕ) : (halo M D).card ≤ D.card * (M+M+1)^4 := by
  let f := fun p : Site n × Cover => p.1+wrap n p.2
  have h : halo M D ⊆ (D ×ˢ box M).image f := by
    intro i hi
    obtain ⟨x,hx,he⟩ := halo_spec.mp hi; rw [separation_comm,separation] at he
    refine Finset.mem_image.mpr ⟨(x,lift (i-x)), Finset.mem_product.mpr ⟨hx,box_test.mpr ⟨fun j => ?_,fun j => ?_⟩⟩, by simp [f]⟩
    all_goals have H := (component_le (i-x) j).trans he; dsimp only; omega
  exact (Finset.card_le_card h).trans ((Finset.card_image_le).trans (by rw [Finset.card_product,box_size]))

lemma pays (D : Support n) (M : ℕ) : D.card ≤ coverNumber M D*(M+M+1)^4 := by
  obtain ⟨A,h1,h2⟩ := coverNumber_realized M D
  exact (Finset.card_le_card h1.1).trans ((halo_size A M).trans (by rw [h2]))

end YM.Lattice.Corona
