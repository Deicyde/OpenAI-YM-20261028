import YM.Extra.WILSON_STARTUP.Channels

/-!
# Forced packet geometry and genuine energy payoffs

At the top use flags joined when their full 2B balls overlap, and sum owed
terms within B from a member flag, once, even in channels with reflected base
shifts. Eligibility will test exact flags in the 2B territory, but membership
and pairwise nonoverlap/coverage have to be checked separately. No order on
witness flags in the assignment. For the price bound it even suffices to use
large-chord contributions from one orientation (these touch all its corners).
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter RG Wilson Lattice Ac
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} (c : Clip) (b : BudgetPoint)

def pad (x : Site n) : Support n := halo (2*b.B) {x}
def region (D : Support n) := D.biUnion (pad b)
def parts (D : Support n) := Parts (pad b) D

lemma mem_pad (x y : Site n) : x ∈ pad b y ↔ separation y x ≤ 2*b.B := by simp [pad,halo_spec]

lemma halo_region (D : Support n) : halo b.B D ⊆ region b D := by
  intro z hz; obtain ⟨x,hx,he⟩ := halo_spec.mp hz
  exact Finset.mem_biUnion.mpr ⟨x,hx,(mem_pad ..).mpr (by omega)⟩

lemma subset_region (D : Support n) : D ⊆ region b D := fun _ hz => halo_region b _ (halo_subset _ _ hz)

lemma region_test {D : Support n} {x : Site n} (hx : x ∈ halo b.B D) : halo b.B {x} ⊆ region b D := by
  intro z hz
  obtain ⟨y,hy,h⟩ := halo_spec.mp hx
  obtain ⟨q,hq,h'⟩ := halo_spec.mp hz; rw [Finset.mem_singleton] at hq; subst q
  refine Finset.mem_biUnion.mpr ⟨y,hy,(mem_pad ..).mpr ?_⟩; have := separation_triangle y x z; omega

lemma coverage (D : Support n) {q : Support n} (hq : q ∈ parts b D) : region b q ∩ D = q := by
  have hQ := Ac.lives (pad b) D hq
  ext z; rw [Finset.mem_inter]
  refine ⟨?_,fun h => ⟨subset_region b q h,hQ.1 h⟩⟩
  rintro ⟨h,hz⟩
  obtain ⟨y,hy,hY⟩ := Finset.mem_biUnion.mp h
  have he := Ac.contains (pad b) hq y hy
  have hb : bonds (pad b) D y z := ⟨hQ.1 hy,hz,z,hY,(mem_pad ..).mpr (by simp)⟩
  rw [← he]; exact (bright ..).mpr ⟨hz,.single hb⟩

def charge (D : Support n) (U : Config G n) := share * ∑ i : Key n,
    if i.native ∈ halo b.B D then Key.owed c b i U else 0

theorem charge_sum (h : Decent c b) (U : Config G n) :
    ∑ q ∈ parts b (flags b.threshold U),charge c b q U = share * ∑ i : Key n,Key.owed c b i U := by
  let D := flags b.threshold U
  unfold charge; rw [← Finset.mul_sum,Finset.sum_comm]; congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hx : i.native ∈ halo b.B D
  · obtain ⟨x,hx,he⟩ := halo_spec.mp hx
    let Y := burst (pad b) D x
    have hY : Y ∈ parts b D := Finset.mem_image_of_mem _ hx
    have hy : i.native ∈ halo b.B Y := halo_spec.mpr ⟨x,(bright ..).mpr ⟨hx,.refl⟩,he⟩
    change (∑ q∈parts b D, _) = _
    rw [Finset.sum_eq_single_of_mem Y hY _ , if_pos hy]
    intro z hz hn; rw [if_neg]
    exact fun h => Finset.disjoint_left.mp (separate (pad b) D hz hY hn) (halo_region b z h) (halo_region b Y hy)
  have ht (Y : Support n) (hY : Y ∈ parts b D) : i.native ∉ halo b.B Y := by
    intro h; obtain ⟨y,hy,hz⟩ := halo_spec.mp h
    exact hx (halo_spec.mpr ⟨y,(lives (pad b) D hY).1 hy,hz⟩)
  rw [Key.owed_zero c b i h hx]; exact Finset.sum_eq_zero (fun Y hY => if_neg (ht Y hY))

theorem charge_range (h : c.direct ≤ 1) (U : Config G n) (D : Support n) :
    charge c b D U ∈ Set.Icc 0 (share * ((Fintype.card (Key n) : ℝ)*2)) := by
  unfold charge
  have he := fun i : Key n => due_range c b h (i.frame U) i.root
  refine ⟨mul_nonneg share_pos.le (Finset.sum_nonneg fun i _ => by split <;> first | exact (he i).1 | exact le_rfl),?_⟩
  refine mul_le_mul_of_nonneg_left ?_ share_pos.le
  rw [show (Fintype.card (Key n) : ℝ)*2 = ∑ _i : Key n,(2:ℝ) by simp]
  exact Finset.sum_le_sum fun i _ => by split <;> first | exact (he i).2 | norm_num

def gain := share * (b.threshold^2/16)
lemma gain_pos : 0 < gain b := mul_pos share_pos (by have := b.threshold_pos; positivity)

theorem charge_price (h : Decent c b) (U : Config G n) (D : Support n) (hd : D ⊆ flags b.threshold U) :
    (D.card:ℝ)*gain b ≤ charge c b D U := by
  let A := Finset.univ.filter (fun i : Cell n => i.1 ∈ halo b.B D ∧ b.threshold < G.chord (faceValue U i))
  have hx : D ⊆ A.biUnion touched := by
    intro z hz
    obtain ⟨p,hp,he⟩ := (flags_spec ..).mp (hd hz)
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      halo_spec.mpr ⟨z,hz,(visit_near p hp).trans h.radius⟩, he⟩, hp⟩
  have hb : D.card ≤ A.card*4 := (Finset.card_le_card hx).trans (Finset.card_biUnion_le.trans ((Finset.sum_le_sum
    (fun i _ => touched_card i)).trans (by simp)))
  let f := fun i : Key n => if i.native ∈ halo b.B D then Key.owed c b i U else 0
  have hf (i) : 0 ≤ f i := by unfold f; split; exact (due_range c b h.direct _ _).1; exact le_rfl
  have he (p) (hp : p ∈ A) : b.threshold^2/4 ≤ f (1,p) := by
    obtain ⟨hr,ht⟩ := (Finset.mem_filter.mp hp).2
    have hq := due_large c b h.direct U p ht
    change _ ≤ if p.1 ∈ _ then _ else _
    rw [if_pos hr, show (1,p) = Key.shifted 1 p from ?_,Key.shift_due,pull_id]
    · exact hq
    change _ = (_,affine _ _ _,p.2)
    simp [affine]
  calc
    _ ≤ share * (A.card*(b.threshold^2/4)) := by
      have hp : (D.card:ℝ) ≤ A.card*4 := by exact_mod_cast hb
      unfold gain; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (by nlinarith) share_pos.le
    _ ≤ share * ∑ i ∈ A, f (1,i) := mul_le_mul_of_nonneg_left
      (le_trans (by simp) (Finset.sum_le_sum he)) share_pos.le
    _ ≤ share * ∑ i : Cell n,f (1,i) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => hf _)) share_pos.le
    _ ≤ _ := by
      unfold charge; rw [Fintype.sum_prod_type (fun i : Key n => _)]
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun x : Signed => ∑ i : Cell n,f (x,i))
        (fun _ _ => Finset.sum_nonneg fun i _ => hf _) (Finset.mem_univ _)) share_pos.le

theorem charge_final (h : Decent c b) (D : Support n) : UsesFinal b.threshold (region b D) (charge c b D (G:=G)) := by
  intro U V he hf
  unfold charge
  refine congr_arg (share*·) (Finset.sum_congr rfl (fun i _ => ?_))
  by_cases hi : i.native ∈ halo b.B D
  · rw [if_pos hi,if_pos hi]
    have hv := Work.H03.reads_larger (region_test b (D:=D) (x:=i.native) hi) (Key.owed_reads (G:=G) c b i h)
    exact hv U V he hf
  · exact (if_neg hi).trans (if_neg hi).symm

theorem charge_gauge (D : Support n) (U : Config G n) (k : Site n → G.El) : charge c b D (gauge k U) = charge c b D U := by
  simp only [charge, Key.owed_gauge]

theorem charge_measurable (D : Support n) : Measurable (charge c b D (G:=G)) := by
  unfold charge; refine Measurable.mul measurable_const (Finset.measurable_fun_sum _ fun i _ => ?_)
  split <;> first | exact (due_measurable ..).comp (continuous_pull .. |>.measurable) | exact measurable_const

theorem halo_image_mem (k : ℕ) (D : Support n) (s : Signed) (x y : Site n) :
    affine s x y ∈ halo k (D.image (affine s x)) ↔ y ∈ halo k D := by
  simp only [halo_spec, Finset.mem_image]
  constructor
  · rintro ⟨_,⟨q,hq,rfl⟩,he⟩; exact ⟨q,hq,by simpa [affine] using he⟩
  rintro ⟨q,hq,he⟩; exact ⟨_,⟨q,hq,rfl⟩,by simpa [affine] using he⟩

lemma pad_image (y : Site n) (s : Signed) (x : Site n) : pad b (affine s x y) = (pad b y).image (affine s x) := by
  ext z; obtain ⟨v,rfl⟩ := (frameSites s x).surjective z
  change affine s x v ∈ pad b _ ↔ _
  rw [pad,← Finset.image_singleton,halo_image_mem]; simp [frameSites,Equiv.ofBijective, aff_inj .. |>.eq_iff, pad]

theorem region_image (D : Support n) (s : Signed) (x : Site n) :
    region b (D.image (affine s x)) = (region b D).image (affine s x) := by
  simp only [region,Finset.image_biUnion,Finset.biUnion_image,pad_image]

lemma spark_image (D : Support n) (s : Signed) (x : Site n) (h : Spark (pad b) D) : Spark (pad b) (D.image (affine s x)) := by
  refine ⟨h.1.image _,fun i hi j hj => ?_⟩
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
  apply Relation.ReflTransGen.lift (r:=bonds (pad b) D) (p:=bonds (pad b) (D.image (affine s x))) (affine s x) _ u v (h.2 _ hu _ hv)
  rintro i j ⟨h₁,h₂,q,hi,hj⟩; exact ⟨Finset.mem_image_of_mem _ h₁, Finset.mem_image_of_mem _ h₂, affine s x q,
    by rw [pad_image]; exact Finset.mem_image_of_mem _ hi, by rw [pad_image]; exact Finset.mem_image_of_mem _ hj⟩

lemma aff_undo (s : Signed) (x y : Site n) : affine s⁻¹ (-(s⁻¹.act x)) (affine s x y) = y := by simp [affine]

theorem spark_transport (D : Support n) (s : Signed) (x : Site n) : Spark (pad b) (D.image (affine s x)) ↔ Spark (pad b) D := by
  refine ⟨fun h => ?_, spark_image b D s x⟩
  simpa only [Finset.image_image,Function.comp_def,aff_undo,Finset.image_id'] using
    spark_image b _ s⁻¹ (-(s⁻¹.act x)) h

theorem charge_oriented (D : Support n) (s : Signed) (x : Site n) (U : Config G n) :
    charge c b (D.image (affine s x)) U = charge c b D (pull s x U) := by
  unfold charge; rw [← Equiv.sum_comp (Key.perm s x)]; congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [show (Key.perm s x i).native = affine s x i.native from rfl,halo_image_mem]
  rw [Key.owed, Key.oriented]; rfl
end YM.WilsonStartup
