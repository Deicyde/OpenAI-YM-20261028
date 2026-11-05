import YM.Bid.Energy
import YM.Complex.Gaps
import YM.Corona.Spend
import YM.Slice.Strips
import YM.Vac.Treasury


/-! # Macro charges and packing estimates on a single oriented sector -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.E01
open Filter Lattice RG Axial Wilson Finset Pressure Pressure.Stores Bid
open scoped Topology BigOperators
variable {G : Gauge} {c f n : Side} (S : StepData c f)

lemma pdist_wrap_le {v : Cover} {R : ℕ} (hv : v ∈ box R) : pdist (wrap n v) ≤ R := by
  apply Finset.sup_le
  intro i _
  apply (Lattice.Corona.lap v i).trans
  obtain ⟨h₁, h₂⟩ := box_test.mp hv
  specialize h₁ i; specialize h₂ i
  omega

lemma macroR_eq : macroR S.patch = (S.patch.J + 7) * S.patch.L.val := by
  unfold macroR Patch.radius
  ring

lemma port_charge (x : Site c) (U : Config G f) :
    port S x U = ∑ b : Cell f, mcharge S x b * toll U b := by
  classical
  let D := box (macroR S.patch)
  let site z := wrap f z + S.ratio.embed x
  let sees (z : Cover) (p : PlaqAxes) := ∀ y ∈ visits z (square p.val.1 p.val.2), y ∈ D
  have he (p : PlaqAxes) (y : Site f) :
      mcharge S x (y,p) * toll U (y,p) = ∑ z ∈ D, if site z=y ∧ sees z p then toll U (y,p) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [Fintype.sum_prod_type]
  simp_rw [he]; rw [sum_comm]
  unfold port faces; change (∑ z ∈ D, ∑ p : PlaqAxes, face D _ z p) = _
  rw [sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [sum_comm]; apply Finset.sum_congr rfl
  intro z _
  change (if sees z p then _ else _) = _
  by_cases h : sees z p
  · simp [h, site, faceValue, toll, travel_at]
  simp [h]

lemma mcharge_le_one (hx : 2 * macroR S.patch < f.val) (x : Site c) (p : Cell f) :
    mcharge S x p ≤ 1 := by
  unfold mcharge
  apply Finset.card_le_one.mpr
  intro z hz y hy
  have h (v : Cover) (hv : v ∈ box (macroR S.patch)) (i : Axis) :
      -(f.val : ℤ) < 2*v i ∧ 2*v i ≤ f.val := by
    have h₁ := (box_test.mp hv).1 i; have h₂ := (box_test.mp hv).2 i
    omega
  obtain ⟨hz,hz',_⟩ := Finset.mem_filter.mp hz
  obtain ⟨hy,hy',_⟩ := Finset.mem_filter.mp hy
  exact wrap_injOn f (h z hz) (h y hy) (add_right_cancel (hz'.trans hy'.symm))

lemma mcharge_maps (x : Site c) (p : Cell f) (h : 0 < mcharge S x p) :
    separation x (S.ratio.parent p.1) ≤ S.patch.J + 8 := by
  obtain ⟨z,hz⟩ := Finset.card_pos.mp h
  obtain ⟨hz,he,_⟩ := Finset.mem_filter.mp hz
  have h₁ : separation (S.ratio.embed x) p.1 ≤ macroR S.patch := by
    rw [separation_comm, ← he, separation, add_sub_cancel_right]; exact pdist_wrap_le hz
  have h₂ := Lattice.Corona.near S.ratio p.1
  change 2*separation p.1 (S.ratio.embed (S.ratio.parent p.1)) ≤ S.patch.L.val at h₂
  apply Nat.le_of_mul_le_mul_left _ S.patch.L.property
  calc S.patch.L.val*separation x (S.ratio.parent p.1) ≤ _ := Lattice.Corona.below S.ratio _ _
       _ ≤ macroR S.patch + S.patch.L.val := (separation_triangle _ p.1 _).trans (Nat.add_le_add h₁ (by omega))
       _ = _ := by rw [macroR_eq]; ring_nf; rfl

lemma mcharge_count (hx : 2 * macroR S.patch < f.val) (p : Cell f) :
    let R := S.patch.J + 8
    (∑ x : Site c, mcharge S x p) ≤ (R+R+1)^4 := by
  intro R
  let D := halo R {S.ratio.parent p.1}
  have h (x : Site c) (hh : 0 < mcharge S x p) : x ∈ D := halo_spec.mpr
    ⟨_,mem_singleton_self _,(separation_comm ..).trans_le (mcharge_maps S x p hh)⟩
  calc
    _ ≤ ∑ x : Site c, if x ∈ D then 1 else 0 := Finset.sum_le_sum fun x _ => by
      split
      · exact mcharge_le_one S hx x p
      next he => exact Nat.le_of_not_gt (fun hv => he (h x hv))
    _ = D.card := by rw [← sum_filter]; simp
    _ ≤ _ := by simpa only [Finset.card_singleton, one_mul] using Lattice.Corona.halo_size {S.ratio.parent p.1} R

lemma base_touched (p : Cell n) : p.1 ∈ touched p := by
  rw [touched, square_corners]; simp

lemma touched_card (p : Cell n) : (touched p).card ≤ 4 := by
  rw [touched, square_corners]
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  rw [insert_eq_of_mem (by simp)]
  calc
    _ ≤ _ := Finset.card_insert_le ..
    _ ≤ 4 := by
      have h := Finset.card_insert_le (p.1+step p.2.val.1+step p.2.val.2) ({p.1+step p.2.val.2,p.1} : Support n)
      have h' := Finset.card_insert_le (p.1+step p.2.val.2) ({p.1} : Support n)
      rw [Finset.card_singleton] at h'; omega

lemma sep_step_le (z : Site n) (i : Axis) : separation z (z+step i) ≤ 1 := by
  rw [separation_comm, separation, add_comm, add_sub_cancel_right]; exact pdist_step i

lemma sep_touched (p : Cell n) (z : Site n) (hz : z∈ touched p) : separation p.1 z ≤ 2 := by
  rw [touched,square_corners] at hz
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl
  · simp
  · exact le_trans (sep_step_le ..) (by norm_num)
  · exact (separation_triangle _ (p.1+step p.2.val.1) _).trans (Nat.add_le_add (sep_step_le ..) (sep_step_le ..))
  · exact le_trans (sep_step_le ..) (by norm_num)
  · simp

variable {S} (A : Stores S)

lemma place_card : A.place.card ≤ 4*A.shares := by
  have h : (A.costs.biUnion (startPos S)).card ≤ A.costs.card * 4 := calc
    _ ≤ ∑ i ∈ A.costs, (startPos S i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A.costs, 4 := Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (touched_card i)
    _ = _ := by simp
  have h' : (A.aisles.biUnion pinPos).card ≤ A.aisles.card * 2 := calc
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ A.aisles, 2 := Finset.sum_le_sum fun i _ => (Finset.card_insert_le ..).trans (by simp)
    _ = _ := by simp
  unfold place shares
  refine (Finset.card_union_le ..).trans ?_
  have he := Finset.card_union_le (A.costs.biUnion (startPos S)) (A.aisles.biUnion pinPos)
  omega

def volumePrice (R : ℕ) := 4*(R+R+1)^4*Fintype.card PlaqAxes

lemma dome_card {b : ℕ} {s : Finset (Cell c)} (h : ∀ i ∈ s,i.1 ∈ A.dome b) : s.card ≤ volumePrice b * A.shares := by
  calc
    _ ≤ (A.dome b ×ˢ (univ : Finset PlaqAxes)).card := Finset.card_le_card fun i hi => mem_product.mpr ⟨h _ hi, mem_univ _⟩
    _ = (halo b A.place).card * Fintype.card PlaqAxes := Finset.card_product ..
    _ ≤ ((4*A.shares)*(b+b+1)^4)*Fintype.card PlaqAxes := Nat.mul_le_mul_right _
      ((Lattice.Corona.halo_size A.place b).trans (Nat.mul_le_mul_right _ (place_card A)))
    _ = _ := by unfold volumePrice; ring

lemma volumePrice_le {B : ℕ} (h : 1 ≤ B) : volumePrice (2*B) ≤ volumePrice 2 * B^4 := by
  unfold volumePrice
  calc
    _ ≤ 4*(5*B)^4*Fintype.card PlaqAxes := by gcongr; omega
    _ = _ := by ring

lemma outs_card {x : ℝ} (h : 1 ≤ radiusB x) : (A.outs x).card ≤ volumePrice 2*(radiusB x)^4*A.shares := by
  apply (dome_card A (b:=2*radiusB x) fun i hi => (Finset.mem_filter.mp hi).2).trans
  exact Nat.mul_le_mul_right _ (volumePrice_le h)

lemma hit_card (U : Config G f) (Q V : Config G c) {x : ℝ} (h : 1 ≤ radiusB x) :
    (A.hit U Q V x).card ≤ volumePrice 2*(radiusB x)^4*(A.spend U Q V x).shares := by
  apply (dome_card (A.spend U Q V x) (b:=2*radiusB x) (fun i hi =>
    Lattice.Corona.halo_mono (show 4*radiusB x/5 ≤ 2*radiusB x by omega) (fun _ h => h) (Finset.mem_filter.mp hi).2)).trans
  exact Nat.mul_le_mul_right _ (volumePrice_le h)

lemma flag_count {x W : ℝ} (h : 1 ≤ radiusB x) {U : Config G f} {V : Config G c} {k : S.Choices}
    (hh : A.Plot U k V x W) : A.flags.card ≤ 4*(A.tides V x (temp x)).card := by
  let D := A.tides V x (temp x)
  have he : A.flags ⊆ D.biUnion touched := by
    intro i hi
    have hi' := (hh.precise i (halo_subset _ _ (Finset.mem_union_right _ hi))).mp hi
    obtain ⟨p,hp,ht⟩ := (flags_spec ..).mp hi'
    have hv := sep_touched p i hp
    rw [separation_comm] at hv
    exact mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,halo_spec.mpr ⟨i, mem_union_right _ hi,by omega⟩⟩, ht⟩,hp⟩
  calc
    _ ≤ _ := card_le_card he
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ D, 4 := Finset.sum_le_sum fun i _ => touched_card i
    _ = _ := by simp [D, Nat.mul_comm]

lemma largeT_eq (s : ℝ) (hs : 0 ≤ s) : ((Real.sqrt s)⁻¹)^((98:ℝ)/100) = s^(-(49/100):ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs, ← Real.rpow_mul hs]
  norm_num

lemma betaF_tendsto (G : Gauge) (L : Side) : Tendsto (fun x => betaF G x L) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_id

lemma largeT_tendsto (G : Gauge) (L : Side) : Tendsto (fun x => largeT G x L) atTop (𝓝 0) := by
  refine ((tendsto_rpow_neg_atTop (y:=49/100) (by norm_num)).comp (betaF_tendsto G L)).congr' ?_
  filter_upwards [(betaF_tendsto G L).eventually (eventually_ge_atTop 0)] with x hx
  exact (largeT_eq _ hx).symm

lemma fiery_le (G : Gauge) (L : Side) (m : ℝ) : ∀ᶠ x : ℝ in atTop, m*fiery G x L ≤ largeT G x L := by
  have he := betaF_tendsto G L
  filter_upwards [he.eventually (eventually_gt_atTop 0),he.eventually (Vac.Numbers.cost 1 (1/200) (by norm_num)),
    ((tendsto_rpow_atTop (y:=1/200) (by norm_num)).comp he).eventually_ge_atTop m] with x hx hp hm
  generalize hs : betaF G x L = s
  change m*temp (betaF G x L) ≤ _
  unfold largeT
  change 0 < betaF G x L at hx
  change Vac.Numbers.P (betaF G x L) ^ (1:ℝ) ≤ _ at hp
  change m ≤ (betaF G x L)^(1/200:ℝ) at hm
  rw [hs] at hx hm hp ⊢
  rw [Real.rpow_one] at hp
  rw [largeT_eq _ hx.le]
  unfold temp
  change m * ((Real.sqrt s)⁻¹ * Vac.Numbers.P s) ≤ _
  have hP : 0 ≤ Vac.Numbers.P s := (Real.exp_pos _).le
  calc
    _ ≤ s^(1/200:ℝ) * ((Real.sqrt s)⁻¹ * s^(1/200:ℝ)) := mul_le_mul hm (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity) (by positivity)
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hx.le, ← Real.rpow_add hx, ← Real.rpow_add hx]; norm_num

lemma radiusB_tendsto : Tendsto radiusB atTop atTop :=
  tendsto_nat_ceil_atTop.comp ((tendsto_pow_atTop (n:=2) (by decide)).comp Real.tendsto_log_atTop)

variable (S) in
lemma port_le (U : Config G f) (x : Site c) (h : ℝ) (hp : 0 ≤ h) (hu : ∀ i : Cell f, 0 < mcharge S x i → toll U i ≤ h) :
    port S x U ≤ ((box (macroR S.patch)).card : ℝ) * Fintype.card PlaqAxes * h := by
  classical
  unfold port faces
  calc
    _ ≤ ∑ _z ∈ box (macroR S.patch), ∑ _p : PlaqAxes,h := Finset.sum_le_sum fun z hz => Finset.sum_le_sum fun p _ => by
      unfold face
      split
      next he =>
        simp only [faceValue, travel_at]
        apply hu (wrap f z + S.ratio.embed x,p)
        exact Finset.card_pos.mpr ⟨z,mem_filter.mpr ⟨hz,rfl,he⟩⟩
      exact hp
    _ = _ := by simp [mul_assoc]

lemma larger_dome {b k : ℕ} {i y : Site c} (hi : i ∈ A.dome (2*b)) (hy : separation i y ≤ k) (hk : k ≤ 3*b) : y ∈ A.dome (5*b) := by
  obtain ⟨o,ho,hd⟩ := halo_spec.mp hi
  refine halo_spec.mpr ⟨o, ho, (separation_triangle o i y).trans (by omega)⟩

def rate (j : ℕ) (L : Side) (C : ℝ) : ℝ :=
  4 + (C/(L.val:ℝ)^2)*(((box ((j+7)*L.val)).card:ℝ)*Fintype.card PlaqAxes)

/-- All coarse charges beyond δ have an actual large input in fixed output-distance radius. -/
lemma witnessed {U : Config G f} {V : Config G c} {k : S.Choices} {x W δ C : ℝ}
    (hc : 0 < C)
    (hc' : ∀ i : Cell c, usable S U i.1 k → toll V i ≤ fuel (S.prediction U k) V i.1 i.2 + C/(S.patch.L.val:ℝ)^2*port S i.1 U)
    (hB : S.patch.J+8 ≤ 4*radiusB x/5)
    (hu : fiery G x S.patch.L/2 ≤ largeT G x S.patch.L)
    (hw : 2*W*fiery G x S.patch.L ≤ largeT G x S.patch.L)
    (ht : rate S.patch.J S.patch.L C * largeT G x S.patch.L ≤ δ)
    (hh : A.Plot U k V x W) {i : Cell c} (hi : i ∈ A.tides V x δ) :
    i.1 ∈ (A.spend U (S.prediction U k) V x).dome (S.patch.J+8) := by
  obtain ⟨hi,hδ⟩ := Finset.mem_filter.mp hi
  have hd : i.1 ∈ A.dome (2*radiusB x) := (Finset.mem_filter.mp hi).2
  have hus : usable S U i.1 k := by
    intro y hy
    apply hh.list
    refine larger_dome A hd (k:=2) ?_ (by omega)
    rw [separation_comm, separation, plank, add_sub_cancel_right]; exact pdist_wrap_le hy
  let Q := S.prediction U k
  let T := largeT G x S.patch.L
  have hT : 0 ≤ T := by unfold T largeT; positivity
  by_contra h
  have h' (y : Site c) (hy : separation i.1 y ≤ S.patch.J+8) : y ∉ (A.spend U Q V x).place := fun he =>
    h (halo_spec.mpr ⟨_,he,(separation_comm ..).trans_le hy⟩)
  have h₁ (p : Cell f) (hp : 0 < mcharge S i.1 p) : toll U p ≤ T := by
    have hsep := mcharge_maps S i.1 p hp
    have hp' : S.ratio.parent p.1 ∈ startPos S p := mem_image_of_mem _ (base_touched p)
    by_cases he : p ∈ A.costs
    · apply le_of_not_gt
      intro hv
      have hm : p ∈ (A.spend U Q V x).costs := mem_filter.mpr ⟨he,hv⟩
      exact h' _ hsep (mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨_,hm,hp'⟩)))
    apply le_trans ((hh.consumes p ?_).2 he) hu
    exact fun h => Finset.disjoint_left.mp h (larger_dome A hd hsep (by omega)) hp'
  have h₂ (b : Bond c) (hb : separation i.1 b.1 ≤ 1) : wire Q V b ≤ T := by
    have hb' : b.1 ∈ pinPos b := by simp [pinPos]
    by_cases he : b ∈ A.aisles
    · apply le_of_not_gt
      intro hv
      have hm : b ∈ (A.spend U Q V x).aisles := mem_filter.mpr ⟨he,hv⟩
      exact h' _ (by omega) (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨_,hm,hb'⟩)))
    apply le_trans ((hh.drive b ?_).2 he) hw
    exact fun h => Finset.disjoint_left.mp h (larger_dome A hd hb (by omega)) hb'
  have hf : fuel Q V i.1 i.2 ≤ 4*T := by
    unfold fuel
    apply (add_le_add (add_le_add (add_le_add (h₂ (_,_) (by simp)) (h₂ (_,_) (sep_step_le ..))) (h₂ (_,_) (sep_step_le ..))) (h₂ (_,_) (by simp))).trans_eq
    ring
  have he := port_le S U i.1 T hT h₁
  rw [macroR_eq] at he
  apply hδ.not_ge
  refine (hc' i hus).trans ((add_le_add hf (mul_le_mul_of_nonneg_left he (by positivity))).trans ((le_of_eq ?_).trans ht))
  unfold rate T
  ring

theorem answer : YM.Bid.E01 := by
  intro G P δ hδ
  let R := P.j+8
  let N := volumePrice R + volumePrice 2 + R + (R+R+1)^4
  have hv : volumePrice R ≤ N := by dsimp only [N]; omega
  have hv' : volumePrice 2 ≤ N := by dsimp only [N]; omega
  obtain ⟨C,hc,hc'⟩ := qdc G P.bind P.j
  refine ⟨N,fun L W _ => ⟨?_⟩⟩
  have hT : Tendsto (fun x => rate P.j L C * largeT G x L) atTop (𝓝 0) := by
    simpa only [mul_zero] using (largeT_tendsto G L).const_mul (rate P.j L C)
  filter_upwards [radiusB_tendsto.eventually_ge_atTop (5*R), fiery_le G L (1/2), fiery_le G L (2*W), hT.eventually (ge_mem_nhds hδ)] with x hx hu hw ht
  intro c f S hL hS T H F A U k V _ hh
  have he := H.atStep
  have hR : S.patch.J+8 = R := congr_arg (·+8) he
  have hB : 1 ≤ radiusB x := by omega
  have hwit : ∀ i ∈ A.tides V x δ, i.1 ∈ (A.spend U (S.prediction U k) V x).dome R := by
    intro i hi
    rw [← hR]
    refine witnessed A hc ?_ (by omega) ?_ ?_ ?_ hh hi
    · exact fun i hz => (hc' c f S H.knobs.symm he.symm U V i.1 k hz i.2).2
    · rw [hL]; linarith only [hu]
    · rwa [hL]
    rw [hL,he]; exact ht
  constructor
  · refine ⟨fun i hi => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,?_⟩, flag_count A hB hh,
      (dome_card _ hwit).trans (Nat.mul_le_mul_right _ hv), ?_, ?_⟩
    · exact Lattice.Corona.halo_mono (by omega) (fun _ h => h) (hwit i hi)
    · exact (outs_card A hB).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hv'))
    · exact (hit_card A _ _ _ hB).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hv'))
  refine ⟨fun u z => port_charge S z u,fun p => ?_,fun z p hp => (mcharge_maps S z p hp).trans ?_⟩
  · have hl : 0 < S.patch.L.val := S.patch.L.property
    have hc : 2*(S.patch.J+7) < c.val := by omega
    have hf : 2*macroR S.patch < f.val := by
      rw [S.sizes,macroR_eq,← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right hc hl
    exact (mcharge_count S hf p).trans (by rw [hR]; dsimp only [N]; omega)
  rw [hR]; dsimp only [N]; omega
end YM.Work.E01

/-! Check why the one-per-macro-box bound has a period qualification. -/
namespace YM.Work.E01
open Lattice RG Bid Pressure

private def trial : StepData (1:Side) (3:Side) where
  patch := ⟨3,4,le_rfl, le_rfl, by decide⟩
  kernel := ⟨1,1,1,1,by norm_num,by norm_num,by norm_num,by norm_num⟩
  sizes := by decide




end YM.Work.E01
