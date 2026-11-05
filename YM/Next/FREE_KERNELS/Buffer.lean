import YM.Next.FREE_KERNELS.Portions

/-!
Uniform (L-unspent) cube receipts, puncture fills. `aliasAt` covers all fine
aliases; high-alias inversions are actually firm. No analytic bound on any
bare harmonic D entry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix
open scoped Topology BigOperators ComplexConjugate

variable {ι : Type*} {j t : ℕ}

namespace Flight
variable (k : ℝ) (hk : 0<k) (hj : 4≤j) (ht : 4≤t) (F : ι → Flight j t)

lemma bills (l : ∀ i, Site (F i).L) : Moderate (fun i => decay j (l i)) fun i p => massFilter (F i).patch (aliasAt p (l i)) := by
  obtain ⟨B,hB,h⟩ := alias_rail
  let K := B^4
  refine ⟨zone,K^j,zone_pos,pow_pos (by unfold K; positivity) _,fun i => ⟨fun p he => ?_,fun p he => ?_⟩⟩
  · exact (((Train.area_diff (F i).L).differentiableAt).comp p (by unfold aliasAt; fun_prop)).pow j
  change ‖area (F i).L (aliasAt p (l i)) ^ j‖ ≤ K^j*decay j (l i)
  rw [norm_pow]
  have hc : ‖area (F i).L (aliasAt p (l i))‖ ≤ K / mix (l i) := by
    unfold area mix; rw [norm_prod]
    refine (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun a (_ : a∈Finset.univ) => (h _ (F i).odd p he _ a).2)).trans ?_
    simp [Finset.prod_mul_distrib, K, Axis,div_eq_mul_inv]
  apply (pow_le_pow_left₀ (norm_nonneg _) hc j).trans; rw [div_pow,decay]; exact le_of_eq (div_eq_mul_inv ..)
lemma bills_firm : Firm (fun _ : ι => 1) fun i p => massFilter (F i).patch ((F i).toe p) := by
  let A := Real.exp (-(4*plankCost))
  refine ⟨zone,A^j,zone_pos,pow_pos (Real.exp_pos _) _,fun i p hp => ?_⟩
  change _ * 1 ≤ ‖area (F i).L _ ^ j‖
  rw [mul_one,norm_pow]
  have he := Train.area_at_root (F i).L (F i).L le_rfl p hp
  rw [div_self (side_pos _).ne',mul_one,← alias_zero_eq] at he; exact pow_le_pow_left₀ (Real.exp_pos _).le he _
lemma back_bills (l : ∀ i, Site (F i).L) :
    Moderate (fun i => decay j (l i)) fun i p => massFilter (F i).patch (-aliasAt p (l i)) := by
  simpa only [decay_negate ((F _).odd),alias_reverse _ ((F _).odd)] using (bills F (fun i => -l i)).reverse
lemma rails (l : ∀ i, Site (F i).L) (a : ι → Axis) :
    Moderate (fun _ : ι => 1) fun i p => rail (F i).L (aliasAt p (l i) (a i)) :=
  (rail_cost _ (fun i => (F i).odd) l a).raise_price fun _ => inv_le_one_of_one_le₀ (up_ge ..)
lemma reverse_rails (l : ∀ i, Site (F i).L) (a : ι → Axis) :
    Moderate (fun _ : ι => 1) fun i p => rail (F i).L (-aliasAt p (l i) (a i)) := by
  simpa only [alias_reverse _ ((F _).odd),Pi.neg_apply] using (rails F (fun i => -l i) a).reverse
lemma hinges_budget (r : ℕ) (l : ∀ i, Site (F i).L) :
    Pay (fun i => decay j (l i)) fun i p => hinges (F i) r (aliasAt p (l i)) := by
  have hh := (Pay.expose_mask r (fun a => rails F l (fun _ => a))).scale (bills F l)
  unfold hinges; simpa only [one_pow,mul_one] using hh
lemma flux_budget (r : ℕ) (l : ∀ i, Site (F i).L) : Pay (fun i => decay j (l i)) fun i p => flux (F i) r (aliasAt p (l i)) := by
  unfold flux; simpa only [decay_negate (ho:=(F _).odd),alias_reverse (ho:=(F _).odd)] using (hinges_budget F r fun i => -l i).reverse.transpose

lemma sigQ_budget (l : ∀ i, Site (F i).L) (a : ι → Axis) :
    Moderate (fun i => grade (l i)) fun i p => tripQ (F i).L (aliasAt p (l i)) (a i) := by
  have he := scaled_seed _ (fun _ : ι => 1) (fun i => (F i).odd) l a
  unfold tripQ; simpa [seedQ,narrow_apply] using he.raise_price (fun i => up_le (l i) (a i))
lemma sig_budget (l : ∀ i, Site (F i).L) (r) :
    Pay (fun i => grade (l i)) fun i p => signal (F i).L r (aliasAt p (l i)) := Pay.expose_wedge r fun a => sigQ_budget F l fun _ => a


include hj
lemma portD_budget (l : ∀ i, Site (F i).L) (he : ∀ i, l i ≠ 0) (a : ι → Axis) :
    Moderate (fun i => (grade (l i)^2)⁻¹) fun i p => portD k (F i) p (l i) (a i) := by
  let M := fun i => (F i).wing.mass
  have ho i := (F i).odd
  have hh := (blow_control _ M ho l).inv (blow_firm _ M ho l he) (fun i => pow_pos (grade_pos _) _)
  have hb := (Train.bulb_budget k hj (fun i => (F i).wing) a).on_alias _ ho l
  unfold portD; simpa only [one_mul,div_eq_mul_inv] using hb.mul hh

include hk in
lemma portR_budget (l : ∀ i, Site (F i).L) (he : ∀ i, l i ≠ 0) :
    Moderate (fun i => ((grade (l i)^2)^2)⁻¹) fun i p => (portR k (F i) p (l i))⁻¹ := by
  let M := fun i => (F i).wing.mass
  let v := fun i => (F i).wing
  have ho i := (F i).odd
  have hh := (blow_control _ M ho l).inv (blow_firm _ M ho l he) (fun i => pow_pos (grade_pos _) _)
  have hb := ((Train.bend_budget k hk hj v).inv (Train.bend_firm k hk hj v) (fun i => one_pos)).on_alias _ ho l
  unfold portR; simpa only [_root_.mul_inv_rev, inv_one, one_mul, inv_pow, v] using hb.mul (hh.pow 2)

lemma hills_budget : Moderate (fun _ : ι => 1) fun i => (F i).hills k := by
  let L := fun i => (F i).L
  let s i := Finset.univ.erase (0 : Site (L i))
  let I := Σ i, {l // l ∈ s i}
  let Φ (i : I) := F i.1
  let l (i : I) := i.2.val
  have hl (i : I) : l i ≠ 0 := (Finset.mem_erase.mp i.2.property).1
  obtain ⟨B,hB,h⟩ := decay_cost
  have hb i : ∑ j∈s i, decay 2 j ≤ B := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (s i)) (fun k _ _ => (decay_pos ..).le)).trans (h _)
  have hp := Moderate.sum Finset.univ _ (fun i : I => show 0≤((grade (l i)^2)⁻¹) by positivity) (fun a _ => portD_budget k hj Φ l hl fun _ => a)
  unfold hills
  apply Moderate.sum_family s (fun i => decay 2) ⟨B,hB,fun i => by rw [mul_one]; exact hb i⟩
  apply (((bills Φ l).mul (back_bills Φ l)).mul hp).raise_price
  intro i
  have hx := decay_pos (l i) j
  have ht : (grade (l i)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (grade_ge _))
  exact ((mul_le_of_le_one_right (mul_pos hx hx).le ht).trans (mul_le_of_le_one_right hx.le (decay_le_one _ _))).trans (decay_anti _ (by omega))

omit hj in
lemma pull_forward (l : ∀ i, Site (F i).L) (a : Axis) : Moderate (fun i => decay j (l i)) fun i p => pullLine (F i).patch a (aliasAt p (l i)) := by
  have he := (bills F l).mul (rails F l (fun _ => a))
  simp only [mul_one] at he; exact he
lemma tail_budget (a : Axis) : Moderate (fun _ : ι => 1) fun i p => (F i).tailings k p a := by
  let L := fun i => (F i).L
  let s i := Finset.univ.erase (0 : Site (L i))
  let I := Σ i, {l // l ∈ s i}
  let Φ (i : I) := F i.1
  let l (i : I) := i.2.val
  have hl (i : I) : l i ≠ 0 := (Finset.mem_erase.mp i.2.property).1
  obtain ⟨B,hB,h⟩ := decay_cost
  have hb i : ∑ j∈s i, decay 2 j ≤ B := (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (s i)) (fun k _ _ => (decay_pos ..).le)).trans (h _)
  have hp := portD_budget k hj Φ l hl fun _ => a
  unfold tailings; refine Moderate.add ?_ (Moderate.const _)
  unfold above; apply Moderate.sum_family s (fun i => decay 2) ⟨B,hB,fun i => by rw [mul_one]; exact hb i⟩
  have ht := pull_forward Φ l a
  have hu : Moderate (fun i => decay j (l i)) fun i p => pullLine (Φ i).patch a (-aliasAt p (l i)) := by
    simpa only [alias_reverse (ho:=(Φ _).odd),decay_negate (ho:=(Φ _).odd)] using (pull_forward Φ (fun i => -l i) a).reverse
  apply ((ht.mul hu).mul hp).raise_price
  intro i
  have hx := decay_pos (l i) j
  have ht : (grade (l i)^2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (grade_ge _))
  exact ((mul_le_of_le_one_right (mul_pos hx hx).le ht).trans (mul_le_of_le_one_right hx.le (decay_le_one _ _))).trans (decay_anti _ (by omega))

lemma abide_budget : Moderate (fun _ : ι => 1) fun i => (F i).abide k := by
  have he := (bills F (fun _ => 0)).mul (back_bills F (fun _ => 0))
  have hh : Moderate (fun _ : ι => 1) fun i p => fore k (F i) p := by
    unfold fore; apply Moderate.sum _ _ (fun i => zero_le_one)
    exact fun a _ => (Train.bulb_budget k hj (fun i => (F i).wing) fun _ => a).on_alias _ (fun i => (F i).odd) (fun _ => 0)
  have hD := (divisor_control fun i => (F i).land.mass).mul (hills_budget k hj F)
  have hp := he.mul hh; simp only [decay_zero,mul_one] at hp hD; unfold abide; exact hp.add hD

omit hj
include hk
lemma abide_firm : Firm (fun _ : ι => 1) fun i => (F i).abide k := by
  obtain ⟨η,C,hη,hC,h⟩ := Train.bulb_firm k hk (fun i => (F i).wing) (fun _ => 0)
  obtain ⟨θ,B,hθ,hB,hh⟩ := bills_firm F
  let z := min η (min θ zone)
  have hz : 0 < z := lt_min hη (lt_min hθ zone_pos)
  refine ⟨z,B*B*C,hz,by positivity,fun i p hp => ?_⟩
  let P := F i
  have he1 : p ∈ realCube η := realCube_mono (min_le_left ..) hp
  have he2 : p ∈ realCube θ := realCube_mono ((min_le_right ..).trans (min_le_left ..)) hp
  have he3 : p ∈ realCube zone := realCube_mono ((min_le_right ..).trans (min_le_right ..)) hp
  have htoe : P.toe p ∈ realCube zone := P.toe_regular he3
  have hJ : C ≤ (fore k P p).re := by
    let g a := P.wing.bulb k (P.toe p) a
    have hg (a : Axis) : Silver (g a) := Train.bulb_cost k hk _ htoe.1 _
    have hk := h i (P.toe p) (alias_in_real hη he1 _ P.odd)
    change C*1 ≤ ‖g 0‖ at hk
    unfold fore; rw [Complex.re_sum]; exact ((mul_one C).symm.le.trans (hk.trans_eq (hg 0).norm)).trans (Finset.single_le_sum (f:=fun a : Axis => (g a).re) (fun a _ => (hg a).re_nonneg) (Finset.mem_univ _))
  have hy : B*B ≤ (yen (massFilter P.patch) (P.toe p)).re := by
    have hX := hh i p he2
    have hY := hh i (-p) (realCube_neg he2)
    simp only [mul_one,toe_bar] at hX hY
    rw [← (P.filter_silver htoe.1).norm,yen,norm_mul]; exact mul_le_mul hX hY hB.le (norm_nonneg _)
  dsimp only
  rw [mul_one]
  apply le_trans _ (Complex.re_le_norm _)
  unfold abide
  rw [Complex.add_re]
  apply le_add_of_le_of_nonneg
  · rw [(filter_silver _ htoe.1).real_mul]
    exact mul_le_mul hy hJ hC.le ((mul_pos hB hB).le.trans hy)
  exact ((Silver.chipSq _ he3.1).mul (hills_positive k hk _ he3)).re_nonneg
end Flight
end YM.Next.Free
