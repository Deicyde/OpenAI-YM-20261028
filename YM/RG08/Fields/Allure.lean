import YM.RG08.Fields.Linen
import YM.Pert.Fourier.Fee

/-!
# Ordinary full cover covariance entries

Massless point integral directly in RG.Fourier chart (measure
imported; not time propagation). Use positive faces, corners, native
period cells. Produce true points for the pre-wing budget incl UV
**differences**. No strip claims for the full propagator itself. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Metric
open scoped Topology BigOperators
open Pert Pert.Cellular Next.Rank.Radian
open MeasureTheory
variable {j : ℕ} {k : ℝ}

def moon (x : E4) : Momentum := fun i => ((Band.turn:ℂ)* (x i:ℝ))
lemma moon_cont : Continuous moon := by apply continuous_pi; intro i; unfold moon; fun_prop
lemma moon_circle {x : E4} (hx : x∈cells) : moon x ∈ baseCube := by
  let p:=Band.turn • x
  have he:= (cells_cube x).1 hx
  have hh (i) : moon x i=(p i:ℝ) := by unfold moon p; simp
  refine ⟨(physical_iff _).2 (fun i=>by rw [hh]; rfl),fun i=>?_⟩; rw [hh]; exact he i
lemma moon_grip (x : E4) : ‖x‖ ≤ ‖moon x‖ := by
  obtain ⟨i,hi⟩:=Band.max_coord x
  have he : ‖moon x i‖=Band.turn*|x i|:= by unfold moon; simp [Real.pi_pos.le]
  refine hi.trans ((le_trans ?_ he.symm.le).trans (norm_le_pi_norm _ _)); exact mul_le_mul_of_nonneg_right (by unfold Band.turn; linarith [Real.pi_gt_three]) (abs_nonneg _)
lemma moon_zero (x : E4) : moon x=0 ↔ x=0 := by
  constructor
  · intro h; apply norm_le_zero_iff.mp; simpa [h] using moon_grip x
  rintro rfl; ext1; simp [moon]
lemma moon_show (c : Side) (p : Site c) : moon (addr c (lift p))=mon p := by
  have he:= physical_iff _ |>.1 (mon_mem c p).1
  ext1 i; rw [moon]; rw [Band.reads_wrap]; apply Complex.ext <;> simp [mon_re, he]; ring
lemma band_plot {v : Train j} (c : Side) (z : Cover) (i t : TypeFace 1) :
    bedtime k v c (0,i) (wrap c z,t)=((c.val:ℝ)⁻¹)^4 * ∑ p:Site c,(curfew k v (mon p) i t*star (mode (mon p) z)).re := by
  unfold bedtime daylight; rw [Matrix.map_apply,orchard_show]; simp_rw [cell_origin,one_mul,cell_wrap]
  rw [show (stageVolume c)⁻¹ = ((((c.val:ℝ)⁻¹)^4:ℝ):ℂ) from by unfold stageVolume; simp]
  rw [Complex.mul_re]; simp only [Complex.re_sum,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
def poet (k : ℝ) (v : Train j) (i t : TypeFace 1) (z : Cover) (x : E4) :=
    (curfew k v (moon x) i t * star (mode (moon x) z)).re
open scoped Classical
-- indicator across genuine puncture (may read outside cells; no assertion there)
def olog (k : ℝ) (v : Train j) : Row (TypeFace 1) (TypeFace 1) := fun i t z =>
    ∫ x : E4,cells.indicator (poet k v i t z) x
lemma walks_cloud {v : Train j} (i t : TypeFace 1) (z : Cover) {c : Side} (he : Even c.val) :
    let f:=poet k v i t z
    bedtime k v c (0,i) (wrap c z,t)=∫ x,cells.indicator (fun p => f (Cellular.visit c p)) x := by
  intro f; rw [band_plot,(integrate_visit c he f).2]; unfold f poet; simp_rw [moon_show]

lemma curfew_still (_ : 0 < k) (hj : 4≤j) (v : Train j) (i j : TypeFace 1) {p} (hp : p∈baseCube) (hx:p≠0) :
    ContinuousWithinAt (fun q=> curfew k v q i j) baseCube p := by
  apply ContinuousWithinAt.congr_of_eventuallyEq (f:=fun q => mask 1 (fun a => (v.bulb k q a/divisor v.mass q)) i j)
  · simp only [mask_value]; split
    · obtain ⟨s,c,hs,hc,H⟩:= Train.bulb_budget k hj (fun _ : Unit => v) (fun _ => axisEquiv.symm i)
      have hi:= (H ()).hol p (mem_cube_real (base_subset_realCube hs hp) hs)
      refine (hi.continuousAt.div ?_ (divisor_ne _ (base_subset_realCube zone_pos hp) hx)).continuousWithinAt
      unfold divisor seedQ narrow chip; fun_prop
    exact continuousWithinAt_const
  all_goals have hm (p) (hp:p∈baseCube) (hx:p≠0) : curfew k v p=mask 1 (fun a => Train.bulb k v p a / divisor v.mass p) := by rw [curfew,if_neg hx]; unfold fieldD; apply congrArg (mask 1); funext i; rw [scaleD_one]; exact Train.D_bulb _ _ (base_subset_realCube zone_pos hp) hx _
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (eventually_ne_nhds hx)] with p hp hx; rw [hm _ hp hx]
  rw [hm _ hp hx]

lemma visit_fit {v : Train j} {i t : TypeFace 1} {z : Cover} (hk : 0<k) (hj : 4 ≤ j) (n : ℕ→Side)
    (hn : Tendsto (fun i=> (n i).val) atTop atTop) (he : ∀ i,Even (n i).val) :
    ∀ᵐ x:E4,Tendsto (fun c=> cells.indicator (fun p=>poet k v i t z (Cellular.visit (n c) p)) x)
       atTop (𝓝 (cells.indicator (poet k v i t z) x)) := by
  filter_upwards [cell_AE,show ∀ᵐ x:E4, x≠0 from MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ:=volume) (0:E4))] with x hx hy
  by_cases h:x∈cells
  · simp_rw [indicator_of_mem h]; unfold poet
    let V c := Cellular.visit (n c) x
    have hV c : V c ∈ cells := by
      unfold V Cellular.visit; obtain ⟨p,H⟩:= (marked_cell (n c) (he c) hx).1 h; rw [← H]; exact (cells_cube _|>.2 (visit_defensive (n c) p |>.symm ▸ Full.moment_cube p))
    have hv : Tendsto V atTop (𝓝 x) := by
        apply tendsto_iff_norm_sub_tendsto_zero.mpr
        apply squeeze_zero (fun _=> norm_nonneg _) (fun i=> visit_eps (n i) x)
        simpa using (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hn)).const_mul (4:ℝ)
    have ho:= moon_cont.continuousAt.tendsto.comp hv
    have hi:= tendsto_nhdsWithin_iff.mpr ⟨ho,.of_forall fun c=> moon_circle (hV c)⟩
    have ht:= Filter.Tendsto.comp (curfew_still hk hj v i t (moon_circle h) (by exact mt (moon_zero _).mp hy)) hi
    have hu : Continuous fun p:Momentum=>star (mode p z):= by unfold mode; fun_prop
    exact Complex.continuous_re.continuousAt.tendsto.comp (Filter.Tendsto.mul ht ((hu.continuousAt).tendsto.comp ho))
  simp only [indicator_of_notMem h]; exact tendsto_const_nhds

lemma poet_pull (hk : 0<k) (hj : 4≤j) : ∃ c : ℝ, 0≤c ∧ ∀ (v : Train j) (i j : TypeFace 1) z x, x∈cells →
    ‖poet k v i j z x‖≤ c/ ‖x‖^2 := by
  obtain ⟨c,hc,H⟩:=full_coin hk hj
  refine ⟨c,hc.le,fun v i j a x hx=> ?_⟩
  unfold poet curfew
  split
  · simp; positivity
  next hp =>
    have he := moon_circle hx; apply (Complex.abs_re_le_norm _).trans; rw [norm_mul,norm_star, mode_real _ _ he.1,mul_one]
    simp only [fieldD,mask_value,scaleD_one]; split
    · have h := H v (axisEquiv.symm i) _ he hp
      refine h.1.trans (div_le_div_of_nonneg_left hc.le ?_ ?_)
      · exact pow_pos (norm_pos_iff.mpr (mt (moon_zero x).mpr hp)) _
      exact pow_le_pow_left₀ (norm_nonneg _) (moon_grip _) _
    rw [norm_zero]; positivity
lemma salary {v : E4→ℝ} {c : ℝ} (hc : 0≤c) (hv : ∀ x∈ cells,‖v x‖≤ c/‖x‖^2) (n : Side) (he : Even n.val) :
    ∀ᵐ x:E4, ‖cells.indicator (fun y=> v (Cellular.visit n y)) x‖ ≤ 25*c*spike 3 x := by
  filter_upwards [cell_AE,show ∀ᵐ x:E4, x≠0 from MeasureTheory.measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ:=volume) (0:E4))] with x hx hh
  let y:=Cellular.visit n x
  by_cases hg:x∈cells
  · rw [indicator_of_mem hg,Cellular.spike, indicator_of_mem (show x∈ball (0:E4) (2*3) from mem_ball.mpr (by rw [dist_zero_right]; linarith [cells_bd hg]))]
    have ht : y∈cells := by
      unfold y Cellular.visit; obtain ⟨p,H⟩:= (marked_cell n he hx).1 hg; rw [← H]; exact (cells_cube _|>.2 (visit_defensive n p |>.symm ▸ Full.moment_cube p))
    refine (hv y ht).trans ?_
    by_cases hy:y=0
    · simp only [hy,norm_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,div_zero]; positivity
    have hl := visit_eps n x
    have hc': ‖x‖ ≤ 5*‖y‖:= by
      have ht:= visit_floor n x hy; have hv:= norm_sub_le y (y-x); rw [sub_sub_cancel] at hv; linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ (pow_pos (norm_pos_iff.mpr hy) _) (pow_pos (norm_pos_iff.mpr hh) _)]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc' _) hc).trans_eq (by ring)
  rw [indicator_of_notMem hg,norm_zero,Cellular.spike]; exact mul_nonneg (by positivity) (indicator_nonneg (fun y _ => by positivity) x)
def even_side (i : ℕ) : Side := ⟨2*(i+1),by omega⟩
lemma evenings (i) : Even (even_side i).val := ⟨_,two_mul (i+1)⟩
lemma evenings_grow : Tendsto (fun i=> (even_side i).val) atTop atTop := tendsto_atTop_mono (fun i=> show i ≤ 2*(i+1) by omega) tendsto_id
lemma poet_ends (hk : 0<k) (hj : 4≤j) (v : Train j) (i b : TypeFace 1) (x : Cover) (n : ℕ→Side)
    (hn : Tendsto (fun i=> (n i).val) atTop atTop) (he : ∀ i,Even (n i).val) :
    Tendsto (fun l=> bedtime k v (n l) (0,i) (wrap (n l) x,b)) atTop (𝓝 (olog k v i b x)) := by
  simp_rw [walks_cloud i b x (he _),olog]
  obtain ⟨c,hc,F⟩:=poet_pull hk hj
  let f:=poet k v i b x
  exact tendsto_integral_of_dominated_convergence _ (fun i=> (integrate_visit (n i) (he i) f).1.aestronglyMeasurable)
    ((spike_int 3).const_mul (25*c)) (fun l=>salary hc (F v i b x) (n l) (he l)) (visit_fit hk hj n hn he)
lemma poet_kern (hk : 0<k) (hj : 4≤j) : ∃ c:ℝ, 0≤c ∧ ∀ (v : Train j) (i b : TypeFace 1) (x : Cover),
    ‖olog k v i b x‖ ≤ c ∧ ∀ n:Side, Even n.val → ‖bedtime k v n (0,i) (wrap n x,b)‖ ≤ c := by
  obtain ⟨c,hc,F⟩:=poet_pull hk hj
  let A:= fun y => 25*c*Cellular.spike 3 y; let a:= max 0 (∫ x,A x); refine ⟨a,le_max_left ..,fun v i b x=>?_⟩
  have hv n (hn:Even (n:Side).val) : ‖bedtime k v n (0,i) (wrap n x,b)‖ ≤ a := by
    rw [walks_cloud i b x hn]; exact (norm_integral_le_of_norm_le ((spike_int 3).const_mul (25*c)) (salary hc (F v i b x) n hn)).trans (le_max_right ..)
  exact ⟨le_of_tendsto ((poet_ends hk hj v i b x _ evenings_grow evenings).norm) (.of_forall fun i=> hv _ (evenings i)),hv⟩
lemma poet_varies (hk : 0<k) (hj : 4≤j) {σ : ℝ} (hs : 0<σ) : ∃ C≥0, ∀ (v w : Train j) X, 0 ≤ X →
    (minusRows (hessian (pink k v)) (hessian (pink k w))).strip σ X →
      ∀ (i b : TypeFace 1) (x : Cover), ‖olog k v i b x-olog k w i b x‖ ≤ C*X ∧
      ∀ n:Side, Even n.val → ‖bedtime k v n (0,i) (wrap n x,b) - bedtime k w n (0,i) (wrap n x,b)‖≤ C*X := by
  obtain ⟨C,hC,F⟩:= furnish hk hj hs
  let c:=max 0 (25*C*∫ x,Cellular.spike 3 x); refine ⟨c,le_max_left ..,fun v w X hX hx i b x=>?_⟩
  let y:=poet k v i b x; let z:=poet k w i b x
  have hv (p:E4) (hp:p∈cells) : ‖(y-z) p‖≤ C*X/‖p‖^2 := by
    change ‖poet k v i b x p - poet k w i b x p‖ ≤ _
    by_cases h:p=0
    · have hz : moon p=0:= (moon_zero p).2 h; simp [poet,hz,curfew]; positivity
    have h₀:= moon_circle hp; have hq:= mt (moon_zero p).mp h
    unfold poet; rw [← Complex.sub_re,← sub_mul]; apply (Complex.abs_re_le_norm _).trans; rw [norm_mul,norm_star, mode_real _ _ h₀.1,mul_one]
    simp only [curfew,hq,fieldD,if_false,mask_value,scaleD_one]; split
    · exact ((F.req X v w hX hx _ h₀ hq (axisEquiv.symm i)).1.both).trans ((mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hC.le (pow_pos (norm_pos_iff.mpr h) _) (pow_le_pow_left₀ (norm_nonneg _) (moon_grip p) _)) hX).trans_eq (by ring))
    rw [sub_zero,norm_zero]; positivity
  have he n (hn : Even (n:Side).val) : ‖bedtime k v n (0,i) (wrap n x,b)- bedtime k w n (0,i) (wrap n x,b)‖ ≤ c*X := by
    rw [walks_cloud i b x hn,walks_cloud i b x hn,← integral_sub (integrate_visit _ hn y).1 (integrate_visit _ hn z).1]
    have hb (p:E4): cells.indicator (fun a=> y (Cellular.visit n a)) p-cells.indicator (fun a=>z (Cellular.visit n a)) p=cells.indicator (fun a=> (y-z) (Cellular.visit n a)) p:= by
       by_cases h:p∈cells <;> simp [h]
    change ‖∫ p,cells.indicator (fun a=>y (Cellular.visit n a)) p-cells.indicator (fun a=>z (Cellular.visit n a)) p‖ ≤ _
    simp_rw [hb]
    refine (norm_integral_le_of_norm_le ((spike_int 3).const_mul _) (salary (mul_nonneg hC.le hX) hv n hn)).trans ?_
    rw [integral_const_mul]; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) hX); exact le_of_eq (by ring)
  refine ⟨le_of_tendsto (((poet_ends hk hj v i b x _ evenings_grow evenings).sub (poet_ends hk hj w i b x _ evenings_grow evenings)).norm) (.of_forall fun i=> he _ (evenings i)),he⟩
end YM.RG08.Drift
