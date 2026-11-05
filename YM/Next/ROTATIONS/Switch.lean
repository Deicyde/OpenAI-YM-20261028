import YM.Next.ROTATIONS.Energy
/-! # Alternation on the same distribution: only using honest integrals -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Row OS Word
open scoped Topology ContDiff BigOperators ENNReal NNReal

abbrev Grouping := Axis→Profile

def Reel (i : Axis) (h : Profile) (p : E4) := (Lap 1 (stamp h) (p i)).re
lemma Reel_real (i : Axis) (h : Profile) (p : E4) (hp : 0≤p i) : ↑(Reel i h p)=Lap 1 (stamp h) (p i) := by
  unfold Reel
  rcases eq_or_lt_of_le hp with hp|hp
  · rw [← hp,zeroLap]; rfl
  rw [evenLap h _ hp]; rfl
lemma reel_int {μ : Measure E4} [SigmaFinite μ] {i : Axis} (h : Profile) (he : Runs μ i 1 (stamp h)) : Integrable (Reel i h) μ :=
  (show Integrable (fun p : E4 => Lap 1 (stamp h) (p i)) μ from Integrable.integral_prod_right he).re

def crop (Q : Finset Axis) (f : Grouping) (p : E4) := ∏ i ∈ Q,f i (p i)
lemma crop_meas (Q) (f : Grouping) : Measurable (crop Q f) := by unfold crop; fun_prop
lemma crop_nonneg (Q) (f : Grouping) (h : ∀ i∈Q,Plus (f i)) (p) : 0 ≤ crop Q f p := Finset.prod_nonneg fun j hj => h j hj _
lemma crop_cons (Q) (f i g p) (hi : i∈Q) : crop Q (update f i g) p = g (p i)*crop (Q.erase i) f p := by
  unfold crop; rw [← Finset.mul_prod_erase _ _ hi]
  rw [update_self]; congr 1; exact Finset.prod_congr rfl fun j hj => by rw [update_of_ne (Finset.mem_erase.mp hj).1]
lemma crop_up (Q f i g) (h : i ∉ Q) : crop Q (update f i g)=crop Q f := funext fun p =>
  Finset.prod_congr rfl fun j hj => by
    change update f i g j (p j) = _
    rw [update_of_ne (show j≠i from fun hp => h (hp ▸ hj))]
lemma crop_int {μ : Measure E4} {g : E4 → ℝ} (hg : Integrable g μ) (Q) (f : Grouping) :
    Integrable (fun p => g p * crop Q f p) μ := by
  refine hg.mul_bdd (crop_meas Q f).aestronglyMeasurable (c:=∏ i∈Q,SchwartzMap.seminorm ℝ 0 0 (f i)) ?_
  filter_upwards with p
  unfold crop; rw [norm_prod]; exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => (f i).norm_le_seminorm ℝ _
lemma crop_read (i : Axis) (f : Grouping) (p : E4) : reading i (fun j => stamp (f j)) p =
    ↑(crop (Finset.univ.erase i) f p) := by
  classical
  -- use products setting time value to 1
  let g := fun j : Axis => stamp (f j)
  let x : Axis→ℂ := update (fun j => g j (p j)) i 1
  have he : reading i g p=∏ j,x j := by
    rw [Fin.prod_univ_succAbove _ i]; unfold x; rw [update_self,one_mul]
    unfold reading tests part
    exact Finset.prod_congr rfl fun k _ => by rw [Function.update_of_ne (i.succAbove_ne k)]
  rw [he,← Finset.mul_prod_erase _ _ (Finset.mem_univ i), show x i=1 from update_self ..,one_mul]
  unfold crop; rw [ofReal_prod]; exact Finset.prod_congr rfl fun j hj => by unfold x; rw [update_of_ne (Finset.mem_erase.mp hj).1]; rfl

/-- Signed response, arbitrary transverse subset. -/
def pay (μ : Measure E4) (i : Axis) (Q : Finset Axis) (h : Profile) (f : Grouping) :=
  ∫ p, Reel i h p * crop (Q.erase i) f p ∂μ

variable {G : Gauge} {L : Register G} {S : Table L}

private lemma full (H : S.Hierarchy) (i j : Axis) (V : Chamber S i) (W : Chamber S j) (A : Weight L) (b c : Bool)
    (hi : Own A i b) (hj : Own A j c) (hbc : b≠c)
    (f : Grouping) (ha : Allows i A A (stamp (f i))) (hb : Allows j A A (stamp (f j))) (hv : Runs (ν V A) i 1 (stamp (f i))) (hw : Runs (ν W A) j 1 (stamp (f j))) :
    pay (ν V A) i Finset.univ (f i) f= -pay (ν W A) j Finset.univ (f j) f := by
  let g : Panels := fun i => stamp (f i)
  have hz (i : Axis) (V : Chamber S i) : (∫ p,answer i 1 g p ∂ν V A)=(pay (ν V A) i Finset.univ (f i) f:ℂ) := by
    unfold pay; rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [before V A] with p hp
    change Lap 1 _ (p i) * _= _
    rw [ofReal_mul, Reel_real _ _ _ hp]; congr 1; exact crop_read ..
  have h₁ := (auto_slice V H A hi g ha hv).2.2; have h₂ := (auto_slice W H A hj g hb hw).2.2
  apply ofReal_injective
  rw [ofReal_neg]
  rw [← hz,← hz]
  apply mul_left_cancel₀ toll_nz
  rw [← h₁,mul_neg,← h₂]
  cases b <;> cases c <;> simp [signValue] at hbc ⊢

private def cloud (f : Grouping) (Q : Finset Axis) (n : ℕ) (j : Axis) :=
    if j ∈ Q then f j else ((n:ℝ)+1) • width (n+1) center
private lemma cloud_at (f : Grouping) (Q n j) (hj : j∉Q) (p : ℝ) : cloud f Q n j p=center (p/((n:ℝ)+1)) := by
  unfold cloud; simp only [if_neg hj,_root_.smul_apply,width_at,smul_eq_mul]; field_simp
private lemma unroll (i : Axis) (A : Weight L) (V : Chamber S i) (Q : Finset Axis) (h : Profile) (f : Grouping)
    (hv : Runs (ν V A) i 1 (stamp h)) :
    Tendsto (fun n => pay (ν V A) i Finset.univ h (cloud f Q n)) atTop (𝓝 (pay (ν V A) i Q h f)) := by
  let l j := max (SchwartzMap.seminorm ℝ 0 0 (f j)) (SchwartzMap.seminorm ℝ 0 0 center)
  have he j p : ∀ᶠ n : ℕ in atTop, cloud f Q n j p= if j∈Q then f j p else 1 := by
    by_cases hk : j∈Q
    · exact .of_forall fun n => by simp [cloud,hk]
    obtain ⟨N,hN⟩ := exists_nat_gt (|p|)
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [if_neg hk,cloud_at _ _ _ _ hk]; apply center_plane
    have hp : 0<(n:ℝ)+1 := by positivity
    rw [abs_div,abs_of_pos hp, div_le_one hp]
    have H : (N:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  let R := Finset.univ.erase i
  let C := ∏ i∈R,l i
  refine tendsto_integral_filter_of_dominated_convergence (F:=fun n p => Reel i h p * crop R (cloud f Q n) p)
    (fun p => ‖Reel i h p‖*C) (Eventually.of_forall fun n => (crop_int (reel_int _ hv) R (cloud f Q n)).1) (Eventually.of_forall fun n => ?_) ((reel_int h hv).norm.mul_const C) ?_
  · filter_upwards with p; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold crop; rw [norm_prod]; unfold C; refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun j _ => ?_
    by_cases h : j∈Q; · simpa [cloud,h,l] using ((f j).norm_le_seminorm ℝ (p j)).trans (le_max_left (SchwartzMap.seminorm ℝ 0 0 (f j)) (SchwartzMap.seminorm ℝ 0 0 center))
    rw [cloud_at f Q n j h]; exact le_max_of_le_right (center.norm_le_seminorm ..)
  filter_upwards with p
  refine Tendsto.congr' ?_ tendsto_const_nhds; filter_upwards [eventually_all.mpr fun j => he j (p j)] with n hn
  congr 1
  unfold crop; symm
  have hh : Q.erase i ⊆ R := Finset.erase_subset_erase _ (Finset.subset_univ _)
  apply Eq.trans (Finset.prod_subset hh (fun j hj hp => ?_)).symm
  · exact Finset.prod_congr rfl (fun j hj => by rw [hn j,if_pos (Finset.mem_of_mem_erase hj)])
  rw [hn j,if_neg]; exact fun H => hp (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1,H⟩)

lemma opp (H : S.Hierarchy) (i j : Axis) (V : Chamber S i) (W : Chamber S j) (A : Weight L) (b c : Bool)
    (hi : Own A i b) (hj : Own A j c) (hbc : b≠c)
    (f : Grouping) (Q : Finset Axis) (he : i∈Q) (hk : j∈Q) (ha : Allows i A A (stamp (f i))) (hb : Allows j A A (stamp (f j))) (hv : Runs (ν V A) i 1 (stamp (f i))) (hw : Runs (ν W A) j 1 (stamp (f j))) :
    pay (ν V A) i Q (f i) f = -pay (ν W A) j Q (f j) f := by
  apply tendsto_nhds_unique (unroll i A V Q (f i) f hv)
  refine ((unroll j A W Q (f j) f hw).neg).congr (fun n => ?_)
  let g := cloud f Q n
  have hz : ∀ i∈Q,g i=f i := by intro i hi; simp [g,cloud,hi]
  exact ((hz i he) ▸ ((hz j hk) ▸ full H i j V W A b c hi hj hbc g ((hz i he).symm ▸ ha) ((hz j hk).symm ▸ hb) ((hz i he).symm ▸ hv) ((hz j hk).symm ▸ hw))).symm

lemma pay_reduce {μ : Measure E4} [SigmaFinite μ] {i : Axis} (f : Grouping) (Q : Finset Axis) (j : Axis) (h g : Profile)
    (hv : Runs μ i 1 (stamp h)) (hk : j∈Q) (he : j≠i) :
    pay μ i Q h (update f j (f j-g))=pay μ i Q h f-pay μ i Q h (update f j g) := by
  have ha := reel_int h hv
  unfold pay
  rw [← integral_sub (crop_int ha _ _) (crop_int ha _ _)]
  congr 1; funext x; rw [crop_cons _ _ _ _ _ (Finset.mem_erase.mpr ⟨he,hk⟩),crop_cons _ _ _ g _ (Finset.mem_erase.mpr ⟨he,hk⟩)]
  have hu : crop (Q.erase i) f x = f j (x j)*crop ((Q.erase i).erase j) f x := (by
    simpa only [update_eq_self] using crop_cons (Q.erase i) f j (f j) x (Finset.mem_erase.mpr ⟨he,hk⟩))
  simp only [_root_.sub_apply,hu,mul_sub,sub_mul]
lemma pay_self {μ : Measure E4} (i : Axis) (Q : Finset Axis) (f : Grouping) (k h : Profile) :
    pay μ i Q k (update f i h)=pay μ i Q k f := by unfold pay; rw [crop_up _ _ _ _ (by simp)]
lemma pay_nonneg {i : Axis} (V : Chamber S i) (A : Weight L) (f : Grouping) (Q : Finset Axis) (h : Profile)
    (hp : ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i h p) (ho : ∀ j∈Q.erase i,Plus (f j)) :
    0 ≤ pay (ν V A) i Q h f :=
  integral_nonneg_of_ae ((before V A).mono fun p hh => mul_nonneg (hp p hh) (crop_nonneg _ _ ho _))
lemma pay_mono {i : Axis} (V : Chamber S i) (A : Weight L) (f : Grouping) (Q : Finset Axis) (h : Profile)
    (hp : ∀ p : E4, 0 ≤ p i → 0 ≤ Reel i h p) (ho : ∀ j∈Q,Plus (f j)) (g k : Profile)
    (hv : Runs (ν V A) i 1 (stamp h)) (j : Axis) (hj : j∈Q) (he : j≠i) (hk : ∀ x : ℝ,g x≤k x) :
    pay (ν V A) i Q h (update f j g) ≤ pay (ν V A) i Q h (update f j k) := by
  have hr : j∈Q.erase i := Finset.mem_erase.mpr ⟨he,hj⟩
  have hu := reel_int h hv
  refine integral_mono_ae (crop_int hu _ _) (crop_int hu _ _) ?_
  filter_upwards [before V A] with p hi
  simp_rw [crop_cons (Q.erase i) _ j _ p hr]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (hk _) (crop_nonneg _ _ (fun i hi => ho i <| Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)) _)) (hp p hi)

lemma alternate (H : S.Hierarchy) (i j : Axis) (V : Chamber S i) (W : Chamber S j) (A : Weight L) (b c : Bool)
    (hi : Own A i b) (hj : Own A j c) (hne : i≠j) (hbc : b≠c)
    (Q : Finset Axis) (f : Grouping) (he : i∈Q) (hk : j∈Q) (a d : Profile)
    (ha : Allows i A A (stamp (f i-a))) (hb : Allows j A A (stamp (f j-d)))
    (hv : Runs (ν V A) i 1 (stamp (f i-a))) (hw : Runs (ν W A) j 1 (stamp (f j-d)))
    (hW : ∀ p : E4, 0 ≤ p j → 0 ≤ Reel j (f j-d) p) (hf : ∀ k∈Q,Plus (f k)) :
    pay (ν V A) i Q (f i-a) f ≤ pay (ν V A) i Q (f i-a) (update f j d) + pay (ν W A) j Q (f j-d) (update f i a) := by
  let g := update (update f i (f i-a)) j (f j-d)
  have hQ : g i=f i-a := (update_of_ne hne ..) |>.trans (update_self ..)
  have hz : g j=f j-d := update_self ..
  have hh := opp H i j V W A b c hi hj hbc g Q he hk (hQ.symm ▸ ha) (hz.symm ▸ hb) (hQ.symm ▸ hv) (hz.symm ▸ hw)
  rw [hQ,hz,pay_self (μ:=ν W A) j Q (update f i _),show g = update (update f j (f j-d)) i (f i-a) from
    update_comm hne _ _ _,pay_self] at hh
  rw [pay_reduce _ _ _ _ _ hv hk hne.symm, pay_reduce _ _ _ _ _ hw he hne] at hh
  have hy := pay_nonneg W A f Q (f j-d) hW (fun i h => hf i (Finset.mem_of_mem_erase h))
  linarith
end YM.Outer
