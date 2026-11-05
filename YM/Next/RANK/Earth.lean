import YM.Next.RANK.Alarm


/-!
# Vertex splitting of the directly clipped base

Retain exact negative direct change in same symmetry/normalization. Trigger
once per flagged site (all incident plaquettes read, true equality retained).
At any such site retain positive gain proportional to k's β and τ² from
at least one incident face. Small or equality at old/new branch checked. Share
short kept-square ratio on whole mask from province.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {ι κ : Type}
variable {c : Clip} {τ t : ℝ}

lemma delta_cut (c : Clip) (hu : 0<τ) (h : 2*τ ≤ t) {r : ℝ} (he : τ < r) :
    c.linear * τ^2 ≤ PathData.clipped c t r - clipped c τ r := by
  unfold clipped; rw [if_neg (not_le_of_gt he)]; split
  · have hT:= c.kink; have hp : 0 < r:= hu.trans he
    have hc := mul_le_mul_of_nonneg_left (show τ*τ ≤ τ*r from mul_le_mul_of_nonneg_left he.le hu.le) c.tail_pos.le
    have heq := mul_lt_mul_of_pos_right hT (show 0 < τ*r from mul_pos hu hp)
    have hb := mul_le_mul_of_nonneg_left (show τ*r ≤ r*r from mul_le_mul_of_nonneg_right he.le hp.le) c.quadratic_pos.le
    linarith only [hc,heq,hb, mul_nonneg c.tail_pos.le (show _ from mul_nonneg hu.le hp.le)]
  have ht:=mul_le_mul_of_nonneg_left h c.tail_pos.le
  have hn :=mul_le_mul_of_nonneg_left he.le (mul_pos c.tail_pos hu).le; linarith only [hn,mul_le_mul_of_nonneg_right ht (hu.trans he).le]
lemma delta_lo (c : Clip) (hu : 0<τ) (h : 2*τ≤t) (r : ℝ) : 0 ≤ clipped c t r - clipped c τ r := by
  rcases lt_or_ge τ r with hh|hh
  · exact (mul_nonneg c.tail_pos.le (sq_nonneg _)).trans (delta_cut c hu h hh)
  simp only [clipped, if_pos (show r≤t by linarith only [hu,h,hh]), if_pos hh]; rw [sub_self]

def Delta (c : Clip) (t τ : ℝ) (p : Face (Per n)) (U : Config G n) := clipped c t (G.chord (faceValue U p))-clipped c τ (G.chord (faceValue U p))
def Shift (c : Clip) (t τ : ℝ) (U : Config G n) := ∑ p : Face (Per n), Delta c t τ p U

lemma sendX (s : Signed) (x : Site n) (U : Config G n) (a : Face (Per n)) : Delta c t τ (Face.send s x a) U = Delta c t τ a (pull s x U) := by
  unfold Delta; rw [Face.send_price U _ _ _ G.chord G.chord_inv (fun k g=>G.chord_conj g k)]
lemma shift (s : Signed) (x : Site n) (U : Config G n) : Shift c t τ U= Shift c t τ (pull s x U) := by
  symm
  exact sum_bij (fun i _=> Face.send s x i) (fun _ _=> mem_univ _) (fun _ _ _ _ h=> Face.injective_send s x h) (by
    intro i _; obtain ⟨j,h⟩:= Finite.injective_iff_surjective.mp (Face.injective_send s x) i; exact ⟨j,mem_univ _,h⟩) (fun i _=> (sendX ..).symm)

lemma touching (a : Face (Per n)) (y : Site n) (he : y∈ touched a) : touched a ⊆ halo 8 {y} := by
  have hp : ¬ Disjoint ({y}:Support n) (touched a) := not_disjoint_iff.mpr ⟨y,mem_singleton_self _,he⟩
  intro x hx; exact inspect {y} (mem_union_right _ (mem_biUnion.mpr ⟨a,mem_univ _,(show _ from by rwa [if_neg hp])⟩))
lemma touch_pay (a : Face (Per n)) : (touched a).card≤5 := by
  unfold touched; apply (List.toFinset_card_le ..).trans; simp [visits,square]
lemma touch_here (a : Face (Per n)) : a.1∈ touched a := by simp [touched,visits,square]

def sceneAt (c : Clip) (t τ : ℝ) (x : Site n) (U : Config G n) :=
    ∑ p∈ Finset.univ.filter (fun p : Face (Per n)=> x∈touched p), Delta c t τ p U/↑(touched p).card

lemma scene_pay (c : Clip) {t τ : ℝ} (hu : 0<τ) (h : 2*τ≤ t) (U : Config G n) (x : Site n) (hx : x∈flags τ U) :
    c.linear / 5 * τ^2 ≤ sceneAt c t τ x U := by
  obtain ⟨a,hv,hp⟩:= (flags_spec ..).1 hx
  let X:= sceneAt c t τ x U; let m := fun p => Delta c t τ (n:=n) p U/↑(touched p).card
  apply le_trans _ (single_le_sum (f:=m) (fun i _=> div_nonneg (delta_lo c hu h _) (Nat.cast_nonneg _)) (mem_filter.mpr ⟨mem_univ _,hv⟩))
  rw [show m a= Delta c t τ a U/_ from rfl, le_div_iff₀ (show 0 < ((touched a).card:ℝ) by exact_mod_cast card_pos.mpr ⟨x,hv⟩)]
  have hh : (↑(touched a).card:ℝ) ≤ 5 := by exact_mod_cast touch_pay a
  linarith only [mul_le_mul_of_nonneg_left hh (mul_nonneg c.tail_pos.le (sq_nonneg τ)), show c.linear*τ^2≤Delta c t τ a U from delta_cut c hu h hp]
lemma scenes (c : Clip) (U : Config G n) (h : τ ≤ t) :
    ∑ x∈ flags τ U,sceneAt c t τ x U = Shift c t τ U := by
  have hv (x) (hx : x∉flags τ U) : sceneAt c t τ x U=0 := by
    apply sum_eq_zero; intro i hi
    have hh : G.chord (faceValue U i) ≤ τ := le_of_not_gt fun he=> hx ((flags_spec ..).2 ⟨i,(mem_filter.mp hi).2,he⟩)
    unfold Delta clipped; rw [if_pos (hh.trans h),if_pos hh,sub_self,zero_div]
  rw [sum_subset (subset_univ (flags τ U)) (fun i hi hn=> hv _ hn)]; unfold sceneAt; simp_rw [sum_filter]; rw [sum_comm]; apply sum_congr rfl; intro p _
  have ha : 0 < (touched p).card := card_pos.mpr ⟨p.1,touch_here _⟩
  let d:= Delta c t τ p U; let w:=(touched p).card
  have hw : 0<w := ha
  calc
    _ = ∑ x ∈ touched p,d/w:=by rw [← sum_filter]; have h : univ.filter (fun x => x∈ touched p)=touched p:=filter_mem_eq_inter .. |>.trans (univ_inter ..); rw [h]
    _ = (w:ℝ)*(d/w):= by simp only [sum_const,nsmul_eq_mul];rfl
    _ = _ := by change _=d; field_simp

lemma scene_loc (x : Site n) : LocalOn (halo 8 {x}) (sceneAt (G:=G) c t τ x) := by
  intro U V h; apply sum_congr rfl; intro i hi
  unfold Delta; rw [show faceValue U i=faceValue V i from travel_local _ _ U V (fun z hx he => h z (touching i x (mem_filter.mp hi).2 (List.mem_toFinset.mpr hx)) (touching i x (mem_filter.mp hi).2 (List.mem_toFinset.mpr he)))]
lemma scene_gauge (x : Site n) : GaugeInvariant (sceneAt (G:=G) c t τ x) := by intro k U; unfold sceneAt Delta; simp only [face_gauge, Gauge.chord_conj]
lemma scene_moves (s : Signed) (x i : Site n) (U : Config G n) : sceneAt c t τ (affine s x i) U = sceneAt c t τ i (pull s x U) := by
  symm; unfold sceneAt; simp_rw [sum_filter]; let Z : Equiv.Perm (Face (Per n)):=Equiv.ofBijective (Face.send s x) ⟨Face.injective_send .., Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩
  apply Fintype.sum_equiv Z; intro p; rw [show Z p=Face.send s x p from rfl,sendX,Work.H03.touched_send]
  by_cases hh : i∈ touched p
  · rw [if_pos hh,if_pos (mem_image_of_mem _ hh),Finset.card_image_of_injective _ (show Function.Injective (affine s x) from (sends s x).injective)]
  rw [if_neg hh]; exact (if_neg (fun H => hh ((stay s x _).1 H))).symm
lemma scene_meas (x : Site n) : Measurable (sceneAt (G:=G) c t τ x) := by
  refine Finset.measurable_fun_sum _ fun j _=> ?_
  have he (p : Face (Per n)) (u : ℝ) : Measurable fun U : Config G n=> clipped c u (G.chord (faceValue U p)):= by
    have hm : Continuous fun U : Config G n=> G.chord (faceValue U p):=by unfold faceValue;fun_prop
    let f (U:Config G n):= G.chord (faceValue U p)
    refine Measurable.ite ((isClosed_le hm continuous_const).measurableSet) (f:=fun U=> c.direct*f U^2/2) (g:=fun U=>c.linear*u*f U) ?_ ?_ <;> unfold f <;> apply Continuous.measurable <;> unfold faceValue <;> fun_prop
  exact ((he ..).sub (he ..)).div_const _
end YM.Next.Rank.Alarm
