import YM.Next.RANK.Anglo
import YM.Work.F05.Actions

/-!
# Kept trigger at the new flags

Always cut ℓ by true length. The short-square ratio has bona fide
footprint O(q) independent of row count. Reserve payment for omitted tails
(on optional groups elsewhere). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {r a : BudgetPoint} {q : ℕ}
variable {C : Clip} {t τ μ A σ Λ : ℝ}
variable (P : PathData G)

def Turnon (C : Clip) (τ : ℝ) (b : ℕ) := 2≤ τ* Real.exp ((b:ℝ)/C.relaxation)

lemma provoke (h : Turnon C t q) (ht : 0<t) (x : Site n) (U : Config G n) : kept C t x U ↔
    ∀ p : Face (Per n), p.1∈ halo q {x} → G.chord (faceValue U p) ≤ t*Real.exp (separation x p.1/C.relaxation) := by
  refine ⟨fun h p _=> h p, fun H p=>?_⟩
  by_cases hh : p.1∈ halo q {x}
  · exact H p hh
  have he : q≤ separation x p.1:= Nat.le_of_lt (lt_of_not_ge fun hp=> hh (halo_spec.mpr ⟨x,mem_singleton_self _,hp⟩))
  apply ((G.chord_le_two _).trans h).trans; gcongr
  · exact C.radius_pos.le

lemma province (h : Turnon C t q) (ht : 0<t) (hb : 8≤q) (x : Site n) (U V : Config G n)
    (hf : Agrees (halo (2*q) {x}) U V) : kept C t x U ↔ kept C t x V:= by
  rw [provoke h ht,provoke h ht]; refine forall_congr' fun p=> imp_congr_right fun hp=> ?_
  have hh : Agrees (touched p) U V := by
    refine agrees_mono hf fun z hz=>?_ ; obtain ⟨y,hy,hf⟩:= halo_spec.mp hp; rw [mem_singleton] at hy; subst y
    obtain ⟨y,he,H⟩:= halo_spec.mp (touching p p.1 (touch_here p) hz); rw [mem_singleton] at he; subst y
    exact halo_spec.mpr ⟨x,mem_singleton_self _,(separation_triangle _ p.1 _).trans (by omega)⟩
  rw [show faceValue U p=faceValue V p from travel_local _ _ _ _ (fun i a b=>hh i (List.mem_toFinset.mpr a) (List.mem_toFinset.mpr b))]
lemma kept_sym (k : Site n→G.El) (x : Site n) (U : Config G n) : kept C t x (Lattice.gauge k U) ↔ kept C t x U := by unfold kept; simp_rw [face_gauge,Gauge.chord_conj]
lemma dam_leg (H : Turnon C τ q) (ht : τ≤t) (hq : 8≤q) (hu : 0<τ) : LocalOn (halo (2*q) ({0}:Support n)) (dam (n:=n) (G:=G) C t τ) := by
  intro U V h
  unfold dam lock; have hh : Turnon C t q := H.trans (mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le)
  simp_rw [province hh (hu.trans_le ht) hq 0 U V h,province H hu hq 0 U V h]; split_ifs<;> rfl
lemma dam_gauge : GaugeInvariant (dam (n:=n) (G:=G) C t τ) := by
  intro i U; unfold dam lock; simp_rw [kept_sym]; split_ifs <;> rfl
lemma dam_zero (q : ℕ) (h : Turnon C τ q) (hu : 0<τ) (U : Config G n) (he : Healthy τ (halo q {0}) U) : dam C t τ U=0 := by
  refine if_neg fun hx => hx.2 ((provoke h hu ..).2 fun i hi=> ?_)
  have hz : G.chord (faceValue U i)≤τ:= le_of_not_gt fun H=> disjoint_left.mp he hi ((flags_spec ..).mpr ⟨i,touch_here _,H⟩)
  have hh := C.radius_pos
  exact hz.trans (le_mul_of_one_le_right hu.le (Real.one_le_exp (by positivity)))
lemma dam_sign (U : Config G n) : 0 ≤ dam C t τ U ∧ dam C t τ U≤1 := by unfold dam; split<;>simp
lemma dam_meas : Measurable (dam (n:=n) (G:=G) C t τ):= by
  apply Measurable.ite _ measurable_const measurable_const
  exact (kept_closed C t 0).measurableSet.inter (kept_closed C τ 0).measurableSet.compl

def drip (q : ℕ) (p : PlaqAxes) (U : Config G n) i := if (P.row p i).2.length≤q then P.ellTerms (0,p) i U else 0

def lakeHead (q : ℕ) (p : PlaqAxes) (U : Config G n) := ∑' i,drip P q p U i

def basin (q : ℕ) (C : Clip) (t τ : ℝ) (U : Config G n) := ∑ p, dam C t τ U * ‖lakeHead P q p U‖^2/2

lemma summable_lake (h : P.Bounds C σ μ Λ) (q : ℕ) (U : Config G n) (p : PlaqAxes) : Summable (drip P q p U) :=
  (((P.ell_dominated h (0,p)).summable U).indicator (s:={ i| (P.row p i).2.length ≤ q})).congr fun i=>by by_cases h : (P.row p i).2.length≤q<;>simp [Set.indicator,drip,h]

lemma steamed (p : Face (Per n)) (i) : LocalOn (lives p.1 (P.row p.2 i).2) (P.ellTerms p i) := by
  intro U V H; unfold ellTerms; apply congr_arg
  let x:=(P.row p.2 i).2
  apply LocalOn.expandAt x.stencil x.eval x.covered p.1
  intro s hs hz; apply H
  · simpa only [lives,Finset.coe_image] using! hs
  simpa only [lives,Finset.coe_image] using! hz
lemma dripping_loc (q : ℕ) (p : PlaqAxes) : LocalOn (halo q ({0}:Support n)) (lakeHead (n:=n) P q p) := by
  intro U V h; refine tsum_congr fun i=>?_ ; unfold drip; split
  · rename_i ht
    refine (steamed P (0,p) i) U V (agrees_mono h fun u hu =>?_)
    let S:= (P.row p i).2
    have he : u∈ visits 0 (S.walk ++ square S.plaq.val.1 S.plaq.val.2):= List.mem_toFinset.mp (show u∈ orbit 0 _ from (show u∈ orbit (0 : Site n) _ from reached 0 S ▸ (show u∈ lives (0 : Site n) S from hu)))
    have hn (u v : Site n) (w : Walk) (he : v∈ visits u w) : separation u v≤ w.length := by
      induction w generalizing u with
      | nil => simp only [visits,List.mem_singleton] at he; simp [he]
      | cons d w ih=>
        rcases List.mem_cons.mp he with he|he
        · simp [he]
        apply (separation_triangle u (u+d.vec) v).trans
        have hh:= ih _ he; have hf : separation u (u+d.vec) ≤ 1 := by
          rw [separation_comm, separation, add_comm, add_sub_cancel_right, Step.vec]; split
          · rw [pdist_neg]; exact pdist_step _
          exact pdist_step _
        simp only [List.length_cons]; omega
    exact halo_spec.mpr ⟨0,mem_singleton_self _,(hn _ _ _ he).trans (by rw [List.length_append]; exact ht)⟩
  rfl
lemma steam (p : Face (Per n)) (i) (U : Config G n) (k : Site n→G.El) : P.ellTerms p i (Lattice.gauge k U)= G.adjoint (k p.1) (P.ellTerms p i U):= by
  unfold ellTerms; rw [Work.F05.slot_gauge,G.adjoint (k p.1)|>.map_smul]
lemma lake_gauge (h : P.Bounds C σ μ Λ) (U : Config G n) (k : Site n→ G.El) (p : PlaqAxes) (q) :
    lakeHead P q p (Lattice.gauge k U)= G.adjoint (k 0) (lakeHead P q p U) := by
  let f := (G.adjoint (k 0)).toContinuousLinearMap
  have hh := f.map_tsum (summable_lake P h q U p)
  unfold lakeHead; apply Eq.trans _ hh.symm; apply tsum_congr; intro i; unfold drip; split_ifs
  · exact steam ..
  exact (map_zero f).symm
lemma basin_positive (U : Config G n) : 0≤ basin P q C t τ U:= sum_nonneg fun i _=> div_nonneg (mul_nonneg (dam_sign _|>.1) (sq_nonneg _)) (by norm_num)
lemma basin_gauge (h : P.Bounds C σ μ Λ): GaugeInvariant (basin P q (n:=n) C t τ):= by
  intro i U; simp only [basin, lake_gauge P h U i, dam_gauge i U,G.norm_adjoint]
lemma lake_meas (p : PlaqAxes) (q : ℕ) : Measurable (lakeHead P q (n:=n) p) := by
  apply Measurable.tsum; intro i; unfold drip; split
  · apply Continuous.measurable; unfold ellTerms Slot.atSite expandAt; fun_prop
  exact measurable_const
lemma basin_meas : Measurable (basin P q (n:=n) C t τ) := Finset.measurable_fun_sum _ fun i _=> (dam_meas.mul ((lake_meas P i q).norm.pow_const _)).div_const _
lemma basin_loc (h : Turnon C τ q) (ht : τ ≤ t) (hq : 8≤q) (hu : 0<τ) : LocalOn (halo (2*q) ({0}:Support n)) (basin (n:=n) P q C t τ) := by
  intro U V hh; unfold basin; rw [dam_leg h ht hq hu U V hh]; simp only [dripping_loc P q _ U V (agrees_mono hh (by intro x hx; exact halo_mono (b:=2*q) (by omega) (subset_refl _) hx))]
lemma basin_void (h : Turnon C τ q) (hu : 0<τ) (U : Config G n) (he : Healthy τ (halo q {0}) U) : basin P q C t τ U=0:= by simp only [basin,dam_zero q h hu U he,zero_mul,zero_div,sum_const_zero]
end YM.Next.Rank.Alarm
