import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Qualify
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical

/-!
Actual value bound on the *selected* part of Rows.base (pointwise for
all k/fallback tags). Independent of the changed fields Y,z. Selection forces
holes out of each of the used physical neighborhoods, permitting separate
rooted evaluation gauges even along one cut transported row and in turned
bonds. Combine the absolute path/pre-Gaussian tools with the same shot lists,
no alignment of the two different affine formulas by fiat.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.Background
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Precision Tree Matrix
  Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier Next.SectorChange.LocalJet
  Next.SectorChange.Motion Next.SectorChange.Rows
  Next.Fluctuations Bid FiniteMatrix Gaussian
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}
  {T : Tube G S} {A : Stores S} {F : Forest S.ratio} {s : Signed} {V : Config G c} {x : ℝ}

lemma safe (ho : A.flags= RG.flags (temp x) V) {i : Site c} {r : ℕ} (hi : i ∉ A.dome r) {j : Site c} (hj : separation i j ≤ r) (p : PlaqAxes) :
    toll V (j,p) ≤ temp x := by
  by_contra! hp
  have hf : j∈A.flags := ho.symm ▸ (flags_spec ..).2 ⟨(j,p),Work.E01.base_touched (j,p),hp⟩
  exact hi (halo_spec.mpr ⟨j,Finset.mem_union_right _ hf,(separation_comm ..).trans_le hj⟩)
lemma setback (o : Site c) (s : Signed) (i : Bond c) : separation (s.act o) (sendEdge s 0 i).1 ≤ separation o i.1+1 := by
  apply (separation_triangle _ (s.act i.1) _).trans; rw [separation_signed]; gcongr
  unfold sendEdge Step.used affine; split <;> rw [add_zero]
  · change separation _ (_- _) ≤ _; rw [separation]; simp [pdist_step]
  simp

lemma spun {i : Where S} (he : span S.patch x ≤ radiusB x/50) (hh : curb (shots S x) A F x s i)
    (ha : A.flags = RG.flags (temp x) V) {o : Site c} (ho : separation (roots S i) o ≤ radiusB x/50)
    (hp : allot S.patch + 1 ≤ radiusB x) (hN : 100*(1+radiusB x) ≤ c.val) :
    let Y := pull s 0 V; let U := facade S s V 0
    ∃ w : Site c → G.El,
      (∀ e : Bond c, separation o e.1+1 ≤ allot S.patch → G.chord (gauge w Y e) ≤ permit S.patch*temp x) ∧
      (∀ e : Bond f, separation o (S.ratio.parent e.1)+1 ≤ allot S.patch → G.chord (gauge (w ∘ S.ratio.parent) U e) ≤ permit S.patch*temp x) := by
  intro Y U
  have hr := (guarded he hh).1
  obtain ⟨z,hZ⟩ := Work.E08.axial_patch (s.act o) V (allot S.patch) (allot S.patch+1) (by omega) (by omega) (temp x) (temp_nonneg x)
    (fun y hy => safe ha hr (le_trans (separation_triangle _ (s.act o) _) (by rw [separation_signed]; omega)))
  let w := fun j : Site c => z (affine s 0 j)
  let g := S.ratio
  refine ⟨w,fun e hl => ?_,fun e hl => ?_⟩
  · rw [show gauge w Y = pull s 0 (gauge z V) from (Work.F05.pull_gauge_zero ..).symm,turn_read]
    split <;> simpa only [G.chord_inv] using! (hZ (sendEdge s 0 e) ((setback o s e).trans hl))
  have hh : (fun j : Site f => (z ∘ g.parent) (affine s 0 j)) = w ∘ g.parent := by ext; simp [w,affine,Ratio.parent_signed g S.patch.odd_side]
  have hx : U = pull s 0 (replica g V) := fixed_facade ..
  rw [hx, ← hh,← Work.F05.pull_gauge_zero,show (z∘g.parent)=constantGauge z g from rfl,copied _ S.patch.odd_side,turn_read]
  have hy : G.chord (replica g (gauge z V) (sendEdge s 0 e)) ≤ permit S.patch * temp x := by
    have hi := spin_separation (S:=S) e s o
    unfold replica; split
    · rw [G.chord_one]; exact mul_nonneg (by unfold permit; positivity) (temp_nonneg _)
    exact hZ _ (hi.trans hl)
  split; · rwa [G.chord_inv]
  exact hy

lemma turned_face {s : Signed} (p : Cell f) (a : ℝ) (ha : 0≤a) (z : Site c → G.El)
    (h : ∀ e : Bond f, separation (S.ratio.parent p.1) (S.ratio.parent e.1)+1 ≤ allot S.patch → G.chord (gauge (z∘S.ratio.parent) (facade S s V 0) e) ≤ a) :
    toll (facade S s V 0) p ≤ 4*a := by
  let W := gauge (z ∘ S.ratio.parent) (facade S s V 0)
  have he : toll (facade S s V 0) p = toll W p := by unfold W toll; rw [face_gauge,G.chord_conj]
  let T : Config G f := fun e => if separation (S.ratio.parent p.1) (S.ratio.parent e.1) ≤ 4 then W e else 1
  have ht : AgreeNear S.ratio.parent (S.ratio.parent p.1) 4 W T := fun e he => (if_pos he).symm
  have hc (e : Bond f) : G.chord (T e) ≤ a := by
    unfold T; split
    next hi => exact h _ (show _ ≤ allot _ by unfold allot; omega)
    rwa [G.chord_one]
  rw [he,toll,faceValue,travel_near _ (Work.E03.parent_step S) W T _ _ 4 le_rfl ht]
  exact travel_chord T (square ..) p.1 a hc

private lemma frees_plot (S : StepData c f) (x W : ℝ) (V : Config G c) (k : S.Choices) :
    ∃ A : Stores S, A.Plot (1:Config G f) k V x W := by
  let A : Stores S := ⟨∅,∅,∅⟩
  have h b : A.dome b=∅ := by ext; simp [Stores.dome,halo_spec,Stores.place,A]
  refine ⟨A,⟨fun p hp => ?_,fun e he => ?_,fun i hi => ?_,fun j hj => ?_⟩⟩ <;> simp_all only [Finset.disjoint_empty_left,not_true_eq_false,Finset.notMem_empty]

lemma face_base (Pt : Teller G) (P : Patch) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (s : Signed), A.flags=RG.flags (temp x) V →
      (∀ j : Bond c, ‖T.Mw (till x) (temp x) (pull s 0 V) j‖ ≤ C*fiery G x P.L) ∧
      ∀ i : Twin f, Rows.keep x (shots S x) A F (s,.inl i) → ‖Rows.faceFixed T x s V i‖ ≤ C*fiery G x P.L := by
  obtain ⟨C,hC,H⟩ := Work.E04.answer Work.E03.answer Pt
  let B := 8*(permit P)*max C (Real.sqrt Pt.top.clip.direct)
  have hp : 0≤B := mul_nonneg (mul_nonneg (by norm_num) (by unfold permit; positivity)) (hC.le.trans (le_max_left ..))
  refine ⟨B+C,add_pos_of_nonneg_of_pos hp hC,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+1),small_span P,Work.E07.temp_coarse_le G P.L, (H P.L 1).late] with x hx he hT hv
  intro c f S T hP hN hf A F V s ha
  let k := Classical.arbitrary S.Choices
  let U := facade S s V 0
  obtain ⟨O₀,hO⟩ := frees_plot S x 1 (pull s 0 V) k
  have he₀ := hv c f S (congr_arg Patch.L hP) hN T hf F O₀ 1 k (pull s 0 V) (fun _ _ => rfl) hO
  obtain ⟨hc, -,hm⟩ := he₀
  have ht : 0≤fiery G x P.L := temp_nonneg _
  have hL := congr_arg Patch.L hP
  refine ⟨fun j => (hm.hot j).trans ?_, fun i hi => ?_⟩
  · rw [hL]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hp) ht
  have hM := hm.phi i; rw [hL] at hM
  have H : ‖T.Xf (till x) U i‖ ≤ B*fiery G x P.L := by
    have hb {j : Cell f} (hh : separation (S.ratio.parent i.1.1) (S.ratio.parent j.1) ≤ radiusB x/50) :
        toll U j ≤ 8*permit P*fiery G x P.L := by
      obtain ⟨z,-,hz⟩ := spun (S:=S) (hP.symm ▸ he) (show curb (shots S x) A F x s (.inl i.1) from hi) ha hh (by rw [hP]; exact hx) hN
      have he := turned_face j _ (mul_nonneg (by unfold permit; positivity) (temp_nonneg _)) z hz
      rw [hP] at he; exact he.trans (by nlinarith [show 0≤permit P by unfold permit; positivity])
    have ho := hb (show separation (S.ratio.parent i.1.1) (S.ratio.parent i.1.1) ≤ radiusB x/50 by simp)
    have ht₀ := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤8) (show 0≤permit P by unfold permit; positivity)) ht
    unfold Tube.Xf plotted; split
    · apply (hc.valued _ U).trans
      refine (le_trans (Finset.sum_le_sum (g:=fun j => crunch T.up (till x) 1 i.1 j * (8*permit P*fiery G x P.L)) (fun j _ => ?_)) ?_)
      · rcases (hc.attic i.1 j).eq_or_lt with h|h
        · rw [← h,zero_mul,zero_mul]
        exact mul_le_mul_of_nonneg_left (hb (hc.maps _ _ h)) h.le
      unfold B; rw [← Finset.sum_mul,mul_comm (8*_) (max ..),mul_assoc (max ..)]; exact mul_le_mul_of_nonneg_right ((hc.finite _).trans (le_max_left ..)) ht₀
    unfold shoot B; rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), hf.high,mul_comm (8*_) (max ..),mul_assoc (max ..)]
    exact mul_le_mul (le_max_right ..) ((G.curvature_norm _).trans ho) (norm_nonneg _) (hC.le.trans (le_max_left ..))
  apply (norm_sub_le ..).trans ((add_le_add H hM).trans ?_)
  have hl : 1 ≤ (P.L.val:ℝ) := by exact_mod_cast P.L.property
  have he := mul_le_mul_of_nonneg_right (div_le_self hC.le (one_le_pow₀ (n:=2) hl)) ht
  linarith

lemma bond_base (Pt : Teller G) (P : Patch) (hP : P.Branches Pt.bind G) : ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (s : Signed), A.flags = RG.flags (temp x) V →
    ∀ (k : S.Choices) (i : Bond c), Rows.keep x (shots S x) A F (s,.inr i) →
      ‖Z S (S.prediction (facade S s V 0) (Oriented.choice s k)) (pull s 0 V) i‖ ≤ C*fiery G x P.L := by
  obtain ⟨D,r,hD,hr,H⟩ := SectorNext.Remainder.Affine.bond_local P Pt.bind G hP
  obtain ⟨E,δ,hE,hδ,hf⟩ := log_chart_cost G
  let K := permit P
  have hk : 0≤K := by unfold K permit; positivity
  let B := 2*K*E+1
  have hb : 0 < B := by unfold B; positivity
  refine ⟨D*B,mul_pos hD hb,?_⟩
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+1),small_span P, Work.E07.temp_coarse_le G P.L,
    Work.E01.fiery_le G P.L B, Work.E01.fiery_le G P.L (2*K), (Work.E01.largeT_tendsto G P.L).eventually (ge_mem_nhds (lt_min hr hδ))]
    with x hx he hT hz hR hr
  intro c f S T hs hN hF A F V s ha k i hi
  obtain ⟨w,h₁,h₂⟩ := spun (S:=S) (hs.symm ▸ he) (i:=Sum.inr i) (show curb (shots S x) A F x s (.inr i) from hi) ha (o:=i.1) (by simp [roots]) (by rw [hs]; exact hx) hN
  rw [hs] at h₁ h₂
  let U := facade S s V 0; let Y := pull s 0 V; let t := fiery G x P.L
  have ht : 0 ≤ t := temp_nonneg _
  let φ (i : G.El) := G.plog (G.mat i)
  have φs {i : G.El} (h : G.chord i ≤ K * temp x) : i = G.lieExp (φ i) ∧ ‖φ i‖ ≤ B*t := by
    obtain ⟨h₁,h₂⟩ := hf i (le_trans h (le_trans (b:=2*K*t) (by nlinarith) (hR.trans (hr.trans (min_le_right ..)))))
    refine ⟨h₁.symm,h₂.trans ((mul_le_mul_of_nonneg_left h hE.le).trans ?_)⟩
    unfold B; change E*(K*temp x) ≤ (2*K*E+1)*fiery G x P.L; nlinarith only [mul_le_mul_of_nonneg_left hT (mul_nonneg hE.le hk),ht]
  let b := φ ∘ gauge (w ∘ S.ratio.parent) U
  have hQ j (hh : separation i.1 (S.ratio.parent (j:Bond f).1) ≤ predReach S.patch) := φs (i:=gauge (w∘S.ratio.parent) U j) (h₂ j (by rw [hs] at hh; unfold allot; omega))
  have hq := φs (i:=gauge w Y i) (h₁ i (by rw [separation_self]; unfold allot; omega))
  have hh := H c f S hs hF.knobs U U Y 0 b (φ (gauge w Y i)) (choice s k) i w (B*t) (mul_nonneg hb.le ht) (hz.trans (hr.trans (min_le_left ..)))
    (fun j hj => ⟨by rw [Pi.zero_apply,norm_zero]; positivity,(hQ j hj).2⟩) hq.2 (by rw [increment_zero]; exact fun _ _ => rfl)
    (fun j hj => (hQ _ hj).1) hq.1
  exact hh.2.2.2.2.1.trans_eq (mul_assoc ..).symm

lemma base_post (Pt : Teller G) (P : Patch) (hp : P.Branches Pt.bind G) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
    ∀ (A : Stores S) (F : Forest S.ratio) (V : Config G c) (k : S.Choices), A.flags = RG.flags (temp x) V →
    ∀ i, Rows.keep x (shots S x) A F i → ‖Rows.base T x V k i‖ ≤ C*fiery G x P.L := by
  obtain ⟨C,hC,H⟩ := face_base Pt P; obtain ⟨K,hK,h⟩ := bond_base Pt P hp
  refine ⟨K+C,add_pos hK hC,?_⟩
  filter_upwards [H,h] with x hx he
  intro c f S T hs ht hT A F V k ha i hi
  have hz : 0 ≤ fiery G x P.L := temp_nonneg _
  obtain ⟨s,j|j⟩ := i
  · exact ((hx S T hs ht hT A F V s ha).2 j hi).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK.le) hz)
  rw [add_mul]; exact (norm_sub_le ..).trans (add_le_add (he S T hs ht hT A F V s ha k j hi) ((hx S T hs ht hT A F V s ha).1 j))
end YM.AnalyticBridge.MarginalMultiplier3b1d.Background
