import YM.Work.D04

/-!
# Charge even when passing to an auxiliary sublimit, without changing the Proof of Base

Adapted from the *private* lemmas in `YM.Work.D04` for the actual D02 costs.
`matched` is extended to any finer filter; can't necessarily assume an iterated-subsequence
witness on a sublimit. No change to the snapshots or f.fuse costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Columns.ExtensionCost

open YM.Bid Set Filter Function MeasureTheory Extraction Extraction.Lease Dash Wilson Table
open scoped Topology BigOperators

variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}

/-! ### Single distinguished slot on the actual Wilson law -/

private lemma sober_of_cont {P : Trial C} (h : ∀ N p x, Continuous (P N p x)) :
    sober C P F := by
  apply (Order.fused F (fun j => ∀ x, Measurable (P j.1 j.2 x) ∧
    ∃ A : ℝ, ∀ v, ‖P j.1 j.2 x v‖ ≤ A)).mp
  exact Eventually.of_forall fun (N,p) x =>
    ⟨(h N p x).measurable,
      (h N p x).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)⟩

lemma sober_upper {e : ℕ} (w : Rowe C e) : sober C (upper C w) F :=
  sober_of_cont fun N p x => C.continuousO N p e (w (N,p)) x

private lemma separate_slot (P : Trial C) (v : Shot C.book) (N p : ℕ)
    (z : Fin v.n → Lattice.Site (C.side N p)) :
    featuring P v.left v.i N p z = moment (C.beta N p)
      (fun U => P N p (z v.i) U * ∏ j ∈ Finset.univ.erase v.i, C.seen (v.left j) (z j) U) := by
  unfold featuring
  congr 1
  funext U
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.i), if_pos rfl]
  congr 1
  exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)

/-- Splitting uses *integrable* moments. Trials used together here are
measurable bounded at each site (eventually; bound can depend on cutoff, period,
site); so are their differences. -/
private lemma target_sub {P Q : Trial C} (hp : sober C P F) (hq : sober C Q F)
    (v : Shot C.book) :
    ∀ᶠ u in F.fuse, targetB (P-Q) v u.1 u.2 = targetB P v u.1 u.2 - targetB Q v u.1 u.2 := by
  rw [Order.fused, Order.late]
  unfold sober Order.late at hp hq
  filter_upwards [hp, hq] with i hi hi'
  filter_upwards [hi, hi'] with j h h'
  let N := F.mesh j
  let p := F.per i
  change targetB (P-Q) v N p = targetB P v N p - targetB Q v N p
  unfold targetB
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_sub]
  congr 1
  rw [separate_slot, separate_slot, separate_slot]
  let R := fun U : Config G (C.side N p) =>
    ∏ j ∈ Finset.univ.erase v.i, C.seen (v.left j) (z j) U
  have hc : Continuous R := continuous_finsetProd _ fun b _ =>
    C.continuousO N p (v.left b).1 (v.left b).2 _
  have hR : Integrable R (law G _ (C.beta N p)) := continuous_integrable _ hc
  have H (T : Config G (C.side N p) → ℂ) (hT : Measurable T ∧ ∃ A : ℝ, ∀ U, ‖T U‖ ≤ A) :
      Integrable (fun U => T U * R U) (law G _ (C.beta N p)) := by
    obtain ⟨hm,A,hA⟩ := hT
    exact hR.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hA)
  unfold moment
  rw [← integral_sub (H _ (h (z v.i))) (H _ (h' (z v.i)))]
  apply integral_congr_ae
  filter_upwards with U
  change (P N p (z v.i) U - Q N p (z v.i) U) * R U = _
  rw [sub_mul]

lemma upper_scan {e : ℕ} (w : Rowe C e) (v : Shot C.book) (N p : ℕ) :
    targetB (upper C w) v N p = snapshots v e (N,p) (w (N,p)) := by
  change targetB _ v N p = Order.smears C N p (v.record (d := e) (w (N,p))) v.f
  unfold targetB Order.smears
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  rw [Family.num]; unfold featuring moment
  apply integral_congr_ae
  filter_upwards with U
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = v.i
  · subst j
    rw [if_pos rfl, Shot.record, update_self]
    rfl
  rw [if_neg h, Shot.record, update_of_ne h]

/-- Transfer of tested values between sober trials with the actual rent on
P-Q. Use the centered book with Lease.take, don't treat point convergence as
covering projection ties. -/
private lemma follow {l : Filter (ℕ × ℕ)} (hl : l ≤ F.fuse) (W : YM.Bid.D02) (h : C.Makes) (c : CenterPort C F)
    {P Q : Trial C} (hp : sober C P F) (hq : sober C Q F)
    (he : YM.Bid.close C F (P-Q)) (v : Shot C.book) {L : ℂ}
    (hL : Tendsto (uncurry (targetB Q v)) l (𝓝 L)) :
    Tendsto (uncurry (targetB P v)) l (𝓝 L) := by
  obtain ⟨y, hy, hr⟩ := he
  have ht := W h c (P-Q) ⟨y,hy,Lease.take h (c.book _ _) hr⟩ v
  have ha := (ht.mono_left hl).add hL
  rw [zero_add] at ha
  apply ha.congr'
  filter_upwards [target_sub hp hq v |>.filter_mono hl] with u hu
  change targetB (P-Q) v u.1 u.2 + targetB Q v u.1 u.2 = _
  rw [hu, sub_add_cancel]; rfl

private lemma marked_silent (W : YM.Bid.D02) (h : C.Makes) (c : CenterPort C F)
    {e : ℕ} (R : Bin S) (hx : RelayBin C R F e) (x : Rowe C e)
    (hr : ∀ j, (R e).step j (x j) = 0) (hd : dollar C F x) (i : Shot C.book) :
    Tendsto (fun u => snapshots i e u (x u)) F.fuse (𝓝 0) := by
  obtain ⟨z,hz,he,hb⟩ := hx.mark x hr hd
  have hg : gain z F (fun _ _ => 0) := by
    intro n q j δ hδ
    refine ⟨0, le_rfl, ?_⟩
    have hm := he n q j δ hδ
    unfold Order.late at hm ⊢
    filter_upwards [hm] with r hm'
    filter_upwards [hm'] with s hs x H
    rw [hs x H]; simp
  have ha := W h c z ⟨_, tendsto_const_nhds, hg⟩ i
  refine (follow le_rfl W h c (sober_upper x) hz hb i ha).congr' (Eventually.of_forall ?_)
  rintro ⟨N,p⟩
  exact upper_scan x i N p

/-! ### Paying only top-coordinate costs -/

private lemma dollar_shrink {e : ℕ} {x : Rowe C e} (h : dollar C F x)
    (b : ℕ × ℕ → ℂ) (hb : ∀ j, ‖b j‖ ≤ 1) :
    dollar C F (fun j => b j • x j) := by
  intro ε hε
  have ht := h ε hε
  unfold Order.late at ht ⊢
  filter_upwards [ht] with p hp
  filter_upwards [hp] with j hj
  rw [map_smul, norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb _)).trans hj

private lemma dollar_sub {e : ℕ} {x y : Rowe C e} (hx : dollar C F x) (hy : dollar C F y) :
    dollar C F (d := e) (fun j => x j-y j) := by
  intro ε hε
  have hr := hx _ (half_pos hε)
  have hs := hy _ (half_pos hε)
  have hm : Tendsto (fun j : ℕ => Real.exp ((ε/2)*C.S.scale (F.mesh j))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((C.S.divergent.comp F.mesh.cofinal).const_mul_atTop (half_pos hε))
  unfold Order.late at hr hs ⊢
  filter_upwards [hr,hs] with p hp hq
  filter_upwards [hp,hq,hm.eventually_ge_atTop 2] with i ha hb hi
  rw [map_sub]
  refine (norm_sub_le _ _).trans ((add_le_add ha hb).trans ?_)
  let s := C.S.scale (F.mesh i)
  change Real.exp ((ε/2)*s) + Real.exp ((ε/2)*s) ≤ Real.exp (ε*s)
  change 2 ≤ Real.exp ((ε/2)*s) at hi
  rw [show ε*s = (ε/2)*s + (ε/2)*s by ring, Real.exp_add]
  nlinarith [Real.exp_pos ((ε/2)*s)]

/-- x itself need not be tight. Normalize both pieces by the size of the
projected piece; this is enough to use mark on the normalized remainder. -/
private lemma cost_limit (T : YM.Bid.D01) (W : YM.Bid.D02) (h : C.Makes)
    (c : CenterPort C F) (R : Bin S) {e : ℕ} (H : RelayBin C R F e)
    {x : Rowe C e} (hx : dollar C F x) (i : Shot C.book) :
    Tendsto (fun u => snapshots i e u (x u - (R e).step u (x u)) /
      (1 + (↑‖(R e).step u (x u)‖ : ℂ))) F.fuse (𝓝 0) := by
  let p : Rowe C e := fun u => (R e).step u (x u)
  let a (j : ℕ × ℕ) := (1+‖p j‖)⁻¹
  let b (j : ℕ × ℕ) := (↑(a j) : ℂ)
  let z : Rowe C e := fun j => b j • (x j-p j)
  have hn (j) : ‖b j‖ = (1+‖p j‖)⁻¹ := by
    unfold b a
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hb (j) : ‖b j‖ ≤ 1 := by
    rw [hn, ← one_div]
    exact (div_le_one (by positivity)).mpr (by simp)
  have ht : tight C F (d := e) (fun j => b j • p j) := by
    refine ⟨1,?_⟩
    apply (Order.fused F (fun j => ‖b j • p j‖ ≤ 1)).mp
    refine Eventually.of_forall fun j => ?_
    rw [norm_smul, hn, mul_comm, ← div_eq_mul_inv]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hz : dollar C F z := by
    have he := dollar_sub (dollar_shrink hx b hb) (T C h e F _ ht)
    simpa only [z, smul_sub] using he
  have hk (j) : (R e).step j (z j) = 0 := by
    simp only [z, p, map_smul, map_sub, (R e).projection, sub_self, smul_zero]
  apply (marked_silent W h c R H z hk hz i).congr'
  filter_upwards with j
  rw [show z j=_ • (x j-p j) from rfl,map_smul,smul_eq_mul]
  rw [div_eq_mul_inv,mul_comm, show b j = (↑((1+‖p j‖)⁻¹) : ℂ) from rfl,
    Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_one]

lemma matched {l : Filter (ℕ × ℕ)} (hl : l ≤ F.fuse) (T : YM.Bid.D01) (W : YM.Bid.D02) (h : C.Makes) (c : CenterPort C F)
    (R : Bin S) {e : ℕ} (H : RelayBin C R F e) {P : Trial C} (hp : sober C P F)
    (hx : vet C F e P) {m : Shot C.book → ℂ}
    (hm : ∀ i, Tendsto (uncurry (targetB P i)) l (𝓝 (m i))) :
    ∃ x, Added m x (R e) l (fun i => snapshots i e) := by
  obtain ⟨x,hw,hz⟩ := hx
  refine ⟨x, fun i => ?_, fun i => (cost_limit T W h c R H hw i).mono_left hl⟩
  refine (follow hl W h c (sober_upper x) hp hz i (hm i)).congr' (Eventually.of_forall ?_)
  rintro ⟨N,p⟩
  exact upper_scan x i N p

end YM.OPE.Columns.ExtensionCost
