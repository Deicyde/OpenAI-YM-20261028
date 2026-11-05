import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Drift

/-!
# Normalized `t'` jets of the actual `chi`-extended frozen logs

A pointwise cost even over arbitrary Haar values. Does not change the
support used by a license. Finite smoothness order unlike group matrix
jets. Handle points even on boundary of the log extension
indicator by a compact margin. Does not read actual seeds as smooth.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Offset
open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange YM.Next.SectorChange.Rows
open YM.Push.Uniform
open YM.Push.SectorMeasure
open YM.LocalH Metric Set
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {R k n L : ℕ} {C M B σ d s t x r κ : ℝ} {S : StepData c f}
    {A : Stores S} {F : Forest S.ratio}

private def resized (q : Chi) (v : G.Color) := broad q 1 v • v
private lemma actual (q : Chi) (v : G.Color) (hd : 0 < d) : broad q d v • v = d • resized q (d⁻¹ • v) := by
  unfold resized; rw [smul_comm d]; simp only [smul_smul, mul_inv_cancel₀ hd.ne', one_smul]
  unfold broad Chi.innerShare; rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hd).le,div_one,mul_comm,div_eq_mul_inv]

private lemma fixed_scale (q : Chi) (G : Gauge) (n : ℕ) : ∃ K : ℝ, 0<K ∧
    ∀ x ∈ closedBall (0:G.Color) 2, Through n (resized q) x K := by
  have hf : ContDiff ℝ ∞ (resized q (G:=G)) := (broad_smooth q 1).smul contDiff_id
  choose X hX using fun k : ℕ => (isCompact_closedBall (0:G.Color) 2).exists_bound_of_continuousOn
    ((hf.continuous_iteratedFDeriv (m:=k) (WithTop.coe_le_coe.mpr le_top)).continuousOn)
  let M := ∑ i ∈ Finset.range (n+1), |X i|
  refine ⟨max 1 M,zero_lt_one.trans_le (le_max_left ..),fun x hx => ⟨(hf.of_le (m:=n) (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    fun i hi => ?_⟩⟩
  have hu : |X i| ≤ M := Finset.single_le_sum (f:=fun j => |X j|) (fun j _ => abs_nonneg _) (Finset.mem_range.mpr (show i < n+1 by omega))
  exact (hX _ _ hx).trans ((le_abs_self _).trans (hu.trans (le_max_right ..)))

-- Sufficient condition keeps the fixed log patches entirely independent of periods.
lemma patch_price (G : Gauge) (hC : 0 ≤ C) (q : Chi) (n : ℕ) (B : ℝ) (hB : 0<B) :
    ∃ M : ℝ, 0<M ∧ ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : E → G.El), Allows n (fun z => G.mat (U z)) 0 C → ∀ (s t : ℝ), 0<t → 0≤s → s≤1 → s ≤ 2*t →
      2*(B*t) ≤ firstRadius G/2 → Through n (fun z => patched q (B*t) (U (s • z))) 0 (M*t) := by
  let Ω := closedBall (0:G.Color) (firstRadius G/2)
  let T := G.lieExp '' Ω
  have hR : firstRadius G/2 < firstRadius G := half_lt_self (first_pos _)
  have he : Ω ⊆ firstBall G := closedBall_subset_ball hR
  have hΩ : T ⊆ firstChart G := image_mono he
  have hT : IsCompact (G.mat '' T) := ((isCompact_closedBall ..).image G.lieExp_cont).image G.continuous_mat
  obtain ⟨K,hK,h⟩ := exists_allows hT (f:=G.plog) (by rintro x ⟨u,hu,rfl⟩; exact (first_geom G).2.2.2.2.2.2 u (hΩ hu)) n
  obtain ⟨b,hb,hh⟩ := fixed_scale q G n
  let P := composeCost n K C; let A := max (2*P) (2*B); let X := composeCost n b (B⁻¹*A)
  have hp : 0 ≤ P := by unfold P composeCost; positivity
  have ha : 0 < A := lt_of_lt_of_le (show 0 < 2*B by positivity) (le_max_right ..)
  have hx : 0 < X := by unfold X composeCost; positivity
  refine ⟨B*X,mul_pos hB hx,?_⟩
  intro E _ _ U hU s t ht hs hs' hv hr
  let W (z : E) := U (s • z); let d := B*t
  have hW0 : W 0=U 0 := by unfold W; rw [smul_zero]
  have hW : ContinuousAt W 0 := (show ContinuousAt U (s • (0:E)) from by
    rw [smul_zero]; exact (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
      hU.analytic.continuousAt.tendsto).comp (continuousAt_id.const_smul s)
  let T' := closedBall (0:G.Color) (2*d); let L := G.lieExp '' T'
  have hL : L ⊆ T := image_mono (closedBall_subset_closedBall hr)
  have ht' : 0<d := mul_pos hB ht
  by_cases hw : U 0 ∈ L
  · let u z := G.plog (G.mat (U z)); let f z := d⁻¹ • u (s • z)
    have hz : ‖u 0‖ ≤ 2*d := by
      obtain ⟨x,hx,h⟩ := hw
      unfold u; rw [← h]
      rw [show G.plog _=x from over_ball (he (closedBall_subset_closedBall hr hx))]; simpa only [T',mem_closedBall,dist_zero_right] using hx
    have hf : Through n f 0 (B⁻¹*A) := by
      have hy : Allows n u 0 P := (h _ (mem_image_of_mem _ (hL hw))).comp (f:=fun z => G.mat (U z)) hU
      have hk : Through n (fun z => u (s • z)) 0 (A*t) := Through.contract (Through.control hy) hs hs'
        (hz.trans (le_trans (le_of_eq (mul_assoc (2:ℝ) B t).symm) (mul_le_mul_of_nonneg_right (le_max_right ..) ht.le)))
        ((mul_le_mul_of_nonneg_left hv hp).trans (calc P*(2*t) = 2*P*t := by ring
                                                       _ ≤ A*t := mul_le_mul_of_nonneg_right (le_max_left ..) ht.le))
      apply (hk.scale d⁻¹).mono; rw [abs_of_nonneg (inv_pos.mpr ht').le]; apply le_of_eq; unfold d; field_simp
    have hz' : f 0∈closedBall (0:G.Color) 2 := by
      unfold f; rw [smul_zero,mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht').le]
      rw [inv_mul_eq_div, div_le_iff₀ ht']; exact hz
    have hl := ((hh _ hz').comp hf).scale d
    refine (hl.mono ?_).germ ?_
    · rw [abs_of_pos ht']; exact le_of_eq (show d*X=B*X*t by unfold d; ring)
    filter_upwards [hW.tendsto.eventually ((first_geom G).1.mem_nhds (hW0.symm ▸ hΩ (hL hw)))] with z hh
    change d • _ = patched q _ (W z)
    unfold patched; rw [indicator_of_mem (show W z ∈ firstChart G from hh)]
    exact (actual q (LocalH.snap G (W z)) ht').symm
  · have hm : Through n (fun _ : E => (0:G.Color)) 0 ((B*X)*t) :=
      Through.control (allows_const _ (show ‖(0:G.Color)‖≤(B*X)*t by rw [norm_zero]; positivity))
    apply hm.germ
    have hl : IsClosed L := ((isCompact_closedBall ..).image G.lieExp_cont).isClosed
    have he : W 0∈Lᶜ := by rw [hW0]; exact hw
    filter_upwards [hW.tendsto.eventually (hl.isOpen_compl.mem_nhds he)] with z hz
    change 0 = patched q d (W z)
    unfold patched
    by_cases hb : W z∈firstChart G
    · rw [indicator_of_mem hb]
      by_cases hx : broad q d (LocalH.snap G (W z)) = 0
      · rw [hx,zero_smul]
      exact (hz ⟨_,mem_closedBall.mpr (by rw [dist_zero_right]; exact (broad_span q ht' _ hx).le),under_ball hb⟩).elim
    exact (indicator_of_notMem hb _).symm

/- On any frozen edge (without read tests). -/
lemma shell_price (G : Gauge) (q : Chi) (P : Patch) (d : ℝ) (hd : 0 < d) (K : ℝ) (hK : 0 < K) (n : ℕ) :
    ∃ M : ℝ, 0<M ∧ ∀ᶠ x : ℝ in atTop,
    let t := fiery G x P.L
    ∀ {c f : Side} (S : StepData c f) (F : Forest S.ratio) (A : Stores S),
    ∀ (V : Config G c) (Y : LinkArray G (Frozen A x F)) (i : Frozen A x F),
      Point 0 (S.ratio.parent i.val.val.1) d n (fun z => autoShell q (K*t) (pulse x V z) Y i) (M*t) := by
  obtain ⟨r,C,hr,hC,h⟩ := coordinates G n
  let J := max C G.colorScale
  have hm : C ≤ J := le_max_left ..
  let E := 2^n * G.colorScale * J
  have he : 0 ≤ E := mul_nonneg (mul_nonneg (by positivity) G.colorScale_pos.le) (hC.le.trans hm)
  obtain ⟨M,hM,H⟩ := patch_price G he q n K hK
  refine ⟨M,hM,?_⟩
  filter_upwards [monitors G P.L, Work.E01.fiery_le G P.L (2*K),
    (Work.E01.largeT_tendsto G P.L).eventually (ge_mem_nhds (half_pos (first_pos G)))] with x hx ht hv
  intro t c f S F A V Y i
  obtain ⟨hp,hl,hQ⟩ := hx
  let a := (S.ratio.parent i.val.val.1,i.val.val.2)
  let L (z : PriceCoords G c) := replica S.ratio (field V z) i.val.val
  have hs : Allows n (fun z => G.mat (L z)) 0 J := by
    unfold L replica; split
    · exact allows_const _ ((mat_paid _).le.trans (le_max_right ..))
    · exact ((h 0 (by simp [hr.le]) V).1 a).mono hm
  have he' := (allows_const (0 : PriceCoords G c) (mat_paid (Y i)).le).times (f:=fun _ => Y i) (hs.inverse (f:=L))
  have hh : 0<t := by unfold t; linarith only [hp,hQ]
  have h₀ := H (U:=fun z => Y i * (L z)⁻¹) he' (temp x) t hh hp.le hl hQ (le_trans
    (le_of_eq (mul_assoc (2:ℝ) K t).symm) (ht.trans hv))
  refine (Point.of_support h₀ (R:=0) ?_ hd.le).mono le_rfl ?_
  · intro u _ v _ h
    have hb : AgreeNear id (S.ratio.parent i.val.val.1) 0 (field V (temp x • u)) (field V (temp x • v)) :=
      field_dep (fun _ _ => rfl) (fun j hj => by change temp x • u j=temp x • v j; rw [h _ hj])
    have hf : L (temp x • u)=L (temp x • v) := by
      unfold L replica; split
      · rfl
      exact hb _ (show separation _ _≤0 by simp)
    dsimp only; rw [hf]
  simp
end YM.AnalyticBridge.SectorAffine.Offset
