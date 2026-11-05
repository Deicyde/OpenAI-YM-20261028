import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Coordinates
import YM.Push.STATIONARY_UNIFORM.Prediction
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Patch
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stencils
import YM.Work.F05.Actions


/-!
# Uniform real germs for the predictor rows of the chosen D

Use *local* gauges per row and keep them fixed in parameter differentiation.
Prices exist for each patch, independent of period, and secure the actual
analytic extensions in an open neighborhood; switch tests at arbitrary
configs are not assumed to be on these branches. In particular the sector
Stores flags are the flags of the base V (including boundary points), and no
statement is made that they remain flags of the perturbed V when the precision
expression at those same Stores is differentiated. We do not choose new tags
inside the prediction formula.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine
open Filter Function Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Motion YM.Next.SectorChange.Rows
open YM.Push.Uniform
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

/-- Uniform C^n price even across volumes, small only on the stencil in the
field supplied to it. The equality across choices here is only a germ for
this one output, and is NOT a removal of the tag from the likelihood etc. -/
theorem prediction_paid (G : Gauge) (P : Patch) (K : KernelChoices) (hk : P.Branches K G)
    (C : ℝ) (n : ℕ) (hn : 2 ≤ n) : ∃ r M : ℝ, 0<r ∧ 0<M ∧
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : E → Config G f) (x : E) (i : Bond c),
      (∀ j : Bond f, separation i.1 (S.ratio.parent j.1) ≤ predReach P → G.chord (U x j) ≤ r ∧
        Allows n (fun z => G.mat (U z j)) x C) →
      (∀ k : S.Choices, Allows n (fun z => G.mat (S.prediction (U z) k i)) x M) ∧
        ∀ᶠ z in 𝓝 x, ∀ k k' : S.Choices, S.prediction (U z) k i = S.prediction (U z) k' i := by
  obtain ⟨D,δ,H⟩ := log_receipt G
  have hD := H.1
  have hδ := H.2.1
  -- secure a patch for the plog derivative prices from real germs
  have hp := G.plog_diff
  obtain ⟨s,hs,h'⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 (hp.eventually (by simp))
  obtain ⟨M,hM,Hm⟩ := exists_allows (isCompact_closedBall (1:G.Mat) s) (f:=G.plog) (fun u hu => h' hu) n
  obtain ⟨κ,-,hκ⟩ := exp_receipt G (n+1)
  obtain ⟨W,v,-,hv⟩ := focus_receipt G n
  let A := composeCost (n+1) κ 1
  let B := predictionRadius P G K n κ A D δ v
  let S₀ : StepData 1 (1*P.L) := ⟨P,K,rfl⟩
  have hB : 0 < B := prediction_radius_pos S₀ (represented hκ _) hn hκ H hv
  let J := composeCost n W (connectorCost P G n κ A)
  let N := max G.colorScale C
  have hN : 0 < N := G.colorScale_pos.trans_le (le_max_left ..)
  let L := composeCost n M N
  let b := min (δ / 2) (min (s/G.colorScale) ((B/2)/D))
  have hb : 0<b := lt_min (half_pos hδ) (lt_min (div_pos hs G.colorScale_pos) (div_pos (half_pos hB) hD))
  refine ⟨b,max 1 (composeCost n J L),hb,zero_lt_one.trans_le (le_max_left ..),?_⟩
  intro c f S h hf E _ _ U x i hx
  have hg : S.patch.Branches S.kernel G := by rw [h,hf]; exact hk
  let T (x : E) : Config G f := fun j => if separation i.1 (S.ratio.parent j.1) ≤ predReach P then U x j else 1
  have ht (z) (k : S.Choices) : S.prediction (U z) k i = S.prediction (T z) k i := by
    refine prediction_near_eq hg _ _ _ _ (fun e he => ?_)
    symm
    exact if_pos (h ▸ he)
  have hb0 : b < δ := lt_of_le_of_lt (min_le_left ..) (half_lt_self hδ)
  have hb1 : b ≤ s/G.colorScale := (min_le_right ..).trans (min_le_left ..)
  have hb2 : b ≤ (B/2)/D := (min_le_right ..).trans (min_le_right ..)
  have ha j : G.chord (T x j) ≤ b ∧ Allows n (fun z => G.mat (T z j)) x N := by
    unfold T
    split
    next h => exact ⟨(hx j h).1,(hx j h).2.mono (le_max_right ..)⟩
    exact ⟨by rw [G.chord_one]; exact hb.le,allows_const _ ((mat_paid _).le.trans (le_max_left ..))⟩
  let p (z : E) : YM.Push.In G f := fun e => G.plog (G.mat (T z (e.1,axisEquiv.symm e.2)))
  have hl (e : Bond f) : Allows n (fun z => G.plog (G.mat (T z e))) x L := by
    apply Allows.comp (f:=fun z => G.mat (T z e)) _ (ha e).2
    refine Hm _ ?_
    rw [Metric.mem_closedBall,dist_eq_norm,← chord_dist]
    rw [mul_comm]; apply (le_div_iff₀ G.colorScale_pos).mp
    exact (ha e).1.trans hb1
  have hz : Allows n p x L := allows_pi ((hl (Classical.arbitrary _)).nonneg) (fun j => hl _)
  have he (z : Bond f) := H.2.2 (T x z) ((ha z).1.trans hb0.le)
  have hbp : p x ∈ Metric.ball 0 B := by
    rw [Metric.mem_ball,dist_zero_right]
    refine lt_of_le_of_lt ?_ (half_lt_self hB)
    apply (pi_norm_le_iff_of_nonneg (half_pos hB).le).mpr
    intro e
    let j : Bond f := (e.1,axisEquiv.symm e.2)
    apply (he j).2.trans
    rw [mul_comm]; apply (le_div_iff₀ hD).1
    exact (ha j).1.trans hb2
  have Hew : ∀ᶠ z in 𝓝 x, represent (p z)=T z := by
    have Ht (j : Bond f) : ∀ᶠ z in 𝓝 x, G.lieExp (G.plog (G.mat (T z j))) = T z j := by
      have Hx : ContinuousAt (fun z => T z j) x :=
        (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (ha j).2.analytic.continuousAt.tendsto
      have Hy : ContinuousAt (fun z => G.chord (T z j)) x := G.continuous_chord.continuousAt.comp Hx
      filter_upwards [Hy.tendsto.eventually (gt_mem_nhds ((ha j).1.trans_lt hb0))] with z hz
      exact (H.2.2 (T z j) hz.le).1
    filter_upwards [eventually_all.mpr Ht] with z hz
    funext j
    rw [Work.F03.represent_link]
    unfold p
    rw [←coord_map,axisEquiv.symm_apply_apply]; exact hz j
  have hR : B = predictionRadius S.patch G S.kernel n κ A D δ v := by rw [h,hf]
  have hJ : J = composeCost n W (connectorCost S.patch G n κ A) := by rw [h]
  constructor
  · intro k
    apply Allows.germ (f:=fun z => G.mat (S.prediction (represent (p z)) k i))
    · have he : Allows n (fun z : YM.Push.In G f => G.mat (S.prediction (represent z) k i)) (p x) J := by
        rw [hJ]; exact prediction_pay S (represented hκ f) hn hκ H hv _ (hR ▸ hbp) k i
      exact (he.comp (f:=p) hz).mono (le_max_right ..)
    filter_upwards [Hew] with z hz
    rw [ht,hz]
  filter_upwards [Hew,hz.analytic.continuousAt.tendsto.eventually (Metric.isOpen_ball.mem_nhds hbp)] with z hz hh
  intro k k'
  simp_rw [ht,← hz]
  exact congr_fun (picked_tags S (represented hκ f) hn hκ H (p z) (hR ▸ hh) k k') i

section selected

variable {G : Gauge} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two constant group letters cannot change volume-uniformity. -/
def dressedCost (G : Gauge) (n : ℕ) (C : ℝ) := 2^n * (2^n * G.colorScale * C) * G.colorScale

lemma allows_dressed {U : E → G.El} {n : ℕ} {C : ℝ} {x : E}
    (h : Allows n (fun z => G.mat (U z)) x C) (u v : G.El) :
    Allows n (fun z => G.mat (u * U z * v)) x (dressedCost G n C) := by
  have he := allows_const (n:=n) x (mat_paid u).le
  exact (he.times (f:=fun _ => u) h).times (f:=fun z => u * U z) (g:=fun _ => v)
    (allows_const _ (mat_paid v).le)

/-- Uniform mixed derivative gate on every selected block predictor row.
Statements keep the *whole* output in the indicated orientation. No use
of small cells around V=1 as a cover of the field space: choose one local
block gauge per row at the genuine field, then perturb in a uniform sup
ball of real field parameters. -/
theorem chosen_branch (G : Gauge) (P : Patch) (K : KernelChoices) (hk : P.Branches K G) (n : ℕ) :
    ∃ r M : ℝ, 0<r ∧ 0<M ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f), S.patch=P → S.kernel=K →
    100*(1+radiusB x) ≤ c.val → ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c),
    A.flags=RG.flags (temp x) V → ∀ (s : Signed) (i : Bond c) (B : PriceCoords G c),
      curb (shots S x) A F x s (.inr i) → ‖B‖ ≤ r →
      (∀ k : S.Choices, Allows n (fun y : FieldPair G c f =>
        G.mat (S.prediction (sceneField S V s y) k i)) (B,0) M) ∧
      ∀ᶠ z : FieldPair G c f in 𝓝 (B,0), ∀ k k' : S.Choices,
        S.prediction (sceneField S V s z) k i = S.prediction (sceneField S V s z) k' i := by
  let m := max n 2
  obtain ⟨r,C,hr,hC,H⟩ := coordinates G m
  let L := dressedCost G m C
  obtain ⟨δ,M,hδ,hM,h⟩ := prediction_paid G P K hk L m (le_max_right ..)
  have hL : 0<L := by unfold L dressedCost; have := G.colorScale_pos; positivity
  let J := dressedCost G m M
  let R := min r ((G.colorScale*(δ/2))/L)
  refine ⟨R,J,lt_min hr (div_pos (mul_pos G.colorScale_pos (half_pos hδ)) hL),
    by unfold J dressedCost; have := G.colorScale_pos; positivity, ?_⟩
  have ht : ∀ᶠ x in atTop, LocalJet.permit P * temp x ≤ δ/2 := by
    filter_upwards [Work.E01.fiery_le G 1 (LocalJet.permit P),
      (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds (half_pos hδ))] with x hx he
    simpa [fiery,betaF] using hx.trans he
  filter_upwards [small_span P, Work.E01.radiusB_tendsto.eventually_ge_atTop (LocalJet.allot P+1),ht] with x hx he hv
  intro c f S hP hK hf F A V hA s i B ht hB
  let o := s.act i.1
  have hl : o ∉ A.dome (9*radiusB x+9*radiusB x/10) := (guarded (hP.symm ▸ hx) ht).1
  obtain ⟨w,hw⟩ := LocalJet.trim (LocalJet.allot P) hl (by omega) (by omega) hA
  let v := fun i : Site f => w (affine s 0 i)
  let X := FieldPair G c f
  let p : X := (B,0)
  let U := sceneField S V s
  let T := fun z => Lattice.gauge v (U z)
  have hg : S.patch.Branches S.kernel G := by rw [hP,hK]; exact hk
  have hu (B : PriceCoords G c) (hB : ‖B‖ ≤ r) (i : Bond f) :
      Allows m (fun z => G.mat (T z i)) (B,0) L :=
    allows_dressed ((H B hB V).2 S s i) _ _
  have hx' (i' : Bond f) (he : separation i.1 (S.ratio.parent i'.1) ≤ predReach P) : G.chord (T 0 i') ≤ δ/2 := by
    have hh : T 0=pull s 0 (Lattice.gauge w (replica S.ratio V)) := by
      change Lattice.gauge v (facade S s (field V 0) 0)=_
      rw [field_zero, fixed_facade]
      exact (Work.F05.pull_gauge_zero ..).symm
    rw [hh,turn_read]; have hi := spin_separation (S:=S) i' s i.1
    have hy := hw (sendEdge s 0 i') (by unfold o LocalJet.allot; omega)
    split
    · rw [G.chord_inv]; exact hy.trans hv
    exact hy.trans hv
  have hy : ‖B‖ ≤ r := hB.trans (min_le_left ..)
  have htest (i' : Bond f) (hh : separation i.1 (S.ratio.parent i'.1) ≤ predReach P) :
      G.chord (T p i') ≤ δ := by
    let A (z : PriceCoords G c) := G.mat (T (z,0) i')
    have he (z : PriceCoords G c) (hz : z ∈ Metric.closedBall 0 r) : Allows m A z L :=
      allows_first_slice (hu z (by simpa using hz) i')
    have hl := (convex_closedBall (0 : PriceCoords G c) r).norm_image_sub_le_of_norm_fderiv_le (f:=A)
      (fun z hz => ((he z hz).analytic.differentiableAt (by simp)))
      (C:=L) (fun z hz => by rw [← norm_iteratedFDeriv_one A]; exact (he z hz).norm_le _ (le_trans (by norm_num) (le_max_right n 2)))
      (Metric.mem_closedBall_self hr.le) (show B ∈ Metric.closedBall 0 r by simpa using hy)
    rw [sub_zero] at hl
    have hx := norm_add_le (A B - A 0) (A 0 - 1)
    rw [sub_add_sub_cancel] at hx
    have hb : L * ‖B‖ ≤ G.colorScale*(δ/2) := by rw [mul_comm]; exact (le_div_iff₀ hL).1 (hB.trans (min_le_right ..))
    change ‖G.mat (T p i')-1‖ ≤ _ + ‖G.mat (T 0 i')-1‖ at hx
    apply le_of_mul_le_mul_left _ G.colorScale_pos
    rw [chord_dist]
    rw [← chord_dist (T 0 i')] at hx
    refine hx.trans ((add_le_add (hl.trans hb) (mul_le_mul_of_nonneg_left (hx' i' hh) G.colorScale_pos.le)).trans_eq ?_)
    ring
  have Hpred := h S hP hK X T p i (fun j hj => ⟨htest j hj,hu B hy j⟩)
  let a := v (S.ratio.embed i.1)
  let b := v (S.ratio.embed (i.1+Lattice.step i.2))
  have hq (z) (k : S.Choices) : S.prediction (U z) k i = a⁻¹ * S.prediction (T z) k i * b := by
    rw [show S.prediction (T z) k=_ from (Push.SectorMeasure.choice_gauge hg (U z) k v).2]
    change _ = a⁻¹ * (a * _ * b⁻¹) * b; group
  constructor
  · intro k
    change Allows n (fun z => G.mat (S.prediction (U z) k i)) _ _
    simp_rw [hq _ k]
    exact (allows_dressed (Hpred.1 k) _ _).order (le_max_left ..)
  filter_upwards [Hpred.2] with z hz
  intro k k'; rw [show sceneField S V s z=U z from rfl,hq z k,hq z k',hz k k']

end selected
end YM.AnalyticBridge.SectorAffine
