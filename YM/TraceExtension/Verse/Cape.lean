import YM.TraceExtension.Verse.Day
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Verse
open Function Filter Set Extraction OS OS.Ground Spec MeasureTheory Wilson Measure
open RG Terrace MergeProof.East Next.Rank Next.Rank.East Next.UVStress Further.CorrectedLift Climb
open Analysis TraceExtension Boundary Over
open scoped Topology BigOperators InnerProductSpace Classical ContDiff
variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} (F:Final C f S)
variable {H:(Cells.standard C).Hierarchy}{J:Scaling S}{V:∀ i,Vane C i}
variable {Z:Terrace.Arch C}(hb:(𝓛:Filter _) ≤ f.fuse)

lemma monotone_axis (s r:ℝ)(h:0 < s)(hp:s ≤ r): (euclidean F r).re ≤ (euclidean F s).re:=by
    obtain ⟨μ,hμ,-⟩:=TraceExtension.traceSpectrum_exists F; have hh:0 < r:= h.trans_le hp
    have hr:= hμ.laplace r hh; have hs:= hμ.laplace s h; rw [hr,hs,Complex.ofReal_re,Complex.ofReal_re]; haveI:= hμ.damped_mass s h
    apply ENNReal.toReal_mono (measure_ne_top (Semigroup.transform timeAxis s μ) _)
    unfold Semigroup.transform; rw [withDensity_apply _ MeasurableSet.univ,withDensity_apply _ MeasurableSet.univ]; simp only [Measure.restrict_univ]
    apply lintegral_mono_ae
    filter_upwards [(show ∀ᵐ i:E4 ∂μ, i∈ Mink.cone from hμ.localcone)] with i hi
    apply ENNReal.coe_le_coe.mpr; have hx:0 ≤ time i:= le_trans (norm_nonneg _) hi
    change Real.exp (-r*time i) ≤ Real.exp (-s*time i); exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hx)

lemma award_pos (h:G.Simple):0<award G:=by
    have hp :0 < b0 G:=by unfold b0; have he:= Gauge.casimir_pos h; positivity
    have ht:0 < (G.lieDim:ℝ):= Nat.cast_pos.mpr (by rw [Gauge.lieDim, ← G.colorIso.finrank_eq]; haveI := h.nontrivial_color; exact Module.finrank_pos)
    have hd:0 < d2 G^ (2:ℕ):=sq_pos_of_ne_zero (by rw [force_b]; exact ne_of_lt (by linarith))
    unfold award; positivity

private def every (s:ℝ): E4:= WithLp.toLp 2 (fun _=> s/2)
private def shot (s:ℝ):Points 2:= points ![0,every s]
private lemma shot_width {s:ℝ}(h:0 ≤ s):width (shot s)=s:=by
    simp only [shot,width,points_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one, zero_sub,norm_neg]; apply (sq_eq_sq₀ (norm_nonneg _) h).mp
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_four]; unfold every;simp;ring
private lemma shot_generic {s:ℝ}(h:0<s): shot s∈generic 2:=by
    intro a i j hi; fin_cases i<;>fin_cases j <;>simp_all [shot,every,h.ne'];linarith
private lemma open_shot {s:ℝ}(hp:1/2 < s)(h:s < 2):Scaling.window 100 2∈𝓝 (shot s):=by
    let f(x:Points 2):=cubedist (x 0) (x 1)
    have hc: Continuous f:=continuous_cubedist.comp (show Continuous (fun x:Points 2=> (x 0,x 1)) by fun_prop)
    have hp':0 < s:=by linarith
    have hz: (100:ℝ)⁻¹ < f (shot s):=by
       simp only [f,shot,points_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,cubedist]
       apply lt_of_lt_of_le _ (dist_le_pi_dist _ _ timeAxis); change _ < dist (0:ℝ) (s/2); rw [Real.dist_eq, zero_sub,abs_neg,abs_of_pos (by linarith)]; linarith
    have hu: ‖shot s‖ < 100:=by
       have ht:= PiLp.norm_sq_eq_of_L2 _ (shot s); have hw:= shot_width hp'.le
       simp only [shot,width,points_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one, zero_sub,norm_neg] at hw
       change ‖points ![(0:E4),every s]‖ < (100:ℝ); simp only [Fin.sum_univ_two,shot,points_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,norm_zero, pow_two,zero_mul,zero_add,hw] at ht; nlinarith
    apply mem_of_superset ((IsOpen.inter (isOpen_lt continuous_const hc) (isOpen_lt continuous_norm continuous_const)).mem_nhds (show (shot s) ∈ {x| (100:ℝ)⁻¹ < f x} ∩ {x:Points 2 | ‖x‖ < 100} from ⟨hz,hu⟩))
    intro x hx; refine ⟨?_, (show ‖x‖ < _ from hx.2).le⟩
    intro i j hij; have hg:(100:ℝ)⁻¹ ≤ f x:= (show (100:ℝ)⁻¹ < _ from hx.1).le
    fin_cases i<;>fin_cases j <;> first| (exfalso; exact hij (by decide)) | exact hg| exact hg.trans_eq (dist_comm ..)

include hb in
lemma border (h:G.Simple)(h₁:Scribe f J V Z F.sector 𝓛 F.room.kernel H): Tendsto (fun i=> clue (J.r i) • euclidean F (J.r i)) atTop (𝓝 (award G:ℂ)):=by
    let f:= fun i=> (clue (J.r i) • euclidean F (J.r i)).re
    have hq(t:ℝ):0 ≤ clue t:= by unfold clue;positivity
    let T (s:ℝ):= award G/s^8; have hM:ContinuousAt T 1:= (continuousAt_const.div (continuous_id.pow _|>.continuousAt) (by simp))
    obtain ⟨Y,hz⟩:= h₁.meters
    have hv(s:ℝ)(hh:1/2<s)(ht:s<2): Tendsto (fun i=>width (fad (V i) (shot s))) atTop (𝓝 s)∧
        Tendsto (fun i=> (clue (J.r i) • euclidean F (J.r i*width (fad (V i) (shot s)))).re) atTop (𝓝 (T s)):=by
       have hx:0<s:=by linarith
       have hu:= shot_width hx.le
       have hg := tagline F hb h h₁ (shot_generic hx) (open_shot hh ht); rw [hu] at hg
       refine ⟨?_,Complex.continuous_re.continuousAt.tendsto.comp hg⟩
       have ht:= (show Continuous (width:Points 2→ℝ) from by unfold width;fun_prop).continuousAt (x:=shot s)|>.tendsto; rw[hu] at ht; exact ht.comp (rounds hz h (shot s))
    have he : T 1=award G:=by simp [T];
    have hm(a b c:ℝ)(ha:0<a)(h:a ≤ b)(hc:0≤c): (c • euclidean F b).re≤(c • euclidean F a).re:=by simp only [Complex.real_smul,Complex.mul_re, Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; exact mul_le_mul_of_nonneg_left (monotone_axis F a b ha h) hc
    have hF:Tendsto f atTop (𝓝 (T 1)):=by
       apply tendsto_order.mpr; constructor
       · intro p h; obtain ⟨s,hs,hs',hp⟩:= ((show ∀ᶠ s:ℝ in 𝓝[>] 1,1<s from self_mem_nhdsWithin).and ((Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (show (1:ℝ)<2 by norm_num))).and ((hM.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds h)))).exists
         obtain ⟨hh,hI⟩:= hv s (by linarith) hs'; filter_upwards [hh.eventually (le_mem_nhds hs), hI.eventually (lt_mem_nhds hp)] with i hi hp; exact lt_of_lt_of_le hp (hm _ _ _ (J.positive i) (le_mul_of_one_le_right (J.positive i).le hi) (hq _))
       intro p h; obtain ⟨s,hs,hs',hp⟩:= ((show ∀ᶠ s:ℝ in 𝓝[<] 1,s<1 from self_mem_nhdsWithin).and ((show ∀ᶠ s:ℝ in 𝓝[<] 1,1/2<s from ((show ∀ᶠ s:ℝ in 𝓝 1,1/2<s from lt_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds)).and ((hM.tendsto.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds h)))).exists
       obtain ⟨ht,hI⟩:= hv s hs' (by linarith); filter_upwards [ht.eventually (ge_mem_nhds hs),ht.eventually (lt_mem_nhds (show 0<s by linarith)),hI.eventually (gt_mem_nhds hp)] with i hi hk hp; exact lt_of_le_of_lt (hm _ _ _ (mul_pos (J.positive i) hk) (mul_le_of_le_one_right (J.positive i).le hi) (hq _)) hp
    rw[he] at hF
    apply (Complex.continuous_ofReal.continuousAt.tendsto.comp hF).congr; intro i
    obtain ⟨μ,H,-⟩:=traceSpectrum_exists F; change (↑(f i):ℂ)=_
    unfold f; rw[H.laplace _ (J.positive i)]; simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,sub_zero,Complex.ofReal_mul,mul_zero]
lemma outside (h:G.Simple)(H:Gallery C f): EuclideanAsymptotic F (award G):=by
    obtain ⟨b,Z,a,hb,hZ,hq₁,hq₂,hx⟩:= H.lead S F.room F.sector F.phase.transport; unfold EuclideanAsymptotic
    rw [Filter.tendsto_def]; intro W hW; by_contra! hh
    let J:=(fun s=> clue s • euclidean F s); let Y:={s | J s∈W}; change Y ∉ _ at hh
    have hp: ∃ s:ℕ→ℝ,Tendsto s atTop (𝓝 0) ∧ ∀ i,0<s i ∧ J (s i) ∉ W:=by
       let d:= costHint; have he (i:ℕ):∃ s:ℝ,0<s ∧ s<d i ∧ J s∉ W:=by
          by_contra! h
          apply hh; have hk: ∀ᶠ s:ℝ in 𝓝[>] 0,0<s:=self_mem_nhdsWithin
          filter_upwards[hk,(Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (show d i > 0 from cost_pos i)))] with s hs hI; exact h s hs hI
       choose s hs hv ht using he
       exact ⟨s,tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds cost_clears (fun i=> (hs i).le) (fun i=>(hv i).le),fun i=>⟨hs i,ht i⟩⟩
    obtain ⟨s,hs,hv⟩:= hp; obtain ⟨p,hP,I,hi,w,hQ⟩:= hx s hs fun i=> (hv i).1; have hu:= border F hb h hQ; rw[hi] at hu; obtain ⟨i,hI⟩:= (hu.eventually hW).exists; exact (hv (p i)).2 hI
end YM.Trace.Verse
#print axioms YM.Trace.Verse.outside
