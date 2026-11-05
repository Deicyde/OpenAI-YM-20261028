import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Guard
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Stamped


/-!
# Post-L counter through THESE costs

Including for licenses at the same aperture (actual `fog` & `meanLog`).
Not on an arbitrary Ringing cost; see Scope and docs. Obtain independent
post-L/threshold choices before using on extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest 
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- At this Teller's post-L quotes, anticipate the actual aperture prices.
Don't need Census of supports etc, they can be bought later at each entrance.
`Sponsored`: starcash data slightly rearranged (use with these entrances also
for full_price, Arthur etc). `Admitted` even if flags incorrectly recorded.
-/
def Sponsored (Z : ChartRatio G) (P : Teller G) (L : Side) (w K E x : ℝ) :=
    let d := K*fiery G x L
    d ≤ 1 ∧ 2*d<firstRadius G ∧ 4*d<Z.radius ∧ (∀ a : G.Color,‖a‖ ≤ 4*d → |Real.log (Z.J a)| ≤ E*‖a‖^2) ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → 100*(1+radiusB x)≤c.val → P.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) (B : Allocation G S x w) (q : Chi),
      Admitted A F x V k Z B d ∧ (A.flags = RG.flags (temp x) V → ∀ β : ℝ, 0<β →
        Permitted x V k A F B Z d β (fog A F T x V k) (meanLog A F T x V k q d) ∧
          (Rows.gram T x V k (shots S x) A F).PosDef ∧ ∃ B:ℝ,0<B ∧ Authorized A V F x B)

private lemma uniq {A B : Patch} (h : A.L=B.L) (hj : A.J=B.J) : A=B := by cases A; cases B; congr

/-- Enlarge aperture vs `matinee`. Need the bigger one even when not
using any `Admitted`: this bridges through the Cleans chart comparison
at **local** Wide, including Y_H in that halo rather than just intact.
-/
lemma openings (P : Teller G) (Z : ChartRatio G) (hZ : LocalRatio Z) (L : Side) (w : ℝ) (hw : 0<w) :
    ∃ K E : ℝ, 0<K ∧ 0<E ∧ ∀ᶠ x : ℝ in atTop, Aperture P L w K x ∧ Sponsored Z P L w K E x := by
  obtain ⟨C,hC,h⟩ := cleans_at P L w hw
  by_cases hx : ∃ T : Patch,T.L=L ∧ T.J=P.j ∧ T.Branches P.bind G
  swap
  · obtain ⟨D,r,hD,hr,hl,hh⟩ := ratio_price hZ
    have hg : Tendsto (fun x => 4*C*fiery G x L) atTop (𝓝 0) := by
      have hv := (Scales.tally_g G L 0 1).const_mul (4*C); rw [mul_zero] at hv; refine hv.congr fun x => ?_; simp [Scales.fi]; exact Or.inl (mul_comm ..)
    have ht := (Work.E01.betaF_tendsto G L).eventually_gt_atTop 0
    refine ⟨C,D,zero_lt_one.trans_le hC,hD,?_⟩
    filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 2,ht,hg.eventually (gt_mem_nhds (by have := first_pos G; positivity : 0 < min r (min (firstRadius G) 1)))] with x h1 h2 h3
    have he : 0<fiery G x L := Work.E09.temp_pos h2
    let d := C*fiery G x L
    have hd : 0<d := by unfold d; positivity
    have hR : 4*d<min r (min (firstRadius G) 1) := (mul_assoc 4 C (fiery G x L)) ▸ h3
    rw [lt_min_iff,lt_min_iff] at hR
    have hi {c f : Side} (S : StepData c f) (T : Tube G S) (ht : S.patch.L=L) (hv : P.Funds S T) := hx
      (Exists.intro S.patch (And.intro ht (And.intro hv.atStep hv.kernel)))
    exact ⟨⟨he,hd,(by change d<_; linarith only [hR.2.1,hd]),h1,fun c f S T ht _ hv => (hi S T ht hv).elim⟩,
      ⟨by change d≤1; linarith only [hR.2.2,hd],by change 2*d<_; linarith only [hR.2.1,hd], hR.1.trans hl,
        fun a hy => (hh _ (hy.trans hR.1.le)).2.2,fun c f S T ht _ hv => (hi S T ht hv).elim⟩⟩
  obtain ⟨T0,ht,hy,hp⟩ := hx
  obtain ⟨A,E,hA,hE,hI⟩ := sponsored_permit P Z hZ T0 hp w hw
  obtain ⟨B,r,hB,hr,hl,hX⟩ := ratio_price hZ
  set K := max C A
  have hc : C ≤ K := le_max_left ..; have ha : A≤K := le_max_right ..
  refine ⟨K,B,hA.trans_le ha,hB,?_⟩
  have hg : Tendsto (fun x => 4*K*fiery G x L) atTop (𝓝 0) := by
    have hv := (Scales.tally_g G L 0 1).const_mul (4*K); rw [mul_zero] at hv; refine hv.congr fun x => ?_; simp [Scales.fi]; exact Or.inl (mul_comm ..)
  rw [ht] at hI
  have h0 := first_pos G
  filter_upwards [h,hI,Work.E01.radiusB_tendsto.eventually_ge_atTop 2,small_span T0,
    hg.eventually (gt_mem_nhds (by positivity : 0 < min r (min (firstRadius G) 1)))] with x hz hl' hθ hq hs
  obtain ⟨he,h',hα,hβ,hw'⟩ := hl'
  let d := K*fiery G x L
  have H : 0 < fiery G x L := pos_of_mul_pos_right h' hA.le
  have hd : 0<d := mul_pos (hA.trans_le ha) H
  have hv : A*fiery G x L ≤ d := mul_le_mul_of_nonneg_right ha H.le
  have hR : 4*d < min r (min (firstRadius G) 1) := (mul_assoc 4 K (fiery G x L)) ▸ hs
  rw [lt_min_iff,lt_min_iff] at hR
  have hh : 2*d<firstRadius G := by linarith only [hR.2.1,hd]
  have hu (c f : Side) (S : StepData c f) (T : Tube G S) (h : S.patch.L=L) (hf : P.Funds S T) : S.patch=T0 :=
    uniq (h.trans ht.symm) (hf.atStep.trans hy.symm)
  constructor
  · refine ⟨H,hd,by change d<_; linarith only [hh,hd],hθ,fun c f S T h he hf => ⟨by rw [hu c f S T h hf]; exact hq,?_⟩⟩
    intro D F O A U k V h1 h2 p hi
    obtain ⟨a,h3,h4⟩ := hz c f S T h he hf D F O A U k V h1 h2
    exact ⟨C,a,hc,h4 p hi⟩
  refine ⟨by change d≤_; linarith only [hd,hR.2.2],hh,hR.1.trans hl,
    fun a ht => (hX _ (ht.trans hR.1.le)).2.2,fun c f S T h1 h2 h3 S0 F k V C0 q => ?_⟩
  obtain ⟨h4,h5,h6⟩ := hw' _ _ S T (hu c f S T h1 h3) h2 h3
  obtain ⟨hm,hn⟩ := h6 S0 F k V C0 q
  constructor
  · intro u hU hb e hx y z
    obtain ⟨a,ht,hβ,hχ,hX,-⟩ := hm u hU hb e hx
    refine ⟨a,ht.trans hv,hβ,hχ,hX,fun q => ?_⟩
    have hY : z=G.lieExp a := by
      change u e * y⁻¹=G.lieExp a
      change G.lieExp a * y=u e at hX; rw [← hX]; group
    rw [hY,patched_agrees q hd (show d<firstRadius G by linarith) (ht.trans hv)]
  intro hX β hβ0
  obtain ⟨g,hQ,ha⟩ := hn hX β hβ0
  refine ⟨⟨g.nativePos,hβ0,(meanLog_cont S0 F T x V k q d h3 hd hh).measurable,?_,hZ,hd,hR.1.trans hl⟩,hQ,ha⟩
  intro u hU hz i
  obtain ⟨a,hz,hm,hu⟩:= g.core u hU hz i
  exact ⟨a,hz.trans hv,hm,hu⟩

end YM.AnalyticBridge.AnnulusRatioInsertions
