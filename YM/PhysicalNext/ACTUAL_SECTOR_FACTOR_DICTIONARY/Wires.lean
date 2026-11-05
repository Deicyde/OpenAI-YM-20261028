import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Tenor
import YM.Next.FREE_KERNELS.Amend
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Geo
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Sloped


/-! Padded precision read in the physical dictionary. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Wires
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)
    {V V' : Config G c} {k k' : S.Choices}

abbrev Full := Physical.Key

lemma curb_by {A : Stores S} {F : Forest S.ratio} {s : Signed} {i : Where S} {e : Bond f} {x : ℝ}
    (h : Physical.openBond A F x e)
    (he : separation (s.act (roots S i)) (portOf S e) ≤ Next.SectorChange.span S.patch x) :
    curb (shots S x) A F x s i := by
  obtain ⟨q,rfl⟩ := h
  exact ⟨q,(contains s i _).mpr he⟩

def clueX (k : S.Choices) (V : Config G c) (x : ℝ) (j : Full G f) (i : Receipt G S) :=
    (Rows.slip • FieldJet.bump' T x V k (axisPrice j)) i.1 i.2

lemma outside {x : ℝ} (k : S.Choices) (V : Config G c) (j : Full G f) (i : Receipt G S)
    (H : Map.Aperture S T x)
    (h : ¬separation (spot S i.1) (portOf S j.1) ≤ Next.SectorChange.span S.patch x) :
    clueX T k V x j i = 0 := by
  rcases i with ⟨⟨s,i|i⟩,a⟩
  · exact Physical.clue_zero T k V H.branched ((s,.inl i),a) j h
  have ht : FieldJet.trial V k s i (axisPrice j) = FieldJet.trial V k s i 0 := by
    apply FieldJet.changes i s H.branched (fun i hi => rfl) ⟨fun i _=>rfl,fun i _=>rfl⟩
    intro e he
    have hi : e ≠ j.1 := fun hy => by
      rw [hy] at he
      apply h
      change separation (s.act i.1) (S.ratio.parent j.1.1) ≤ _
      unfold Next.SectorChange.span; omega
    rw [on_axis,Pi.single_eq_of_ne hi]; rfl
  unfold clueX
  change (slip • (-(Real.sqrt S.kernel.penalty • FieldJet.trial V k s i (axisPrice j)))) a=0
  rw [ht,FieldJet.trial,Curve.motionless,smul_zero,neg_zero,smul_zero]; rfl

lemma clueX_meas (k : S.Choices) (x : ℝ) (j : Full G f) (i : Receipt G S) (hS : S.patch.Branches S.kernel G) :
    Measurable (fun V : Config G c => clueX T k V x j i) := by
  have ht := (FieldJet.bump'_meas T x hS k i.1).comp (measurable_id.prodMk (measurable_const (a:=axisPrice j)))
  have hf : Continuous (fun y : G.Color => y i.2) := PiLp.continuous_apply ..
  unfold clueX; simp only [Pi.smul_apply]
  exact hf.measurable.comp ((measurable_const (a:=Rows.slip)).smul ht)

lemma clueX_align {x : ℝ} (V : Config G c) (k : S.Choices) {F : Forest S.ratio} {A : Stores S}
    {M : ℝ} (hA : Map.Aperture S T x) (hp : Authorized A V F x M) (j : Full G f)
    (h : Physical.openBond A F x j.1) (i : Receipt G S) :
    clueX T k V x j i = Physical.clue T k V x j i := by
  by_cases hr : separation (spot S i.1) (portOf S j.1) ≤ Next.SectorChange.span S.patch x
  swap
  · rw [outside T k V j i hA hr, Physical.clue_zero T k V hA.branched i j (show _ from hr)]
  unfold clueX Physical.clue
  simp only [Pi.smul_apply]
  rw [FieldJet.agrees T x V k hp _ i.1 (by
    rcases i with ⟨⟨s,i|i⟩,i'⟩
    · exact curb_by (s:=s) (i:=.inl i.1) h hr
    · exact curb_by (s:=s) (i:=.inr i) h hr)]

lemma clueX_scoped {x : ℝ} {X : Support c} {F F' : Forest S.ratio} {A A' : Stores S}
    (hA : Map.Aperture S T x) (H : Physical.Reads X A A' F F' V V' k k')
    (i : Receipt G S) (j : Full G f) (h : Shields X (spot S i.1) (4*radiusB x+1)) :
    clueX T k V x j i=clueX T k' V' x j i := by
  unfold clueX; simp only [Pi.smul_apply,FieldJet.around T x (axisPrice j) (axisPrice j) i.1 hA
    (Geo.Reads.visit H h) (Geo.Reads.way H h) (fun i _=>rfl)]

/-- Full surrogate of the identity-completed precision. -/
def beam (k : S.Choices) (V : Config G c) (x : ℝ) (A : Stores S) (F : Forest S.ratio) : Square (Full G f) :=
    Matrix.of fun i j => if Physical.openBond A F x i.1 ∧ Physical.openBond A F x j.1 then
      ∑ r : Receipt G S, clueX T k V x i r * clueX T k V x j r else (1:Square (Full G f)) i j

lemma beam_meas (k : S.Choices) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (i j : Full G f)
    (hS : S.patch.Branches S.kernel G) : Measurable fun V => beam T k V x A F i j := by
  simp only [beam,Matrix.of_apply]
  split
  · exact Finset.measurable_fun_sum _ fun m _ => (clueX_meas T k x _ _ hS).mul (clueX_meas T k x _ _ hS)
  exact measurable_const

theorem beam_exact (k : S.Choices) (V : Config G c) (x : ℝ) (A : Stores S) (F : Forest S.ratio)
    (hA : Map.Aperture S T x) {m} (h : Authorized A V F x m) :
    beam T k V x A F = Physical.AFull T A F x V k := by
  ext i j
  rw [beam,Matrix.of_apply,Physical.read_kernel _ _ _ _ _ _ hA.branched]; split
  next hi =>
    exact Finset.sum_congr rfl fun r _ => by
      rw [clueX_align T V k hA h i hi.1, clueX_align T V k hA h j hi.2]
  rfl

lemma range_limit (k : S.Choices) (V : Config G c) (x : ℝ) (A : Stores S) (F : Forest S.ratio)
    (hA : Map.Aperture S T x) :
    Reaches (Physical.place S) (2*Next.SectorChange.span S.patch x) (beam T k V x A F) := by
  intro i j h
  simp only [beam,of_apply]; split
  · refine Finset.sum_eq_zero fun r hr => ?_
    by_cases hi : separation (spot S r.1) (portOf S i.1) ≤ Next.SectorChange.span S.patch x
    · rw [outside T _ _ j r hA ?_,mul_zero]
      intro he
      apply h
      apply (separation_triangle _ (spot S r.1) _).trans
      rw [separation_comm (Physical.place S i)]
      change separation (spot S r.1) (portOf S i.1)+separation (spot S r.1) (portOf S j.1)≤_
      omega
    rw [outside _ _ _ _ _ hA hi,zero_mul]
  exact Reaches.one _ _ _ _ h

lemma beam_aperture {x : ℝ} (hA : Map.Aperture S T x) (k : S.Choices) (V : Config G c) (A : Stores S) (F : Forest S.ratio) :
    AnalyticBridge.RelativeLogdet.Aperture (Physical.place S) (radiusB x) (Physical.windows S x) (beam T k V x A F) :=
  ⟨(range_limit T k V x A F hA).trans (by have hh := hA.spans; omega),fun i j hj => (Physical.contained i j hj).trans (by omega)⟩

lemma beam_read {x : ℝ} (hA : Map.Aperture S T x) {X : Support c} {A A' : Stores S} {F F' : Forest S.ratio}
    (h : Physical.Reads X A A' F F' V V' k k') (i j : Full G f)
    (hp : Shields X (Physical.place S i) (14*radiusB x)) : beam T k V x A F i j=beam T k' V' x A' F' i j := by
  let R:=Next.SectorChange.span S.patch x
  by_cases hl : nearby (Physical.place S) (2*R) i j
  swap
  · rw [range_limit T _ _ _ _ _ hA _ _ hl, range_limit T _ _ _ _ _ hA _ _ hl]
  let B:=radiusB x
  have hB : 120≤B := hA.scale
  have ht : R≤B/50 := hA.spans
  have he : separation (Physical.place S i) (Physical.place S j) ≤ 2*R := hl
  simp only [beam,of_apply,h.frozen_bits hA.scale _ (hp.shrink (by omega)),h.frozen_bits hA.scale _ (hp.shift (by change separation (Physical.place S i) (Physical.place S j)+12*B≤14*B; omega))]
  split
  · refine Finset.sum_congr rfl fun r hr => ?_
    by_cases hv : separation (spot S r.1) (portOf S i.1) ≤ R
    · have hz : Shields X (spot S r.1) (4*radiusB x+1) := hp.shift (by
        rw [separation_comm]
        change separation _ (portOf S i.1)+(4*B+1)≤14*B; omega)
      rw [clueX_scoped T hA h _ i hz,clueX_scoped T hA h _ j hz]
    rw [outside T k V i r hA hv,outside T k' V' i r hA hv]; simp
  rfl

lemma positioned {x : ℝ} (hA : Map.Aperture S T x) {X : Support c} {F F' : Forest S.ratio} {A A' : Stores S}
    (H : Physical.Reads X A A' F F' V V' k k') :
    ReadTogether (Physical.place S) X (radiusB x) (Physical.windows S x) (Physical.windows S x)
      (beam T k V x A F) (beam T k' V' x A' F') :=
    ⟨beam_aperture T hA k V A F,beam_aperture T hA k' V' A' F',Physical.centered hA.scale,
      fun i h j => beam_read T hA H i j h,fun _ _ => rfl⟩
end Wires
end YM.PhysicalNext.Dictionary
