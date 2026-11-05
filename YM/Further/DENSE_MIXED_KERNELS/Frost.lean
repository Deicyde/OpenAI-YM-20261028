import YM.Further.DENSE_MIXED_KERNELS.Hall
import YM.Further.DENSE_MIXED_KERNELS.Stroke


/-!
# Generating the actual Word for the all-frozen alternative

Uses a ZERO-dimensional Gaussian, not a Lebesgue normalization
multiplying the vacuum grant anew or omitting tags. This service for
constructing `Stamp`'s, especially the Throng specialization with all
incoming marks considered before any smooth-patch eligibility.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Measure Finset Lattice RG Wilson Pressure Precision Module Tree
open Push.SectorMeasure Next.Fluctuations.Sector Push.AbsoluteSums Corona Overlay Extra.Multi Labels Marker
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical NNReal ENNReal
variable {c f : Side} {G : Gauge} {A : ChartRatio G} {H : Port A}
    {S : StepData c f} {F : Forest S.ratio}

section surface
variable {Ω ι κ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] {m : Measure Ω} {Z : Surface H ι κ Ω}

lemma Surface.Valid.just_tags (h : Z.Valid) : MeasurePreserving (fun x => x.1) (Z.ante m) m := by
  refine ⟨measurable_fst, Measure.ext_of_lintegral _ fun φ hm => ?_⟩
  have := Surface.add_haar H ι κ
  have he (x : Ω) : (∫⁻ z : H.front ι (H.Room κ),ENNReal.ofReal (Z.lifted (x,z)))=1 := by
    obtain ⟨c,hc,Hc⟩ := h.firm x
    change (∫⁻ z : H.front ι (H.Room κ), ENNReal.ofReal (Gaussian.pdf volume (Z.B x) z))=_
    rw [← ofReal_integral_eq_lintegral_ofReal (Gaussian.pdf_integrable volume hc Hc) (Eventually.of_forall
      fun i => (Gaussian.pdf_pos volume hc Hc i).le), Gaussian.normalized volume hc Hc,ENNReal.ofReal_one]
  unfold ante; rw [lintegral_map hm measurable_fst, lintegral_withDensity_eq_lintegral_mul _
    h.lifted_meas.ennreal_ofReal (show Measurable (fun a : Ω × H.front ι (H.Room κ) => φ a.1) from hm.comp measurable_fst)]
  rw [lintegral_prod _ (h.lifted_meas.ennreal_ofReal.mul (show Measurable (fun a : Ω × H.front ι (H.Room κ) => φ a.1) from hm.comp measurable_fst)).aemeasurable];
  apply lintegral_congr; intro x; simp only [Pi.mul_apply]
  rw [show (∫⁻ y : H.front ι (H.Room κ), ENNReal.ofReal (Z.lifted (x,y))*φ x)=(∫⁻ y : H.front ι (H.Room κ), ENNReal.ofReal (Z.lifted (x,y)))*φ x from
    lintegral_mul_const _ (h.lifted_meas.ennreal_ofReal.comp (show Measurable (fun y : H.front ι (H.Room κ) => (x,y)) from measurable_prodMk_left)),he x,one_mul]
end surface

namespace Frost
variable (F : Forest S.ratio) (H : Port A)

def view : View H F where
  J := ∅
  K := ∅
  Y := univ
  separated := by simp
  frozen := by simp
  base _ := ⟨fun _ => 0, fun _ => 1, fun _ => 0⟩
  lean := fun _ _ => 0
  way := fun _ _ => 1

lemma solid (U) : ((view F H).base U).Valid := by
  refine ⟨fun _ => ⟨1,by norm_num,fun x => ?_⟩,measurable_const,measurable_const,measurable_const⟩
  letI : IsEmpty (view F H).J := by unfold view; dsimp only; infer_instance
  letI : IsEmpty (view F H).K := by unfold view; dsimp only; infer_instance
  rw [show x = 0 from Subsingleton.elim ..]; simp



def all (k : (view F H).Frame) : F.Slice G := fun i => k.2 ⟨i, mem_univ i⟩
def drop (k : (view F H).Frame) : Keyed S × F.Slice G := (k.1,all F H k)
lemma drops : MeasurePreserving (drop F H) (view F H).fare ((Keyed.primary S).prod (F.order G)) := by
  let X : (view F H).Y ≃ F.Free := ⟨Subtype.val,fun i => ⟨i,mem_univ _⟩,fun _ => rfl,fun _ => rfl⟩
  let Y := MeasurableEquiv.piCongrLeft (fun _ : F.Free=>G.El) X
  have he : MeasurePreserving Y (Port.heldLaw) (F.order G) := measurePreserving_piCongrLeft (fun (_:F.Free) => G.probHaar) X
  have hy : MeasurePreserving (Prod.map id Y) ((view F H).fare) ((Keyed.primary S).prod (F.order G)) :=
    (MeasurePreserving.id _).prod he
  rw [show drop F H=Prod.map id Y from ?_]; exact hy
  funext i; refine Prod.ext rfl (funext fun j => ?_)
  exact (MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ => G.El) X i.2 ⟨j,mem_univ _⟩).symm

theorem boarding (U) : MeasurePreserving (drop F H ∘ Prod.fst) (((view F H).base U).ante (view F H).fare)
    ((Keyed.primary S).prod (F.order G)) := (drops F H).comp (solid F H U).just_tags

theorem shared (U : Config G c) (g : ℝ) (p) : (view F H).config U g p=F.drape (all F H p.1) := by
  unfold View.config; refine congr_arg _ (funext fun i => ?_)
  unfold View.inputs all view; simp

end Frost
end YM.Further.DenseMixedKernels
