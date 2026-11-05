import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Gauged
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Consumer


/-!
# Return the tests and the actual law to the original frame

Some applications want sums within a single probability-E (e.g. V
ungauged/with no global health). Here we can still use *one* gauge from
the Folio for all reads under comparison, and return simultaneously at
all k,Y,χ in *that* sector and budget. No assertion that the linear
limiting expression with FULL ψ itself transforms like the whole potential
or is gauge-independent. Its assessment after rotating observers back (and
removing V' only on the target) will be a priced approximation, not an
identity with a k(V) substituted for k(V') there. No selection likelihood
or support statement aside from the same read assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid Gaussian
open YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local Assembly ColorBook GaugeRoute
open MeasureTheory SectorTools.PhysicalGaussianSwitch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

open FreeResolvent (treeInverse insertion ix flatten tensor)
variable {G : Gauge} {c f n : Side} {S : StepData c f} {A : Stores S}
    {F : Forest S.ratio} {x : ℝ}

/-- Coordinates on the positive physical colors. -/
def toGauge (z : Site c → G.El) (A : Stores S) (F : Forest S.ratio) (x : ℝ) :=
    onPage (Equiv.refl (Active A x F)) (tagColor (fun i => adBody (columnAt S z x A F i)))

lemma ortho (z : Site c → G.El) (A : Stores S) (F : Forest S.ratio) (x : ℝ) :
    let R:=toGauge z A F x
    R.transpose*R=1 ∧ R * R.transpose=1 := by
  let B i := adBody (columnAt S z x A F i)
  exact ⟨onPage_left _ (tagColor B) (tag_checked B), onPage_right _ (tagColor B) (tag_checked B)⟩

section turn
variable (z : Site c → G.El) (A : Stores S) (F : Forest S.ratio) (x : ℝ)

lemma turn_color (Z : Vec (In x A F (G:=G))) (i) :
    tape (toGauge z A F x *ᵥ Z) i = G.adjoint (z (S.ratio.parent i.val.val.1)) (tape Z i) := by
  let v:=tape Z; let R b := adBody (columnAt S z x A F b)
  have he : toGauge z A F x *ᵥ Z=tape.symm (pivot (columnAt S z x A F) v) := by
    rw [show Z=tape.symm v from (tape.symm_apply_apply _).symm]; exact onPage_read (Equiv.refl _) R ..
  rw [he,tape.apply_symm_apply]; rfl
lemma gauge_in {Z : Vec (In x A F (G:=G))} (W : Finset (Bond f)) (R : ℝ) :
    Guards W ((toGauge z A F x)*ᵥ Z) R ↔ Guards W Z R := by
  unfold Guards; simp_rw [turn_color,G.norm_adjoint]
def swung (Γ : Vec (In x A F (G:=G)) → ℝ) (Z : Vec (In x A F (G:=G))) :=
    Γ ((toGauge z A F x).transpose *ᵥ Z)
lemma swung_turn (Γ : Vec (In x A F (G:=G)) → ℝ) (Z) :
    swung z A F x Γ ((toGauge z A F x) *ᵥ Z)=Γ Z := by unfold swung; rw [mulVec_mulVec,(ortho ..).1,one_mulVec]


lemma turned_law (Pt : Teller G) (T : Tube G S) (V : Config G c) (k : S.Choices)
    (s : Geometry) (Y : LinkArray G (Frozen A x F)) (q : Push.SectorMeasure.Chi) (d : ℝ)
    (h : Pt.Funds S T) :
    let Y':=sendFrozen S z x A F Y
    let V':=Lattice.gauge z V
    let Q := palette T A F k x V s
    let P := palette T A F k x V' s
    let a := portrait T A F k x V s q d Y
    let b := portrait T A F k x V' s q d Y'
    let R:=toGauge z A F x
    P.PosDef → b=R *ᵥ a ∧ P=covView R Q ∧ Q.PosSemidef ∧ MeasurePreserving (view R) (cloud Q) (cloud P) := by
  intro Y' V' Q P a b R hP
  obtain ⟨u,v,hu,hv⟩ := h.feeds
  have he : S.patch.Branches S.kernel G := h.knobs.symm ▸ h.kernel
  have H := GaugeRoute.stays S T z V x A F k q d Y hu he (shots S x) s
  obtain ⟨-,hf,hz,-⟩ := H.2.2 0
  have hr' : P=covView R Q := hf
  have hk := (ortho z A F x).1
  have hv : Q=covView R.transpose P := by
    rw [hr']; unfold covView; rw [transpose_transpose]
    change R.transpose*R=1 at hk
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hk,Matrix.one_mul,Matrix.mul_assoc,hk, Matrix.mul_one]
  have hQ : Q.PosSemidef := hv.symm ▸ covView_posSemi _ hP.posSemidef
  refine ⟨hz,hr',hQ,?_⟩; rw [hr']; exact view_cloud hQ _

lemma turning_photo (V : Config G c) (a : Vec (In x A F (G:=G))) (Y : LinkArray G (Frozen A x F))
    (g : ℝ) (Z : Vec (In x A F (G:=G))) :
    let L:=toGauge z A F x
    photo g (Lattice.gauge z V) (L*ᵥ a) (sendFrozen S z x A F Y) (L *ᵥ Z) =
      Lattice.gauge (constantGauge z S.ratio) (photo g V a Y Z) := by
  intro L
  let R:=constantGauge z S.ratio; let V':=Lattice.gauge z V
  unfold photo
  rw [← Matrix.mulVec_smul,← Matrix.mulVec_add]
  let q := a+g • Z; let U:=physical A F V Y (tape q)
  let U':=physical A F V' (sendFrozen S z x A F Y) (tape (L *ᵥ q)); funext e
  change U' e= R e.1 * U e * (R (e.1+step e.2))⁻¹
  by_cases he : e∈F.trunks
  · have h : U e=1 := F.on_tree _ ⟨e,he⟩
    have h' : U' e=1 := F.on_tree _ ⟨e,he⟩
    have he : R e.1=R (e.1+step e.2) := congr_arg z (F.trunk_internal (show (e.1,e.2) ∈ F.trunks from he)).symm
    rw [h,h',he]; group
  let j : F.Free := ⟨e,he⟩
  have hf (a : Vec (In x A F (G:=G))) (Y V) :
      physical A F V Y (tape a) e=returned A F V Y (tape a) j := F.off_tree _ j
  by_cases hv : chill A x F j
  · let i : Frozen A x F := ⟨j,hv⟩
    have he' b Y V : physical A F V Y (tape (G:=G) b) e=Y i := (hf b Y V).trans (freeze_held (j:=i) ..)
    unfold U' U; rw [he',he']; rfl
  let i : Active A x F := ⟨j,hv⟩
  have hh (a : Vec (In x A F (G:=G))) (Y V) :
    physical A F V Y (tape a) e=G.lieExp (tape a i) * replica S.ratio V e :=
      (hf a Y V).trans (freeze_regular (j:=i) ..)
  have he (U : G.Color) : G.lieExp (G.adjoint (R e.1) U)= R e.1* G.lieExp U * (R e.1)⁻¹ := by
    apply G.mat_injective; simp only [G.mat_lieExp,G.mat_adjoint,G.mat_mul,G.exp_conjugate,G.mat_inv]; rfl
  unfold U' U
  rw [hh,hh,turn_color,show z (S.ratio.parent i.val.val.1)=R e.1 from rfl, he,
    show replica S.ratio V'=Lattice.gauge R (replica S.ratio V) from (copied S.ratio S.patch.odd_side V z).symm]
  unfold Lattice.gauge; group
end turn

section return_
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {I : Type} [Fintype I] [DecidableEq I]

def rotateBack (z : Site f → G.El) (P : I → Occasion G f) (r : I → G.El) := fun i => r i * (z (P i).location)⁻¹
omit [Fintype I] [DecidableEq I] in
lemma sampler (P : I → Occasion G f) (z : Site f → G.El) (r : I → G.El) (g : ℝ) (U : Config G f) :
    sampled P (rotateBack z P r) g (Lattice.gauge z U)=sampled P r g U := by
  funext i
  let s := (P i).link; let x:=(P i).location;let y := Work.F03.slotFace s x
  have h : stop x s.walk=y.1 := by
    unfold y Work.F03.slotFace Slot.offset; rw [wrap_stop_cover,map_zero,add_comm]; nth_rw 1 [show x=x+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]
  have hk : s.atSite (Lattice.gauge z U) x=G.adjoint (z x) (s.atSite U x) := by
    rw [Work.F03.atSite_path,Work.F03.atSite_path,face_gauge,G.curvature_conjugate,← h]; exact GaugeRoute.travel_ad z U x s.walk (G.curvature (faceValue U (Work.F03.slotFace s x)))
  change G.adjoint (r i*(z x)⁻¹) (g⁻¹ • (s.atSite (Lattice.gauge z U) x)) (P i).color = _
  rw [hk,← map_smul (G.adjoint (z x)),← G.adjoint_mul]
  rw [mul_assoc,inv_mul_cancel,mul_one]; rfl

omit [CompleteSpace E] in
lemma Assessment.return_to (P : I → Occasion G f) (z : Site c → G.El) (r : I → G.El)
    (t g : ℝ) (X : Support f) (Γ : Vec (In x A F (G:=G)) → ℝ) (a : Vec (In x A F (G:=G)))
    (Y : LinkArray G (Frozen A x F)) (V : Config G c) {u m C} (R : Vec I → E) {Q Q' : Gaussian.Table (In x A F (G:=G))}
    (J : Gaussian.Table I) :
    let L := toGauge z A F x; let U:=Lattice.gauge z V; let Y':=sendFrozen S z x A F Y
    MeasurePreserving (view L) (cloud Q) (cloud Q') →
    Assessment P (rotateBack (constantGauge z S.ratio) P r) X t x g (photo g U (L*ᵥ a) Y') Q' J
      (swung z A F x Γ) u m R C → Assessment P r X t x g (photo g V a Y) Q J Γ u m R C := by
  intro L U Y' h H
  let k:=constantGauge z S.ratio;let r' := rotateBack k P r
  let f' (V) := R (sampled P r' g V - u); let q := photo g U (L*ᵥ a) Y'
  let v (V) := R (sampled P r g V - u); let q' := photo g V a Y
  let f (V) := masked t X f' (q V);let w (V):=masked t X v (q' V); let Γ':=swung z A F x Γ
  have he i : q (view L i)=Lattice.gauge k (q' i) := turning_photo z A F x V a Y g i
  have ht i : f' (q (view L i))=v (q' i) := by rw [he]; unfold f' r' v; rw [sampler]
  have hm i : f (view L i)=w i := by
    have hH : Healthy t X (q (view L i)) ↔ Healthy t X (q' i) := by rw [he]; unfold Healthy; rw [gauge_flags]
    by_cases hi : Healthy t X (q' i) <;> unfold f w
    · rw [masked_eq _ _ _ _ (hH.mpr hi),masked_eq _ _ _ _ hi,ht]
    rw [masked_ne _ _ _ _ (hH.not.mpr hi),masked_ne _ _ _ _ hi]
  have hΓ i : Γ' (view L i)=Γ i := swung_turn ..
  have h₁ := pay_pull h (fun i => f' (q i)) H.full.aestronglyMeasurable
  have h₂ := pay_pull h f H.auth.aestronglyMeasurable
  have h₃ := pay_pull h (fun i => Γ' i • f i) H.both.aestronglyMeasurable
  simp_rw [ht] at h₁
  simp_rw [hm] at h₂ h₃
  simp_rw [hΓ] at h₃
  let t := ∫ z, R (m-u+z) ∂cloud J
  refine ⟨H.reference,H.forecastBound,h₁.1.mpr H.full,h₂.1.mpr H.auth,h₃.1.mpr H.both,?_,?_,?_,?_⟩
  · intro i
    change Γ i • v (q' i)=Γ i • w i
    rw [← ht,← hm,← hΓ]; exact H.whole _
  · change ‖(∫ i, Γ i • w i ∂cloud Q)-t‖ ≤ _; rw [h₃.2]; exact H.charged
  · change ‖(∫ i, w i ∂cloud Q)-t‖ ≤ _; rw [h₂.2]; exact H.bare
  change ‖(∫ i, v (q' i) ∂cloud Q)-t‖ ≤ _; rw [h₁.2]; exact H.unmasked




end return_
end YM.PhysicalNext.PhysicalGuard7f546.Curved
