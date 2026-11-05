import YM.OPE.Orbits.Port

/-!
# Orthogonalized finite horizon projections

Polarizers in the unselected hierarchy, read only in their eventual
rotation-safe collars (extended by zero when these would not fit).
At this stage no inter-horizon compatibility. Reality of these
readouts uses a further conjugation average. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Filter Set MeasureTheory Extraction Table Prescription
open scoped Matrix.Norms.Frobenius BigOperators Topology ContDiff Classical

attribute [local instance] YM.Work.A15.compact_ortho
private abbrev secO : SecondCountableTopology Ortho := by
    haveI:SecondCountableTopology M4:= inferInstanceAs (SecondCountableTopology Lines)
    exact inferInstanceAs (SecondCountableTopology ↥(Matrix.unitaryGroup Axis ℝ : Set M4))
attribute [local instance] secO
local instance measO : MeasurableSpace Ortho := borel Ortho
local instance borelO : BorelSpace Ortho:= ⟨rfl⟩
private def allO : TopologicalSpace.PositiveCompacts Ortho := ⟨⟨univ,isCompact_univ⟩,by simp⟩
def haar : Measure Ortho:= Measure.haarMeasure allO
local instance : haar.IsHaarMeasure:= by unfold haar; infer_instance
local instance : IsProbabilityMeasure haar := ⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ allO⟩

variable {G:Gauge} {L:Register G} {S:Table L} {Q:DiffPlan S}
variable (P:Prescription Q) {X: Rotation S}{ρ:S.RealSpin} {I:Type}[Fintype I] {d:I→ℕ} (hX:X.Laws Q ρ)
    (hS:S.Hierarchy) (j n:ℕ) (x:I→E4)(o:E4)(i:Mode Q)(w:Labels S d)

/-- Rotated value integrated at each k. Keep rotation of OUTPUT as well,
or else averaging wouldn't fix lower fields. -/
def spinning (P:Prescription Q) (X:Rotation S)(n:ℕ)(x:I→E4)(o:E4)(k:Ortho) (w:Labels S d): S.Field n := X.act n k (shadow P n (Ortho.move k⁻¹ ∘ x) (names (roll X k⁻¹ w)) (Ortho.move k⁻¹ o))

def orbitMargin (P:Prescription Q)(n:ℕ) (x:I→E4)(o:E4):Prop:=∀ i∈ bands Q n, Dock P i x o

def bears (X:Rotation S) (P:Prescription Q)(i:Mode Q)(n:ℕ)(x:I→ E4)(o:E4)(w:Labels S d) (k:Ortho): S.Field n := checkRow P i (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o) (roll X k⁻¹ w) • (X.act n k (P.loaded i n))
include hS in
lemma scatter (k:Ortho) : spinning P X n x o k w=∑ i∈ bands Q n,bears X P i n x o w k := by
   unfold spinning bears; simp [Orbits.check_eq _ _ hS,shadow,map_smul,map_sum]

def entries (z: ((I→E4)×E4) × (Lines × (Labels S d)×S.Field n)): S.Field n:=
    checkRow P i (M4.move z.2.1 ∘ z.1.1) (M4.move z.2.1 z.1.2) z.2.2.1 • z.2.2.2

def rotateSample (X:Rotation S)(P:Prescription Q) (i:Mode Q) (n:ℕ) (w:Labels S d) (k:Ortho) : Lines × (Labels S d) × S.Field n:= ((k⁻¹).val, (roll X k⁻¹ w), (X.act n k (P.loaded i n)))
omit [Fintype I] in
private lemma sample_cont (hw:X.Laws Q ρ) : Continuous (rotateSample X P i n w):=by
   have hf : Continuous (fun k:Ortho=> (k.val:Lines)):= continuous_subtype_val
   refine ((hf.comp continuous_inv).prodMk ((continuous_pi fun j=> (hw.spin (d j) (w j)).comp continuous_inv).prodMk (hw.spin n _)))
lemma entries_bear (w:Labels S d)(k:Ortho) : bears X P i n x o w k = entries P n i ((x,o),rotateSample X P i n w k):=rfl
include hS in
set_option maxHeartbeats 1000000 in
private lemma smooth_section (hx:Dock P i x o){n:ℕ}(t:Labels S d)(a:S.Field n)(k:Ortho):
    ContDiffAt ℝ ∞ (entries P n i) ((x,o),((k.val:Lines),t,a)):=by
    let x':= Ortho.move k ∘ x; let o' := Ortho.move k o
    have hr (x₁:I→E4)(o₁:E4)(v:Labels S d): ((fun z:((I→E4)×E4)× Labels S d=>checkRow P i z.1.1 z.1.2 z.2) ((x₁,o₁),v)) = checkRow P i x₁ o₁ v:= rfl
    have ht:= check_smooth P i hS (o:=o') (x:=x') (v:=t) (hx k)
    let Z := ((I→E4)×E4) × (Lines × (Labels S d)×S.Field n)
    let V(z : Z):= (M4.move z.2.1 ∘ z.1.1,M4.move z.2.1 z.1.2)
    let f (z:Z):= (V z,z.2.2.1)
    have hv: ContDiff ℝ ∞ f:= by
       have hf:ContDiff ℝ ∞ (fun z:Z=>(M4.move z.2.1 ∘ z.1.1)):= contDiff_pi.mpr fun j=> smoothMotion.comp ((by fun_prop): ContDiff ℝ ∞ fun z:Z=>(z.1.1 j,z.2.1))
       have hg:ContDiff ℝ ∞ (fun z:Z=>(M4.move z.2.1 z.1.2)):= smoothMotion.comp ((by fun_prop):ContDiff ℝ ∞ fun z:Z => (z.1.2,z.2.1))
       exact (hf.prodMk hg).prodMk (by fun_prop)
    refine ContDiffAt.smul (𝕜':=ℂ) (f:=(fun z:((I→E4)×E4)× Labels S d=> checkRow P i z.1.1 z.1.2 z.2) ∘ f) ?_ ?_
    · exact ht.comp (f:=f) _ hv.contDiffAt
    exact (show ContDiff ℝ ∞ (fun z:Z => z.2.2.2) from by fun_prop).contDiffAt -- inspect
    -- replace
include hS hX in
set_option maxHeartbeats 400000 in
lemma integrable_bears (hx:Dock P i x o): Integrable (bears X P i n x o w) haar:=by
    let p:= rotateSample X P i n w
    let f:= fun q:Lines × Labels S d × S.Field n=> entries P n i ((x,o),q)
    have ht(k:Ortho): ContinuousAt f (p k):= (smooth_section P hS x o i hx (p k).2.1 (p k).2.2 k⁻¹).continuousAt.comp (continuous_const.prodMk continuous_id|>.continuousAt)
    have hP := sample_cont P n i w hX
    exact Continuous.integrable_of_hasCompactSupport ((continuous_iff_continuousAt (f:=f ∘ p)).mpr (fun x=>(ht x).comp hP.continuousAt)) (HasCompactSupport.of_compactSpace _)
private lemma integrated {F E A:Type} [NormedAddCommGroup F][NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E][NormedAddCommGroup A][NormedSpace ℝ A][FiniteDimensional ℝ A]
    {O:Set A}{p:Ortho→F} (hp:Continuous p){x:A}(ho:IsOpen O)(hx:x∈O){f:A×F→E} (hf:∀ z∈O ×ˢ Set.range p,ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (fun y=>∫ k,f (y,p k) ∂haar) x:=by
    letI: MeasurableSpace F:= borel _
    letI: BorelSpace F:=⟨rfl⟩
    have hK:=isCompact_range hp; have hm:AEMeasurable (μ:=haar) p:=hp.aemeasurable
    have h':ContDiffOn ℝ ∞ (fun y=>∫ k,f (y,p k) ∂haar) O:=contDiffOn_infty.mpr (fun m=>parametrize_smooth_nat m (fun z hz=>(hf z hz)|>.of_le (show (m:WithTop ℕ∞) ≤ ∞ from by exact_mod_cast (show (m:ℕ∞) ≤ (⊤:ℕ∞) from le_top))) ho hK (fun _=>mem_range_self _) hm)
    exact (h' _ hx).contDiffAt (ho.mem_nhds hx)
include hX hS in
set_option maxHeartbeats 1800000 in
lemma smooth_orbit_row (hx:Dock P i x o):ContDiffAt ℝ ∞ (fun z:(I→E4)×E4=>∫ k:Ortho,bears X P i n z.1 z.2 w k ∂haar) (x,o):=by
    let F := Lines × Labels S d × S.Field n
    let p:Ortho→F:= rotateSample X P i n w; let K:= range p
    have hP : Continuous p:=sample_cont P n i w hX
    have hK:IsCompact K := isCompact_range hP
    let O: Set ((I→E4)×E4):={z | Dock P i z.1 z.2}; have hOpen:IsOpen O:=compact_dock P i
    have hw(z:((I→E4)×E4) × F) (hz:z∈O ×ˢ K):ContDiffAt ℝ ∞ (entries P n i) z:=by
         rcases z with ⟨⟨u,v⟩,q⟩; obtain ⟨k,rfl⟩:= hz.2; exact smooth_section P hS u v i hz.1 (p k).2.1 (p k).2.2 k⁻¹
    change ContDiffAt ℝ ∞ (fun z:((I→E4)×E4)=>∫ k,entries P n i (z,p k) ∂haar) (x,o); exact integrated (F:=F) (f:=entries P n i) (x:=(x,o)) hP hOpen hx hw
end YM.OPE.Orbits
