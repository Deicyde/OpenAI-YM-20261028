import YM.EveryPhase.Decay

/-! # No exceptional characters -/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Filter Set Spec Boundary Next.BOUNDARY Spectral Mink Probe MeasureTheory Measure OS Analysis
open scoped Topology NNReal InnerProductSpace ComplexOrder
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {F : Final C f S} (L : Almanac F)

section
variable {V : Wightman S} {W : Surface S} {R : S.Rotation} {s : S.RealSpin}
    {T : Table C.book} {D : Chamber T timeAxis} {J : V.operators.H →L[ℂ] D.H}

lemma groundvac (h : Attachment V D J) (H : FieldCore W R s V) :
    V.momentum.region zeroE V.operators.vacuum=V.operators.vacuum := by
  apply (show Injective J from (⟨J.toLinearMap,h.acts.scale⟩ : V.operators.H →ₗᵢ[ℂ] D.H).injective)
  rw [h.projections H _ zeroE_m,h.acts.start,← reflection_projection]
  exact (D.flow.ground.starProjection_eq_self_iff.mpr D.omega0.property)

theorem proj_eq (h : Attachment V D J) (H : FieldCore W R s V) (hp : D.UniqueHeat) (x : V.operators.H) :
    V.momentum.region zeroE x=inner ℂ V.operators.vacuum x • V.operators.vacuum := by
  let Ω := V.operators.vacuum
  let P := V.momentum.region zeroE
  have hi : Injective J := (⟨J.toLinearMap,h.acts.scale⟩ : V.operators.H →ₗᵢ[ℂ] D.H).injective
  have he : J (P x) ∈ D.flow.ground := by
    unfold P; rw [h.projections H _ zeroE_m,← reflection_projection]
    exact Submodule.starProjection_apply_mem ..
  obtain ⟨a,hA⟩ := hp ⟨_,he⟩
  have hh : a • Ω=P x := hi (by rw [map_smul]; exact h.acts.start.symm ▸ congrArg Subtype.val hA)
  have hk : P.adjoint=P := V.momentum.real zeroE_m
  have hz : a=inner ℂ Ω x := by
    have he : inner ℂ Ω (P x)=inner ℂ Ω x := calc
      _ = inner ℂ (P.adjoint Ω) x := by rw [ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by rw [hk, show P Ω=Ω from groundvac h H]
    rw [← hh, inner_smul_right,inner_self_eq_norm_sq_to_K,show ‖Ω‖=1 from H.total.norm] at he
    simpa using he
  rw [← hz]; exact hh.symm


lemma univ_of_closed {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [μ.IsOpenPosMeasure] (Z : Set α) (p : IsClosed Z) (h : ∀ᵐ i ∂μ, i∈Z) : Z=univ := by
  by_contra! hh
  have ht : μ Zᶜ ≠ 0 := p.isOpen_compl.measure_ne_zero _ (nonempty_compl.mpr hh)
  exact ht h

-- Extend bounds on the *vacuum*-subtracted pairing through continuity on the
-- whole character space, without at first asserting continuity of the actual
-- ground projection matrix elements.
theorem extends_decay (w : SumOfWords S) (h : finite w) : ∃ M : ℝ, 0≤M ∧ ∀ (s : ℝ≥0), 1 ≤ s → ∀ i,
    let x := stands (L.actors i).operators w
    let v := (L.actors i).operators.vacuum
    let r := inner ℂ x (bHeat (L.J i) s x) - (↑(‖inner ℂ v x‖ ^ 2):ℂ)
    0≤r ∧ r ≤ ↑(M*(s:ℝ)⁻¹^2) := by
  haveI := F.phase.phase.decomposition.support
  obtain ⟨M,hM,hm⟩ := inverse_square L w h
  refine ⟨M,hM, fun t ht => ?_⟩
  let p (i : F.α.space.X) := stands (L.actors i).operators w
  let u (i : F.α.space.X) := ‖inner ℂ (L.actors i).operators.vacuum (p i)‖^2
  let g (i : F.α.space.X) := inner ℂ (p i) (bHeat (L.J i) t (p i))-(u i:ℂ)
  have he i : (L.actors i).operators.vacuum=stands (L.actors i).operators [(1,[])] := by
    rw [stands_cons,one_smul]; simp only [stands, operator, LinearMap.zero_apply,ZeroMemClass.coe_zero,add_zero]; rfl
  have hu : Continuous u := by unfold u; simp_rw [he]; exact (sum_pair L _ _).norm.pow _
  have hg : Continuous g := (uniform_heat L w t (zero_lt_one.trans_le ht)).sub (Complex.continuous_ofReal.comp hu)
  let A : ℂ := ↑(M*(t:ℝ)⁻¹^2)
  have hp : g ⁻¹' Icc 0 A = univ := by
    apply univ_of_closed (μ:=F.α.space.μ) _ (isClosed_Icc.preimage hg)
    filter_upwards [L.almostEvery] with i hi
    have hh : inner ℂ (p i) ((L.actors i).momentum.region zeroE (p i))=(u i:ℂ) := by
      rw [proj_eq (L.links i) (L.cores i) hi, inner_smul_right]
      have hk : inner ℂ (p i) (L.actors i).operators.vacuum =
          (starRingEnd ℂ) (inner ℂ (L.actors i).operators.vacuum (p i)) := (inner_conj_symm _ _).symm
      rw [hk,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    change 0 ≤ g i ∧ g i ≤ _
    rw [show g i = inner ℂ (p i) ((bHeat (L.J i) t - (L.actors i).momentum.region zeroE) (p i)) by
      rw [_root_.sub_apply,inner_sub_right,hh] ]; exact hm _ _ ht
  exact fun i => (show g i ∈ Icc 0 A from (hp.symm ▸ (mem_univ i) : i∈g ⁻¹' Icc 0 A))

lemma cluster_zero (i) (w : SumOfWords S) (h : finite w) :
    let x := stands (L.actors i).operators w
    (L.actors i).momentum.region zeroE x = inner ℂ (L.actors i).operators.vacuum x • (L.actors i).operators.vacuum := by
  let x := stands (L.actors i).operators w
  let Ω := (L.actors i).operators.vacuum
  let a := inner ℂ Ω x
  let c := ‖a‖^2
  let P := (L.actors i).momentum.region zeroE
  have hh : inner ℂ x (P x)=(c:ℂ) := by
    obtain ⟨M,hM,H⟩ := extends_decay L w h
    let g t := inner ℂ x (bHeat (L.J i) t x)-(c:ℂ)
    have hg := (bHeat_limit (L.links i) (L.cores i) x)
    have he : Tendsto g atTop (𝓝 (inner ℂ x (P x)-(c:ℂ))) := (tendsto_const_nhds.inner hg).sub tendsto_const_nhds
    apply sub_eq_zero.mp; apply le_antisymm
    · apply le_of_tendsto_of_tendsto he (g:=fun s : ℝ≥0 => (↑(M*(s:ℝ)⁻¹^2):ℂ))
      · have hu : Tendsto (fun s : ℝ≥0 => ((s:ℝ)⁻¹ : ℝ)) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
        simpa [Function.comp_def] using! Complex.continuous_ofReal.continuousAt.tendsto.comp ((hu.pow 2).const_mul M)
      exact (eventually_ge_atTop (1:ℝ≥0)).mono fun s hs => (H s hs i).2
    exact ge_of_tendsto he ((eventually_ge_atTop (1:ℝ≥0)).mono fun s hs => (H s hs i).1)
  have hP : P.adjoint=P := (L.actors i).momentum.real zeroE_m
  have hPx : P (P x)=P x := (L.actors i).momentum.idempotent zeroE_m x
  have hv : P Ω=Ω := groundvac (L.links i) (L.cores i)
  have hp : inner ℂ (P x) (P x)=(c:ℂ) := calc
    _ = inner ℂ (P.adjoint x) (P x) := by rw [hP]
    _ = _ := by rw [ContinuousLinearMap.adjoint_inner_left,hPx,hh]
  have hu : inner ℂ (a • Ω) (P x)=(c:ℂ) := by
    rw [inner_smul_left,← ContinuousLinearMap.adjoint_inner_left P x Ω,hP,hv]
    change (starRingEnd ℂ) a*a=_; rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  change P x=a • Ω; apply sub_eq_zero.mp; apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [inner_sub_left,inner_sub_right, inner_sub_right,hp,hu, ← inner_conj_symm (P x) (a • Ω),hu,
    inner_self_eq_norm_sq_to_K,norm_smul,show ‖Ω‖=1 from (L.cores i).total.norm]
  simp [c]
end

lemma all_plant (i) (x : (L.actors i).operators.H) :
    (L.actors i).momentum.region zeroE x = inner ℂ (L.actors i).operators.vacuum x • (L.actors i).operators.vacuum := by
  let Z := (L.actors i).operators
  let Ω := Z.vacuum
  let Q := (L.actors i).momentum.region zeroE
  let P := (innerSL ℂ Ω).smulRight Ω
  suffices H : Q=P from DFunLike.congr_fun H x
  apply Kernel.Gram.by_bud (L.cores i).soil
  intro b
  let v := fun j => (b.get j).1
  let f := fun j => (b.get j).2
  obtain ⟨Ψ,hΨ,hu⟩ := (L.links i).smears b.length v
  have hv (k : ℕ) : Q (Ψ (Joint.materialize _ fun i => Probe.cap k (f i)))=
      P (Ψ (Joint.materialize _ fun i => Probe.cap k (f i))) := by
    rw [hΨ (fun i => Probe.cap k (f i))]
    let g := tensorWord v (fun i => Probe.cap k (f i))
    have he : stands Z [(1,g)] = Z.vector g := by rw [stands_cons,one_smul]; simp [stands,operator]
    change Q (Z.vector g)=P (Z.vector g)
    rw [← he]; apply cluster_zero
    intro i hi j hj
    obtain rfl := List.mem_singleton.mp hi
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hj
    exact Probe.finite_cap _
  have he : Tendsto (fun k => fun i => Probe.cap k (f i)) atTop (𝓝 f) :=
    tendsto_pi_nhds.mpr fun i => persistent (f i)
  have ht := ((Joint.jointCont b.length).tendsto f).comp he
  have h := (Ψ.continuous.tendsto (Joint.materialize b.length f)).comp ht
  rw [hΨ,show tensorWord v f=b by simp [tensorWord,v,f]] at h
  exact tendsto_nhds_unique_of_eventuallyEq (Q.continuous.continuousAt.tendsto.comp h)
    (P.continuous.continuousAt.tendsto.comp h) (Eventually.of_forall hv)

theorem every (i : F.α.space.X) : (L.chambers i).UniqueHeat := by
  intro v
  let V := L.chambers i
  obtain ⟨x,hx⟩ := reaches L i v.val
  let a := inner ℂ (L.actors i).operators.vacuum x
  have he : V.flow.orth ((L.J i) x)=(L.J i) x := by rw [hx]; exact V.D.starProjection_eq_self_iff.mpr v.property
  rw [reflection_projection,← (L.links i).projections (L.cores i) _ zeroE_m,all_plant,map_smul,(L.links i).acts.start] at he
  exact ⟨a,Subtype.ext (he.trans hx)⟩

lemma boundary_realizes (i) : (L.actors i).Realizes (W:=(L.contours i).world)
    F.sector.turns F.room.kernel.spin := (L.links i).with_heat (L.cores i) (every L i)

lemma boundary_zero_energy (i) (x : (L.actors i).operators.H) :
    (L.actors i).momentum.region zeroE x=x ↔ ∃ z : ℂ, z • (L.actors i).operators.vacuum=x := by
  constructor
  · intro h; exact ⟨_, (all_plant L i x).symm.trans h⟩
  rintro ⟨z,rfl⟩; rw [map_smul,groundvac (L.links i) (L.cores i)]
end YM.EveryPhase
