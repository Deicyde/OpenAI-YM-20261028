import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Double

/-! # Single double-marked expectation at the SAME E execution.
Exact expression under the endpoint fog; no analyticity of h across a
branch asserted without `Museum` + no-hole payment. Constants under fixed
price geometry and even winding supports. Sign and convex parameter
uniformity included via Marked. No generic Mayer factor integral bound
or reconstructing missing suppliers for density/compatibility. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Solo
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score Push.SectorMeasure
    Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussianLaws ColorBook
    AnalyticBridge.LocalGaussian Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record} {Γ : Prices G ι → ℝ}
    {H : ℝ → ℝ → ℝ} {K : ℝ}
variable (a : Museum F x A X Y ι) (T u q d k f' Γ H) (U : Config G f)

def concerted (V : Config G c) := let Q := a.twilight k T V
    if Q.PosDef then ∫ z, Γ z * H (Γ z) (f' (a.received k T q d u V U z)) ∂(Gaussian.cloud Q) else 0
abbrev coefficient (V : Config G c) (z : Prices G ι) := a.concert T u q d k (H (Γ z) ∘ f') Γ U V z

def repaired := repair (concerted T u q d k f' Γ H a 1)
variable {T u q d k f' Γ H} (b : Folio.Bulletin x Pt T) (hf' : B.Regular X f')
include b hf'




omit b hf'
variable (hG : G.Simple) (he : Plays C D P B Pt T x) (hf : Seed B o X f') (hτ : B.supBounds o X f' τ)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ) (hV : Healthy P.threshold Y V) (hH : Wholesome H)
include hG he hf hτ hY hu hΓ hH hV
lemma covered (μ : Measure (Prices G ι)) [IsFiniteMeasure μ] : Covered μ (fun z => coefficient T u q d k f' Γ H a U V z ∘ increment V) n 0 := by
  letI : ProperSpace (Directions G c) := FiniteDimensional.proper ℝ _
  have ha := he.cantos (k:=k) a hV hY hf.site
  refine domeCovered hΓ.finite (fun z hz => funext fun _ => by simp [coefficient,Museum.concert,image_eq_zero_of_notMem_tsupport hz]) (fun z hz => ?_)
  have hc := he.prior (q:=q) (d:=d) (k:=k) a hf hV hG U z hu (hΓ.stay z hz) hτ |>.1
  have hh := (((hH.joint.of_le (budgetThrough n)).contDiffAt).comp _ ((hΓ.real.contDiffAt.comp (0,z) contDiffAt_snd).prodMk hc))
  unfold coefficient Museum.concert; simp only [Function.comp_apply, mul_assoc, ← Complex.ofReal_mul]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((ha.joint z).mul hh)

lemma exchange (L : List (Directions G c)) (hl : L.length ≤ n) :
    let h := concerted T u q d k f' Γ H a U; let b := coefficient T u q d k f' Γ H a U V; let μ := Gaussian.cloud (a.twilight k T V)
    Multi.Puff.Crest n h V ∧ Integrable (fun z => leftDerivs (b z) L V) μ ∧ ((leftDerivs h L V : ℝ):ℂ) = ∫ z,leftDerivs (b z) L V ∂μ := by
  intro h b μ; have ha := he.cantos (k:=k) a hV hY hf.site
  have ht : ((fun U => (h U:ℂ)) ∘ increment V) =ᶠ[𝓝 0] fun v => ∫ z,b z (increment V v) ∂μ := by
    filter_upwards [(increment_germ V).eventually ha.near] with v hv
    have hh := Density.exchange _ _ hv ha.pos (0:Prices G ι) (fun z => Γ z * H (Γ z) (f' (a.received k T q d u (increment V v) U z)))
    unfold h concerted; rw [Function.comp_apply,if_pos hv,hh.2,← integral_complex_ofReal]; congr! 1; ext1 z; simp [Density.priced,Carillon.vary,b,Museum.concert,mul_assoc]
  have hc := covered a U hG he hf hτ hY hu hΓ hV hH μ (k:=k) (q:=q) (d:=d)
  obtain ⟨hQ,hI,hL⟩ := left_integral V L.get hl hc ht
  have hb : ∀ᵐ z ∂μ, leftDerivs (b z) L V=iteratedFDeriv ℝ L.length (b z ∘ journey V L.length L.get) 0 cart := hc.ae.mono (fun z hz => by
    simpa only [List.ofFn_get] using Germ.ordered L.get ((show Germ n (b z) V from hz).prod hl))
  have hr : Multi.Puff.Crest n h V := crest_cast.mp (Multi.Puff.into n _ hQ)
  refine ⟨hr,hI.congr (hb.mono fun _ hx => hx.symm),?_⟩
  rw [List.ofFn_get] at hL; rw [show ((leftDerivs h L V:ℝ):ℂ)=leftDerivs (fun U => (h U:ℂ)) L V from (Push.Local.left_linear Complex.ofRealCLM L hr.germ hl).symm, hL]
  exact integral_congr_ae (hb.mono fun _ hx => hx.symm)



omit hV hH


end YM.PhysicalNext.JointLoad.Psalm.Solo
