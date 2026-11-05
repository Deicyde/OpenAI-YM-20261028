import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Drums
/-!
 # Unchanged model receipt, V9 R9 principal. adapt Hymn without phantom null.
  NO recognition of Seal for every Term.Request at all configs. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    Push.SectorMeasure SelectedOrderedKernels SelectedOrderedKernels.Sector Next.SectorChange.Rows Wisps
    Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r m : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
variable {Γ : Prices G ι → ℝ} (k q d) (a : Museum F x A X Y ι) (U : Config G f)
variable (he : Plays C D P B Pt T x) (hf : B.Regular X f') (hp:o∈X)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ) (hV : Healthy P.threshold Y V)
include he hf hp hY hu hΓ hV

lemma pollen (μ : Measure (Prices G ι)) [IsFiniteMeasure μ] : Covered μ (fun z => a.concert T u q d k f' Γ U V z ∘ increment V) n 0 := by
  letI : ProperSpace (Directions G c) := FiniteDimensional.proper ℝ _
  have ha:= he.cantos (k:=k) a hV hY hp
  refine domeCovered hΓ.finite (fun z hz => funext fun _ => by simp [Museum.concert,image_eq_zero_of_notMem_tsupport hz]) (fun z hz => ?_)
  have hc := clue (k:=k) (q:=q) (d:=d) he a hf hu hV U z (hΓ.stay z hz) --does it include hτ?
  have hh : ContDiffAt ℝ n (fun p: Directions G c × Prices G ι=>Carillon.vary V (a.twilight k T) p.2 (increment V p.1)* Γ p.2) (0,z):= (ha.joint z).mul (hΓ.real.contDiffAt.comp _ contDiffAt_snd)
  unfold Museum.concert; simp only [Function.comp_apply,← Complex.ofReal_mul]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hh.mul hc)
lemma opaqueE (L:List (Directions G c))(hl:L.length≤n):
    let f:= a.hymn T u q d k f' Γ U
    let b:= a.concert T u q d k f' Γ U V
    let μ:= Gaussian.cloud (a.twilight k T V)
    Multi.Puff.Crest n f V ∧ Integrable (fun z=>leftDerivs (b z) L V) μ ∧ ((leftDerivs f L V:ℝ):ℂ)=∫ z, leftDerivs (b z) L V ∂μ:= by
  intro h b μ; have ha:= he.cantos (k:=k) a hV hY hp
  have ht : ((fun U => (h U:ℂ)) ∘ increment V) =ᶠ[𝓝 0] fun v => ∫ z,b z (increment V v) ∂μ := by
    have hy := Multi.Puff.inc_tr V |>.tendsto 0; rw [Work.G07.at_zero_increment] at hy
    filter_upwards [hy.eventually ha.near] with v hv
    have hh := Density.exchange _ _ hv ha.pos (0:Prices G ι) (fun z => Γ z * f' (a.received k T q d u (increment V v) U z))
    unfold h Museum.hymn; rw [Function.comp_apply,if_pos hv,hh.2,← integral_complex_ofReal]; congr! 1; ext1 z; simp [Density.priced,Carillon.vary,b,Museum.concert,mul_assoc]
  have hc := pollen q d k a U he hf hp hY hu hΓ hV μ
  obtain ⟨hQ,hI,hL⟩ := left_integral V L.get hl hc ht
  have hb : ∀ᵐ z ∂μ, leftDerivs (b z) L V=iteratedFDeriv ℝ L.length (b z ∘ journey V L.length L.get) 0 cart := hc.ae.mono (fun z hz => by
    simpa only [List.ofFn_get] using Germ.ordered L.get ((show Germ n (b z) V from hz).prod hl))
  have hr : Multi.Puff.Crest n h V := crest_cast.mp (Multi.Puff.into n _ hQ)
  refine ⟨hr,hI.congr (hb.mono fun _ hx => hx.symm),?_⟩
  rw [List.ofFn_get] at hL; rw [show ((leftDerivs _ L V:ℝ):ℂ)=leftDerivs (fun U => (h U:ℂ)) L V from (Push.Local.left_linear Complex.ofRealCLM L hr.germ hl).symm, hL]
  exact integral_congr_ae (hb.mono fun _ hx => hx.symm)

lemma allotted (z:Prices G ι) (t:ℝ)(ht:0≤t) (hs: z∈ tsupport Γ → ∀ (j:ℕ),j≤n →∀ D':Slab G c j,(∀ i, P.dirBound (S.ratio.parent o) (D' i)) → ‖iteratedFDeriv ℝ j (fun y=> f' (a.received k T q d u (journey V j D' y) U z)) 0‖ ≤ t) :
    let m:=1+Carillon.speed n D.Z B.threshold P.power (JointLoad.Heir.scope B X r x) z
    Band n (P.dirBound (S.ratio.parent o)) V m t (a.concert T u q d k f' Γ U V z):=by
    intro m; have ha:=he.cantos (k:=k) a hV hY hp; have hy:= ha.sing B.threshold_pos.le B.threshold_le D.chimes z
    change Band n (P.dirBound _) V (Carillon.speed n D.Z B.threshold P.power (JointLoad.Heir.scope B X r x) z) 1 _ at hy
    by_cases hz:z∈ tsupport Γ
    swap; · rw [show a.concert T u q d k f' Γ U V z =(fun _=>(0:ℂ)) from funext fun _=>by simp [Museum.concert,image_eq_zero_of_notMem_tsupport hz]]; exact band_rise (band_constant n _ (r:=m) (by have :=hy.sane; unfold m; positivity)) (norm_zero.le.trans ht) le_rfl
    let f : Config G c→ℝ := fun i=>f' (a.received k T q d u i U z)
    have he := clue (q:=q) (d:=d) (k:=k) he a hf hu hV U z (hΓ.stay z hz)
    have h' : Germ n f V:=ContDiffAt.comp (f:=fun p:Directions G c=> (p,z)) 0 he (contDiffAt_id.prodMk contDiffAt_const)
    have hj : Band n (P.dirBound (S.ratio.parent o)) V 1 t (Complex.ofRealCLM ∘ f):=by
       refine ⟨crest_cast.mpr (Multi.Puff.into _ f h'), zero_le_one, ht,fun L hl hp=>?_⟩ -- order
       rw [one_pow,mul_one, Push.Local.left_linear Complex.ofRealCLM L (show Push.Local.Chart n f V from h') hl, show leftDerivs f L V= iteratedFDeriv ℝ L.length (f ∘ journey V L.length L.get) 0 cart by simpa only [List.ofFn_get] using Germ.ordered L.get (h'.prod hl)]
       rw [show ∀ x:ℝ,‖Complex.ofRealCLM x‖=‖x‖ from fun _ => Complex.norm_real _]
       simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hs hz L.length hl L.get (fun i=> hp _ (List.get_mem ..))) (show ∀ i:Fin L.length,‖cart i‖ ≤ (1:ℝ) from fun i => (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by simp only [cart,Pi.single_apply]; split <;> norm_num))
    have hL : a.concert T u q d k f' Γ U V z = ((Γ z:ℂ) • fun W => (Carillon.vary V (a.twilight k T) z W:ℂ)) * (Complex.ofRealCLM ∘ f) :=by ext1 W; simp [Museum.concert, f,mul_comm]
    rw [hL,show m=Carillon.speed n D.Z B.threshold P.power (JointLoad.Heir.scope B X r x) z+1 from add_comm ..]; exact band_rise ((hy.scale (Γ z:ℂ)).multiply hj) (by rw [Complex.norm_real,mul_one]; exact mul_le_of_le_one_left ht (hΓ.little _)) le_rfl
end YM.PhysicalNext.Repeat.Peak
