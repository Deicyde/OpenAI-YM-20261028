import YM.RG08.Ward.Caravan
/-! # Apply path walk test on joint-neighborhood equality, ignoring offsets outside
small windows. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory Set
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Next.Free
open PertExtension.Series.Tested Profiles PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius Matrix
section change
variable {X : Type} [TopologicalSpace X][MeasurableSpace X][BorelSpace X]
variable {a : X}
omit [MeasurableSpace X][BorelSpace X] in
lemma incline (u v : Set X)(hu : u∈𝓝 a)(hv : v∈𝓝 a) (e : ℝ→ (X≃ₜX))
    (hp : Tendsto (fun p:ℝ×X=> e p.1 p.2) (𝓝 (0,a)) (𝓝 a))
    (he : Tendsto (fun p:ℝ×X=> (e p.1).symm p.2) (𝓝 (0,a)) (𝓝 a))
    (F H : ℝ→X→ℝ)(hz : ∀ᶠ p:ℝ×X in 𝓝 (0,a),F p.1 p.2=H p.1 (e p.1 p.2)) :
    ∃ s ∈ 𝓝 a, s ⊆ u ∧ IsOpen s ∧
      (∀ᶠ t in 𝓝[>]0,e t '' s ⊆ v ∧ ∀ x∈s,F t x= H t (e t x)) ∧
      ∃ t∈𝓝 a,∀ᶠ z in 𝓝[>]0, t⊆ e z '' s := by
  obtain ⟨z,hz,t,ht,hQ⟩:=mem_nhds_prod_iff.mp (hz.and (show ∀ᶠ p:ℝ×X in 𝓝 (0,a),e p.1 p.2 ∈ v from hp hv))
  obtain ⟨s,hs,hO,hS⟩:=mem_nhds_iff.mp (inter_mem ht hu); have H' := hO.mem_nhds hS
  obtain ⟨x,hx,y,hy,Hx⟩:=mem_nhds_prod_iff.mp (he H'); refine ⟨s,H',fun i hi=>(hs hi).2,hO,?_,y,hy,?_⟩
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ t in 𝓝 (0:ℝ),t∈z from hz)] with r hr
    exact ⟨Set.image_subset_iff.mpr (fun i hi=> (show F r i = H r (e r i) ∧ _ from hQ (show (r,i)∈z ×ˢ t from ⟨hr,(hs hi).1⟩)).2), fun i hi=>(hQ (show (r,i)∈z ×ˢ t from ⟨hr,(hs hi).1⟩)).1⟩
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ t in 𝓝 (0:ℝ),t∈x from hx)] with r hr
  exact fun i hi=> ⟨(e r).symm i, Hx (show (r,i)∈x ×ˢ y from ⟨hr,hi⟩),(e r).apply_symm_apply _⟩
lemma kohler (e : X ≃ₜ X) (μ : Measure X) (hE : MeasurePreserving e μ μ) (u : Set X) (hp : IsOpen u)
    (f g : X→ℝ) (h : ∀ x∈u,f x=g (e x)) : (∫ x in u,f x∂μ) = ∫ x in e '' u, g x ∂μ := by
  rw [← integral_indicator hp.measurableSet, ← integral_indicator (e.isOpenMap _ hp|>.measurableSet)]
  let E:=e.toMeasurableEquiv; let s:= e '' u; let F:=s.indicator g
  refine Eq.trans ?_ (MeasurePreserving.integral_comp' (f:=E) hE F); apply integral_congr_ae; apply Eventually.of_forall
  intro i; have he (hu : E i∈s): i ∈ u := by obtain ⟨v,hv,hV⟩:=hu; exact E.injective hV ▸ hv
  by_cases hh:i∈u
  · change u.indicator f i=s.indicator g (e i); rw [indicator_of_mem hh,indicator_of_mem (Set.mem_image_of_mem _ hh)]; exact h i hh
  dsimp only; unfold F; rw [indicator_of_notMem hh,indicator_of_notMem (hh ∘ he)]
end change
variable {c f m : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable (U : Matrix (Body 1 f) (Body 1 c) ℝ) (v w : ℝ→ Link G c)
local notation "A" => FreeResolvent.Active G T →ℝ
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ
variable (κ : S.Choices) (n : ℕ) (V : ℕ → Config G f → ℝ) (F F' : Air G) (K M : FreeResolvent.FaceRow) (i : G.ColorIndex)
variable (D : ChartRatio G) (hD : LocalRatio D)
local notation "Q" => YM.RG08.quad G (YM.RG08.hessian M)
local notation "Θ[" t "]" => discPay S G T t κ n V -- syntax not param; fix
local notation "Δ" => treeMatrix G S T K
include hD
set_option maxHeartbeats 400000 in
theorem bless (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i))
    (hF : Gets F) (hA : Halt F) (hX : Whole K) (hR : Whole M) (hK : ∀ m,(K.acts m).IsSymm) (hM : ∀ m,(M.acts m).IsSymm)
    (hU : Inputs S U (K.acts f) (M.acts c)) (hΔ : (Δ).PosDef)
    (hyp : ∀ w : Link G c, Aura (fun j=> leaned hΔ (snow G T) (chargeS S T G) (lodgeP G S.ratio (riseM S G T U *ᵥ w) w) (expEra (surge S G F i D) j)) (fun j=> -grand (j+2) (F' j) c w))
    (hv : AnalyticAt ℝ v 0) (hw : AnalyticAt ℝ w 0)
    (e : ℝ → ((T.Slice G) ≃ₜ (T.Slice G)))
    (hs : Tendsto (fun p:ℝ×T.Slice G=>e p.1 p.2) (𝓝 (0,1)) (𝓝 1)) (ht : Tendsto (fun p:ℝ×T.Slice G=> (e p.1).symm p.2) (𝓝 (0,1)) (𝓝 1))
    (hy : ∀ t,MeasurePreserving (e t) (T.order G) (T.order G)) (hh : ∀ᶠ p:ℝ×T.Slice G in 𝓝 (0,1), Θ[v] p.1 p.2 = Θ[w] p.1 (e p.1 p.2)) :
    Fit (n+1) (fun t=> oblige Q F' n t (v t)) (fun t=> oblige Q F' n t (w t)) := by
  obtain ⟨v',hV,H⟩:=linings hv.contDiffAt; obtain ⟨w',hW,hO⟩:=linings hw.contDiffAt
  have hz:∀ᶠ p:ℝ×T.Slice G in 𝓝 (0,1), Θ[v'] p.1 p.2= Θ[w'] p.1 (e p.1 p.2) := by
    filter_upwards [hh,(continuous_fst.tendsto ((0:ℝ), (1:T.Slice G))).eventually H,(continuous_fst.tendsto ((0:ℝ),(1:T.Slice G))).eventually hO] with x hx he hh
    unfold discPay; rw [he,hh]; exact hx
  have hf:= hv.congr H.symm; have ht':=hw.congr hO.symm
  obtain ⟨a,b,c'⟩:= unbless S G T U v' κ n V F F' K M i D hD hf.contDiffAt hV hp he hF hA hX hR hK hM hU hΔ hyp
  obtain ⟨u,hu,hA'⟩:= unbless S G T U w' κ n V F F' K M i D hD ht'.contDiffAt hW hp he hF hA hX hR hK hM hU hΔ hyp
  obtain ⟨s,hS,hL,hN,hC,hD'⟩:=incline _ _ b hu _ hs ht _ _ hz
  have h := (c' (fun _=>s) (Eventually.of_forall fun t=> ⟨hN.measurableSet,hL⟩) ⟨s,hS,Eventually.of_forall fun t=> le_rfl⟩)
  have hh':=(hA' (fun z=> e z '' s) (hC.mono fun t ht=> ⟨(e t|>.isOpenMap _ hN).measurableSet,ht.1⟩) hD')
  let C := (∫ x,(crownM hΔ).kern x ∂snow G T)* hatsScale S T D
  have HC : C≠0 := (mul_pos (normSun hΔ (snow G T)) (pow_pos hD.scale _)|>.ne')
  let Y (f : ℝ→ Link G c) := fun t=> oblige Q F' n t (f t)
  have Hv : Fit (n+1) (C • (Real.exp ∘ (-Y v'))) (C • (Real.exp∘(-Y w'))) :=
    h.turn.join ((Fit.join (Fit.supply (hC.mono fun t hh=> congr_arg (fun p:ℝ=> (t^Module.finrank ℝ (L))⁻¹*p) (kohler _ _ (hy t) s hN _ _ hh.2)) _) hh'))
  have hq : Fit (n+1) (Real.exp∘(-Y v')) (Real.exp∘(-Y w')) := by
    have hh:=Hv.scale C⁻¹; rw [inv_smul_smul₀ HC,inv_smul_smul₀ HC] at hh; exact hh
  have hC' (f) (hx : AnalyticAt ℝ f 0) : Bill 0 (-Y f) := by
    apply life_price (ContinuousAt.tendsto ?_ |>.mono_left nhdsWithin_le_nhds) -- ?_
    unfold Y oblige; refine (ContDiffAt.continuousAt (n:=ω) ((((stanza_smooth Q c).contDiffAt).comp _ hx.contDiffAt).add (ContDiffAt.sum (fun e _=> (contDiffAt_id.pow _).mul ?_))|>.neg))
    exact (show Grass (grand (e+2) (F' e) c) from Grass.list (fun r _=> Grass.base (Hemi.pos (recital _ _)))).smooth.contDiffAt.comp (0 : ℝ) hx.contDiffAt
  have hPI:= (hq.unelevate (hC' _ hf) (hC' _ ht')).negate; rw [neg_neg,neg_neg] at hPI
  exact (Fit.join (Fit.supply ((H.filter_mono nhdsWithin_le_nhds).mono (fun x hx=> congr_arg _ hx.symm)) _) hPI |>.join (Fit.supply ((hO.filter_mono nhdsWithin_le_nhds).mono (fun x hx=> congr_arg _ hx)) _)) -- defeq congr placeholders
end YM.RG08.Reflect
