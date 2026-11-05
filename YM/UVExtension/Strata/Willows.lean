import YM.UVExtension.Strata.Wilson
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Strata
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Polish
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
open Polar Silica Shield Score Flux Matter
-- provide one Bulb price tight with point domination absolute all measured legs
open Eider
variable {t:κ→Bool→ι}(h:∀ b,Tendsto (fun n=> t n b) qq v)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ:κ→ E} {Y:κ→ E→ Config G c}
variable {F:Forest S.ratio} (M:κ→ Hat G F)
variable (he:∀ i,Mode (Y i) (τ i) k u)(hK:∀ i,(M i).legal s ∧ Y i (τ i)=(M i).bill)(qV:StableR v R)
include h he p hK qV
variable [NeBot v](hn:0≤u)
include hn
lemma pound (B':Finset (Bond f)) (P:Molecule S)(x:F.Slice G × Air f G): ∀ i≤k, Together qq (fun n b=> shiftV (R:=R) (t n b) (Abide s χ U.K T M t n b)
    (JetF (fun y=> rhythm B' (Abide s χ U.K T M t n b) (Y n y) A Q.table P (R (t n b)) w U.a Q.halo) i (τ n)) x):=by
  rcases x with ⟨z,x⟩; let X i b:= Abide s χ U.K T M t i b; let μ i:=renew z (M i); let X' i b:= (X i b).wrapY z; let y n b:= wound (R:=R) (t n b) (X n b) (z,x)
  have hY i : (μ i).legal s∧ Y i (τ i)=(μ i).bill:= hK i; have hv : Walt qq τ k (fun i b t=> scalp B' (X' i b) (Y i t) (R (‹κ→Bool→ι› i b)).beta A (y i b)):= wages p h μ he hY qV B' (fun _=> bend x) ⟨‖bend x‖,Eventually.of_forall fun _=>le_rfl⟩
  have hp:=hv.times (standsP p h (Eventually.of_forall he) (Eventually.of_forall hY) qV (fun _=>bend x) ⟨_,Eventually.of_forall fun _=>le_rfl⟩ (fun _=>Matter.own P) P)
  have hf := topicM p h M qV (fun i=>(hK i).1) hn (z,x)
  intro i hi
  -- no FD instance E [?]→L needed; use Walt twins on constant. 
  exact ((Walt.stamp (x:=τ) (k:=k) hf).pay (Walt.stamp (hp.jets i hi))).atProbe

omit he hK [FiniteDimensional ℝ E] in
lemma pounce (hm:∀ i,(M i).legal s) (L: Molecule S)(J:κ→ Finset ℕ)(x:F.Slice G × Air f G): Together qq (fun n b=> shiftV (R:=R) (t n b) (Abide s χ U.K T M t n b)
    ((Abide s χ U.K T M t n b).body (R (t n b)) Q.table w U.a (J n) Q.halo L) x):= by
  rcases x with ⟨z,x⟩; let μ i:=renew z (M i); let X i b:=(Abide s χ U.K T M t i b); have hp i:=Walt.stamp (x:=bracket) (k:=0) (Score.alight p h qV μ hn hm (fun _=>bend x) ⟨‖bend x‖,Eventually.of_forall fun _=>le_rfl⟩ J i)
  exact ((Walt.stamp (topicM p h M qV hm hn (z,x))).pay (caraffa L _ fun j (_:j∈L)=> hp j)).atProbe
section filters
omit p h he hK hn qV [NeBot v] [FiniteDimensional ℝ E]
variable {F:Type} [NormedAddCommGroup F] [NormedSpace ℝ F][CompleteSpace F] {f:κ→ Bool→α→ F}
variable [MeasurableSpace α]{μ:Measure α}[qq.IsCountablyGenerated]
lemma oars {g:α→ℝ}(hg:Integrable g μ)(hp:∀ᶠ n in qq,∀ b,Integrable (f n b) μ∧∀ᵐ i ∂μ,‖f n b i‖≤g i)(h:∀ᵐ i ∂μ,Together qq (fun n b=> f n b i)): Together qq (fun n b=> ∫ i,f n b i ∂μ):=by
  refine ⟨⟨_,hp.mono fun n h b=> (norm_integral_le_integral_norm _).trans (integral_mono_ae (h b).1.norm hg (h b).2)⟩,?_⟩
  let v n i:= f n true i-f n false i; let t n:= ‖∫ i,v n i ∂μ‖
  have hh:Tendsto (fun n=> ∫ i,v n i ∂μ) qq (𝓝 0):=by
    rw [← show ∫ _i:α,(0:F) ∂μ = 0 from by simp]
    refine tendsto_integral_filter_of_dominated_convergence (F:=v) (fun i=>g i+g i) (hp.mono fun n hn=> ((hn true).1.sub (hn false).1).1) (hp.mono fun n hn=>?_) (hg.add hg) (h.mono fun i hi=> ?_)
    · exact (((hn true).2).and ((hn false).2)).mono (fun i h=> (norm_sub_le ..).trans (add_le_add h.1 h.2))
    apply Metric.tendsto_nhds.mpr; intro ε he
    filter_upwards [hi.cap _ (half_pos he)] with i hi; rw [dist_zero_right]; exact hi.trans_lt (half_lt_self he)
  refine (show Tendsto t qq (𝓝 0) from (by simpa using hh.norm)).congr' (hp.mono fun n hn=>?_)
  unfold t v; dsimp only; rw [dist_eq_norm]; exact congr_arg norm (integral_sub (hn true).1 (hn false).1)
end filters
variable (V':Air f G→ℝ)(P:ι→ Molecule S→ℝ)(hV: Crystal (v:=v) (H:=H) (χ:=χ) (k:=k) (u:=u) (A:=A) V' P)
-- product Fubini; Haar. cap across n
include hV
variable [qq.IsCountablyGenerated]
lemma lyric (B':Finset (Bond f))(L:Molecule S)(hh:∀ i b, Healthy (temp s) ((H (t i b)).unionP L) (Y i (τ i))) : Walt qq τ k (fun n b y=> ∫ i: (F.Slice G × Air f G), rhythm B' (Abide s χ U.K T M t n b) (Y n y) A Q.table L (R (t n b)) w U.a Q.halo i ∂((F.order G).prod (Abide s χ U.K T M t n b).dice)):=by
    let X i b:= Abide s χ U.K T M t i b; let μ i b:=(F.order G).prod (X i b).dice
    let g n b y:= rhythm B' (X n b) (Y n y) A Q.table L (R (t n b)) w U.a Q.halo
    have hp n b : Meristem (g n b) (τ n) (μ n b) k:= (Flux.boosts (X:=X n b) (H _) rfl (hK n|>.1) rfl ((p.realm.granted _ _ _ (T (t n b)) _ _ (H _) (p.rails _) rfl).2 E _ F (X n b) (τ n) rfl rfl rfl (hK n|>.1) (hK n|>.2) (he n)|>.1) p.realm.bay p.realm.foot L B').1
    refine ⟨Eventually.of_forall fun n b=>(hp n b).calls.1,fun i hi=>?_⟩
    let v0 i b:=X i b; let fF n b:= shiftV (R:=R) (t n b) (v0 n b) (JetF (g n b) i (τ n));
    let P' := (F.order G).prod (volume : Measure (Air f G)); obtain ⟨d,hd,hr⟩:= hV.receipt.tills
    have hQ(n b):= pedals p (t n b) (X n b) rfl rfl (hK n|>.1) _ ((hp n b).calls.2 i hi).1
    have h : Together qq (fun n b=>∫ i,fF n b i ∂P'):=by
       refine oars (μ:=P') (f:=fF) (g:=fun i:F.Slice G × Air f G=> d * V' i.2) (hV.employs.comp_snd _|>.const_mul _) (eventually_all.mpr (fun b=>(h b).eventually (hV.uv.and hr)|>.mono fun j hj=>?_)) (ae_of_all _ (fun v=>pound p h M he hK qV hn B' L v i hi))
       refine ⟨(hQ j b).1,ae_of_all _ fun i'=>?_⟩
       have hh:=hh j b; rw [hK j|>.2] at hh
       exact ((hj.1 _ (X j b) rfl rfl (hK j|>.1) rfl L).2 E (τ j) _ (hK j|>.2) hh (he j) B' i hi i').trans (mul_le_mul_of_nonneg_right (budget_single hj.2 L) (hV.positive _))
    refine h.shimmy (Eventually.of_forall fun n=>funext fun b=> (((hp n b).calls.2 i hi).2.trans (hQ n b).2).symm)
omit he hK [FiniteDimensional ℝ E] in
lemma atCash (hm:∀ i,(M i).legal s) (L:Molecule S)(J:κ→Finset ℕ): Together qq (fun i b=> (Abide s χ U.K T M t i b).attains (R (t i b)) Q.table w U.a (J i) Q.halo L):=by
    let μ:=(F.order G).prod (volume (α:=Air f G)); let X i b:= Abide s χ U.K T M t i b; let fF n b:= (X n b).body (R (t n b)) Q.table w U.a (J n) Q.halo L; let g n b:=shiftV (R:=R) (t n b) (X n b) (fF n b)
    obtain ⟨d,hd,hr⟩:= hV.receipt.tills; have hQ(i b):= pedals p (t i b) (X i b) rfl rfl (hm i) _ ((H (t i b)).integrated (X i b) rfl rfl (hm i) (J i) L)
    have he: Together qq (fun n b=>∫ i,g n b i ∂μ):=by
       refine oars (μ:=μ) (f:=g) (g:=fun i:F.Slice G×Air f G=> d * V' i.2) (hV.employs.comp_snd _|>.const_mul _) (eventually_all.mpr (fun b=>(h b).eventually (hV.uv.and hr)|>.mono fun j hj=> ⟨(hQ j b).1,ae_of_all _ fun i=>?_⟩)) (ae_of_all _ (fun x=> pounce p h M qV hn hm L J x))
       exact ((hj.1 _ (X j b) rfl rfl (hm j) rfl L).1 (J j) _).trans (mul_le_mul_of_nonneg_right (budget_single hj.2 L) (hV.positive _))
    exact he.shimmy (Eventually.of_forall fun n=>funext fun b=>(hQ n b).2.symm)
end Polish
end YM.UVExtension.Strata
#print axioms YM.UVExtension.Strata.Polish.lyric
#print axioms YM.UVExtension.Strata.Polish.atCash
