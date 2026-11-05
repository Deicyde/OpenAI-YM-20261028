import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Levels
/-! # width staircase for one auxiliary V9 film.Arch
 `Z,F` fixed pre Authorship. Cstar then knows F and Teller. Billboard requirements independent of P, halo. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Circlet
open Function Filter Set Lattice RG RG.Supply Wilson Pressure Pressure.Tube Tree Next Next.Foundations Precision
open Push Push.PriceCompiler AnalyticBridge LocalGaussianLaws JointLoad JointLoad.Heir JointLoad.Heir.Suite
open Input Org Extra.Histories Planned.PrimaryIntegral295 WaterLevels Bloch Bid Planned.AtomRegular Planned.AtomRegular.Foliage
open AnalyticBridge.VerifiedReset.Time Next.Scheduling
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G: Gauge}{M : Sheet G} {K : MapPrices}
-- explicit sphere.PYX

def Az (G : Gauge)(n:ℕ) : Collar G n := Classical.choice (Foliage.collarSupply G n)
def store (G:Gauge)(n:ℕ) : Rights G n := Classical.choice (authority G n)
lemma arrange (Pt:Teller G) (δ y:ℝ)(hd:0<δ)(hy:0≤y) (u:ℕ)(ht:u=Pt.below.order) (i:ℕ)(hu:i=Pt.top.power) : ∃ C: Libretto G u, C.δ=δ ∧ C.N=y ∧ C.Z=Az G u∧ C.rights=store G u ∧
    ∀ {c f:Side} (S : StepData c f)(T: Tube G S),Pt.Funds S T → ∀ F, Matins T F i (2*C.C) C.M:=by
   subst u i; obtain ⟨W⟩:= webExists G; have he:= Foliage.Cube.fee_one (Az G Pt.below.order); obtain ⟨N,hN,H⟩:= coaches Pt Pt.top.power (2*Foliage.Cube.fee (Az G Pt.below.order)) Pt.top.power_ge (by positivity); exact ⟨⟨Az G Pt.below.order,store G Pt.below.order,W,δ,hd,y,hy,N,hN⟩,rfl,rfl,rfl,rfl,H⟩
variable {Γ:ℕ→ℕ→ Teller G}

structure Pitch (M:Sheet G) (K: MapPrices) (Γ:ℕ→ℕ→ Teller G)(C:Programs M)(r:ℕ→ℕ) :Prop where
    crown:WaterLevels.Capital M K Γ
    licenses j i (h:StepStages j i) (hp:M.first≤ i)(L: Side)(hv:r j≤L.val): licensed (wide K j i) (scale K j i) L
    gift(j i:ℕ): let A:= C j i;
                  A.Z=Az G (M.profile i).order ∧ A.rights=store G (M.profile i).order ∧ A.δ= wide K j i∧ A.N=scale K j i
    bidden (j i:ℕ){c f:Side} (S : StepData c f)(T:Tube G S): (Γ j i).Funds S T→ ∀ F, Matins T F (M.profile j).power (2*(C j i).C) (C j i).M

lemma pose (M:Sheet G)(K:MapPrices): ∃ Q: ℕ→ℕ→Teller G,∃ C:Programs M,∃ r:ℕ→ℕ, Pitch M K Q C r:=by
  obtain ⟨Q,hQ⟩ := WaterLevels.invest M K
  choose C h₁ h₂ h₃ h₄ h₅ using fun j i=> arrange (Q j i) (wide K j i) (scale K j i) (wide_pos ..) (scale_nn ..) (M.profile i).order (congr_arg RG.Stage.order (hQ.setup.braids j i).2.1.symm) (M.profile j).power (congr_arg RG.Stage.power (hQ.setup.braids j i).1.symm)
  obtain ⟨u,-,-,H⟩:= collect_upper M.floorL (fun j n=>∀ i, StepStages j i→ yarn (wide K j i) (scale K j i) ≤ (n:ℝ)^2/128) (fun j=> eventually_transitions j _ _ (fun i _ =>by
     apply (tendsto_natCast_atTop_atTop (R:=ℝ) |>.eventually -- ??
           (show ∀ᶠ x:ℝ in atTop,yarn (wide K j i) (scale K j i) ≤ x^2/128 from ((tendsto_pow_atTop (show 2≠0 by decide): Tendsto (fun x:ℝ=>x^2) atTop atTop).atTop_div_const (by norm_num : (0:ℝ)<128)).eventually_ge_atTop _))
  ))
  exact ⟨Q,C,u, hQ,fun j i h ht L hv=> H _ _ hv _ h,fun j i=> ⟨h₃ j i,h₄ j i,h₁ j i,h₂ j i⟩,h₅⟩

lemma transcribe (Pt:Teller G) (δ A:ℝ) {J:Stage}(hp:Pt.below=J) (C:Libretto G J.order) (h:(C.δ)=δ)(hc:C.N=A)
    (H:Patch)(hi:H.Branches Pt.bind G)(hv:licensed δ A H.L)(hO:J.order ≤ Pt.top.order)(hB:J.power≤Pt.top.power)(ht: ∀ {c f:Side} (S : StepData c f)(T:Tube G S),Pt.Funds S T→ ∀ F, Matins T F Pt.top.power (2*C.C) C.M) (e:ℝ) (he:0<e):
    ∃ D:Record, D.ε≤e ∧ ∀ᶠ x in atTop, ∀ B' B:BudgetPoint, B'.threshold=temp x → B.threshold= fiery G x H.L→ B.B=radiusB (betaF G x H.L)→B'.order=J.order→B.order=Pt.top.order→B'.power=J.power→B.power=Pt.top.power→∀ {c f:Side}(S:StepData c f)(T:Tube G S),S.patch=H→Seam T δ A→Lift.Booth Pt S T→100*(1+radiusB x)≤c.val→Plays C D B' B Pt T x:=by
  subst J δ A; obtain ⟨D,hD,-,h⟩:= Heir.songs H Pt C hi hv hO hB ht 42 e he
  exact ⟨D,hD,h.mono fun x hx U V h b c d f p g=> (hx _ _ h b c d f p g).2⟩

variable {C:Programs M}
variable (Y:Rolls M)
structure Sax (D:ℕ→ℕ→Record) (j i:ℕ) (x:ℝ) (Γ:ℕ→ℕ→ Teller G) (K:MapPrices)(C:Programs M) : Prop where
    earn(P B:BudgetPoint): P.threshold=temp x→ B.threshold= fiery G x (Y.L j)→B.B=radiusB (betaF G x (Y.L j))→ P.order=(M.profile i).order → B.order=(M.profile j).order→ P.power=(M.profile i).power→B.power=(M.profile j).power→∀ {c f:Side}(S:StepData c f)(T:Tube G S), S.patch.J=j→ S.patch.L=Y.L j→Seam T (wide K j i) (scale K j i)→Lift.Booth (Γ j i) S T→100*(1+radiusB x)≤c.val →Plays (C j i) (D j i) P B (Γ j i) T x

-- Later.Evidence.*ALL* stretching monotone delays.
abbrev Pads (Q:ℕ→ℕ→ Record) (p:ℕ→ℕ→ Teller G) (K:MapPrices)(C:Programs M) {θ: Protection Y}(D:Delays θ) := ∀ j x,D.betaEntry j≤x →∀ i:ℕ, StepStages j i → M.first ≤ i→Sax Y Q j i x p K C

lemma cymbals {u:ℕ→ℕ} (hh:Pitch M K Γ C u)(hp:u ≤ M.floorL) (Q:ℕ→ℕ→ℝ)(he:∀ j i,0<Q j i):∃ A:ℕ→ℕ→Record,
    (∀ j i,StepStages j i → M.first≤ i→(A j i).ε ≤ Q j i)∧∀ (θ:Protection Y)(D:Delays θ),∃ U:Delays θ,DelayLe D U∧∀ V:Delays θ,DelayLe U V→Pads Y A Γ K C V:=by
  have ha (j i:ℕ): ∃ A:Record,(StepStages j i→ M.first≤ i→ A.ε ≤ Q j i)∧ ∀ᶠ x in atTop, StepStages j i→ M.first≤ i→Sax Y (fun _ _=> A) j i x Γ K C := by
    by_cases hi:StepStages j i∧M.first ≤ i
    swap; exact ⟨Suite.one,fun a b=>False.elim (hi ⟨a,b⟩), Eventually.of_forall (fun _ a b=>False.elim (hi ⟨a,b⟩))⟩
    let L:= Clockwork.patch Y hi.1 hi.2; obtain ⟨hT,hJ,hK,h'⟩:= hh.crown.setup.braids j i
    obtain ⟨D,hD,hP⟩:= transcribe (Γ j i) _ _ hJ (C j i) (hh.gift j i|>.2.2.1) (hh.gift j i|>.2.2.2) L (by rw [← h']; exact M.has L) (hh.licenses j i hi.1 hi.2 L.L ((hp j).trans (Y.large _).need)) (by rw [hT]; exact M.orders hi.1.1) (by rw [hT]; exact M.powers hi.1.1) (fun S T ht F=> (by rw [hT]; exact hh.bidden j i _ _ ht _)) (Q j i) (he j i)
    refine ⟨D,fun _ _=>hD,hP.mono fun x hx _ _ => ⟨fun P B h p q v b k y c f S T h' ht=> hx P B h p q v ((by rw [hT]; exact b)) k ((by rw [hT]; exact y)) _ _ ?_⟩⟩
    · cases h:S.patch; rw [h] at h' ht; unfold L Clockwork.patch; congr
  choose A ha hA using ha
  refine ⟨A,ha,fun θ T=>?_⟩; obtain ⟨X,-,hX,H⟩:= collect_upper T.betaEntry _ (fun j=> eventually_transitions j _ _ fun i h=> (hA j i).mono fun x hx ht=> (⟨(hx h ht).earn⟩: Sax Y A j i x Γ K C))
  exact ⟨{T with betaEntry:=X},⟨hX,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hv=> H _ _ ((h.beta j).trans hv)⟩
end YM.PhysicalNext.Repeat.Circlet
