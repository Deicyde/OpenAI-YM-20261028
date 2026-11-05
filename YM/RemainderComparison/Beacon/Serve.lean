import YM.RemainderComparison.Beacon.Prices
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Docket
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Skills
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment

/-!
# Serving the high-arity and excursion credits in the real history format

At the same output threshold. Exact, BEFORE reset. No scalar/affine projection
assigned a contraction here. The *complement* at every beacon threshold is kept
and not called an analytic perturbative truncation. Earliest K charge from the
integrated library, not from unaligning two regular responses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Beacon
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext.Repeat Height Match Song Refrain Beam
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R I : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ}
    {χ : Chi} {H : Cash W s μ L Q o α T I} {J : Cash W s μ L Q o α T R}
    (X : Alliance H J 1 0) (p : BudgetPoint)
local notation "θ" => Beam.marquee H p
local notation "D" => Height.grow G L s

-- use at any set of log addresses of the *same* chargeable integral
lemma filtered (N : Captain J j C' d v Y A b r B q k χ) (hp : p.threshold = Pressure.temp s)
    (ha : preExponent p ≤ a) (ho : p.order ≤ j) (hP : p.power≤n) (ht : p.B=radiusB s)
    (f : J.fragrances→Prop) (β : ℝ)
    (hg : Ac.Hit (Captain.reachability (H:=J)) (radiusB s) (fun z=>if f z then N.markΦ z n else 0) a β)
    (hf : Cash.Renewed ℓ a δ e J) :
    Collection.Local (θ) p (serve H X χ (f ∘ X.furrow)) (turnFee p*β) (Cash.armK Q L μ s 0 ℓ) := by
  let b (z : Magazine H) : ℝ := z.elim (fun i=> if f (X.furrow i) then N.markΦ (X.furrow i) n else 0) fun _=>0
  have he (i : Magazine H): p.Regular (contents H p i).support (skilled H X χ (f ∘ X.furrow) i) ∧
      p.supBounds (contents H p i).site (contents H p i).support (skilled H X χ (f ∘ X.furrow) i) (b i):= by
    have hh i (h : ¬chosen H (f ∘ X.furrow) i) (ht:b i=0): p.Regular (contents H p i).support (skilled H X χ (f ∘ X.furrow) i) ∧
        p.supBounds (contents H p i).site (contents H p i).support (skilled H X χ (f ∘ X.furrow) i) (b i):= by
      rw [pivot H X χ (f ∘ X.furrow) 0,if_neg h,ht]; refine ⟨CouplingShape.reg_const _,?_⟩
      simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (o:=(contents H p i).site) (X:=(contents H p i).support) 0)
    rcases i with i|i
    swap; · exact hh _ (fun h=>h) rfl
    by_cases he' : f (X.furrow i)
    swap; · exact hh _ he' (show b _=0 from if_neg he')
    let E:=N.markΦ (X.furrow i) n; let t := dashboard H i
    rw [pivot H X χ (f ∘ X.furrow) 0, if_pos (show chosen H (f ∘ X.furrow) (.inl i) from he')]
    have h : b (.inl i)=E:=by unfold b; dsimp only [Sum.elim_inl]; rw [if_pos he']
    rw [h]
    have hk := N.gloryBudget (X.furrow i) p hp ho
    have hz : t.support=perf J (X.furrow i):= (Beam.see H i).trans (reconnects H X i)
    change p.Regular t.support (sequence H X χ i) ∧ p.supBounds t.site t.support (sequence H X χ i) E
    rw [hz]; refine ⟨CouplingShape.reg_scale _ hk.2.1,?_⟩
    have hv := CouplingShape.sup_scale (-1) (hk.2.2 n hP t.site (show t.site∈ perf J (X.furrow i) from hz ▸ t.anchor))
    rw [abs_neg,abs_one,one_mul] at hv; exact hv
  have hy : Quotes.early p (contents H p) b β := by
    intro x; nth_rw 1 [← add_zero β]
    refine Cost.sum ?_ (by simp [b,SumBudget] -- edit
        )
    have hk:= Cost.equiv X.furrow (hg x)
    refine budget_mono hk (fun z=>?_) fun z=> ?_
    · dsimp only; split
      · exact mul_nonneg (he _).2.1 (Real.exp_pos _).le
      exact le_rfl
    dsimp only; split
    next hx=>
      let t:= dashboard H z
      have hl : t.support=perf J (X.furrow z):= (Beam.see H z).trans (reconnects H X z)
      have hb : x∈ Captain.reachability (X.furrow z):= (show x∈ perf J (X.furrow z) from hx ▸ hl ▸ t.anchor)
      rw [if_pos hb,ht,show (contents H p (Sum.inl z)).support=perf J (X.furrow z) from hl]
      exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))) (he _).2.1
    exact hk.1 z
  obtain ⟨hk,hq⟩:= spiral _ _ _ (fun i=> (he i).1) (fun i=> (he i).2) hy
  exact ⟨fun i=>(hk (pennant H i)).1, qualified p H X χ _ _ hp, fun s t=> moves H p χ X s t _,⟨_,fun i=> (hk (pennant H i)).2, fun o=> Cost.equiv (pennant H) (hq o)⟩, chargesOut p H X χ hf ht (show p.supportExponent+1 ≤ a by unfold preExponent at ha; linarith)⟩

lemma combine (f : H.fragrances → Prop) (χ : Chi) (γ : ℝ) (i : ℕ) (A : Config G c) :
    ((θ).read (serve H X χ f)).regularOccurrence p i A+
      ((θ).read (sleeping H X χ f γ)).regularOccurrence p i A=((θ).read (plusone H X χ γ)).regularOccurrence p i A := by
  let P:=(θ).reg i
  let y g:=masked p.threshold P.support (Collection.Source.logRead g i) A
  obtain ⟨he,hk⟩:=bolted H X χ f γ i
  have h:masked p.threshold P.support (0:Config G _ → ℝ) A=0:= by by_cases h:Healthy p.threshold P.support A; exact masked_eq _ _ _ _ h; exact masked_ne _ _ _ _ h
  change y (serve H X χ f) + y (Height.sleeping H X χ f γ)= y (plusone H X χ γ); unfold y; rw [he,hk]; split <;> simp only [h,zero_add,add_zero]

lemma reunite (f : H.fragrances → Prop) (χ : Chi) (γ τ β : ℝ) {W V A Z : ℝ} -- W shadow ok?
    (h : Collection.Local (θ) p (serve H X χ f) V A)
    (ht : Collection.Local (posting p H) p (plusone H X χ γ) Z W) (U : Config G c) :
    (Summable fun i=> ((θ).read (sleeping H X χ f γ)).regularOccurrence p i U) ∧
    earlyValue (posting p H) T.down T.low p (plusone H X χ γ) β τ γ U =
      Real.exp (-(((θ).read (serve H X χ f)).additive p U)) *
        earlyValue (θ) T.down T.low p (sleeping H X χ f γ) β τ γ U := by
  let t:=plusone H X χ γ; let d:= serve H X χ f; let b:= sleeping H X χ f γ
  have he := Roof.Embrasure.series _ _ h U
  have hs : Summable fun i=> ((θ).read t).regularOccurrence p i U:=
    (Roof.Embrasure.series _ _ ht U).congr fun i=> by
      change masked _ (Song.posting _ H|>.reg i).support _ _=masked _ (Beam.marquee _ _|>.reg i).support _ _; rw [Beam.rewrite_rule]; rfl
  have hu (i) : ((θ).read t).regularOccurrence p i U=((θ).read d).regularOccurrence p i U+
      ((θ).read b).regularOccurrence p i U:=(combine X p f χ γ i U).symm
  have hb := (hs.sub he).congr (g:=fun i=> ((θ).read b).regularOccurrence p i U) (fun i=> by rw [hu]; abel)
  refine ⟨hb,?_⟩
  have hh : ((θ).read t).additive p U=((θ).read d).additive p U+((θ).read b).additive p U:=
    (tsum_congr hu).trans (he.tsum_add hb)
  have hR := Beam.travels H p t β τ γ U
  rw [← hR]; unfold earlyValue Rep.eval Rep.exponent
  dsimp only [Collection.frozen]; rw [hh,show ((θ).read (sleeping H X χ f γ)).gas= ((θ).read t).gas from rfl]; unfold d b; rw [sub_add_eq_sub_sub_swap,sub_eq_add_neg (b:=((θ).read _).additive p U),Real.exp_add]; ring
end YM.RemainderComparison.Beacon
