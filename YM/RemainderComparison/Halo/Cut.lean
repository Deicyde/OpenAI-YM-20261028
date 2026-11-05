import YM.RemainderComparison.Gear.Bones
import YM.RemainderComparison.Cascade.Environment
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Opacity

/-!
 # Halo. No expansion of the inherited E components.

 `Presents` on an actual indexed E subfamily. Requiring zero
 weight on excluded rows is canonical; obtaining `w` from
 `boundE` or stronger per-kernel payment using slice. No claim that
 Ebound pins expand at same clock.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Raw Itinerary Opacity Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}

structure Presents (R:Rep G f) (E : Set ℕ) (w:ℕ→ℝ) (δ:ℝ): Prop where
    marked (i:ℕ)(hi:i∈E) : R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (w i)
    missed i : i∉E → w i=0
    backed : Footprint.Anchored (fun i=> (R.activities.reg i).site) w (regularExtra R) R.p.supportExponent δ
namespace Presents
variable {E : Set ℕ}{w:ℕ→ℝ} {δ ε:ℝ}(h : Presents R E w δ)
include h
lemma pay i : 0≤w i:=by by_cases he:i∈E; exact (h.marked i he).1; rw [h.missed i he]
lemma roof (i:ℕ) : w i ≤ δ:=by
  let p:=(R.activities.reg i); obtain hh:= budget_single (h.backed p.site) i
  change (if p.site=p.site then _ else _)≤ _ at hh
  refine (R.p.loMass (p.support) (w i) (h.pay i)).trans ?_; rw [BudgetPoint.mass, mul_comm]; simpa only [ite_true] using! hh
lemma positive : 0≤ δ:= (h.pay 0).trans (h.roof 0)
lemma value {i:ℕ} (hi:i∈E) (U: Config G f) : |R.activities.regularOccurrence R.p i U| ≤ w i := by
  unfold Activities.regularOccurrence
  by_cases he:Healthy R.p.threshold (R.activities.reg i).support U
  · rw [masked_eq _ _ _ _ he]; exact (h.marked i hi).2 _ he [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ he,abs_zero]; exact h.pay i
omit h
lemma wages (R:Rep G f) (hh:R.activities.EBound R.p δ) (E:Set ℕ) : ∃ w:ℕ→ℝ,Presents R E w δ:=by
  obtain ⟨w,h,h'⟩:=hh
  refine ⟨fun i=> if i∈E then w i else 0,fun i hi=>?_ ,fun i hi=>if_neg hi,?_⟩
  · rw [if_pos hi]; exact h i
  intro x; refine budget_mono (h' x) (fun i=>?_) (fun i=>?_)
  · dsimp only; split_ifs; exact mul_nonneg (h i).1 (Real.exp_pos _).le; simp; rfl
  dsimp only; split_ifs with hv hh; next =>rw [BudgetPoint.mass, mul_comm]; rfl
  next=>rw [zero_mul]; exact mul_nonneg (Real.exp_pos _).le (h i).1
  next=>rfl

lemma zeroG (R:Rep G f) : Presents R ∅ 0 0 :=by
  refine ⟨fun i hi=>by simp at hi,fun i _=>rfl,fun x=>?_⟩
  simp [SumBudget]
end Presents

variable {E : Set ℕ}{w:ℕ→ℝ} {δ:ℝ}
def cost (L : Side) (Q:ConnectedActivityE6.Target G P)(x:ℝ):= Footprint.payment (L.val^4) (Footprint.extentCost (Q.halo+5) (radiusB x)) 0 Q.ε 1 1 Q.relative (Footprint.preCost (Q.halo+5))
lemma cost_p (G:Gauge)(P:Teller G)(Q:ConnectedActivityE6.Target G P)(L:Side) : Reserve G L (cost L Q):=by
  let b:=fun x:ℝ=> Footprint.extentCost (Q.halo+5) (radiusB x)
  have he : Reserve G L (fun x=>(b x:ℝ)):=by simpa only [add_zero] using! Reserve.lag (G:=G) (L:=L) (Q.halo+5+20) 0
  have hh : Reserve G L (fun x=> (Footprint.spread (L.val^4) (b x):ℝ)):=by
    simp only [Footprint.spread,Nat.cast_mul]; exact (Reserve.const _).mul (Reserve.ball _ he)
  unfold cost Footprint.payment Footprint.degreeIncome
  exact ((((Reserve.const _).mul hh).mul (Reserve.const _)).mul (Reserve.const _))
lemma halos (P : Teller G) (Q:ConnectedActivityE6.Target G P):
    ∃ n : ℕ, ∀ L : Side, n≤L.val → ∀ᶠ x : ℝ in atTop, ∀ {c f: Side} (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L → Intake P T x R →
    ∀ (E : Set ℕ) (w:ℕ→ℝ)(δ:ℝ), Presents R E w δ→ Sales (radiusB x) Q.relative Q.ε (regularFoot S.ratio Q.halo (radiusB x) R)
       w (regularExtra R) (|cost L Q x| *δ):=by
  have hr:0 ≤ Q.relative:=by unfold Target.relative; linarith [Q.usable,Q.pos,Q.bound]
  have he:=Q.usable; have hv:= Q.grants.1
  obtain ⟨n,H⟩:= Fees.exponent (Q.halo+5) he hr (show 2*Q.ε<P.top.supportExponent-2*Q.ε by linarith)
  refine ⟨n,fun L hL=>?_⟩; filter_upwards [Fees.horizons G L Q.halo he hr (show 2*Q.ε<P.top.supportExponent by linarith)] with x hh c f S T R ht h E w δ hW
  let p:= S.ratio; let B:=radiusB x; have hP' : p.count=L:= ht
  let Y i:=(R.activities.reg i).support; let X:=R.p
  apply Sales.raise (Sales.anchored_sale (z := w) (l:=Q.halo+5) (M:=R.p.B) S.ratio (fun i=>(R.activities.reg i).site) (Y:=Y)
     (fun i=> (R.activities.reg i).anchor) (h.exponent.symm ▸ hW.backed) hW.pay
     (X:=regularFoot p Q.halo B R) (fun i=> inspected_price p Q.halo _ (Y i) hh.1) hh.1
     (by rw [h.sizes,ht]; exact hh.2.1) (H c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one (fun i=>⟨hW.pay _,by simp⟩))
  apply le_trans _ (mul_le_mul_of_nonneg_right (le_abs_self _) hW.positive)
  unfold cost; rw [show S.ratio.count=L from hP']; unfold B Footprint.payment degreeIncome; apply le_of_eq; ring

def inherited (S:StepData c f) (E:Set ℕ) (i : Head S):Prop:= ∃ j∈E,i=Opacity.key S j
def weather (S:StepData c f)(E:Set ℕ)(w: ℕ→ℝ)(f':Head S→ℝ):Head S→ℝ :=fun i=> if h:inherited S E i then w h.choose else f' i
lemma weather_at {E:Set ℕ}{w: ℕ→ℝ} (f':Head S→ℝ) {i:ℕ} (hi:i∈E) : weather S E w f' (Opacity.key S i)=w i := by
  unfold weather; rw [dif_pos (show inherited S E _ from ⟨i,hi,rfl⟩)]
  let h:inherited S E (Opacity.key S i):= ⟨i,hi,rfl⟩; suffices i=h.choose by exact congr_arg w this.symm
  simpa only [Opacity.key,Sum.inr.injEq,Sum.inl.injEq] using h.choose_spec.2
lemma snow_pos {g : Head S→ℝ} (hh:∀ i,g i≥0)(hs:∀ i∈E,0≤w i) (i) : 0≤weather S E w g i:=by
  unfold weather; split; next h=>exact hs _ h.choose_spec.1
  next h=>exact hh i
-- use charge at the key without boxing E in fixed headed Norm Smooth region. Does not need cluster Healthy here.
lemma pending (G:Gauge) (j:ℕ): ∃ B, 0≤B ∧ ∀ (c f L:Side)(S:StepData c f)(T:Tube G S)(F:Forest S.ratio)(P:Teller G)
   (W x μ C:ℝ)(R:Rep G f)(Q:ConnectedActivityE6.Target G P)(o: ConnectedActivityE6.Target.Order G W) (_H:Cash W x μ L Q o C T R) (X: Coat T F)(E:Set ℕ)(w:ℕ→ℝ)(δ:ℝ), Presents R E w δ→ δ≤1→ X.x=x → ∀ (E':Type)[NormedAddCommGroup E'][NormedSpace ℝ E'](f':E'→ Directions G f) (V : E'→ Config G c)(U : Config G f) (g:E'→Air f G) (y:E') (p:ℝ),0≤p→
    (∀ Y Z:Support c,Y⊆ Z → Brush j 1 (p*coverNumber X.B Z) (fun t=> X.enforce (2*o.a) (f' t) (X.plaza Y)) y) →
      ∀ i∈E, ∀ k:Finset ℕ, let h:=Opacity.key S i
        Brush j (B*w i) (p*spanW T R X.B Q.halo h) (fun t=> Polar.ember (vary X (V t)) o.a R W Q.table (f' t) U (g t) k Q.halo h) y:=by
  obtain ⟨B,hB,hp⟩:= Brush.expands j
  refine ⟨B,hB,?_⟩
  intro c f L S T F P W x μ C R Q o H X E w δ h hd ht E' _ _ f' V U g y p hh he i hi k d
  let r:=(-R.activities.regularOccurrence R.p i U); have hb: ‖r‖ ≤w i:=by unfold r; rw [norm_neg]; exact h.value hi U
  have hF: Raw.space T 0 X.B R (.inl i)⊆H.supportP d:=by
    change Raw.regularFoot S.ratio _ _ R i ⊆ Raw.regularFoot S.ratio _ _ R i; apply Corona.halo_mono _ (Finset.Subset.refl _); simp
  have hM:= he _ _ hF
  -- constant doesn't consume p
  let M:= X.plaza (Raw.space T 0 X.B R (.inl i))
  have hx: Brush j (w i) (p*coverNumber X.B (H.supportP d)) (fun t=> r*X.enforce (2*o.a) (f' t) M) y := by
    have hx:= (((Brush.certified (x:=y) (k:=j) (d:=0) (le_refl 0) r).climb hb le_rfl).paints hM); rw [mul_one,zero_add] at hx; exact hx
  refine (hp E' y _ _ _ hx ((h.roof i).trans hd)).climb le_rfl (mul_le_mul_of_nonneg_left ?_ hh)
  change ((coverNumber X.B (Raw.regularFoot S.ratio Q.halo (radiusB x) R i)):ℝ)≤1+(_ + _)
  rw [← show X.B=radiusB x from congr_arg radiusB ht]; exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one)
end YM.RemainderComparison.Halo
