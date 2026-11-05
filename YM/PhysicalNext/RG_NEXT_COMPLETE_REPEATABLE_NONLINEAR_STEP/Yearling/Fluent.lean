import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Vested
/-!
 # flat-ancestor compatibility. Use X,Y for pricing on actual Mask. ∆ paid even away from anchor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Yearling
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet March Hues
open Gas Ursell Trees Multiple Alabaster Match Greenbelt Letter
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Geo Ovens
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I U : RG.Rep G f}
    {x μ C v e d D : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W x μ L Q o C T R}
section bind
variable {X : Cash W x μ L Q o C T I} {Y : Cash W x μ L Q o C T U}
variable (s : Alliance H X 1 0) (w : Alliance X Y 1 0) (u : Alliance H Y 1 0) (hs:s.units=Equiv.refl _) (hw:w.units= Equiv.refl _) (hu : u.units=Equiv.refl _)
include hs hw hu
lemma genesis (x : H.ThinP) : w.bearing (s.bearing x)=u.bearing x:= by
  apply Subtype.ext; change w.units (s.units x.val)=u.units x.val; rw [hs,hw,hu]; rfl
lemma trappings (x : H.fragrances) : w.furrow (s.furrow x)=u.furrow x:= by
  rcases x with ⟨i,x⟩
  change Sigma.mk i _=Sigma.mk i _; congr 1; funext j; exact genesis s w u hs hw hu _
lemma buds (x : H.Chapter) : w.editor (s.editor x)=u.editor x:= by
  rcases x with x|x
  · suffices w.honoring (s.honoring x)=u.honoring x from congr_arg Sum.inl this
    apply Subtype.ext; change w.units (s.units x.val)=u.units x.val; rw [hs,hw,hu]; rfl
  exact congr_arg Sum.inr (trappings s w u hs hw hu x)
omit hs hw hu in
lemma scrolls_trans {E F K : Type} (f:E≃F) (g:F≃K) (x : Reps E) : scrolls g (scrolls f x)=scrolls (f.trans g) x:= by
  obtain ⟨b,c⟩:=x
  have hg : (scrolls g (scrolls f ⟨b,c⟩)).fst=(scrolls (f.trans g) ⟨b,c⟩).fst:= by
    change (b.map _).map _= b.map _; rw [Finset.map_map]; rfl
  let l:= (scrolls g (scrolls f ⟨b,c⟩)); let r:= scrolls (f.trans g) ⟨b,c⟩
  refine Sigma.ext hg ?_; apply Function.hfunext _ _
  · rw [hg]
  intro i j hij
  obtain ⟨x,hx⟩:= (tallyVip g (f.finsetCongr b)).surjective (show ↥(g.finsetCongr (f.finsetCongr b)) from i); obtain ⟨x,rfl⟩:= (tallyVip f b).surjective x
  suffices l.snd i = r.snd j from heq_of_eq this
  have he : i=tallyVip g (f.finsetCongr b) (tallyVip f b x):=hx.symm
  have hh : (i: K) = (j: K):= by
    apply eq_of_heq <| ?_
    -- simple
    generalize_proofs; grind
  have hr : j=tallyVip (f.trans g) b x:= Subtype.ext (hh.symm.trans (congr_arg Subtype.val he))
  change l.snd i = r.snd j
  have ht := numbers g (scrolls f ⟨b,c⟩) (show ↥(scrolls f ⟨b,c⟩).1 from tallyVip f b x)
  rw [he,hr]; apply ht.trans; exact (numbers f ⟨b,c⟩ x).trans (numbers (f.trans g) ⟨b,c⟩ x).symm
lemma patrol (x : H.Chainbook) : w.tongs (s.tongs x) =u.tongs x:= by
  change scrolls _ (scrolls _ _)=scrolls _ _; rw [scrolls_trans s.editor w.editor, show s.editor.trans w.editor=u.editor from Equiv.ext (buds s w u hs hw hu)]
end bind

-- ∑ exact potentials on H.p mask..
variable (Θ : Year H j v χ) (p : BudgetPoint) (hp : p.threshold=Pressure.temp x) (hf : p.order ≤ j)
include Θ hp hf
theorem fext : ∃ M : ℝ,0 ≤ M ∧∃ s:ℝ,0 < s∧∀ (I:RG.Rep G f) (a b:ℕ→ℝ) (t:ℝ),Equalized Q.table R I a b t→ t ≤ s →0<t →∀ (H':Cash W x μ L Q o C T I),Year H' j v χ→ ∀ {V:RG.Rep G f} {H₀ : Cash W x μ L Q o C T V} (X:Match.Alliance H₀ H 1 0) (Y: Match.Alliance H₀ H' 1 0), X.units=Equiv.refl _→ Y.units=Equiv.refl _→
    ∃ f:H₀.fragrances→ℝ, SumBudget f M ∧∀ z o,p.supBounds o (Song.perf H₀ z) (Song.sequence H₀ X χ z-Song.sequence H₀ Y χ z) (t*f z) := by
  obtain ⟨K,hK,s,hs,hP⟩:= eventide Θ
  let v:= univ.sup fun a:Site c× Site c=> separation a.1 a.2; let e:ℝ:= 1+ v; have he:1≤e:= le_add_of_nonneg_right (Nat.cast_nonneg _)
  let A:=e^(p.power*j); have hA:0 ≤ A:=pow_nonneg (zero_le_one.trans he) _; refine ⟨A*K,mul_nonneg hA hK,s,hs,?_⟩; intro I a b t Hh ht he' H' Θ' V H₀ X Y hx hy; let Z: Alliance H H' 1 0:= staple Hh.path Hh.reg Hh.forced
  obtain ⟨f',hF,h⟩:= hP I a b t Hh ht he' H' Θ' Z rfl
  refine ⟨fun z=> A*f' (X.furrow z),budget_scale hA (Cost.equiv X.furrow hF),?_⟩; intro z x'
  let Z₀ := Song.perf H₀ z; have hh:= (Song.pocketScore p H₀ X χ Θ.net hp hf p.power le_rfl z).1; have hg:= (Song.pocketScore p H₀ Y χ Θ'.net hp hf p.power le_rfl z).1
  let a:= Song.sequence H₀ X χ z-Song.sequence H₀ Y χ z
  have ha:p.Regular Z₀ a:= CouplingShape.reg_sub hh hg
  refine ⟨mul_nonneg he'.le (mul_nonneg hA (hF.1 _)),fun U hu l hl hd=>?_⟩
  let u' := t*f' (X.furrow z)
  have hx' : a=(fun V=> stream H' χ V (Z.furrow (X.furrow z))-stream H χ V (X.furrow z)):= by rw [trappings X Z Y hx rfl hy]; ext; unfold a Song.sequence; simp; abel
  have hh :Healthy (Pressure.temp x) (Song.perf H (X.furrow z)) U:= by rw [← Song.reconnects H₀ X, ← hp]; exact hu
  have he':= h (X.furrow z) U hh; rw [← hx'] at he'
  apply (costsD ha.1 (show Sailor G p.threshold Θ.year.mark j from (hp.symm ▸ Θ.year.groom)) Θ.year.rate x' u' Θ.year.near he' ?_ he l (hl.trans hf) hd).trans_eq
  swap
  · intro i _; apply add_le_add_right; exact_mod_cast Finset.le_sup (f:=fun a:Site c× Site c=> separation a.1 a.2) (mem_univ (i,x'))
  unfold u' A; ring
end YM.PhysicalNext.Repeat.Yearling
