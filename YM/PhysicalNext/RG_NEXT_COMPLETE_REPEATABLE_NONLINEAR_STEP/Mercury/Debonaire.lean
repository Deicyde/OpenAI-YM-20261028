import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Hearth
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Puff
/-!
 # Burnished.L Coordinate comparison.E soft.Layout.En. no global model.Borrow.He
  Turns budgets reduced wherever PAY.NEED support. Preserve P.R perm.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak Greenbelt WardBin.Lies March
open Gas Ursell Trees Daisy Daisy.Charity
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
    {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {W μ x C' : ℝ} {R : Rep G f}
    {p j n m k : ℕ} {L : Side} {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {d A t C w M N z β r η v b Y' q: ℝ}{C₀ : Libretto G n}
variable (H : Cash W x μ L Q o C T R) (f' : Lotus.Leaf R) (i : ℕ) (hx:f'.turn = .logKey i)
variable (D : Record) (χ κ q' : Chi)(ε:ℝ)(h : Captain H p C' d v t A b r M q m χ) (U: Config G c)
variable (F : Forest S.ratio) (g:S.Choices)
-- aggregate ℓ.Body.Difference at all points with W.E heights; use Halo.Support.T.Temp.
section sense
lemma candles {ι: Type}[Fintype ι] (F:ι→ Config G c→ℝ)(h:∀ i,Germ p (F i) U):
    let g U:=likely (fun p=> F p U); Germ p g U ∧ ∀ l:List (Directions G c),l.length≤p → leftDerivs g l U= likely (fun p=> leftDerivs (F p) l U):=by
  intro g; let a:ℝ:= (Fintype.card ι:ℝ)⁻¹
  have hF: g= a • ∑ i,F i :=by funext p; simp only [g, likely,Pi.smul_apply,Finset.sum_apply]; rfl
  have hg:Germ p (∑ i,F i) U:=by unfold WardBin.Lies.Germ; simp_rw [Finset.sum_apply]; exact ContDiffAt.sum fun i _=> h i
  let L:= a • ContinuousLinearMap.id ℝ ℝ; rw [hF, show a • ∑ i,F i = L ∘ (∑ i,F i) from rfl]
  refine ⟨L.contDiff.contDiffAt.comp _ hg,fun l hl=>?_⟩; rw [Push.Local.left_linear L l (f:=∑ i,F i) (by exact hg) hl,Push.Local.left_sum Finset.univ F U l (fun i _=> (show Push.Local.Chart p _ _ from h i)) hl]; rfl
variable (hQ: Plays C₀ D B R.p P T x) (L':Config G f→ℝ)(h':R.p.Regular (R.activities.reg i).support L') (hy:Healthy B.threshold (plate H i).support U)
    (hL: B.B=radiusB x) (hB:Herd H h.conduit A M m) (hn:B.order≤p) (hp:Q.halo+5 ≤ k)
local notation "Fi"=> Charity.matin f' H (icon H i) χ
local notation "g!" => (fun V:Config G c=>groves H i D κ q' ε V L')
abbrev hore (H : Cash W x μ L Q o C T R)(i:ℕ)(D: Record)(κ q':Chi)(ε:ℝ)(L':Config G _→ℝ)(F:Forest S.ratio)(y:S.Choices) := (mapcase H i F).hymn T (gStep R.beta) q' ε y L' (Baffle.magic D R.p R.beta κ) 1
include hx
lemma grinch : prince f' H (icon H i) ∧ (∀ j,prince f' H j → j=icon H i) :=by
   have hp := Brim.pistil (R:=R) (T:=T) i Q.halo (radiusB x) |>.1
   refine ⟨⟨rfl,by rw [hx]; rfl,hp⟩,fun j ⟨hj,hv,h⟩=> ?_⟩
   rw [single H j hj]; exact congr_arg (chip H) (Subtype.ext (by rw [hx] at hv; exact hv)) --ambig
lemma grinchY (y:Site c): locus f' H y (icon H i)=(plate H i).support:=by unfold locus; rw [if_pos, sites_icon]; have hp:= (grinch H f' i hx).1; exact ⟨none,(by rw [hp.2.1]; simp),hp.2.2⟩
include hQ hn hB
lemma cornice : B.Regular (plate H i).support (Fi):=by
   have hp :(plate H i).site ∈ f'.crest.image S.ratio.parent:=by rw [Leaf.crest,hx]; exact Finset.mem_image.mpr ⟨_,(R.activities.reg _).anchor,rfl⟩
   rw [← grinchY H f' i hx ((plate H i).site)]; exact scops f' H h hB B hp hQ.rehearsed.temp_eq hn _
omit hx hn hB
include hy h'
lemma masts : Germ n (g!) U ∧ ∀ l:List (Directions G c), l.length ≤ n → leftDerivs (g!) l U= likely (fun F: Greenbelt.Reserve S=> likely (fun g:S.Choices=> leftDerivs (hore H i D κ q' ε L' (allot F) g) l U)):=by
   have hg:0 < gStep R.beta:=inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)
   let Y (z:Greenbelt.Reserve S)(V:Config G c) :=likely (fun g=> hore H i D κ q' ε L' (allot z) g V); let f:= R.activities.reg i
   have hx (i':Greenbelt.Reserve S): Germ n (Y i') U ∧ ∀ l:List (Directions G c),l.length ≤ n → leftDerivs (Y i') l U = likely fun g=> leftDerivs (hore H i D κ q' ε L' (allot i') g) l U:=by
      let F:=Greenbelt.allot i'; exact candles U _ fun g=> (Peak.opaqueE q' ε g (mapcase H i F) 1 hQ h' f.anchor (billboard H le_rfl i) hg.le (guard_silent κ hg (mul_pos D.guards R.p.threshold_pos)) hy [] (by simp)).1.germ
   have h:= candles U Y (fun p=> (hx p).1)
   refine ⟨h.1,fun l hl=> ?_⟩; exact (h.2 l hl).trans (congr_arg likely (funext fun z=> (hx z).2 l hl))
--
lemma strums (w:ℝ) (hh:∀ (F : Forest S.ratio) (g:S.Choices),∀ l:List (Directions G c),l.length≤n→(∀ A∈l,B.dirBound (plate H i).site A)→ ‖leftDerivs (hore H i D κ q' ε L' F g) l U‖ ≤ w) (l:List (Directions G c))(hl:l.length ≤ n)(hz:∀ A∈l,B.dirBound (plate H i).site A): ‖leftDerivs (g!) l U‖ ≤ w:=by
   letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side
   have hx{ι:Type}[Fintype ι][Nonempty ι](f:ι→ℝ)(hp:∀ i, ‖f i‖ ≤ w) : ‖likely f‖ ≤ w:= by
      have hv:0< (Fintype.card ι:ℝ):=by positivity
      unfold likely; rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr hv.le)]; refine (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=> hp i))) (inv_nonneg.mpr hv.le)).trans_eq ?_; rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,inv_mul_cancel_left₀ hv.ne']
   rw [(masts H i D κ q' ε U hQ L' h' hy).2 l hl]; exact hx _ fun z=> hx _ fun g=> hh _ g l hl hz

include hx hB hn h hy
lemma silhouette (l:List (Directions G c))(hl:l.length≤ B.order)
   (hs: Brush n z 1 ((Fi-g!) ∘ journey U l.length l.get) 0):‖leftDerivs Fi l U-leftDerivs (g!) l U‖ ≤ z:=by
   let W:= (Fi); let Z:=g!; have hT:B.order=n:=hQ.rehearsed.test; let Hs:=W-Z; have hz : l.length≤n:=hl.trans_eq hT
   have hg : Push.Local.Chart n W U := hT ▸ ((cornice H f' i hx D χ h hQ hB hn).smooth U hy) --edit
   have hp:= (masts H i D κ q' ε U hQ L' h' hy).1
   have hk: Germ n Hs U:= hg.sub hp
   have hb : leftDerivs Hs l U=leftDerivs W l U-leftDerivs Z l U:=by
       let Q:= (-1:ℝ) • ContinuousLinearMap.id ℝ ℝ
       have hW:Hs=W+(Q ∘ Z):=by funext x; change W x-Z x=W x+ -1*Z x; ring
       rw [hW, Push.Local.left_add l hg (show Push.Local.Chart n (Q ∘ Z) U from Q.contDiff.contDiffAt.comp _ hp) hz,Push.Local.left_linear Q l (show Push.Local.Chart n Z U from hp) hz]; change _+ -(1:ℝ)*leftDerivs Z l U= _; ring
   let J:= journey U l.length l.get
   rw [show leftDerivs Fi l U-_=leftDerivs Hs l U from hb.symm, show leftDerivs Hs l U=iteratedFDeriv ℝ l.length (Hs ∘ J) 0 cart from (by simpa only [List.ofFn_get] using Germ.ordered l.get (hk.prod hz))]; have he:= hs.order l.length hz; rw [one_pow, mul_one] at he
   simpa only [Finset.prod_const_one,mul_one] using! ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le he (show ∀ j:Fin l.length, ‖WardBin.Lies.cart j‖≤ (1:ℝ) from fun i=> (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun j => by simp only [WardBin.Lies.cart,Pi.single_apply]; split <;> norm_num))
end sense
end YM.PhysicalNext.Repeat.Mercury
