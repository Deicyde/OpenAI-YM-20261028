import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Addresses
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Print
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Lighting


/-!
# Vital extensions to the matched Rank chart

Apply authorization (sector allocation flags, regardless of which
eligibility is tested on W) to roots in every chart, all indicated inputs.
Obtain Borel extensions from matches, for both gazed field reads (joint)
and viewer integrals. Kept to justify e.g. measurability of actual
source-value integrals in original V. No locality claims from these
extensions, prove on the stencil of Beamline rather.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Marker Value
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    AnalyticBridge.GaussianFieldAlignment.Locations SectorNext.Vacuum
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
    AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.RelativeLogdet 
    Dictionary Dictionary.Geo Dictionary.Print AnalyticBridge.Annulus Schur LocalJet
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Teller G}
    {X X' : Support c} {x β : ℝ} {U V : Config G c} {A B : Stores S}
    {F : Forest S.ratio} {T : Tube G S} {k k' : S.Choices}

def Positioned (x : ℝ) (A : Stores S) (U : Config G c) := A.flags=RG.flags (temp x) U

lemma Positioned.turn (h : Positioned x A U) (t : Site c→ G.El) : Positioned x A (Lattice.gauge t U):=by unfold Positioned; rw [gauge_flags]; exact h

/-- Prices available before markers. No issue by relocation to a new family.
Here across L paid for the SAME P width. -/
structure Boosted (T : Tube G S) (P : Teller G) (x : ℝ) : Prop where
  funded : P.Funds S T
  ready : PatchReads.Ready T x
  produced : Map.Aperture S T x
  license (A : Stores S) F (V : Config G c) : Positioned x A V → ∃ C, Authorized A V F x C
  fogged A F V k : Positioned x A V → (palette T A F k x V .endpoint).PosDef
  enough A F (V : Config G c) k : Positioned x A V → ∃ b, 0<b ∧ Gapped (Rows.gram T x V k (shots S x) A F) b

lemma booster (Q : Patch) (P : Teller G) (hp : Q.Branches P.bind G) :
    ∀ᶠ x : ℝ in atTop,∀ {c f : Side} (S : StepData c f) (T : Tube G S),
    S.patch=Q → 100*(1+radiusB x) ≤ c.val → P.Funds S T → Boosted T P x := by
  obtain ⟨v,K,η,b,E,-,-,hη,-,-,H⟩:= opaqueCost G Q P hp
  obtain ⟨C,δ,hC,hδ,Hd⟩ := earned Q P.bind G hp
  have hm : ∀ᶠ x : ℝ in atTop,permit Q*temp x≤δ := by
    filter_upwards [Work.E01.fiery_le G (1:Side) (permit Q),
      (Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx h; simpa [fiery,betaF] using hx.trans h
  filter_upwards [H, hm,Map.aperture P Q, PatchReads.reserve P Q, small_span Q,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot Q+1)] with x hx he hp hC hA hz
  intro c f S T h hF hT
  refine ⟨hT,hC S T h hF hT,hp S T h hT,fun A F V hv=> ?_,fun A F V k hv=> ?_,fun A F V k hv=> ?_⟩
  · exact ⟨C,Hd S h hT.knobs F A V x hv hA (by omega) (by omega) he⟩
  · rw [← Q_endpoint]; exact (hx S T h hF hT A F k V hv).2.2.2.2
  exact ⟨_,hη,(hx S T h hF hT A F k V hv).2.1⟩

lemma recording (x : ℝ) (A : Stores S) (F : Forest S.ratio) : Measurable (Print.backdrop x A F (G:=G)) := by
  unfold Print.backdrop; apply Measurable.prodMk
  · refine measurable_pi_lambda _ fun i=> ?_; split
    next he => split
               next h => exact (measurable_pi_apply _).comp measurable_fst
               exact measurable_const
    exact measurable_const
  refine measurable_pi_lambda _ fun i=> ?_
  unfold fresh
  split
  next he => split
             next hk => exact (measurable_pi_apply _).comp (tape.measurable.comp measurable_snd)
             exact measurable_const
  exact measurable_const
lemma gazed_tag (ht : Boosted T P x) (L : Lantern G S) (β : ℝ) (A : Stores S) (k : Streak L.park) :
    ∃ g : Config G c × RoomView A x k.wood G → Config G f, Measurable g ∧
      ∀ (V), Positioned x A V → ∀ z, g (V,z) = gazed T k.tag L.χ V x β L.hood z := by
  let H (p : Config G c × RoomView A x k.wood G) := (p.1,Print.backdrop x A k.wood p.2)
  refine ⟨_,(Print.printed_meas T x L.χ _ (coupling β) ht.funded k.tag A k.wood L.heat L.bright).comp
       (show Measurable H from measurable_fst.prodMk ((recording x A k.wood).comp measurable_snd)), fun V hv z=> ?_⟩
  obtain ⟨s, hs⟩:= ht.license A k.wood V hv; obtain ⟨_,hb,hQ⟩:= ht.enough A k.wood V k.tag hv
  have he := Print.painted T x L.χ L.hood (coupling β) k.tag V ht.produced hs hb hQ (Print.backdrop x A k.wood z)
  dsimp only at he; rw [rollback,mean_endpoint] at he; exact he
lemma tag_table (ht : Boosted T P x) (F : Forest S.ratio) (A : Stores S) (k : S.Choices) :
    ∃ B : Config G c → Gaussian.Table (In (G:=G) x A F), (∀ i j,Measurable fun V=> B V i j) ∧
      ∀ (V), Positioned x A V → B V=palette T A F k x V .endpoint := by
  let E (V : Config G c) (i j : In (G:=G) x A F) := Wires.cloudX T x k V A F (Wires.active x A F i) (Wires.active x A F j)
  refine ⟨E, fun i j=> Wires.cloudX_meas T _ _ _ _ ht.produced.branched _ _, fun V hV=> ?_⟩
  obtain ⟨s,hs⟩:=ht.license A F V hV; obtain ⟨b,hb,hB⟩:=ht.enough A F V k hV
  apply Matrix.ext; intro i j
  rw [← Q_endpoint]; unfold E
  rw [Wires.cloudX_exact T _ ht.produced _ _ _ _ hs hb hB]
  simp only [Physical.CFull,Matrix.submatrix_apply,Wires.active,Wires.finger, Equiv.symm_apply_apply]
  rfl

-- Use junk value off authorization for constructing `local` amounts
-- at some x. Across Axis, integrate only when matched (see Lens below).
def ShellView {E : Type*} [MeasurableSpace E] (g : Config G c→ RoomView A x F G → E) :=
    ∃ p : Config G c × RoomView A x F G→ E,Measurable p ∧ ∀ V,Positioned x A V→ ∀ a,g V a=p (V,a)
lemma ShellView.atLens {E : Type*} [MeasurableSpace E] {g : Config G c→ RoomView A x F G → E} (hg : ShellView g) (hv : Positioned x A U) : Measurable (g U) := by
  obtain ⟨p,hh,H⟩ := hg; rw [funext (H U hv)]
  exact hh.comp (measurable_const.prodMk measurable_id)
private lemma joint_price {I : Type} [Fintype I] [DecidableEq I] {α : Type*} [MeasurableSpace α] (w : α→Gaussian.Table I)
    (v : α→ Gaussian.Vec I) (h : ∀ i j, Measurable fun a=>w a i j) (hp : Measurable v) : Measurable fun a=> Gaussian.ratio (w a) (v a) := by
  have he i j : Measurable fun a=>(w a)⁻¹ i j := Numerals.Watched.inverse h i j
  have ht i : Measurable fun a=>v a i := (measurable_pi_apply i).comp hp
  have hx : Measurable fun a=> (w a).det := by simp_rw [Matrix.det_apply]; fun_prop
  have hm : Measurable fun a=> (w a)⁻¹ *ᵥ v a:= by
    refine measurable_pi_lambda _ fun i=>Finset.measurable_fun_sum _ fun j _=> (he i j).mul (ht j)
  exact (measurable_const.mul hx.sqrt).inv.mul (((Finset.measurable_fun_sum _ fun i _=>
    (ht i).mul ((measurable_pi_apply i).comp hm)).neg.div_const _).exp)
lemma shell_beacons {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ht : Boosted T P x) {g : Config G c→ RoomView A x F G→ E} (hg : ShellView g) (k : S.Choices) :
    ∃ p : Config G c→ E,Measurable p ∧ ∀ V,Positioned x A V → (∫ a,g V a ∂viewer T A x F k V)=p V := by
  obtain ⟨w,hh,hV⟩:=tag_table ht F A k; obtain ⟨p,hp,H⟩:=hg
  let q (u : Config G c × RoomView A x F G):= Gaussian.ratio (w u.1) u.2.2
  have hq : Measurable q:=joint_price _ _ (fun i j=>(hh i j).comp measurable_fst) (measurable_snd.comp measurable_snd)
  let M := piHaar G (Frozen A x F); let ν := Gaussian.Vec (In x A F (G:=G)); let μ : Measure ν:= volume
  haveI : SigmaFinite μ:= by unfold μ; infer_instance
  refine ⟨_, ((hq.smul hp).stronglyMeasurable.integral_prod_right' (ν:=M.prod μ)).measurable, fun V hv=>?_⟩
  change _=∫ y, q (V,y) • p (V,y) ∂M.prod μ
  unfold viewer; rw [← hV V hv]
  let v := w V
  have hh : (w V).PosDef:= hV V hv|>.symm ▸ ht.fogged A F V k hv
  let r:= Gaussian.ratio v
  have hm:= (Gaussian.measurable_ratio v).ennreal_ofReal
  rw [Gaussian.cloud_formula hh, prod_withDensity_right hm, integral_withDensity_eq_integral_toReal_smul]
  · change v.PosDef at hh
    simp_rw [ENNReal.toReal_ofReal (Gaussian.ratio_pos hh _).le,H V hv]; rfl
  exact hm.comp measurable_snd; exact Eventually.of_forall (fun x=> ENNReal.ofReal_lt_top)
end YM.PhysicalNext.InteractingRank
