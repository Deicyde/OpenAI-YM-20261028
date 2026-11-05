import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Oriole
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Yearling.Adorn

/-! # One finite Ledger cutoff earned inside the Curve by parameter continuity.
  `tower` books emitted with all K; `petal` foreground record; need one more reattachment.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p

def bouquet (I:Cash W p a L₀ X o U T R') (k:ℕ): Finset (Magazine I):= disjSum ((Meadow.calendar I k).map (booths I)) ((univ ×ˢ (ripened T.down B k)).map (rollers c).toEmbedding)
lemma notKept (z:Magazine I) (h:z ∈ bouquet I m) : ¬keep I z:= by
  unfold bouquet at h; rcases z with z|z
  · obtain ⟨i,hi,hz⟩:= mem_map.mp (inl_mem_disjSum.mp h); exact fun he=> he ⟨i,hz⟩
  obtain ⟨⟨s,i⟩,hi,hz⟩:= mem_map.mp (inr_mem_disjSum.mp h); have ht : arc T.down z≤ B:= by rw [← (show legs s i=z from hz),arc_receipt]; exact (mem_filter.mp (mem_product.mp hi).2).2
  exact fun h=> not_lt.mpr ht h
lemma unfurls (z:Magazine I) (hp:¬keep I z): ∀ᶠ m in atTop,z∈bouquet I m:= by
  rcases z with z|z
  · change ¬z∉_ at hp; obtain ⟨w,rfl⟩: z ∈ Set.range (booths I):= Classical.byContradiction hp; filter_upwards [retires w] with m hm; exact inl_mem_disjSum.mpr (mem_map_of_mem _ hm)
  obtain ⟨⟨s,i⟩,hv⟩:= (rollers c).surjective z
  have h: Meadow.melody T.down i≤ B:= by rw [← arc_receipt T.down s i, show legs s i=z from hv]; exact le_of_not_gt hp
  filter_upwards [burgeoning T.down B i h] with m hm; exact inr_mem_disjSum.mpr (mem_map.mpr ⟨(s,i),mem_product.mpr ⟨mem_univ _,hm⟩,hv⟩)

def debris (I:Cash W p a L₀ X o U T R') (k:ℕ) (w:ℕ) := ¬keep I (Song.pennant I w).2∧ (Song.pennant I w).2∉ bouquet I k
lemma dissolved (I:Cash W p a L₀ X o U T R') (w:ℕ): ∀ᶠ k in atTop,¬debris I k w := by
  by_cases h:keep I (Song.pennant I w).2
  · filter_upwards with k using (fun hx=> hx.1 h)
  exact (unfurls _ h).mono fun k h H=> H.2 h


section curve
variable {P : Listing G c} (X : BudgetPoint) (A : ℕ→ℕ→Prop)
   {h : ℝ→ Collection.Source G c} {T : Set ℝ} (hv : Compared P X h T)
   (hp : ∀ x∈T,∀ i,X.Regular (P.reg i).support ((h x).logRead i))
lemma limits {k} (a : ℝ) (ha : ∃ f:ℕ→ℝ, Summable f ∧∀ i,X.supBounds ((P.reg i).site) (P.reg i).support ((h a).logRead i) (f i)) (he:∀ i,∀ᶠ k in atTop,¬ A k i) (hk:0<k):
    ∀ᶠ m in atTop,∃ f:ℕ→ℝ, (∀ i,X.supBounds (P.reg i).site (P.reg i).support (if A m i then (h a).logRead i else 0) (f i)) ∧ Quotes.early X P.reg f k:= by
  obtain ⟨f,hf,hP⟩:=ha; let Y m i:= if A m i then f i else 0
  let g i:= f i * Real.exp (preExponent X*coverNumber X.B (P.reg i).support); let u m i:= if A m i then g i else 0
  have h i : 0 ≤ g i:= mul_nonneg (hP i).1 (Real.exp_nonneg _)
  have he' : Summable g:= by
    have hz:= BetaTransport.summable_mass (headline X) (fun i=> (hP i).1) hf (X:=fun i=>(P.reg i).support) -- args
    unfold g; simp_rw [mul_comm (f _)]; exact hz
  have hu m : Summable (u m):= he'.of_nonneg_of_le (fun i=> by unfold u; split; exact h _; rfl) (fun i=> by unfold u; split; rfl; exact h _)
  have hv i : Tendsto (fun m=> u m i) atTop (𝓝 0):= tendsto_const_nhds.congr' ((he i).mono fun v hv=> (if_neg hv).symm)
  have hz : Tendsto (fun m=> ∑' i,u m i) atTop (𝓝 0):= by
    have hh:= tendsto_tsum_of_dominated_convergence he' hv (Eventually.of_forall (fun m i=> (show ‖u m i‖≤ g i from (by
      unfold u; split
      · exact (Real.norm_of_nonneg (h _)).le
      rw [norm_zero]; exact h _))))
    rwa [tsum_zero] at hh
  filter_upwards [hz.eventually_le_const hk] with m hm; refine ⟨Y m,fun i=> ?_,?_⟩
  · unfold Y; split; exact hP i
    exact VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)
  intro o; refine budget_mono (f:=u m) ⟨(fun i=> by unfold u; split; exact h _; rfl),hu m,hm⟩ (fun i=> ?_) (fun i=>?_)
  · split; next=> apply mul_nonneg; unfold Y; split; exact (hP _).1; rfl; exact Real.exp_nonneg _
    exact le_rfl
  dsimp only; split
  · unfold Y u; split; rfl; rw [zero_mul]
  unfold u; split; exact h _; exact le_rfl

include hv hp
-- use `.early` vs .mass d may cause +3 not dominated. volume finite Scale e^3#; ok.
theorem exceeded {x : ℝ} (hX : x∈T) (hy : ∃ f:ℕ→ℝ,Summable f ∧∀ i,X.supBounds (P.reg i).site (P.reg i).support ((h x).logRead i) (f i)) (hm:∀ i,∀ᶠ k in atTop,¬ A k i) (t:ℝ) (ht:0<t):
    ∃ Z ∈ 𝓝[T] x,∀ᶠ k in atTop,∀ y∈Z,Meadow.Budget X P.reg (fun i=> if A k i then (h y).logRead i else 0) t := by
  obtain ⟨B₀,hB,H⟩:= Yearling.bounty c (headline X)
  have hb := zero_lt_one.trans_le hB; let z:= t/ (2*B₀); have hz:0<z:= div_pos ht (mul_pos (by norm_num) hb)
  let Z:= { y | y∈T∧deviation X (P.read (h x)) (P.read (h y)) z }
  refine ⟨Z,inter_mem self_mem_nhdsWithin (hv.deviation_at hX hz),?_⟩
  filter_upwards [limits X A x hy hm (half_pos ht)] with m he y hy
  obtain ⟨f,hf,hK⟩:=he; obtain ⟨hz,c,b,hc,hk,hC,hD⟩:=hy
  let g i:= if A m i then (h y).logRead i else 0; have hV:= H _ (fun i=>(P.reg i).support) _ z (BetaTransport.budget_unweighted (fun i=> (hc i).1) hC)
  refine ⟨f+c,fun x=> ?_,fun i=> ?_⟩
  · let a i:= if (P.reg i).site=x then c i*Real.exp (preExponent X*coverNumber X.B (P.reg i).support) else 0
    have ha: SumBudget a (t/2):= by
      apply budget_loosen (budget_mono hV _ _) _
      · intro i; unfold a; split; exact mul_nonneg (hc i|>.1) (Real.exp_nonneg _); rfl
      · intro i; unfold a; split; exact le_of_eq (mul_comm ..); exact hV.1 _
      unfold z; apply le_of_eq; field_simp
    have h' := budget_plus (hK x) ha; rw [add_halves] at h'; convert h' using 2 with i; unfold a; dsimp only [Pi.add_apply]; split <;> ring
  dsimp only; split
  next he=>
    have hE:= hf i; rw [if_pos he] at hE; refine ⟨hp y hz i,add_nonneg hE.1 (hc i).1, fun U h l hl hd=> ?_⟩
    have hh (u v:ℝ): ‖v‖≤‖u‖+‖u-v‖:=by nth_rw 1 [← sub_sub_cancel u v]; exact norm_sub_le .. -- edit
    apply (hh _ _).trans (add_le_add (hE.2 U h l hl hd) ((hc i).2 U h l hl hd))
  next hz => have hE:= hf i; rw [if_neg hz] at hE; exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le hE (le_add_of_nonneg_right (hc i).1)⟩ -- rw
end curve
end YM.PhysicalNext.Repeat.Meadow
