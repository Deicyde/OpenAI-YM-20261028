import YM.RG08.Door.Snow
/-!
# Gauge on summit balanced jets and normalization through test.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Matrix Summit
open PertExtension.Series.Tested PertExtension.Series.Radial Scores
open scoped BigOperators Topology Real Classical ContDiff
variable {X:Chain}{G:Gauge}{E e r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}
open Wings
section convergence
variable {I J α β : Type} {X:ℕ→BoardU D R G}{U:BoardU D R G}{A:Shale (Loc G 1) r}{p:Side}
variable [NormedAddCommGroup β] {Y₁ Y₂ : I→Rooted β α r}{V:ℕ→Rooted β α r}{F: Rooted β α r} {y δ g:I→ℝ}{v:ℕ→ℝ}
lemma Twill.move (b:J→I) (h:Twill y δ Y₁ Y₂ g):Twill (y∘b) (δ∘b) (fun i=> Y₁ (b i)) (fun i=>Y₂ (b i)) (g∘b):= ⟨h.one.move b,h.two.move b,h.goes.move b⟩
lemma Twill.stint (h:Twill (fun _=>C) v V (fun _=> F) (fun _=>w))(hv : Tendsto v atTop (𝓝 0))(he : 0≤v) (hp : 0 ≤ w) : Hurled V F := by
    have hX:= h.soften (v:=0) (fun _=> hp)
    refine ⟨hX.two.solo le_rfl 0,?_⟩; obtain ⟨A,⟨B,k,hB,H⟩,HX⟩:=hX.goes.serves; exact ⟨_,(show Tendsto (fun j=> B*C^k *v j) atTop (𝓝 0) by simpa using hv.const_mul (B*C^k)),fun i=> Ink.raise (HX i) (mul_le_mul_of_nonneg_right (H i|>.2) (he i))⟩
lemma hurled_t (h:Hurled V F) : Tendsto V atTop (𝓝 F) := by
    obtain ⟨f,he,H⟩:=h.moment.thus; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_iff_norm_sub_tendsto_zero.mpr; exact squeeze_zero (fun i=>norm_nonneg _) (fun j=> (le_mul_of_one_le_left (norm_nonneg _) (ling_one le_rfl i)).trans (budget_single (H j) i)) he
lemma tid_leases (h:Hurled V F)(hp:∀ i,Tidy (V i)): Tidy F := ⟨h.old,fun a s=> tendsto_nhds_unique_of_eventuallyEq (tendsto_pi_nhds.mp (hurled_t h) _) (tendsto_pi_nhds.mp (hurled_t h) _) (Eventually.of_forall (fun i=> (hp i).woven a s))⟩
lemma stained_all (b:Site p)(he: Stained G (rootSong A p b)) (i:G.El) (x : Link G p) : rootSong A p b (stain i x)=rootSong A p b x := by
    have ht: Tendsto (fun t:ℝ=>t• x) (𝓝[>]0) (𝓝 0) := by simpa using! ((continuous_id (X:=ℝ)).smul (continuous_const (y:=x))).continuousAt.continuousWithinAt.tendsto (x:=0) -- parameters
    obtain ⟨t,ht,hP⟩:= (eventually_pos.and (ht.eventually (he i))).exists
    apply mul_left_cancel₀ (show t^r ≠ 0 by positivity); simpa only [Function.comp_apply,map_smul,root_scaleX] using hP
lemma tourDone (h:Hurled (fun l=> X l i r) (U i r))(hp:∀ i,Marvel τ (X i)): Toute (U i r):= by
   refine ⟨tid_leases h (fun j=> (hp j).hem i r),fun m p b s=> Eventually.of_forall (fun x=>?_)⟩
   let A:= plug p R; have hz := pens_tuft (h.maps A) m b
   exact tendsto_nhds_unique_of_eventuallyEq (((ContinuousMultilinearMap.apply ℝ _ ℝ (fun _:Fin r=> stain s x)).continuous.continuousAt.tendsto).comp hz) (((ContinuousMultilinearMap.apply ℝ _ ℝ (fun _:Fin r=> x)).continuous.continuousAt.tendsto).comp hz) (Eventually.of_forall (fun j=> stained_all b ((seat_made (hp j)).seatM m p b) s x))

-- limit lanes all bounded INPUT horizon in question. Stated without requiring unsupplied other horizons.
structure SnowFirm (E k:ℕ)(X:BoardU D R G) : Prop where
  sector j : j ≤ E → ∀ r,Toute (X j r) ∧ Polished (X j r) ∧ (X j r≠0→ r≤k+j)
  gazes : ∀ (m:Side)(φ:Exam D)(x:Site m)(v w:ℝ→Link G m), AnalyticAt ℝ v 0→AnalyticAt ℝ w 0→ GaugeNear (suitify v) (suitify w) → ∀ j≤E,let L i:= large x (k+i) (fun r=> plug φ R∘X i r); Fit (j+1) (arco m L v j) (arco m L w j)
lemma gazette (h : ∀ i≤ E,∀ j,Hurled (fun l=> X l i j) (U i j))(hp:∀ i,Marvel k (X i))(hv : ∀ i≤E,∀ j,Polished (U i j)): SnowFirm E k U := by
    constructor
    · intro i hi r; refine ⟨tourDone (h i hi r) hp, hv i hi r,fun ht=> ?_⟩
      by_contra hQ; exact ht (tendsto_nhds_unique_of_eventuallyEq (hurled_t (h i hi r)) tendsto_const_nhds (Eventually.of_forall (fun x=> not_ne_iff.mp (mt ((hp x).cap i r) hQ))))
    intro m φ x v w hx ht hv j hj L
    let f (U:BoardU D R G) i r:= plug φ R∘ U i r; let l (U:BoardU D R G)(i r:ℕ):= if i≤ E then f U i r else 0
    have hz i s:Hurled (fun v=>l (X v) i s) (l U i s):= by
      unfold l; split; next hi=> exact (h i hi s).maps (plug φ R)
      exact Hurled.fixed (Pens.zero ..) -- indent
    let B (P: BoardU D R G) i := large x (k+i) (l P i); let F (P:BoardU D R G) i:= large x (k+i) (f P i)
    have hc (P:BoardU D R G)(W): arco m (B P) W j=arco m (F P) W j:= by unfold arco year; funext b; apply sum_congr rfl; intro i hi; unfold B F l; simp only [if_pos ((mem_range_succ_iff.mp hi).trans hj)]
    change Fit _ (arco m (F U) v j) (arco m (F U) w j); rw [← hc U,← hc U]; refine pulse_bound (fun a ha=>?_) (arco_t _ _ hx (fun i=>dryL ..) _) (arco_t _ _ ht (fun i=>dryL ..) _)
    apply tendsto_nhds_unique_of_eventuallyEq (pen_arco (Z:=fun n=>l (X n)) hz x k v hx a j) (pen_arco (Z:=fun n=>l (X n)) hz x k w ht a j); refine Eventually.of_forall fun b=> ?_
    change ink (arco m (B (X b)) v j) a= ink (arco m (B (X b)) w j) a; rw [hc,hc]; exact aspiredV ((hp b).wardrobe m φ x v w hx ht hv j) (ink_aspire (arco_t _ (F (X b)) hx (fun i=> dryL ..) _)) (ink_aspire (arco_t _ _ ht (fun i=>dryL ..) _)) (mem_range_succ_iff.mp ha)
end convergence
end YM.RG08.Door
