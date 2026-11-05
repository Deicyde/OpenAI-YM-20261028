import YM.RemainderComparison.Breeze.Baskets

/-! # True length expeditions on assessed member/representation data.

 Interpretation: RG02+03 present models with the true-length and geometry/test derivative properties AFTER displacement (at all stipulations). Don't prove coefficient bounds of RG02. Need all mask-alignment input supports including Ω.H.Scope. Enable pullback into Treasury/Rift budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Breeze
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {ι ρ J β:Type}{α:Type*} {c f:Side} {R:RG.Rep G f} {S:StepData c f} {L:Side}
variable (P:BudgetPoint)(T:Manor G c ι α J)(l:J→ℕ) {o:ι→Support c} {k m n s:ℕ} {x a u v γ σ τ b : ℝ}
local notation "p'" => Sleet.pigment γ x
lemma flanked (hu:0≤γ) (he:Pressure.Stores.till x ≤ n) : (p')⁻¹ ≤ Real.exp (γ*n):=by unfold Sleet.pigment; rw [neg_mul, Real.exp_neg,inv_inv]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast he) hu)
lemma cooled (hv:0≤γ)(hg:Pressure.Stores.till x≤ n) : 1 ≤ p' * Real.exp (γ*n):=le_trans (le_of_eq (Eq.symm <| mul_inv_cancel₀ (show p'≠0 from (Real.exp_pos _).ne'))) (mul_le_mul_of_nonneg_left (flanked hv hg) (Real.exp_pos _).le)

-- Expenses at any stipulated support exponent BEFORE reserves. Model asset class. Owner RG02 bounds true-length e.g. from path grade; RG03 owns transport S.Area.Theorem.
structure Sonorous (V:Set J) (root:ι→Support c)(σ γ A:ℝ) : Prop where
    works : ∃ f:J→ℝ,(∀ i,0≤ f i) ∧ (∀ i∈V,Manor.Sees T P root i ∧ ∀ a x,x∈T.halls i→P.supBounds x (T.halls i) (T.solvent a i) (f i)) ∧ Ac.Hit T.halls P.B (fun i=>f i*Real.exp (γ*l i)) σ A

variable {T l} {V:Set J} -- invalid
lemma refers (hs:0≤ γ) (hf:Sonorous P T l V o σ γ a): T.Spinal V o P σ a:=by
   obtain ⟨f,h,hp,hF⟩:= hf.works; refine ⟨f,h,hp,fun x=> budget_mono (hF x) (fun i=>?_) (fun i=>?_)⟩
   · split; exact mul_nonneg (h _) (Real.exp_pos _).le; exact le_rfl
   split; next=> exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (h _) (Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _)))) (Real.exp_pos _).le
   next=>exact le_rfl
lemma sung (hs:0≤ γ) (hf:Sonorous P T l V o σ γ a) {A:Set J}(hb:A⊆V)(he:∀ i∈A,Pressure.Stores.till x≤ l i) : T.Spinal A o P σ (p'*a):=by
    obtain ⟨f,h,hp,hF⟩:= hf.works; let g:=fun i=> p' * (f i * Real.exp (γ*l i)); have ht:= AnalyticBridge.VerifiedReset.Quotes.hit_scale (show 0≤p' from Real.exp_nonneg _) hF
    refine ⟨g,fun i=>mul_nonneg (Real.exp_nonneg _) (mul_nonneg (h _) (Real.exp_nonneg _)),fun i hi=>⟨(hp _ (hb hi)).1,fun a x hx=>?_⟩,ht⟩
    apply Manor.Stem ((hp i (hb hi)).2 _ x hx); unfold g; rw [mul_left_comm]; exact le_mul_of_one_le_right (h i) (cooled hs (he i hi))
-- cofinite termwise support at same S. variant independent of arguments.Already uses absolute values.
namespace Cut
lemma rest {S:Set J}(he:T.Spinal S o P σ b)(θ:ℝ)(ht:0<θ): ∀ᶠ s:Finset J in atTop, T.Spinal (S\ (s:Set J)) o P σ θ :=by
    obtain ⟨f,h,hp,hQ⟩:= he.grants
    let p i z:= if i∈ T.halls z then f z * Real.exp (σ*coverNumber P.B (T.halls z)) else 0
    let ζ(s:Finset J)(i:J):= if i∉ s then f i else 0; have hf s i:0≤ ζ s i:=by unfold ζ; split; exact h _; exact le_rfl
    have hh (i:Site c): Tendsto (fun s:Finset J=>∑' j:↥((s:Set J)ᶜ),p i j.val) atTop (𝓝 0):= tendsto_tsum_compl_atTop_zero (p i)
    filter_upwards [eventually_all.mpr (fun i=> (hh i).eventually_lt_const ht)] with s hs
    refine ⟨ζ s,hf s,fun i hi=>?_,fun x=>?_⟩
    · rw [show ζ s i=f i from if_pos (show i∉s from hi.2)]; exact hp i hi.1
    let q:=fun i=> if x∈T.halls i then ζ s i*Real.exp (σ*coverNumber P.B (T.halls i)) else 0
    have hz i:0 ≤ q i:=by unfold q; split; exact mul_nonneg (hf _ _) (Real.exp_pos _).le; exact le_rfl
    let S':=(s:Set J)ᶜ; have hy i : q (i:S').val=p x i.val:=by unfold q; rw [show ζ s i.val=f i.val from if_pos (show i.val∉s from i.2)]
    have he : Function.support q⊆ S':=by intro i hi; by_contra hg; apply hi; have h:i∈s:=not_not.mp hg; unfold q ζ; simp [h]
    have hg := ((hasSum_subtype_iff_of_support_subset he).1 (show HasSum (fun i:S'=>q i.val) _ from (show HasSum (fun i:S'=>q i.val) (∑' i:S', p x i.val) from (Summable.hasSum ((hQ x).2.1.subtype S')).congr_fun fun i=> hy i)))
    exact ⟨hz,hg.summable,hg.tsum_eq.trans_le (hs x|>.le)⟩
end Cut

-- E budget & M multi-cost production (for RG03). Accepts presentation input credit at chosen path & α masks incl optional marked K. Not used to infer movement or that hHalo lives along selected path.
variable {E F':Set ℕ} {H:Set ι}
open Lyric Typeface Merge PhysicalNext.Repeat Pressure.Stores Raw
variable (M:ι→Lotus.Leaf R)(t:ι→ℝ)
lemma sings (g:ℕ→ℕ)(f:ℕ→ℝ)(hs:E⊆F')(hq:0≤γ)(ht:∀ i∈ E,till x≤ g i)(hv:∀ i,0 ≤ f i)(hp:∀ i∈F',R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (f i)) (hf: Footprint.Anchored (fun i=>(R.activities.reg i).site) (fun i=>f i * Real.exp (γ*g i)) (regularExtra R) R.p.supportExponent v) :
    ∃ w:ℕ→ℝ, Halo.Presents R E w (Sleet.pigment γ x * v):=by
   let k i := if i∈E then f i else 0; have hk i :0 ≤ k i:=by unfold k; split; exact hv i; exact le_rfl
   refine ⟨k,fun i hi=>?_ ,fun i hi=> if_neg hi, fun x=>budget_mono (budget_scale (show 0 ≤ p' from Real.exp_nonneg _) (hf x)) (fun i=> ?_) (fun i=>?_)⟩
   · rw [show k i= f i from if_pos hi]; exact hp i (hs hi)
   · split; exact mul_nonneg (hk _) (Real.exp_nonneg _); exact le_rfl
   split; next=>
      rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; by_cases hn:i∈E; swap; · rw [show k i=0 from if_neg hn]; exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (hv _) (Real.exp_nonneg _))
      rw [mul_left_comm, show k i=f i from if_pos hn]; exact le_mul_of_one_le_right (hv i) (cooled hq (ht i hn))
   next=> rw [mul_zero]

variable [Fintype ρ] (η : ρ→Site f)(K : ι→Finset ρ)(u:ι→ℕ)
-- spectral.Site Owner pin.Kernel. Costs on same radius-as-M assumes true displacements and exponent reserve in REAL estimate. Leaves value K.El fitted, marker preferences. λ weighted before division for p.E.
lemma pluvious (hg:0≤γ)(ht:∀ i,0≤t i)(hm : Extra.Multi.Occupancy (S.ratio.parent ∘ η) k) (hd:∀ i,0<Palette.wages M t i→∃ v∈K i,η v∈(M i).crest) (hp:∀ i∈H,till x≤ u i)(hx:0≤b)
     (hh: Extra.Multi.Rooted K (fun i=>(M i).crest) R.p.B σ (fun i=>Palette.wages M t i * Real.exp (γ*u i)) b) : Lyric.Scale η K M (Creek.rage H p' t) k σ b S ∧ Lyric.Scale η K M t k σ b S:=by
    let v:= Creek.rage H p' t; let W i:= Mosaic.Verse.marked H (p')⁻¹ i; have hf i: 0 < W i:=by unfold W Mosaic.Verse.marked; split; exact inv_pos.mpr (Real.exp_pos _); exact zero_lt_one
    have hv i : Palette.wages M v i = W i * Palette.wages M t i:= mul_assoc ..
    have h i: 0≤ Palette.wages M t i:=mul_nonneg (ht i) (Lotus.Leaf.profit _)
    refine ⟨⟨fun i=> mul_nonneg (hf _|>.le) (ht i),fun i hi=> hd i (by change 0 < Palette.wages M v i at hi; rw [hv] at hi; exact pos_of_mul_pos_right hi (hf i|>.le)), Extra.Multi.Rooted.mono hh (fun i=>?_) (fun i=>?_) le_rfl le_rfl,hx,hm⟩,ht,hd,Extra.Multi.Rooted.mono hh h (fun i=> le_mul_of_one_le_right (h i) (Real.one_le_exp (mul_nonneg hg (Nat.cast_nonneg _)))) le_rfl le_rfl,hx,hm⟩
    · change 0≤ Palette.wages M v i; rw [hv]; exact mul_nonneg (hf _|>.le) (h i)
    change Palette.wages M v i ≤ _; rw [hv,mul_comm (W _)]; apply mul_le_mul_of_nonneg_left _ (h i); unfold W Mosaic.Verse.marked; split; next hi=> exact flanked hg (hp i hi)
    next=> exact Real.one_le_exp (mul_nonneg hg (Nat.cast_nonneg _))
end YM.RemainderComparison.Breeze
