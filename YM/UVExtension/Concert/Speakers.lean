import YM.UVExtension.Concert.Vats
import YM.UVExtension.Concert.Lyres
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost Wick Wick.Bower MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ}
open Animals Reserves Gas Ursell Trees Multiple Letter OmitClusters
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
open March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt Wick
variable (hF:Festa Q L H V w g){q:Q.rate≤γ}{hk:γ<0}(Y:Festa.Pavilion H V g γ v d q hk) (hi:0≤Q.exp-d)
    (J : (d:Canvas (betaF G x L) w ι)→ Cash W x μ L Q o a T (freshen d R V)) (U:Config G c) (χ: Chi)
-- forced entry on common dictionary
open Match Refrain
variable {α e₀ e₁ : ℝ} (hA:0≤α)(he:0<e₀)(hh:0<e₁) (hp:α+e₀+e₁≤Q.exp-d)
    (hs: degreePrice (radiusB x) ((stalk Q q hk).overture L μ x 0) e₀ ≤ 1/2) (hv : degreePrice (radiusB x) ((stalk Q q hk).mergeScale L μ x 0) e₁≤1/2) (hq: (stalk Q q hk).mergeScale L μ x 0 ≤ 1/2)
local notation "Jp"=> (stalk Q q hk)

def bell {I : Type*}(S : I→ ForcedAddress G c) (p:ℕ)(α:ℝ): Meter I (Site c) where
  cost x i:= if x∈(S i).support then Real.exp (α* coverNumber p (S i).support) else 0
  test _:= Config G c
  nonneg i j:= by split <;> positivity
  awake i:= by obtain ⟨x,hx⟩:= (S i).inventory_ne; exact ⟨x,(if_pos ((S i).inventory_sup hx)) ▸ Real.exp_pos _⟩
lemma bellbook {I : Type*} (S:I→ ForcedAddress G c)(p:ℕ)(α:ℝ)(f:I→ℝ)(t:ℝ): (∀x:Site c, SumBudget (fun i=> (bell S p α).cost x i*f i) t)↔ Ac.Hit (fun i=> (S i).support) p f α t:= by
  unfold bell Ac.Hit; simp only [ite_mul,zero_mul]; simp only [mul_comm]

include hF Y
lemma grip (z:Vines ι)(hz:z∈ parade (betaF G x L) g){t:ℝ}(ht:t≤ Q.exp-d) : -- regen thin/thick posted
    ∃ (f:H.ThinP→ℝ)(g:H.ThickP→ℝ), Ac.Hit H.smallAt (radiusB x) f t ((stalk Q q hk).overture L μ x 0) ∧ Ac.Hit H.largeAt (radiusB x) g t ((stalk Q q hk).quantum L μ x 0 0 1 0) ∧(∀ i, 0 ≤ f i)∧ (∀ i,0≤ g i)∧
    ∀ U,(∀ i:H.ThinP,‖grain U χ H V i.val z‖≤f i)∧∀ i:H.ThickP,‖grain U χ H V i.val z‖≤g i:=by
  obtain ⟨f,h,hF',hE⟩:= grainS hF Y χ z hz 0; obtain ⟨g,ha,hG,hK⟩:= grainS hF Y χ z hz 1
  refine ⟨f∘Subtype.val,g∘Subtype.val,fun x=>?_,fun x=>?_,fun i=>h _,fun i=>ha _,fun U=> ⟨fun i=> hE _ _ (by omega),fun i=> hK _ _ (Cash.forced_cost i.val i.2.2)⟩⟩
  all_goals
    first
    | exact (show SumBudget _ ((stalk Q q hk).overture L μ _ 0) from by
        refine budget_mono (budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (hF' x)) (fun i=> ?_) fun i=>?_ ; swap
        · dsimp only [Function.comp_apply]; split
          next hx=> rw [if_pos (show x∈H.unionP i.val from hx)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (h _)
          exact (budget_pull (fun i:H.ThinP=>Subtype.val i) Subtype.val_injective (hF' x)).1 _
        split; next => exact mul_nonneg (h _) (Real.exp_pos _).le
        exact le_rfl)
    | refine budget_mono (budget_pull (fun i:H.ThickP=>Subtype.val i) Subtype.val_injective (hG x)) (fun i=> ?_) fun i=>?_ ; swap
      · dsimp only [Function.comp_apply]; split
        next hx=> rw [if_pos (show x∈H.unionP i.val from hx)]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (ha _)
        exact (budget_pull (fun i:H.ThickP=>Subtype.val i) Subtype.val_injective (hG x)).1 _
      split; next => exact mul_nonneg (ha _) (Real.exp_pos _).le
      exact le_rfl
include hA he hh hp hs hv hq
lemma thickP (z:Vines ι)(hz:z∈ parade (betaF G x L) g): Meter.MeasureP (bell (reserve H ∘ Refrain.badge H) (radiusB x) α) (fun i U=> tonic U χ H V z (Refrain.badge H i)) (Cash.armK Jp L μ x 0 0):=by
  obtain ⟨f,g,h,hg,hy,h',hf⟩:= grip hF Y χ z hz (show α+e₁+e₀ ≤ Q.exp-d by linarith)
  let t:=(stalk Q q hk).mark L μ x; let v:= (stalk Q q hk).mergeScale L μ x 0; let c₀:= (stalk Q q hk).overture L μ x 0; let d':= (stalk Q q hk).quantum L μ x 0 0 1 0; let B:= radiusB x
  have hm : 0≤t:= H.laws.acquired.marked
  have hi : 0<c₀:= (stalk Q q hk).overture_pos x 0 (Festa.altitude (H:=H))
  have ht': d'=c₀ * Real.exp (-t):= by unfold d' c₀ t; rw [(stalk Q q hk).quantum_form (r:=1)]; push_cast; rw [mul_one]; rfl
  have hZ : Real.exp t*d'= c₀ := by rw [ht',mul_left_comm,← Real.exp_add]; simp
  have hr: Ready H.smallAt B f (α+e₁) c₀ e₀ (1/2):= ⟨hi,he,hs,by norm_num,hy,h⟩
  have hd: Ac.Hit H.largeAt B g (α+e₁) d':=by
    intro y; refine budget_mono (hg y) (fun i=>?_) fun i=>?_
    · split; next => exact mul_nonneg (h' _) (Real.exp_pos _).le
      exact le_rfl
    split; next hx=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right he.le) (Nat.cast_nonneg _))) (h' _)
    exact le_rfl
  have hU(y:Site c):= OmitClusters.restore H.seam H.smallAt H.largeAt _ _ B hy h' (fun i=> i.2.1) (fun i=> i.2.1) (by norm_num : (1:ℝ)≤2) (σ:=1/2) (by norm_num) (by norm_num) hm hA hh H.testS hr hd (by
    norm_num; change (2:ℝ)*Real.exp t*_ *d'+_*_ ≤20*c₀; linarith) (show 0<v from mul_pos (by norm_num) hi) hq hv (show (1:ℝ)/2<1 by norm_num) y 0
  let b (p : H.Chainbook):= if H.Fresh p ∧ Ac.Spark H.bookFoot p.1 then manyW (grade H.seam f g) p else 0
  have hB(p:H.Chainbook):0≤ b p:=by
    unfold b; split; next h=> exact manyW_nonneg (w:=grade H.seam f g) (fun j=> match j with | Sum.inl i=> h' _ | Sum.inr i=> clusters_nonneg _ hy _) p
    exact le_rfl
  let a' := Sum.elim (fun p:Leaf H=>b p.val) (fun _:Blank (c:=c)=>0)
  have ht (p: Annual H): 0 ≤ a' p∧∀ U, ‖tonic U χ H V z p‖≤ a' p:=by
    rcases p with i|i
    swap; · exact ⟨le_refl _,fun i=> norm_zero.le⟩
    refine ⟨hB i.val,fun U=>?_⟩
    unfold tonic; dsimp only [Sum.elim_inl]; split; next hx=>
      change _≤ b i.val; unfold b; rw [if_pos ⟨hx.1,hx.2.1⟩]; rw [norm_prod]; apply prod_le_prod (fun _ _=> norm_nonneg _)
      intro p hp; rw [norm_div,norm_pow,Complex.norm_natCast]; apply div_le_div_of_nonneg_right _ (by positivity); apply pow_le_pow_left₀ (norm_nonneg _)
      have H(j:H.Chapter): ‖juiceK U χ H V z j‖≤ grade H.seam f g j:=by
        rcases j with i|i; exact (hf U).2 _
        change ‖-((coefficient H.seam i.2:ℂ)*_ / ((i.1+1).factorial:ℂ))‖ ≤ clusters _ f i.2
        rw [norm_neg,norm_div,norm_mul,norm_prod,Complex.norm_real,Complex.norm_natCast,Real.norm_eq_abs]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun n _=> (hf U).1 (i.2 n))) (abs_nonneg _)) (by positivity)
      exact H p.val
    next => rw [norm_zero]; exact hB _
  let k:=Refrain.badge H
  refine ⟨a' ∘ k,fun i=>ht _,(bellbook _ _ _ _ _).2 ?_⟩
  intro y; let u(p: Annual H):= if y∈ (reserve H p).support then a' p*Real.exp (α*coverNumber B (reserve H p).support) else 0
  have h (y:Site c): Ac.Hit H.library B b α (Cash.armK Jp L μ x 0 0):=by
    intro y; refine budget_mono (hU y) (fun i=>?_) fun i=>?_
    · split; next => exact mul_nonneg (hB _) (Real.exp_pos _).le
      exact le_rfl
    split; next hy=>
      unfold b; split; next ht=> rw [if_pos ⟨H.regains i ht.2 ht.1,Nat.zero_le _⟩,Multiple.connected,if_pos ⟨ht.2,hy⟩]; exact (mul_comm ..).le
      rw [zero_mul]; exact (hU y).1 _
    exact (hU y).1 _
  have he : SumBudget u ((Cash.armK Jp L μ x 0 0)+0):= Extra.Iteration.Cost.sum (budget_pull (fun i:Leaf H=> i.val) Subtype.val_injective (h y y)) (show SumBudget (fun i=> u (.inr i)) 0 from by unfold u; simp [a',SumBudget])
  rw [add_zero] at he; exact Extra.Iteration.Cost.equiv k he
include hi
lemma bellsOut : Nonempty (Atlas (bell (reserve H ∘ Refrain.badge H) (radiusB x) α) (aperture hF) (fun t i U=> Refrain.fuse H (fleet t J H) χ (Refrain.badge H i) U) (fun _=> Cash.armK Jp L μ x 0 0)):= by
  refine ⟨⟨fun z i U=> tonic U χ H V z (Refrain.badge H i),fun t i U=> tonicR hF J U χ t _,fun i U=> tonicH hF Y hi U χ _,fun z hz=>?_⟩⟩; exact thickP hF Y χ hA he hh hp hs hv hq z hz
end YM.UVExtension.Concert
