import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Blox
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Roth
/-!
 # Actual Tower and fringes desks budget. This makes the obsolete canopy a reusable
 emitted side. Orth group orbit ALWAYS explicit on smaller Leper powers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' j m: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi}
local notation "B" => radiusB p
open Brim Height Refrain
variable (X' : Match.Alliance I H 1 0) (p' : BudgetPoint)
private lemma cap_sum {ι:Type} (f h u:ι→ Config G c→ℝ) (he : u=f+h) (A: ι→RegularAddress c) (p : BudgetPoint)
   (hp : Budget p A f a) (hv:Budget p A h W): Budget p A u (a+W):= by
  obtain ⟨k,h',hv'⟩:=hv; obtain ⟨c',hc,hF⟩:=hp; rw [he]; refine ⟨c'+k,fun i=> ?_,fun i=>?_⟩
  · convert budget_plus (hc i) (h' i) using 2 with x; dsimp only [Pi.add_apply]; split <;> ring
  have hh:(f+h) i=f i-((-1:ℝ) • h i):= by simp
  have hp:= CouplingShape.reg_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1); rw [hh]; refine ⟨hp,?_⟩
  have hb:= CouplingShape.sup_scale (-1) (hv' i).2; rw [abs_neg,abs_one,one_mul] at hb; exact CouplingShape.sup_sub (hF i).1 (CouplingShape.reg_scale (-1) (hv' i).1) (hF i).2 hb
lemma soared (f:Magazine I→ Config G c→ℝ) {t : ℝ} (h: Budget p' (Beam.contents I p') f t): Budget p' (Beam.marquee I p').reg (choir f ∘ pennant I) (turnFee p'*t):= by
  obtain ⟨f,h,hf⟩:=h; obtain ⟨hx,hK⟩:= Song.spiral _ _ _ (fun i=> (hf i).1) (fun i=> (hf i).2) h; exact ⟨_,fun i=> Cost.equiv (Song.pennant I) (hK i),fun i=> hx (Song.pennant I i)⟩

variable (γ : ℝ)
def hKeep (t : ℕ) (z:Magazine I) := if z∈Meadow.bouquet I t then 0 else opus I X' χ γ z

def timbres (t:ℕ): Collection.Source G c:= ⟨choir (hKeep X' (χ:=χ) γ t) ∘ pennant I, fuse I X' χ ∘ Refrain.badge I⟩

lemma compass (k:ℕ) (x: ℕ) : (timbres X' (χ:=χ) γ k|>.logRead x) = (if (pennant I x).2 ∈ Meadow.bouquet I k then 0 else (plusone I X' χ γ).logRead x):= by
  unfold timbres plusone choir; let y:= Song.pennant I x; change Rim c • ((if _ then (_:Config G c→ℝ) else _) ∘ y.1.view)= _; split
  · ext; simp
  rfl

-- add any tower.D.Dep support + Preserved Phi.A.
lemma candles (k:ℕ) {t w : ℝ} (h : Budget p' (Beam.marquee I p').reg (choir (tower (χ:=χ) X' γ) ∘ pennant I) t) (hp: Budget p' (Beam.marquee I p').reg (fun i=> if debris I k i then (plusone I X' χ γ).logRead i else 0) w) :
   Budget p' (Beam.marquee I p').reg (timbres X' γ k (χ:=χ)|>.logRead) (t+w):= by
  refine cap_sum _ _ _ ?_ _ _ h hp
  ext x i; rw [compass]; let y:= pennant I x; let z:= y.2; let u:= y.1.view i
  change ((if z∈ bouquet I k then (_:Config G c→ℝ) else _) i)= Rim c * ((if keep I z then (_:Config G c→ ℝ) else _) u)+(if Meadow.debris I k x then (_:Config G c→ ℝ) else _) i
  by_cases he:z∈ bouquet I k; · rw [if_pos he, if_neg (notKept z he), if_neg (show ¬debris I k x from (fun h=> h.2 he))]; simp
  rw [if_neg he]; split
  next hv=> rw [if_neg (show ¬debris I k x from (fun h=> h.1 hv))]; change _= _ + 0; rw [add_zero]; rfl
  next hh=> rw [if_pos (show debris I k x from ⟨hh,he⟩)]; simp

-- when building tower sym, real from Height incarnations and path tail
variable {C' t Λ b d: ℝ} (hp:R.path=R'.path) (ha:R'.activities.reg=R.activities.reg)
  (hk:R'.activities.forced=R.activities.forced) (hz: X'.units=Equiv.refl _)
  (hO : Collection.Local (Beam.marquee I p') p' (Height.serve I X' χ (Beam.lit I)) V d)
  (he:p'.threshold=Pressure.temp p) (ht:p'.B=radiusB p) (hX:T.down.Bounds T.low t C' Λ) (hd:WilsonStartup.Decent T.low p')
  (hf:preExponent p'/p'.B≤t/4) (hv:Real.exp (-(t/4)*p'.B)*Song.octaveNeed G p' T.low t C' Λ R.beta γ ≤ b)
include hp ha hk hz hO ht hX hd hf hv
lemma podiumAll : Budget p' (Beam.marquee I p').reg (choir (Meadow.tower X' (χ:=χ) γ) ∘ pennant I) (V+turnFee p'*b):= by
  have hB := Meadow.realB (γ:=γ) X' hz hp ha hk p' V d hO -- args
  let V i:= if Meadow.keep I i ∧ (∃ z, i=Sum.inl z) then opus I X' χ γ i else 0
  let u:=tower X' (χ:=χ) γ; let v i:= Sum.elim (fun _:I.fragrances=> (0:Config G c→ℝ)) (fun k=> u (.inr k)) i
  have hv : Budget p' (Beam.contents I p') v b := by
    obtain ⟨f,h,hF⟩:= lent (c:=c) p' T.down T.low R.beta γ hX hd hf
    let w i:=if Meadow.keep I (Sum.inr i) then f i else 0
    have hg i:0≤w i:=by unfold w; split; exact (hF _).2.1; exact le_rfl
    refine ⟨Sum.elim (fun _=>0) w,fun i=> ?_,?_⟩
    · rw [ht] at hv
      have hy:= (arch_tail _ p' (arc T.down) h (k:=B) (by have hx := hX.width; positivity) (fun i=> (hF i).2.1)) i
      rw [← zero_add b]; apply Cost.sum ?_ (budget_loosen (budget_mono hy ?_ ?_) hv); · simp [SumBudget]
      · intro i; split; next=> exact mul_nonneg (hg _) (Real.exp_nonneg _)
        exact le_rfl
      intro i; dsimp only [Sum.elim_inr, Beam.contents]; split
      next h =>
        unfold w; split; next hv=> rw [if_pos (le_of_lt (show _ < _ from hv))]
        rw [zero_mul]; split; exact mul_nonneg (hF _|>.2.1) (Real.exp_nonneg _); simp
      exact le_rfl
    intro i; rcases i with i|i
    · exact ⟨CouplingShape.reg_const _,VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
    change _ ∧ p'.supBounds _ _ _ (w i); dsimp only [v,u,tower, Sum.elim]; unfold w; split
    next hv=> exact hF _
    exact ⟨CouplingShape.reg_const _, VerifiedReset.sup_le (CouplingShape.sup_const _) (le_of_eq abs_zero)⟩
  have hθ:= soared p' v hv
  refine cap_sum (choir V ∘ _) (choir v ∘ _) _ ?_ _ _ hB hθ
  suffices hM : ∀ x:Magazine I,u x=V x+v x by
    ext x i; let p:=pennant I x; let z:=p.1.view i; change Song.Rim c * u p.2 z= Song.Rim c * V p.2 z+ Song.Rim c * v p.2 z; rw [hM]; exact mul_add ..
  rintro (z|z)
  · simp only [u,V,v,tower,Sum.elim_inl,and_true, add_zero,show (∃ i', (Sum.inl z:Magazine I)=.inl i') from ⟨z,rfl⟩]
  simp [V, v]
end YM.PhysicalNext.Repeat.Meadow
