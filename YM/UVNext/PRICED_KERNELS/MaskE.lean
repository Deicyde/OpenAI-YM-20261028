import YM.Next.SCHEDULE.SlotPay
import YM.Push.PRICE_COMPILER.Post
import YM.UVNext.PRICED_KERNELS.Costed
import YM.UVNext.PRICED_KERNELS.Echo
import YM.UVNext.PRICED_KERNELS.Strolling




set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Valuation-five pre-L derivative/hit-local estimate for delta tip residue

Immediate  use. Chord-small via Healthy or just the kept criterion.
Handles all prechosen finite orders & powers, across any depths and no loss
of order powers. Don't infer anything about clustered nonlocal startup paths
(e.g. on the ordinary `wire` horizon instead of `rewire`). This is for the new
choice of `V` all the way. And integrating & assembling the startup still needs
actual retention, address supports, flag allocations, hit accounting, continuity,
and sizes bought/sharing the `Wages.fund` etc prices. Only a *true input* to E
sup etc on 5th-order terms (word bills also useful independently of selector).

No Hessian assumption taken on Q layouts at each p, and no schedule money used
from earlier BC after p. Computed only on the actual known fourth correction. _All_
orders assigned even though Caps cut off the named degree (possible on this
analytic germ, no claim Costed would work on mere smooth extension at each horizon).
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Wilson Precision Exterior Gauge Work.G07
open Next.Scheduling.Wages
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

-- R price on any path of shape length L. For local residues the chord
-- bound required AT THE WORD (under gauge U). No distributional or
-- Fourier interpretation nor coarse confusion with block L.
private lemma WalkUsed (x : Site n) (l : Walk) :
    Path.price (Path.tissue (G:=G) x l)=1 ∧ (Path.uses (Path.tissue (G:=G) x l)).length=l.length ∧
      ∀ i∈Path.uses (Path.tissue (G:=G) x l),separation i.1 x ≤ l.length := by
  -- Scheduling.Wages.Path.sieve private. Establish again.
  induction l generalizing x with
  | nil => simp [Path.tissue,Path.price,Path.uses]
  | cons a l ih =>
    obtain ⟨h,h',he⟩:=ih (x+a.vec)
    have hx : (Path.single (G:=G) x a).size=1 ∧ (Path.single (G:=G) x a).links = [a.used x] := by
      unfold Path.single; split <;> exact ⟨rfl,rfl⟩
    have ha := oneStep_le x a
    rw [Path.tissue,Path.price,h,hx.1, one_mul,Path.uses,hx.2]
    simp only [List.singleton_append,List.length_cons,h']
    refine ⟨trivial,trivial,fun i hi => ?_⟩; rcases List.mem_cons.mp hi with rfl|hg
    · rw [separation_comm]; cases a with
      | mk i b =>
        cases b
        · rw [show (Step.used _ _).1=x from rfl]; simp
        apply le_trans (b:=1) _ (Nat.le_add_left ..)
        simpa [Step.vec,Step.used,sub_eq_add_neg] using ha
    rw [separation_comm] at ha
    exact (separation_triangle i.1 (x+a.vec) x).trans (by have := he i hg; omega)

def feeWalk (G : Gauge) (L P m : ℕ) := G.colorScale+‖(1:G.Mat)‖ * (1+G.colorScale*(1+L)^P*L)^m
lemma feeWalk_nonneg (G : Gauge) (L P m : ℕ) : 0 ≤ feeWalk G L P m := by unfold feeWalk; have := G.colorScale_pos; positivity

def wordStamp (x : Site n) (l : Walk) (U : Config G n) := G.mat (travel U x l) - 1

lemma stamp_soft (o : Site n) (l : Walk) (k : ℕ) : LeftSmooth k (wordStamp (G:=G) o l) := by
  rw [show wordStamp (G:=G) o l = (fun U : Config G n => Path.eval (Path.tissue o l) U + (-1:G.Mat)) by funext U; rw [wordStamp,Path.picture,sub_eq_add_neg]]
  exact (Path.soft (Path.tissue o l) k).add
    ((LeftBound.const (G:=G) (n:=n) (D:=fun _ => True) (Z:=fun _ => True) (k:=k) (r:=1) (by norm_num) (-1:G.Mat)).smooth)

lemma word_fund (o : Site n) (l : Walk) (b : BudgetPoint) (Z : Config G n → Prop)
    (h : ∀ U, Z U → G.chord (travel U o l) ≤ b.threshold) :
    bill b.order (b.dirBound o) Z (feeWalk G l.length b.power b.order * b.threshold) (wordStamp o l) := by
  let k:=b.order; let P:=b.power; let t:=b.threshold; let L := l.length
  let w := Path.tissue (G:=G) o l
  have hX := stamp_soft (G:=G) o l k
  have hp := b.threshold_pos.le
  refine ⟨hX,mul_nonneg (feeWalk_nonneg ..) hp,fun a ha hD U hU => ?_⟩
  simp only [one_pow,mul_one]
  let T : ℝ := G.colorScale * t * (1+L)^P
  have hg:=G.colorScale_pos
  have he : 0 ≤ T := by unfold T t; positivity
  have hz : wordStamp o l = (fun U : Config G n => Path.eval w U + (-1:G.Mat)) := by funext U; rw [wordStamp,Path.picture,sub_eq_add_neg]
  by_cases ht : a=[]
  · subst a
    have hf := h U hU
    have hh : ‖wordStamp o l U‖ /G.colorScale ≤ t := hf
    apply ((div_le_iff₀ hg).mp hh).trans
    rw [mul_comm t]; unfold feeWalk; gcongr; simp; positivity
  rw [hz,left_add (Path.soft w _) ((LeftBound.const (G:=G) (n:=n) (D:=fun _ => True) (Z:=fun _ => True) (k:=b.order) zero_le_one (-1:G.Mat)).smooth) ha]
  dsimp only; rw [left_const,if_neg ht, add_zero]
  obtain ⟨h1,h2,h3⟩:= WalkUsed (G:=G) o l
  have hF := Path.bill w T he U a (fun i hi j hj => show _ ≤ T by
    rw [G.colorMat_norm]
    apply (mul_le_mul_of_nonneg_left (hD j hj i) hg.le).trans
    have ht := h3 _ hi
    unfold T t P; rw [mul_assoc]; gcongr)
  refine hF.trans ?_
  have hy : 1 ≤ 1+G.colorScale*(1+L)^P*L := by have hh : 0 ≤ G.colorScale*(1+(L:ℝ))^P*L := (by positivity); linarith
  have ht' : t^a.length ≤ t := by simpa using pow_le_pow_of_le_one hp b.threshold_le (show 1 ≤ a.length from List.length_pos_iff.mpr ht)
  unfold w; rw [h1,h2,one_mul]
  let m := G.colorScale*(1+(L:ℝ))^P*L
  calc
    _ = ‖(1:G.Mat)‖*(m^a.length*t^a.length) := by unfold m T L; rw [← mul_pow]; ring
    _ ≤ ‖(1:G.Mat)‖*((1+m)^b.order*t) := by
      have hm : 0 ≤ m := by unfold m; positivity
      gcongr
      exact (pow_le_pow_left₀ hm (show m ≤ 1+m by simp) a.length).trans (pow_le_pow_right₀ hy ha)
    _ ≤ _ := by unfold feeWalk; change ‖(1:G.Mat)‖*((1+m)^b.order*t)≤(G.colorScale+‖(1:G.Mat)‖*(1+m)^b.order)*t; rw [← mul_assoc,add_mul]; exact le_add_of_nonneg_left (mul_nonneg hg.le hp)






end YM.UVNext.PricedKernels
