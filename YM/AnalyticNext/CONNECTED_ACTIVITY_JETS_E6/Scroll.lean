import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Assignment
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush

/-!
# Unmasked branch read for V. Values when its `Healthy` predicate holds

Drop the coarse m and clamp. Keep oriented U prediction. Bills at
actual tilted sectors use lemma by comparison under V stencil; away may
carry extension. Include hard U held branch variant (needed for steam core;
don't remove its thresholds, which vary even when V counts unchanged). -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows  Coat SliceRows.DataKernel
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {V W Q Q' : Config G c} {U U' : Config G f} {k : S.Choices} {R : ℕ} {s : ℝ}
variable {P : Teller G} {o : Site c}
open Brush

namespace Scroll
def canopyF (T : Tube G S) R (V : Config G c) := zip (T.Φ R V) (T.Xn R V)
def canopyI (T : Tube G S) R (V : Config G c) := zip (T.Φ' R V) (T.Xn R V)
def canopyN (T : Tube G S) R (V : Config G c) := zip (T.N R V) (T.Xn R V)
def visual (T : Tube G S) (R : ℕ) (V : Config G c) : Rod c f→G.Color := Sum.elim (canopyF T R V) (canopyI T R V)
def freely (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (i : Rod c f) := baseStroke T x k V i-visual T (till x) V i

def effective (T : Tube G S) (R : ℕ) (U : Config G f) (Q V : Config G c) (p : Rod c f) := Sum.elim (T.Xf R U) (Tube.Z S Q V) p -visual T R V p
-- `cost` verify

def flora (T : Tube G S) (R : ℕ) (U : Config G f) (Q V : Config G c) (b : Cell f) := T.high.direct*flaw (faceValue U b)+
    ∑ i : Bool, ‖effective T R U Q V (.inl (b,i))‖^2/2
def nora (T : Tube G S) R (U : Config G f) (Q V : Config G c) (i : Bond c) := S.kernel.penalty*flaw (V i*(Q i)⁻¹)+
    ‖effective T R U Q V (.inr i)‖^2/2

def stormL (T : Tube G S) R (U : Config G f) (Q V : Config G c) (i : Cell c) := ∑ j : Bool,
    inner ℝ (T.Xn R V (i,j)) (unzip (T.Φ R V) (T.Xf R U) (i,j)+unzip (T.Φ' R V) (Tube.Z S Q V) (i,j)-T.Xn R V (i,j))
def stormD (T : Tube G S) R (V : Config G c) (i : Cell c) := ∑ j : Bool,
    inner ℝ (T.Xn R V (i,j)) (T.Xn R V (i,j)-(unzip (T.Φ R V) (canopyF T R V) (i,j)+
      unzip (T.Φ' R V) (canopyI T R V) (i,j)+unzip (T.N R V) (canopyN T R V) (i,j)))/2
-- division parse as whole inner! copy grammar

def stormC (T : Tube G S) (V : Config G c) (i : Cell c) := -T.low.direct*flaw (faceValue V i)
def stormN (T : Tube G S) R (V : Config G c) (i : Co c Gain) := ‖canopyN T R V i‖^2/2

def finest (T : Tube G S) (R : ℕ) (U : Config G f) (t : ℝ) (V : Config G c) (p : Cell f) :=
    crown T.up T.high R 1 t U p + ∑ i : Bool, (‖canopyF T R V (p,i)‖^2/2-inner ℝ (canopyF T R V (p,i)) (T.Xf R U (p,i)))

def loft (T : Tube G S) (x : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) (paint : Bool) : Spot c f → ℝ :=
    let R:= till x; let Q:= S.prediction U k
    Sum.elim (if paint then flora T R U Q V else finest T R U (Pressure.fiery G x S.patch.L) V)
      (Sum.elim (nora T R U Q V) (Sum.elim (fun i=> stormC T V i+(stormL T R U Q V i+stormD T R V i)) (stormN T R V)))

lemma canopy {a : Type} [Fintype a] (K : Config G c→ a→ Twin c→ Pay G) (f : a→ Site c)
    (p : Room P S T s) (h : Rule (till s) K f (fun i=> i.1.1)) (i : a)
    (he : Clean V s (f i) (radiusB s/4)) : zip (K V) (T.vision (till s) (Pressure.temp s) V) i=zip (K V) (T.Xn (till s) V) i := by
  unfold zip; apply sum_congr rfl; intro j _
  by_cases hi : K V i j=0
  · rw [hi,_root_.zero_apply,_root_.zero_apply]
  rw [complete_vision p V (f i) V (fun _ _=> rfl) he j (h.reach _ _ _ hi)]

lemma frameCost (p : Room P S T s) (i : Rod c f) (h : Clean V s (focus S i) (radiusB s/4)) : guide T s V i=visual T (till s) V i := by
  rcases i with i|i
  · exact canopy _ _ p (crosses _ _ P p.accepted) i h
  exact canopy _ _ p (sameLevel _ _ S.patch.L.property T.R.mn (Row.rights _ _ p.accepted.crosses.1 P.width.le) pole mesh) i h

lemma lodge {α : Type} [Fintype α] (K : Config G c→ α→ Twin c→ Pay G) (q : α→ Site c)
    (p : Room P S T s) (h : Rule (till s) K q (fun i=> i.1.1)) (i : Twin c)
    (he : Clean V s i.1.1 (radiusB s/2)) : unzip (K V) (zip (K V) (T.vision (till s) (Pressure.temp s) V)) i =
      unzip (K V) (zip (K V) (T.Xn (till s) V)) i := by
  unfold unzip; apply sum_congr rfl; intro j _
  by_cases hi : K V j i=0
  · simp_rw [hi,map_zero,_root_.zero_apply]
  rw [canopy _ _ p h j (he.shrink (by rw [separation_comm]; have hh:= h.reach _ _ _ hi; unfold till at hh; have hx:=p.sight; omega))]

lemma nims (p : Room P S T s) (i : Cell c) (h : Clean V s i.1 (radiusB s/2)) :
    T.workC (till s) V (Pressure.temp s) i=stormC T V i ∧
      T.workL (till s) U Q V (Pressure.temp s) i = stormL T (till s) U Q V i ∧
        T.workD (till s) V (Pressure.temp s) i=stormD T (till s) V i := by
  let R:=till s; let x:= Pressure.temp s; let o:=i.1
  have hu : Clean V s o (radiusB s/4) := h.shrink (by unfold o; rw [separation_self]; omega)
  have hv (j : Bool) : T.vision R x V (i,j) = T.Xn R V (i,j) := complete_vision p _ o _ (fun _ _=> rfl) hu (i,j)
    (by change separation o o≤_; rw [separation_self]; omega)
  have hk := hu.kept p i.1 (by have he:=p.sight; change separation o o+_ ≤ _; rw [separation_self]; omega)
  have hd := hu.toll (b:=i) (by change separation o o≤_; rw [separation_self]; omega)
  constructor
  · change T.workC R V x i=_; unfold Tube.workC; simp_rw [hv]
    rw [Fintype.sum_bool]; simp only [real_inner_self_eq_norm_sq]; unfold Tube.Xn crown trunk PathData.clipped plotted
    rw [if_pos hk,if_pos (show G.chord _ ≤ x from hd)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold shoot stormC flaw; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,Real.sq_sqrt T.low.quadratic_pos.le]; ring
  constructor
  · change T.workL R U Q V x i=_; unfold Tube.workL; simp_rw [hv]; rfl
  change T.workD R V x i=_; unfold Tube.workD stormD; apply sum_congr rfl; intro j _
  rw [hv]; unfold canopyF canopyI canopyN Tube.Mv Tube.Mw
  rw [lodge _ _ p (crosses _ T P p.accepted) (i,j) h,lodge (T.Φ' R) _ p (sameLevel _ _ S.patch.L.property T.R.mn
    (Row.rights _ _ p.accepted.crosses.1 P.width.le) pole mesh) (i,j) h, lodge (T.N R) _ p (sameLevel _ _ S.patch.L.property T.R.o
    (Row.rights _ _ p.accepted.crosses.2.1 P.width.le) id mesh) (i,j) h]

lemma yields (p : Room P S T s) (i : Spot c f) (h : Clean V s (lead S i) (radiusB s/2)) (U k) :
    yielding T s U V k i=loft T s U k V true i ∧ principal T s U V (S.prediction U k) i=loft T s U k V false i := by
  have he : Clean V s (lead S i) (radiusB s/4) := h.shrink (by rw [separation_self]; omega)
  let R:=till s; let x:= Pressure.temp s; let Q:=S.prediction U k
  rcases i with i|i|i|i
  · have hg j := frameCost p (.inl (i,j)) he
    have hf j : T.Mv R x V (i,j)=canopyF T R V (i,j) := hg j
    constructor
    · change soft T s U V k i=flora T R U Q V i; unfold soft flora; simp only [SliceRows.bill,hg]; rfl
    change T.workF R U V _ x i=finest T R U _ V i; unfold Tube.workF; simp_rw [hf]; rfl
  · have hg := frameCost p (.inr i) he
    suffices hh : T.workI R Q V x i=nora T R U Q V i from ⟨hh,hh⟩
    rw [show T.workI R Q V x i=softI T s U V k i from splitI ..]; unfold softI SliceRows.bill; rw [hg]; rfl
  · obtain ⟨h1,h2,h3⟩ := nims (U:=U) (Q:=Q) p i h
    have hh := congr_arg₂ (·+·) h1 (congr_arg₂ (·+·) h2 h3); exact ⟨hh,hh⟩
  have hh := canopy _ _ p (sameLevel _ _ S.patch.L.property T.R.o (Row.rights _ _ p.accepted.crosses.2.1 P.width.le) id mesh) i he
  exact ⟨congr_arg (fun x : G.Color=> ‖x‖^2/2) hh,congr_arg (fun x : G.Color=>‖x‖^2/2) hh⟩
end Scroll
end YM.ConnectedActivityE6.Blaze
