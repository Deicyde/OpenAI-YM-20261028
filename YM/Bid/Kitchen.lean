import YM.Ovens.Coffee

/-!
Κ before forgetting labels, keep true addresses. `Launch` test with ANY OVEN prepared tap;
upstream supplier therefore must freeze ALL Λ, Curve, β tests. No β dressing from this Prop.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Filter Function Set RG Wilson Lattice Supply Pressure Shoot Ovens Ovens.Pipes
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal ENNReal ComplexOrder Classical

variable {G : Gauge} {C : Sheet G} {D : Rolls C} {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y}

def H01 : Prop := ∀ (G : Gauge) (n : Side) (X : Pipes G n) (d : Tap G n) (F : ℕ≃Pellet X) (δ u κ γ : ℝ) (P : BudgetPoint),
    X.Digests d P δ u → X.Buys d P κ γ → ∀ V : Config G n, (fused F P d).gas P V=(X.pours d).gas P V*Real.exp (∑' i,d.logarithm i V)

def quote (κ γ : ℝ) := Real.exp (-κ)*(Real.exp γ-1)

def H02 : Prop := ∀ (G : Gauge) (n : Side) (X : Pipes G n) (d : Tap G n) (F : ℕ≃Pellet X) (δ u κ γ v : ℝ) (P : BudgetPoint),
    quote κ γ≤v → X.Digests d P δ u → X.Buys d P κ γ → (fused F P d).KBound P v

def H03 : Prop := ∀ (G : Gauge) (n : Side) (X : Pipes G n) (d : Tap G n) (F : ℕ≃ Pellet X) (δ u : ℝ) (P : BudgetPoint),
    X.Digests d P δ u → (fused F P d).ForcedFamily P ∧ ∀ s b, Nonempty ((fused F P d).Moves s b)

-- continuity. given commonly addressable curve of E/B/K trunks before forging.
def Cake {n G} (S : ℝ→Tap G n) (X : Pipes G n) (R : PathData G) (A : Clip) (P : BudgetPoint) (β : ℝ) : Rep G n :=
    ⟨R,A,X.pours (S β),P,β,0⟩

def cookie {n G} (S : ℝ→Tap G n) {X : Pipes G n} (F : ℕ≃Pellet X) (R : PathData G) (A : Clip) (P : BudgetPoint) (β : ℝ) : Rep G n :=
    { Cake S X R A P β with activities:=fused F P (S β) }

def H04 : Prop := ∀ (G : Gauge) (n : Side) (X : Pipes G n) (S : ℝ → Tap G n) (F : ℕ≃ Pellet X) (T : Set ℝ)
    (R : PathData G) (A : Clip) (P : BudgetPoint), Curve P (Cake S X R A P) T → invariantJet P S T → X.little P S T →
    Curve P (cookie S F R A P) T

open Input Precision
variable {Z : ChartRatio G} {K : MapPrices} {Q : PostCost D}
variable (B : Directed G I Z K Q)

abbrev topRatio (N : ℕ) := B.bake.path N N
abbrev topClip (N) := (B.a.params N).clip
structure Oust (N p : ℕ) : Prop where
  launches :
    ∃ X : Pipes G (B.a.S.side N p), ∃ d : ℝ → Tap G (B.a.S.side N p), ∃ F : ℕ ≃ Pellet X,
    let T := band B.a N; let P := B.a.budget N
    let δ := B.a.clock.allowance N; let w := B.a.clock.forcedAllowance N
    let C := Cake d X (topRatio B N) (topClip B N) P
    let Q := cookie d F (topRatio B N) (topClip B N) P
    (Curve P C T ∧ invariantJet P d T ∧ X.little P d T) ∧
      ∀ i∈T,(B.bake.retain N N p (Q i) ∧ B.bake.first N p (Q i)) ∧
      ∃ κ γ u, Digests X (d i) P δ u ∧ X.Buys (d i) P κ γ ∧ quote κ γ ≤ w ∧
        ∀ y : Config G (B.a.S.side N p), (C i).eval y * Real.exp (∑' j,(d i).logarithm j y)=bare i y

-- Curve already old-E continuity. Real fit on any D, PL.Use shares.
lemma Oust.begins {N p : ℕ} (H : Oust B N p) (a : H01) (b : H02) (c : H03) (d : H04) : ∃ F, Curve (B.a.budget N) (n:=B.a.S.side N p) F (band B.a N) ∧
      ∀ β∈band B.a N,(F β).beta=β ∧ Lives B.bake N N p (F β) ∧ B.bake.Starter N p (F β) := by
  obtain ⟨X,Z,F,⟨hx,hy,hz⟩,t⟩ := H.launches
  refine ⟨cookie Z F (topRatio B N) (topClip B N) (B.a.budget N), d G _ X Z F _ _ _ _ hx hy hz,fun i hi => ?_⟩
  obtain ⟨⟨h1,h2⟩,u,v,c',he,hh,hL,hr⟩ := t _ hi
  refine ⟨rfl,⟨rfl,rfl,rfl,⟨?_,⟨⟨he.stamp.regular.smooth,he.stamp.regular.at_flat,he.stamp.regular.vanish⟩,(c G _ X _ F _ _ _ he).1,(c G _ X _ F _ _ _ he).2,he.stamp.boundE, b G _ X _ F _ _ u v _ _ hL he hh⟩⟩,h1⟩,rfl,?_,h2⟩
  · have hh := B.support.cap N N le_rfl
    change (B.bake.path N N).Bounds _ _ _ _; rw [B.bases]; exact hh
  funext y
  change _ = bare i y; rw [← hr]
  unfold cookie Cake Rep.eval; simp only; rw [mul_assoc, ← a G _ X (Z i) F _ _ u v _ he hh y]; rfl
end YM.Bid
