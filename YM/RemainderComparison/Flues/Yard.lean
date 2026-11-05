import YM.RemainderComparison.Serif.Price

/-!
# Mask leaks, re-closure, and annotated forces

Estimate in representative budgets. Keep every origin and test before taking
sums over marker evaluations. Geometry after gluing is that of baseline
Ovens (predicate evaluations inspect the enlarged support there).
No forced garden assumed lucrative because of paths alone; must retain old
flags and charge them. `load` is capacity already substantiated for these
substitutes and serves only to avoid paying exponential in large marked hit
budgets. No volume nor mark-card factor attached to the output bound, all
`α : probe` simultaneous.

No signed-symmetrisation here. Pert/RG03 consumes at presentation alignment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Push Push.AbsoluteSums Finset Merge
open Mosaic Mosaic.Verse Marker
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

structure Yard (ι:Type)(α:Type*)(G:Gauge)(n:Side) where
   more : ℕ→ ForcedAddress G n
   score : ℕ→ Multiset ι
   glow : α→ ℕ→ Config G n→ℝ

structure Scone (ι : Type)(α:Type*)(G:Gauge)(n:Side) where
   leg : ℕ→Support n
   rest i : (leg i).Nonempty
   glyph : ℕ→ Multiset ι
   glow : α→ℕ→ Config G n→ℝ
variable {G : Gauge} {n : Side} {ι θ : Type}[DecidableEq θ] {α:Type*} {J : Census θ}
variable (H:Yard ι α G n) (L:Scone ι α G n) (P:BudgetPoint) (root:ι→Support n)(Z:Set ι)(k:ℕ)

def apex (s:Support n)(q:Multiset ι)(f:Config G n→ℝ): Prop:= ∀ i∈q,∀ U,f U≠0 → root i⊆s
namespace Yard

def manifest (a:α):Activities G n:= ⟨fun _=>⟨0,{0},mem_singleton_self _⟩,H.more,0,H.glow a⟩

def plane (i:ℕ):= (H.more i).support
structure Sounds : Prop where
    families a : (H.manifest a).ForcedFamily P
    invested i a : apex root (H.plane i) (H.score i) (H.glow a i)

-- Hit/anchored post-budget for Physics
structure Pays (B:ℕ)(σ d:ℝ) : Prop where
    wages : ∃ f:ℕ→ℝ, (∀ i, 0≤ f i) ∧ Ac.Hit H.plane B f σ d ∧ ∀ i, load Z (H.score i) ≤ k → ∀ a V, ‖H.glow a i V‖≤f i

def song (z:ι→Poly J)(a:α)(V:Config G n):ℕ→Poly J:= fun i=> (↑(H.glow a i V):ℂ) • controls Z z (H.score i)

def gala (z:ι→Poly J)(a:α) (V:Config G n): Finset ℕ→Poly J := Photo.fronts (H.manifest a) (song H Z z a V) V P
end Yard
namespace Scone
structure Rises : Prop where
    reads a i : UsesFinal P.threshold (L.leg i) (L.glow a i)
    borel a i : Measurable (L.glow a i)
    durable a i : GaugeInvariant (L.glow a i)
    origin i a : apex root (L.leg i) (L.glyph i) (L.glow a i)
    leaked i a V : Healthy P.threshold (L.leg i) V → L.glow a i V=0
structure Treasures (B:ℕ)(σ v d:ℝ): Prop where
    wages : ∃ u f:ℕ→ℝ,(∀ i, 0 ≤ u i)∧ (∀ i,0≤ f i)∧Ac.Hit L.leg B u σ v∧ Ac.Hit L.leg B f σ d∧
       ∀ i, load Z (L.glyph i) ≤ k → ∀ a V, ‖L.glow a i V‖≤ if load Z (L.glyph i)=0 then u i else f i

def plume (z:ι→Poly J)(a:α)(V:Config G n):ℕ→Poly J := fun i=> (Complex.ofReal (L.glow a i V)) • controls Z z (L.glyph i)

def tinct (a:α)(i:ℕ)(V:Config G n):ℝ:= if load Z (L.glyph i)=0 then Real.exp (L.glow a i V)-1 else L.glow a i V
lemma ashes {a:α}{i:ℕ}{U:Config G n} (hx: L.glow a i U=0): L.tinct Z a i U=0:= by unfold tinct; rw [hx];simp
end Scone
-- Pipes grammar unchanged

def fireplace : Pipes G n:= ⟨fun _=>⟨0,{0},mem_singleton_self _⟩, H.more,L.leg,L.rest⟩
local notation "C" => fireplace H L
variable (F:ℕ ≃ (fireplace H L).Pellet)

def rune : Ovens.Label → Multiset ι := Sum.elim H.score L.glyph
def stoke (a:α): Ovens.Label → Config G n→ℝ:= Sum.elim (H.glow a) (L.tinct Z a)

def flash : Yard ι α G n:=
   ⟨addr F P,fun i=>∑ j∈(F i).val,rune H L j, fun a i V=> if (addr F P i).eligible P.threshold V then ∏ j∈ (F i).val,stoke H L Z a j V else 0⟩
end YM.RemainderComparison.Flues
