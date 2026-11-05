import YM.Dash.Inert
import YM.Spin.Sheets


/-!
Need weak k family only after finite weights/box. Use separate U any
sequencer per request; stress scale ρ & ξ tied. P real/H filtered-compatible
exactly. No need import lattice theorem to derive later; labels come from it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Climb
open Filter Function Set Complex Analysis Table Spin Ward
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ComplexOrder
variable {G : Gauge} {L : Register G} {S : Table L} {d : ℕ}

abbrev Matrix (d e : ℕ) (S : Table L) := S.Field d →L[ℂ] S.Field e
abbrev Vector (d : ℕ) (S : Table L) := Axis → Matrix d (d+1) S

abbrev Bel (L : Register G) := Spin.comparator L

/-- U from exact compatible system. Uses total U even d>D, for simpler linear-data shapes;
those maps unconstrained above D (need rank global to permit). -/
structure Scaling (S : Table L) where
  U (k : ℕ) (d : ℕ) : Spin.change S d
  xi : ℕ → ℝ
  r : ℕ → ℝ
  sign k : 0 < xi k
  positive k : 0 < r k
  later : StrictAnti r
  drips : Tendsto r atTop (𝓝 0)

namespace Scaling
variable (p : Scaling S)

/-- Weak on compacta through a **prespecified** finite ball bound per input arity/order/weight.
The requestor can choose R large enough after choosing his finite points; no simultaneity all R here.
Pay LET specimen as one shot. If R≤1 still meaningful usually finite.
-/
def window (R : ℝ) (n : ℕ) := {x : Points n|spaced R⁻¹ x ∧ ‖x‖ ≤ R}
def pins (k : ℕ) (v : (Bel L).Tag) : S.Tag := ⟨v.1,p.U k v.1 v.2⟩

structure Align (X : DiffPlan S) (T : DiffPlan (Bel L)) (H : S.RealSpin) (a : (Bel L).RealSpin) (D : ℕ) : Prop where
  Hsym k d : d≤D → realH H a (p.U k d)
  carries (k : ℕ) (d) : d ≤ D → p.U k d ((Bel L).unit d)=S.unit d
  incl k d e (h : d≤e) (hp : e ≤ D) v : p.U k e (T.rise h v)=X.rise h (p.U k d v)

def jets (p : Scaling S) (N d m : ℕ) (R : ℝ) := ∀ n : ℕ, n ≤ N → ∀ j ≤ m, ∀ v : Fin n → (Bel L).Tag,
    (∀ i,(v i).1≤d) → ∀ ε : ℝ,0<ε→ ∀ᶠ k in atTop,∀ x∈ window R n,
    ‖iteratedFDeriv ℝ j (fun y => disc (p.pins k ∘ v) (p.r k • y)) x-
        iteratedFDeriv ℝ j (disc v) x‖ ≤ ε

/-- normalized stress p.T, τ folded into request leaf. -/
def meter (p : Scaling S) (B : S.Stress) (B0 : (Bel L).Stress) := ∀ i j,Tendsto
    (fun k => (p.U k 4).symm ((↑((p.xi k)⁻¹*p.r k^4):ℂ) • B i j)) atTop (𝓝 (B0 i j))
end Scaling

abbrev Parts (S : Table L) := ∀ d, Axis → S.Field d→ₗ[ℂ] S.Field (d+1)

def leaves (p : Parts S) (d : ℕ) : Vector d S := fun i => LinearMap.toContinuousLinearMap (p d i)

/-- Candidate proper detail. Use extension through all stages finite. -/
def obey (g : Matrix d (d+1) S) (P : DiffPlan S) := ∀ (a : ℕ) (h : a ≤ d) v,
    g (P.rise h v)∈LinearMap.range (P.rise (Nat.succ_le_succ h))

def Colors (P : DiffPlan S) (H : S.RealSpin) (d) : Submodule ℝ (Vector d S) where
  carrier := {g | (∀ i,g i (S.unit d)=0 ∧ obey (g i) P) ∧
    (∀ i (k : Signed) v, S.mirror H (d+1) k (g i v)=∑ j : Axis,(↑(k.matrix j i):ℂ) • g j (S.mirror H d k v)) ∧
       (∀ i v, S.conj H (d+1) (g i v)=g i (S.conj H d v))}
  add_mem' := by
    intro x y ⟨A,T,J⟩ ⟨B,F,U⟩
    simp only [mem_setOf_eq,Pi.add_apply,_root_.add_apply]
    refine ⟨fun i => ⟨by rw [(A i).1,(B i).1]; simp, fun a h v => (LinearMap.range _).add_mem ((A i).2 a h v) ((B i).2 a h v)⟩,
      fun i k v => ?_,fun i v => by simp [J,U]⟩
    simp only [map_add,smul_add,Finset.sum_add_distrib,T,F]
  zero_mem' := by constructor <;> simp [obey]
  smul_mem' := by
    intro c x hx
    obtain ⟨H1,H2,H3⟩ := hx
    have he i v : (c • x : Vector d S) i v=(↑c : ℂ) • x i v := by
      change c • (x i v)=_
      exact RCLike.real_smul_eq_coe_smul (K:=ℂ) c _
    change (∀ _,_) ∧ _
    refine ⟨fun i => ⟨by rw [he,(H1 i).1]; simp, fun a h v => by rw [he];exact (LinearMap.range _).smul_mem _ ((H1 i).2 a h v)⟩,
      fun i k v => ?_,fun i v => ?_⟩
    · simp_rw [he,map_smul,H2 i k v, Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; rw [smul_comm]
    rw [he,map_smulₛₗ,H3,conj_ofReal,he]

structure ColorLaw (p : Parts S) (X : DiffPlan S) (H : S.RealSpin) : Prop where
  sight d : leaves p d ∈ Colors X H d
  incl d e (h : d≤e) i v : p e i (X.rise h v)= X.rise (Nat.succ_le_succ h) (p d i v)

lemma native (X : DiffPlan S) (H : S.Hierarchy) (hx : X.Inclusions S) (hp : X.Derivatives S) (h : X.Orientation H.spin) : ColorLaw X.deriv X H.spin := by
  have ht d e (h : d≤e) i (v:S.Field d) : X.deriv e i (X.rise h v)= X.rise (Nat.succ_le_succ h) (X.deriv d i v) := (X.commute_rise H.laws.toSymmetric hx hp _ _ _).symm
  refine ⟨fun d => ⟨fun i => ⟨X.unit_drop H.laws hp H.smooth _ _, fun a g v => ⟨_,(ht a d g i v).symm⟩⟩,fun i k v => ?_,fun i => h.realDer d i⟩,ht⟩
  exact h.mirrorDer ..
end YM.Climb
