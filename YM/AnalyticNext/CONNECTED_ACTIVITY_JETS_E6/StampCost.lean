import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arms

/-!
# Sharp beta gifts on determinant chains

True `3B` hops. All matrices color counting. C-chain costs can use Torch
per actual post. Factor exp arm estimate still has cover cost; from Tax.
Joint old path sails not under-ordered. Signs don't eat the root factors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse.Itinerary
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {c f : Side} {S : StepData c f} {d u m B : ℕ} {G : Gauge} {η r Q : ℝ}
variable (D : Window (along (G:=G) S) B) (A : Mat f G) (h : Allow A (along S) m η r Q) (ht : Torch η r Q)

lemma one_hut (u : ℝ) (n : ℕ) : tally (n:=n) (fun _ => u)=u^n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [count_mul, ih,pow_succ']

def flagP := (Fintype.card G.ColorIndex:ℝ)
def centreA (η r Q : ℝ) (m B : ℕ) (G : Gauge) := flagP (G:=G) ^4*((Q+1)*payE η r Q m)*scraps η r Q m B
def etaA (η r Q : ℝ) (m B : ℕ) (G : Gauge) := flagP (G:=G)*scraps η r Q m B

def centreS (η r Q : ℝ) (m B : ℕ) (G : Gauge) := flagP (G:=G)^2*(Q*distPay η r Q m B)
def etaS (η r Q : ℝ) (m B : ℕ) (G : Gauge) := flagP (G:=G)*(Q*distPay η r Q m B)

/-- Costs independent of V etc. Define envelopes to zero on the
invariant bad-address tests. -/
def cap (S : StepData c f) (B u : ℕ) (p : Ledger f u) (C Q : ℝ) :=
    if Armed S (3*B) p.2.1 p.2.2 then C*Q^p.1 else 0

def capA (G : Gauge) (S : StepData c f) (η r Q : ℝ) (m B : ℕ) (p : Ledger f 3) :=
    cap S B 3 p (centreA η r Q m B G) (etaA η r Q m B G)
def capS (G : Gauge) (S : StepData c f) (η r Q : ℝ) (m B : ℕ) (p : Ledger f 1) :=
    cap S B 1 p (centreS η r Q m B G) (etaS η r Q m B G)

lemma iso (P : Mat f G) {d : ℕ} (h : Thin (along S) (along S) P d) (x : ℝ) : Thin (along S) (along S) (x • P) d := by
  intro i j hk; rw [Matrix.smul_apply, h i j hk, smul_zero]
lemma opposite (P : Mat f G) {d : ℕ} (h : Thin (along S) (along S) P d) : Thin (along S) (along S) (-P) d := by
  intro i j hk; rw [Matrix.neg_apply,h i j hk, neg_zero]

lemma effects (hs : Thin (along S) (along S) A (B/2)) (hd : 4 ≤ B) :
    Thin (along S) (along S) (D.flawed A) (3*B) := fun i j he => D.height A hs i j (by omega)

include h ht in
lemma first (hs : Thin (along S) (along S) A (B/2)) (hd : 4 ≤ B) (p : Ledger f 3) :
    |ArmA D A p| ≤ capA G S η r Q m B p := by
  let q := retain η r Q
  let u := scraps η r Q m B
  let t := payE η r Q m
  let l (n : ℕ) := match n with
    | 0 => Q+1
    | 1 => t
    | _+2 => u
  have hn : 0≤u := h.heap B
  have hl : 0≤t := h.disc
  have hk : 0≤Q := h.fuel.le
  have hh : 0≤q := h.weather.1.le
  have hv (x) (he : x∈Set.Icc (0:ℝ) 1) := h.glide ht.hv ht.hQ x he
  have hP x (he : x∈Set.Icc (0:ℝ) 1) n : Price (along S) (along S) (aSeq D A x n) q (l n) := by
    match n with
    | 0 =>
      have ht := paid_add h.relented (spent_neg (one_pay (along (G:=G) S) q))
      rw [aSeq, sub_eq_add_neg]; exact ht
    | 1 => exact increase ((hv _ he).primal D) (show q≤2*q by linarith) le_rfl
    | n+2 => exact spent_neg ((hv _ he).discrepancy D)
  have hR x n : Thin (along S) (along S) (aSeq D A x n) (3*B) := by
    rintro i j he; match n with
    | 0 =>
      have hi : i ≠ j := by rintro rfl; simp at he
      rw [aSeq,Matrix.sub_apply,hs _ _ (by omega)]; simp [hi]
    | 1 => exact (D.thin _) _ _ (by omega)
    | n+2 => exact (opposite _ (D.stencil _ (Window.Thin.glides A hs x))) i j (by omega)
  rcases p with ⟨n,v,P⟩
  refine (sum_cost (b:=3*B) v P (fun i _ => ?_) (fun x _ k _ => hR x k) (fun x hs k _ i j => only_price (hP x hs k).1 hh i j)).trans_eq ?_
  · cases i with
    | zero => change 0≤Q+1; linarith
    | succ i => cases i with
      | zero => exact hl
      | succ i => exact hn
  unfold capA cap; dsimp only; split
  next he =>
    rw [count_mul (n+2),count_mul (n+1)]
    change _ * ((Q+1)*(t*tally (n:=n+1) (fun _ => u)))=_
    rw [one_hut]; unfold centreA etaA flagP t u; ring
  rfl

include h in
lemma next_cost (hs : Thin (along S) (along S) A (B/2)) (hd : 4 ≤ B) (p : Ledger f 1) :
    |ArmS D A p| ≤ capS G S η r Q m B p := by
  let u := Q*distPay η r Q m B
  have hh : 0≤u := mul_nonneg h.fuel.le (mul_nonneg h.disc (h.heap B))
  have ht := h.flank D
  have hP x (he : x∈Set.Icc (0:ℝ) 1) n : Price (along S) (along S) (sSeq D A x n) (retain η r Q) u := by
    cases n with
    | zero => exact ht
    | succ n =>
      apply increase (spent_neg (weighted_by ht x)) le_rfl
      rw [abs_of_nonneg he.1]; exact mul_le_of_le_one_left hh he.2
  have hp x n : Thin (along S) (along S) (sSeq D A x n) (3*B) := by
    have hv := effects D A hs hd
    cases n
    · exact hv
    exact opposite _ (iso _ hv x)
  rcases p with ⟨n,v,P⟩
  refine (sum_cost (b:=3*B) (l:=fun _=>u) v P (fun _ _ => hh) (fun x _ k _ => hp x k)
    (fun x hs k _ i j => only_price (hP x hs k).1 h.weather.1.le i j)).trans_eq ?_
  unfold capS cap; dsimp only; split
  next he => rw [one_hut]; unfold centreS etaS flagP u; ring
  rfl
end YM.ConnectedActivityE6.Pulse.Itinerary
