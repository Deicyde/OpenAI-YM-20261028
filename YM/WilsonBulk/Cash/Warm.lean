import YM.WilsonBulk.Cash.Trajectory
import YM.WilsonBulk.Recast.Reproduce

/-!
# Receipt telescope costs (Part1 gates & assembler structural identity)

Parameter-exp polynomial charges paid for value and difference in actual full rules; `age` later.

Separate all gate dependence order & quantifier.

Input Primary Q,h beams & x_pivot are pre length
   amounts whenever used in **recurrent** judgments (choose σ θ lvl-constraints first).

Constants for
   assembly ports also require parameter `Season` holding analytic recurrence restrictions
   only; not a claim on positivity or gap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f L : Side} {X Y : Type} {n k e E : ℕ} {σ μ θ η ζ x A B M Q S : ℝ}
variable {T : Cross L X Y} {P : Patch} {K : KernelChoices} {J : ChartRatio G}

-- inverse scalings at covariance events incur SMALL width strip but fixed before L.
structure Season (L : Side) (θ σ μ : ℝ) (E : ℕ) : Prop where
 input : 0<θ
 output : 0<σ
 horizonM : 0 < μ
 input_small : θ ≤ 1
 output_small : σ ≤ 1
 analytic : ((E+2:ℕ):ℝ)*σ ≤ μ
 windows (e : ℕ) : e≤E→ σ ≤ saveWidth e μ
 -- three LENGTH requests
 width_in : μ/L.val ≤ θ
 hyper : σ/L.val ≤ θ/2
 highGate : pulseGrow (σ/L.val) (E+1) ≤ θ
lemma Season.bill (h : Season L θ σ μ E) : σ ≤ μ := by
  have hp : 1 ≤ ((E+2:ℕ):ℝ) := by norm_cast; omega
  exact (le_mul_of_one_le_left h.output.le hp).trans h.analytic
lemma Season.lamp (h : Season L θ σ μ E) (hh : n ≤ E+2) : (n:ℝ)*σ≤ μ := (mul_le_mul_of_nonneg_right (by exact_mod_cast hh) h.output.le).trans h.analytic
lemma Season.high_use (h : Season L θ σ μ E) (hr : n ≤ E+1) : pulseGrow (σ/L.val) n ≤ θ := by
  have hX:= h.output; apply le_trans ?_ h.highGate; unfold pulseGrow; gcongr
lemma climbBill {Z d : Duct X Y} (hn : k ≤ n) (h : AuditLine Z d n x x) (hv : x ≤ M) : AuditLine Z d k M M:= h.narrow hn hv hv (fun _ _=>le_rfl) h.fronts
lemma climbCost {Z d : Duct X Y} (h : AuditLine Z d n x A) (hx : x≤M) (ha : A≤M) : AuditLine Z d n M M := h.narrow le_rfl hx ha (fun _ _=>le_rfl) h.fronts
lemma line_empty {Z d : Duct X Y} (h : AuditLine Z d n x x) (hh : 0 ≤ M) : AuditLine (Z-Z) d n M M := by
  rw [sub_self]; refine ⟨hh,hh,h.fronts,fun x=> by simp [Pert.Bulk.bill], fun y=>by simp [Pert.Bulk.bill]⟩

-- House light: stencil and strip/L costs only (not asking input/output fit bounds)
abbrev Beds (θ : ℝ) (e : ℕ) (M : ℝ) (I : Record (Market X)) := ∀ i≤e,∀ n ≤ i+2, Within (lawn X) θ M (I i n)
structure Warm (P : Patch) (K : KernelChoices) (J : ChartRatio G) (θ σ μ r : ℝ) (E : ℕ) (A : ℝ) : Prop where
 -- r : RANK-two projection summit-pre-price on THIS mesh (selected before L)
 era : Season P.L θ σ μ E
 height : 1 ≤ A
 epoch : AuditLine (oil G P) (spotCost P.L μ) (E+2) A A
 -- no limitation on MARK count by these; use unmarked only
 top : Beds 1 E A (upstream G)
 hair : Beds 1 E A (curtainHair J)
 crown : Beds μ E A (noisePart P K G)
 coin : momentWeight σ 2 ≤ A
 ruby : r ≤ A
lemma Warm.more (h : Warm P K J θ σ μ x E A) (he : A ≤ M) : Warm P K J θ σ μ x E M :=
  ⟨h.era,h.height.trans he, climbBill le_rfl h.epoch he,fun i hi n hn=>(h.top i hi n hn).mono le_rfl he, fun i hi n hn=>(h.hair i hi n hn).mono le_rfl he, fun i hi n hn=>(h.crown i hi n hn).mono le_rfl he,h.coin.trans he,h.ruby.trans he⟩

section graft
variable {Z N V U : Bed} {F : Model P K}
abbrev Shaft (L : Side) := Cross L PotentialForm PotentialForm
variable {D : Shaft P.L} {J : ChartRatio G}
abbrev comfort (F : Model P K) (B : Bed) := pair (plain (cargo (G:=G) F B))
structure Tarmac (k : G.ColorIndex) (J : ChartRatio G) (F : Model P K) (B Q : Bed) (D : Shaft P.L)
    (θ σ μ r q : ℝ) (E : ℕ) (A : ℝ) : Prop where
  warm : Warm P K J θ σ μ r E A
  h : Passage J B Q F
  hUnit : subdue k (summit G Q 0 2)=1
  curtain : Serves G F B μ A
  arise : (beams G F B).strip μ A
  corners : (lanternPhi G F D).strip μ A
  greet : GrowsHigh G (preGate G D) (beams G F B) (lanternPhi G F D) K (cascade 1)
  deep : Heights (preGate G D) 3 μ q -- all strict moments needed for n≥1 ≤3; q cost already before L.
  harbor_in : Walls (P:=P) (preGate G D) (E+2) σ A
  harbor_post : Walls (P:=P) (beams G F B) (E+2) σ A
  harbor_lamp : Walls (P:=P) (lanternPhi G F D) (E+2) σ A
  pot : AuditLine (plain (pilot (G:=G) F B)) (spotCost 1 σ) (E+2) A A
  cargo_in : Within (lawn _) μ A (comfort (G:=G) F B)
  summit_home : Within (lawn _) σ r (onTop G Q)
variable {i : G.ColorIndex}
lemma Tarmac.more (h : Tarmac i J F V U D θ σ μ x Q E A) (he : A ≤ M) : Tarmac i J F V U D θ σ μ x Q E M :=
  ⟨h.warm.more he,h.h,h.hUnit,h.curtain.lower le_rfl he,strip_mono h.arise le_rfl he,strip_mono h.corners le_rfl he,h.greet,h.deep, climbBill le_rfl h.harbor_in he, climbBill le_rfl h.harbor_post he,climbBill le_rfl h.harbor_lamp he,climbBill le_rfl h.pot he,h.cargo_in.mono le_rfl he,h.summit_home⟩

-- coins converge with independently issued height, no A0 difference hypothesis.
structure TollDelta (G : Gauge) (T : Model P K) (B Q B' Q' : Bed) (σ μ : ℝ) (E : ℕ) (A δ : ℝ) : Prop where
  nonneg : 0 ≤ δ
  sea : (minusRows (fluct G T B) (fluct G T B')).strip μ (A*δ) -- no strength on Φ
  beacon : (minusRows (beams G T B) (beams G T B')).strip μ (A*δ)
  stake : AuditLine (install (beams G T B)-install (beams G T B')) (spotCost P.L σ) (E+2) (A*δ) (A*δ)
  lake : AuditLine (plain (pilot (G:=G) T B) - plain (pilot (G:=G) T B')) (spotCost 1 σ) (E+2) (A*δ) (A*δ)
  shift_in : Within (lawn _) μ (δ*A) (comfort (G:=G) T B-comfort (G:=G) T B')
  ahead : Within (lawn _) σ (δ*A) (onTop G Q-onTop G Q')
lemma TollDelta.more (h : TollDelta G F V U Z N σ μ E A η) (hf : A ≤ M) : TollDelta G F V U Z N σ μ E M η := by
  have hm : A*η≤M*η := mul_le_mul_of_nonneg_right hf h.nonneg
  have he : η*A≤η*M := mul_le_mul_of_nonneg_left hf h.nonneg
  exact ⟨h.nonneg,strip_mono h.sea le_rfl hm,strip_mono h.beacon le_rfl hm, climbBill le_rfl h.stake hm,climbBill le_rfl h.lake hm,h.shift_in.mono le_rfl he, h.ahead.mono le_rfl he⟩
lemma Tarmac.delta₀ (h : Tarmac i J F V U D θ σ μ x Q E A) (he : 0≤ η) : TollDelta G F V U V U σ μ E A η := by
  have hx : 0≤ A:= zero_le_one.trans h.warm.height
  have hc {α β : Type} (K : Row α β) : (minusRows K K).strip μ (A*η) := by unfold minusRows; simp only [sub_self]; exact zero_cost _ (mul_nonneg hx he)
  refine ⟨he,hc _,hc _,line_empty h.harbor_post (by positivity),line_empty h.pot (by positivity),?_,?_⟩ <;> rw [sub_self] <;> exact Within.zero (by positivity)
end graft
end Parapet
end YM.WilsonBulk
