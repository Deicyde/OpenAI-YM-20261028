import YM.Push.ABSOLUTE_SUMS.Mixed
/-!
# Uniform headcount charge

A mixed (E6 ingress) member of the analyticity supplies has vertices already bought at
rootHit=O(betaF^rate). Can pay a factor growing as nearly one coupling power PER HEAD
(determined by -rate) *without* rebuilding any analytic estimate. Includes compulsory
inventories, keeps marks on the ENTIRE attached set, not just the final polymer tally. Standard
analogue also applies to second graph series, provided we keep this head charge when passing
through its input solvency. delta rules now invoked AFTER L, doesn't feed back to
ofHarness etc for analytic launch itself. Not inferring supBounds here yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Mixed.Coupons
open Lattice Wilson RG Finset Pressure Trees Reserves
open scoped Classical Topology BigOperators
variable {n : Side} {ι : Type*} {η s a b r c e t : ℝ}

lemma inflate (X:ι→Support n) (B:ℕ)(w:ι→ℝ)(h:Ready X B w a b r c) (hs:0<s) (hp: Trees.degreePrice B (s*b) r ≤ t)(hv:t<1) : Ready X B (fun i=>s*w i) a (s*b) r t:=by
   refine ⟨mul_pos hs h.1,h.2.1,hp,hv,fun i=>mul_nonneg hs.le (h.2.2.2.2.1 i),fun x=>?_⟩
   have hx:= budget_scale hs.le (h.2.2.2.2.2 x)
   convert! hx using 2; rename_i i; split <;> simp_all only [mul_assoc,mul_zero]
lemma collect {c f:Side}(S:StepData c f)(l B : ℕ)(b: Costs)(X:ι→ Support c)(w d:ι→ℝ)(p:Stores S→ℝ)
   (hr : b.Buy S.patch.L l B) (ha : Accounts S l B b X w d p)
   (hs:0<s)(hp: Trees.degreePrice B (s*b.rootHit) b.reserveTree ≤ t)(hv:t<1)(m k r : ℕ)(T:ℝ): Ac.Hit (fun i:Finset (Alphabet S ι)=>i.biUnion (foot S l B X)) B
    (fun i=> s^i.card * selected S l B b X w d p m k r T i) b.exponent (extract b.reservePoly k T (b.markSeed*r) * treeYield (s*b.rootHit) t m):=by
  let Y := foot S l B X; let g := costs S l B p w
  have he i : 0 ≤ g i := by
    rcases i with A|i
    · unfold g costs; dsimp only [Sum.elim]; split; next hh => exact (ha.packetBound A hh).1
      exact le_rfl
    exact ha.holds i
  have ht i : 0 ≤ lengths S b d i := by
    rcases i with A|i
    · exact mul_nonneg hr.extra (Nat.cast_nonneg _)
    exact ha.extra i
  have hh := inflate Y B (tariff g (lengths S b d) (stamp S b) b.reservePoly) (ready_vertices S l B b X w d p hr ha) hs hp hv
  let z i:=s*g i
  have heq : (fun i=>s*tariff g (lengths S b d) (stamp S b) b.reservePoly i)=tariff z (lengths S b d) (stamp S b) b.reservePoly:= funext (fun i=>(mul_assoc ..).symm)
  rw [heq] at hh
  intro x
  let Q:=Allowed S l B b X d m r T
  have hM i (h:Q i): T≤ charges S l B X b d i∧ b.markSeed*r≤ ∑ j∈i,stamp S b j:=by
      refine ⟨h.2.2.2,?_⟩; simp only [stamp,←mul_sum]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast h.2.2.1) hr.marked
  have h:= Reserves.sets Y B z (lengths S b d) (stamp S b) (fun i=> mul_nonneg hs.le (he i)) ht hr.eps hr.price hh m k x Q (fun i _ _ _ h=>hM i h)
  convert! h using 2; rename_i i
  dsimp only
  by_cases hx:x∈i.biUnion Y; swap
  · rw [if_neg hx]; unfold rooted; split <;> simp [hx]
  by_cases hl: Q i
  · rw [if_pos hx,selected,if_pos hl,if_pos ⟨hl,hl.2.1⟩, rooted,if_pos ⟨hl.1,hx⟩]; unfold Price z; rw [prod_mul_distrib,prod_const]; unfold currency Y g charges; ring
  rw [if_pos (show x∈ i.biUnion (foot S l B X) from hx),selected,if_neg (show ¬Allowed S l B b X d m r T i from hl),mul_zero,zero_mul,if_neg (show ¬ (Q i ∧ m ≤ i.card-1) from fun h=>hl h.1)]
end YM.Push.AbsoluteSums.Mixed.Coupons
