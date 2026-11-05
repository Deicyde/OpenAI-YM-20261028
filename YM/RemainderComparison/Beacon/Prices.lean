import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Wing

/-!
# Arbitrary-depth truncation of the intrinsic real graded E6 densities

One pruning/tool for clause A. Re-use the full calibrated log labels. `Height.beacon`
is simultaneous exponential credit in degree, seed shares and shape expenditure -- not
claiming *just* support radius pays an inverse forced rate. Gives weighted real
derivative estimates uniform in the period, in the actual `Temp` domains of E6.
Remaining known-low germs still need analysis (can include mask/profile failure costs
and additional small-field factors). No mask drops here: all large labels are paid but
retained. The threshold on shape is allowed a fixed-order-dependent multiple of the
existing cutoff. No regularity of inherited E in coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Beacon
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext.Repeat Height
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ}
    {χ : Chi} {H : Cash W s μ L Q o α T R}
local notation "D" => Height.grow G L s

-- the key extra-pay criterion
lemma weight (N : Captain H j C' d v Y A b r B q k χ)
    (ht : Armada Q L μ a s i B j k) (n : ℕ) (hd : 1 ≤ D) (h : Heavy N.conduit)
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (D*salary Q L μ B s j k) i ≤ 1/2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> beacon H z*N.markΦ z n) a
        (collars G i s j n * (D*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  intro x
  have hy:= log_hit_tail _ _ _ H.testS
    (stable N hd h i a ht.delta ht.little ht.earned hs hp) (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero,mul_one] at hy
  let v:= collars G i s j n
  have he:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hv:0 ≤ v:=by unfold v collars Reserves.polyPrice; have he := ht.delta; positivity
  have hz z : 0 ≤ N.markΦ z n:= mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  have hm z : 0 ≤ beacon H z := mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hd) _) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hW := budget_scale hv hy
  refine budget_mono hW (fun z=>?_) fun z=> ?_
  · dsimp only; split
    · exact mul_nonneg (mul_nonneg (hm _) (hz z)) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split
  next hx =>
    rw [if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),wield N]
    let y:ℝ:=coverNumber (radiusB s) (reachability (H:=H) z); have hg:0 ≤ y:= Nat.cast_nonneg _
    change beacon H z * ((shiftG s*(1+y))^(n*j)*N.design z) *Real.exp (a*y) ≤
      v*(beacon H z*N.design z*Real.exp ((a+i)*y))
    rw [mul_pow, add_mul a i, Real.exp_add]
    apply le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (polynomial_cost ht.delta hg _) (pow_nonneg he _)) (N.pvc z)) (hm _)) (Real.exp_pos _).le)
    unfold v collars Reserves.polyPrice; apply le_of_eq; ring
  exact hW.1 z

-- depth in fine length units of the actual letters, including position-weighted
-- costs in `H.shapeW`; not evaluation-point-dependent

def large (H : Cash W s μ L Q o α T R) (m : ℕ) (w : ℝ) (z : H.fragrances) :=
  m ≤ Height.degree H z ∨ 1 ≤ Height.overlap H z ∨ w ≤ Height.depth H z

lemma takes (m : ℕ) (hd : 1≤ D) (w : ℝ) (hu : D^m ≤ Real.exp (Q.ε*w))
    (hT : D^m ≤ Real.exp (Q.mark L μ s)) (z) (hz : large H m w z) : D^m ≤ beacon H z := by
  let a := D ^ Height.degree H z
  have he : 1 ≤ a := one_le_pow₀ hd
  have hp: 1 ≤ Real.exp (Q.ε*Height.depth H z) := Real.one_le_exp (mul_nonneg Q.usable.le
      (sum_nonneg fun i _=> H.positive_volume _))
  have ht':0≤Q.mark L μ s:= H.laws.acquired.marked
  have hM:1≤Real.exp (Q.mark L μ s*Height.overlap H z):=Real.one_le_exp (mul_nonneg ht' (Nat.cast_nonneg _))
  rcases hz with h|h|h
  · exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right (zero_le_one.trans he) hM).trans
        (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le he hM)) hp))
  · exact hT.trans ((Real.exp_monotone (le_mul_of_one_le_right ht' (show (1:ℝ) ≤ Height.overlap H z by exact_mod_cast h))).trans
        ((le_mul_of_one_le_left (Real.exp_pos _).le he).trans (le_mul_of_one_le_right (zero_le_one.trans (one_le_mul_of_one_le_of_one_le he hM)) hp)))
  exact hu.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans
          (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_mul_of_one_le_of_one_le he hM)))

-- Expose derivative certificate and bookkeeping at exactly same addresses on all fields.
lemma paid (N : Captain H j C' d v Y A b r B q k χ)
    (ht : Armada Q L μ a s i B j k) (n : ℕ) (hd : 1 ≤ D) (h : Heavy N.conduit)
    (hs : degreePrice (radiusB s) (D*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (D*salary Q L μ B s j k) i ≤ 1/2)
    (m : ℕ) (w : ℝ) (hu : D^m ≤ Real.exp (Q.ε*w)) (hz : D^m ≤ Real.exp (Q.mark L μ s)) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> if large H m w z then N.markΦ z n else 0) a
        ((D^m)⁻¹ * (collars G i s j n * (D*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  intro x
  have hD: 0 ≤ (D^m)⁻¹:= inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hd) _)
  have hv:= budget_scale hD (weight N ht n hd h hs hp x)
  have he:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hq z:0≤ N.markΦ z n:= mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  refine budget_mono hv (fun z=>?_) fun z=> ?_
  · split
    · apply mul_nonneg _ (Real.exp_pos _).le; dsimp only; split_ifs <;> first|exact hq _| rfl
    exact le_rfl
  dsimp only; split
  next hx=>
    by_cases hg : large H m w z
    · rw [if_pos hg]; rw [← mul_assoc,← mul_assoc]; exact mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_left (hq z) (by have hk:= mul_le_mul_of_nonneg_left (takes m hd w hu hz z hg) hD; rw [inv_mul_cancel₀ (pow_ne_zero _ (zero_lt_one.trans_le hd).ne')] at hk; exact hk))
        (Real.exp_pos _).le
    rw [if_neg hg,zero_mul]; simpa only [if_pos hx] using hv.1 z
  simp

open Packets Stained
-- replacing arity-2 simplification in Height.Tryouts
structure core (H : Cash W s μ L Q o α T R) (z : H.fragrances) (m : ℕ) (w : ℝ) : Prop where
  arity : Height.degree H z < m
  shape : Height.depth H z < w
  steps : z.fst+1 < m
  no_packet (u : Option (Fin z.fst)) : Ac.Spark H.supportP (z.2 u).val ∧ troupe T R Q.halo (radiusB s) (z.2 u).val ∧
      (z.2 u).val.toLeft=∅ ∧ own (z.2 u).val = ∅

lemma remains (χ : Chi) (m : ℕ) (w : ℝ) (z : H.fragrances) (hb : ¬large H m w z)
    (V : Config G c) (hy : stream H χ V z ≠ 0) : core H z m w := by
  have h₁: Height.degree H z < m:= lt_of_not_ge (fun h=> hb (Or.inl h))
  have h₂: Height.overlap H z < 1:= lt_of_not_ge (fun h=> hb (Or.inr (Or.inl h)))
  have h₃: Height.depth H z < w:= lt_of_not_ge (fun h=> hb (Or.inr (Or.inr h)))
  have hh i : Ac.Spark H.supportP (z.2 i).val ∧ troupe T R Q.halo (radiusB s) (z.2 i).val := by
    by_contra hp
    have hl : leaflet H χ V (z.2 i) = 0:= by unfold leaflet likely; simp_rw [vacuity V (z.2 i) hp,sum_const_zero,mul_zero]
    exact hy (by unfold stream Gas.term; rw [Finset.prod_eq_zero (Finset.mem_univ i) hl,mul_zero,zero_div])
  have he l : 1 ≤ ((z.2 l).val).card := Nat.succ_le_of_lt (Finset.card_pos.mpr (hh l).1.1)
  refine ⟨h₁,h₃,lt_of_le_of_lt ((le_trans ?_ (Finset.sum_le_sum (s:=univ) (fun i _ => he i))).trans (Nat.le_add_left (Height.breadth H z) (Height.acme H z))) h₁,fun i=>?_⟩
  · simp
  obtain ⟨hs,hv⟩:=hh i; let p := (z.2 i).val
  have hg : Cash.numP p < 1:= lt_of_le_of_lt (single_le_sum (f:=fun i=>Cash.numP (z.2 i).val) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)) h₂
  have hr:p.toLeft=∅:= Finset.not_nonempty_iff_eq_empty.mp fun ⟨x,hx⟩=>by
    apply not_le_of_gt hg; have hx' : 1≤x.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr (hv.1.checkpoints x hx).1
    exact hx'.trans (show x.shares ≤ Cash.numP p from Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hx))
  refine ⟨hs,hv,hr,Finset.not_nonempty_iff_eq_empty.mp ?_⟩; rintro ⟨j,hj⟩
  obtain ⟨k,hk⟩:= (R.activities.forced j).inventory_ne
  obtain ⟨b,hb,-⟩:= hv.2.2 j hj k hk
  unfold roster Packets.store at hb; rw [hr] at hb; simp at hb
end YM.RemainderComparison.Beacon
