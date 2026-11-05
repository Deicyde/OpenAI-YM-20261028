import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Trail

/-!
# Full address support budgets on Itinerary

Even though grade wires estimated per route with no distance summation,
length movements all counted; full volumes of e neighborhoods. Use endpoint
Armed (including queries that result in zero). Count only once on a torus.
Supports large enough eventually to include V table, masks, geometry and
post-cov arguments. This proof keeps true shapes, not disjoint prescriptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse.Itinerary
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {B m d u : ℕ} {A ε Q C : ℝ}

lemma sigmaB {ι : Type*} {α : ι → Type*} [∀ i, Fintype (α i)] {W : Sigma α → ℝ}
    (hg : ∀ i,0 ≤ W i) {u : ι→ℝ} (ht : SumBudget u C) (he : ∀ i, ∑ j : α i,W ⟨i,j⟩ ≤ u i) : SumBudget W C := by
  apply budget_fiberwise Sigma.fst hg _ ht
  intro i s hi
  let b : α i ↪ Sigma α := ⟨Sigma.mk i,fun p q h=>Sigma.mk.inj_iff.mp h|>.2|>eq_of_heq⟩
  have he' : s ⊆ univ.map b := by
    rintro ⟨j,p⟩ h; have hj : j=i := hi _ h; subst j; exact mem_map.mpr ⟨p,mem_univ _,rfl⟩
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg he' fun i _ _ => hg _) _
  rw [sum_map]; exact he i

abbrev Ledger (f : Side) (u : ℕ) := Σ n : ℕ,Bond f × Itinerary f (n+u)
def receipt (S : StepData c f) (B m u : ℕ) (k : Ledger f u) := visited S B m k.2.1 k.2.2

def density (L : Side) := L.val^4 * Fintype.card Axis

def abundance (L : Side) (d : ℕ) : ℝ := (Animals.ballCost (d+2):ℝ)*density L

lemma count_card (v : Bond f) (S : StepData c f) : ∀ n : ℕ,
    (∑ l : Itinerary f n, if Armed S d v l then (1:ℝ) else 0) ≤ (abundance S.patch.L d)^n := by
  intro n; induction n generalizing v with
  | zero =>
    let k : Itinerary f 0 := ()
    rw [sum_eq_single k]
    · rw [pow_zero, if_pos (show Armed S d v k from trivial)]
    · intro i _ hi; exact (hi (Subsingleton.elim (α:=Unit) _ _)).elim
    simp
  | succ n ih =>
    let K := abundance S.patch.L d
    rw [sum_components]
    let D := withinH (atEdge S) (atEdge S v) (d+2)
    calc
      _ ≤ ∑ j : Bond f, (if j ∈ D then K^n else 0) := by
        apply sum_le_sum; intro j _; by_cases he : hop S d v j
        · simp only [Armed,next_bank,after_bank, he, true_and]; rw [if_pos ((joins ..).mpr (hop_cost he))]; exact ih j
        simp only [Armed,next_bank,he,false_and, ite_false,sum_const_zero]
        split
        next hk => unfold K abundance; positivity
        next hk => exact le_rfl
      _ ≤ _ := by
        rw [← sum_filter, show univ.filter (fun i=>i∈D)=D from by ext; simp]
        rw [sum_const,nsmul_eq_mul,pow_succ']
        exact mul_le_mul_of_nonneg_right (by unfold abundance; exact_mod_cast count_near (perch S) (atEdge S v) (d+2)) (by unfold K abundance; positivity)

lemma ball (g u : ℕ) (k : ℕ) : ballCost ((k+u+1)*g) ≤ ballCost ((u+1)*g)*16^k := by
  have he (k : ℕ) : k+u+1 ≤ (u+1)*2^k := by
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ]; nlinarith only [ih, Nat.zero_le n,Nat.zero_le u]
  unfold Animals.ballCost; rw [show (16:ℕ)=2^4 by norm_num, ← pow_mul, Nat.mul_comm 4 k, pow_mul, ← mul_pow]
  apply pow_le_pow_left'; nlinarith [he k,show 1≤2^k by exact Nat.one_le_iff_ne_zero.mpr (by positivity)]

/-- Pay at geometric ratio after buying all stamps from every address, so
slack used BEFORE old-tree/geodesic shortening. `u` counts additional
obligatory entry hops beyond chain correction order. For any halo size m.
-/
def expoHead (L : Side) (m B d u : ℕ) (A : ℝ) := (ballCost ((u+1)*(m*B+1)):ℝ)*density L *
    (abundance L d)^u * Real.exp (A*((u:ℝ)+1)*steady m)
def expoRatio (L : Side) (m d : ℕ) (A ε : ℝ) := 16 * (abundance L d) * Real.exp (A*steady m+2*ε)

lemma scalar (S : StepData c f) (B m d u : ℕ) (A ε : ℝ) (w : Ledger f u → ℝ)
    (hw : ∀ k,0 ≤ w k) (hc : 0≤C) (hq : 0≤Q) (hi : ∀ k : Ledger f u,
      w k ≤ if Armed S d k.2.1 k.2.2 then C * Q^k.1 else 0)
    (he : d+2 ≤ m*B) (hp : 0 < B) (hA : 0 ≤ A) (hs : Q * expoRatio S.patch.L m d A ε ≤ 1/2) :
    Sales B A ε (receipt S B m u) w Sigma.fst (2*(expoHead S.patch.L m B d u A * C)) := by
  let W := Reserves.tariff w (fun k=> (k.1:ℝ)) (fun _=>0) ε
  let X := receipt S B m u
  let P := abundance S.patch.L d
  let H := expoHead S.patch.L m B d u A
  let y := expoRatio S.patch.L m d A ε
  have hP : 0 ≤ P := by unfold P abundance; positivity
  have hy : 0≤y := by unfold y expoRatio abundance; positivity
  have hH : 0 ≤ H := by unfold H expoHead abundance; positivity
  have ht : SumBudget (fun n : ℕ => (H*C)*(1/2:ℝ)^n) (2*(H*C)) := by
    have he := budget_geometric (mul_nonneg hH hc) (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)
    convert he using 1; ring
  refine ⟨hw, fun x => sigmaB (fun i => ?_) ht ?_⟩
  · change 0 ≤ if _ then W i*Real.exp _ else 0
    unfold W Reserves.tariff; split <;> have := hw i <;> positivity
  intro n
  let T k := if x∈X k then W k * Real.exp (A*coverNumber B (X k)) else 0
  let k := n+u
  let Bx v (l : Itinerary f k) : Ledger f u := ⟨n,v,l⟩
  let E := C*Q^n*Real.exp (2*ε*n)*Real.exp (A*(k+1:ℕ)*steady m)
  let Y := withinH (atEdge S) x ((k+1)*(m*B+1))
  have hE : 0≤E := by unfold E; positivity
  have hR v : (∑ l : Itinerary f k, T (Bx v l)) ≤ (if v∈Y then E*P^k else 0) := by
    have HH v l (hn : x∈X (Bx v l)) (ht : Armed S d v l) : v∈Y := (joins ..).mpr
      ((separation_comm ..).trans_le (tenure (show d+2 ≤ m*B+1 from he.trans (by omega)) _ _ ht x hn))
    have hN v l (ho : ¬ Armed S d v l) : W (Bx v l)=0 := by
      have hh : ¬ Armed S d (Bx v l).2.1 (Bx v l).2.2 := ho
      have he := hi (Bx v l); rw [if_neg hh] at he
      unfold W Reserves.tariff; rw [le_antisymm he (hw (Bx v l)),zero_mul]
    split
    next hv =>
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (count_card (d:=d) v S k) hE)
      rw [mul_sum]; apply sum_le_sum; intro l hl
      unfold T; by_cases he' : Armed S d v l
      swap
      · rw [if_neg he',mul_zero,hN v l he',zero_mul,ite_self]
      rw [if_pos he',mul_one]; split
      next hx =>
        let p := Bx v l
        have ht := hi p; rw [if_pos (show Armed _ _ _ _ from he')] at ht
        have hk := pockets hp he v l he'
        unfold W Reserves.tariff; rw [add_zero]
        calc
          _ ≤ (C*Q^n)*Real.exp (2*ε*n)*Real.exp (A* coverNumber B (X p)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht (Real.exp_pos _).le) (Real.exp_pos _).le
          _ ≤ _ := by
            unfold E
            refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (by positivity)
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hA
      exact hE
    next hv => apply sum_nonpos; intro l hl; unfold T; split
               next hk => rw [hN v l (fun hh => hv (HH v l hk hh)),zero_mul]
               next ht => exact le_rfl
  unfold Ledger
  rw [Fintype.sum_prod_type]
  refine (sum_le_sum (fun v _ => hR v)).trans ?_
  have hc' : (Y.card:ℝ) ≤ (ballCost ((u+1)*(m*B+1)):ℝ)*16^n*density S.patch.L := by
    apply le_trans (b:=((ballCost ((k+1)*(m*B+1)):ℝ)*density S.patch.L))
    · exact_mod_cast count_near (perch S) x ((k+1)*(m*B+1))
    gcongr; exact_mod_cast ball (m*B+1) u n
  rw [← sum_filter, show (univ.filter (fun v=>v∈Y))=Y by ext; simp,sum_const,nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hc' (by positivity)).trans ?_
  have he : Real.exp (A*(k+1:ℕ)*steady m)=Real.exp (A*((u:ℝ)+1)*steady m)*Real.exp (A*steady m)^n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; unfold k; push_cast; ring
  have hY : Real.exp (2*ε*n)=Real.exp (2*ε)^n := by rw [← Real.exp_nat_mul,mul_comm]
  apply le_trans (b:=H*C*(Q*y)^n) _ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hq hy) hs n)
    (mul_nonneg hH hc))
  unfold E H P y expoHead expoRatio; rw [he,hY,Real.exp_add]; dsimp only [k]; rw [pow_add]; simp_rw [mul_pow]; exact le_of_eq (by ring)
end YM.ConnectedActivityE6.Pulse.Itinerary
