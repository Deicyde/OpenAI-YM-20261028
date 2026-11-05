import YM.MultiNext.VACUUM_STABILITY.Component.Pasture

set_option warningAsError false

/-!
# Charge every post-integration component needed by the scalar susceptibility estimate

 with the real support norms, also for all the perturbed amplitudes. There may be
attachments arbitrary powers of a single E, shifted anchors, and nonstarter/reference
strokes in the same source lists. Keep exponent stage and arbitrary finite reserves, all
per-core. Do not infer this component-form bound from cost of individual row integrals!
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Component
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Alternatives Desk Rejoin Stamp Restock
open Jets Hits Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {V I : Type} {G : Gauge} {n : Side} {B : Brush V G n} (A : Pasture I B)

namespace Pasture

def sizeTax (k : ℕ) := ((k.factorial : ℕ):ℝ)*Real.exp 1
lemma sizeTax_pos (k : ℕ) : 1 ≤ sizeTax k := one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos k)
  (Real.one_le_exp zero_le_one)

def feast (f : I → ℝ) (k M : ℕ) (s : Fruit) :=
    (1+((∑ i∈A.bud s,coverNumber M (A.sites i):ℕ):ℝ))^k * ∏ i∈A.bud s,f i

lemma feast_nn {f : I → ℝ} (hf : ∀ i,0≤f i) (k M : ℕ) (s : Fruit) : 0≤feast A f k M s :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ => hf _)

private lemma budget_inj {ι ε : Type} (t : ι → ε) (h : Injective t) {u : ε → ℝ} {s : ℝ} (hh : SumBudget u s) :
    SumBudget (u ∘ t) s := by
  have he := hh.2.1.comp_injective h
  exact ⟨fun i => hh.1 _, he, (Summable.tsum_le_tsum_of_inj t h (fun i _ => hh.1 i) (fun i => le_rfl) he hh.2.1).trans hh.2.2⟩

lemma places (k M : ℕ) {f : I → ℝ} {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hh : siteUnit M * t ≤ 1)
    (h : Ac.Hit A.sites M f (a+2) t) : Ac.Hit (ends B) M (feast A f k M) a (sizeTax k*(Real.exp t-1)) := by
  have hf := (Absolute.burden A.origin h).1
  let q i := ((coverNumber M (A.sites i):ℕ):ℝ)
  let g i := f i * Real.exp (q i)
  have he i : 0 ≤ g i := mul_nonneg (hf _) (Real.exp_pos _).le
  have hs : Ac.Hit A.sites M g (a+1) t := by
    intro x; have he i : f i * Real.exp ((a+2)*q i)=g i * Real.exp ((a+1)*q i) := by
      unfold g; rw [mul_assoc, ←Real.exp_add]; congr 2; ring
    have hx : SumBudget (fun i => if x∈A.sites i then f i*Real.exp ((a+2)*q i) else 0) t := h _
    simp_rw [he] at hx; exact hx
  intro x
  have he := Ac.forest A.sites M ha he hs hh ht x
  let C := sizeTax k
  have hc : 0 ≤ C := zero_le_one.trans (sizeTax_pos _)
  refine Absolute.compare (permit_mul (budget_inj A.bud A.unique he) hc) ?_ fun i => ?_
  · intro i; split; exact mul_nonneg (feast_nn A hf ..) (Real.exp_pos _).le; exact le_rfl
  split; rename_i hi
  · have hI : x∈(A.bud i).biUnion A.sites := A.lives i ▸ hi
    dsimp only [Ac.roots,Function.comp]; rw [if_pos ⟨A.connected i,hI⟩]; rw [A.lives]
    let d := ∑ j∈A.bud i, coverNumber M (A.sites j)
    have hr : (1+(d:ℝ))^k ≤ C*Real.exp d := by
      have hp : (1+(d:ℝ))^k ≤ k.factorial*Real.exp (1+d) := (inv_mul_le_iff₀ (show (0:ℝ)<k.factorial by positivity)).mp
        (Absolute.little (Absolute.rexp _ (by positivity : (0:ℝ)≤(1+d))) k)
      unfold C sizeTax; simpa only [Real.exp_add,mul_assoc] using hp
    have hG : ∏ j∈A.bud i,g j=(∏ j∈A.bud i, f j) * Real.exp d := by unfold g d; rw [Finset.prod_mul_distrib, ←Real.exp_sum]; simp [q,Nat.cast_sum]
    unfold feast; rw [hG]
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr (prod_nonneg fun i _ => hf _)) (Real.exp_pos _).le)
    change C*_ * _*_ ≤ C*_; apply le_of_eq; ring
  exact mul_nonneg hc (he.1 _)

structure Visited (P : BudgetPoint) (L : V → Support n → Prop) : Prop where
  ok i : P.Regular (B.u i).zone (B.u i).stamp.ink
  legible i : Legible P (B.pack i) (B.d i).ink
  enrollment i x : x∈(A.hue i).support → L x (A.sites i)

variable [Fintype V]

/-- Earlier estimate on ONE literal component with first-system atom weights and any
compulsory extra payment on forced components. Input r is pre-bought outgoing exponent.
k any fixed overhead on size after-L. -/
structure ProductCost (P : BudgetPoint) (z : V → ℂ) (c r κ : ℝ) : Prop where
  tall : 0≤r
  estimates : ∃ (k : ℕ) (C t : ℝ) (f : I→ℝ), 0 ≤ C ∧ 0 ≤ t ∧ siteUnit P.B*t ≤ 1 ∧
    C*(sizeTax k*(Real.exp t - 1)) ≤ c ∧ Ac.Hit A.sites P.B f (r+2) t ∧
    (∀ i, P.supBounds (B.u i).anchor (B.u i).zone ((B.u i).stamp.tell z) (C*feast A f k P.B (.inl i))) ∧
    ∀ i U, ‖(B.d i).tell z U‖ ≤ κ * (C*feast A f k P.B (.inr i))

structure PathBudget (P : BudgetPoint) (z : V→ℂ) (c r κ : ℝ) : Prop where
  guide : ∃ f : ℕ→ℝ, (∀ i, P.supBounds (B.u i).anchor (B.u i).zone ((B.u i).stamp.tell z) (f i)) ∧
        Ac.Hit (fun i => (B.u i).zone) P.B f r c
  guard : ∃ f : ℕ→ℝ, (∀ i, 0 ≤ f i ∧ ∀ U, ‖(B.d i).tell z U‖ ≤ f i) ∧
        Ac.Hit (fun i => (B.pack i).zone) P.B f r (κ*c)

lemma accomplish (P : BudgetPoint) (z : V → ℂ) (c r κ : ℝ) (hA : A.ProductCost P z c r κ) (hk : 0≤κ) :
    PathBudget (B:=B) P z c r κ := by
  obtain ⟨k,C,t,f,hC,hp,hP,hG,hH,hS,hv⟩:=hA.estimates
  have hf := (Absolute.burden A.origin hH).1
  let g i := C*feast A f k P.B i
  have he : Ac.Hit (ends B) P.B g r c := by
    intro x; refine Absolute.loosen ?_ hG
    have hx := permit_mul (A.places k P.B hA.tall hp hP hH x) hC
    let u (i) := C*(if x∈ends B i then feast A f k P.B i * Real.exp (r*coverNumber P.B (ends B i)) else 0)
    have h i : u i=(if x∈ends B i then g i * Real.exp (r*coverNumber P.B (ends B i)) else 0) := by
      unfold u g; split; exact (mul_assoc ..).symm; rw [mul_zero]
    simp_rw [←h]; exact hx
  refine ⟨⟨fun i=>g (.inl i),hS, fun x => budget_inj (fun i : ℕ => (Sum.inl i : Fruit)) Sum.inl_injective (he x)⟩,
    fun i=>κ*g (.inr i),fun i=>⟨mul_nonneg hk (mul_nonneg hC (feast_nn A hf ..)),hv i⟩,fun x=>?_⟩
  let p (i : ℕ) := if x∈(B.pack i).zone then g (.inr i)* Real.exp (r*coverNumber P.B (B.pack i).zone) else 0
  have hp : SumBudget p c := budget_inj (fun i : ℕ => (Sum.inr i : Fruit)) Sum.inr_injective (he x)
  have ht i : (if x∈(B.pack i).zone then κ*g (.inr i)*Real.exp (r*coverNumber P.B (B.pack i).zone) else 0)=κ*p i := by unfold p; split; exact mul_assoc ..; rw [mul_zero]
  simp_rw [ht]; exact permit_mul hp hk

omit [Fintype V] in
lemma lottery {L : V → Support n → Prop} {P} (h : A.Visited P L) (hv : Widens L) (i : Fruit) (x : V) :
    x ∈ (calls B i).support → L x (ends B i) := by
  intro ht; by_contra he
  apply Finsupp.mem_support_iff.mp ht
  rw [A.full,Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero; intro j hj
  apply Finsupp.notMem_support_iff.mp; intro hz; apply he; refine hv _ _ _ ?_ (h.enrollment _ _ hz)
  rw [A.lives]; exact fun k hk => Finset.mem_biUnion.mpr ⟨j,hj,hk⟩
end Pasture
end YM.Multi.Vacuum.Component
