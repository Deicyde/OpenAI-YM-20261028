import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.LogAction

set_option warningAsError false

/-!
# Convergence and output K prices under AbsoluteSums criteria

Consumable with any positive absolute estimates on the *components*
(e.g. spelled/mixed prices); don't require the physical weights be
positive. Does NOT produce estimates on a sector integrand or on
B/δ/q from the transfer/schedule; see `FromWords` for separate lower
level entry. On K use the receipt even for the merged labels correcting
*both* costs: exclusion and scalar compensation. Empty-address inflation
not required here (require actual labels with nonempty footprints).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Price
open Lattice RG Wilson AbsoluteSums Ursell Trees Finset Filter Function Attach Restore OmitClusters
open scoped Topology Classical BigOperators
variable {n : Side} {ι κ : Type*} (X : ι → Support n) (B : ℕ)

lemma permit {b : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B b a γ δ q)
    {w : ι → ℝ} (he : ∀ i, 0 ≤ w i ∧ w i ≤ b i) : Ready X B w a γ δ q := by
  obtain ⟨hf,h1,h2,h3,-,h4⟩ := h
  exact ⟨hf,h1,h2,h3,fun i => (he i).1,AbsoluteSums.Labels.raise_prices X B (fun i => (he i).1) h4 fun i => (he i).2⟩

lemma priced_total {b : ι → ℝ} {a c : ℝ} (hb : ∀ i,0 ≤ b i) (ha : 0 ≤ a)
    (h : Ac.Hit X B b a c) (hn : ∀ i,(X i).Nonempty) : SumBudget b ((n.val^4:ℕ)*c) := by
  apply budget_mono (AbsoluteSums.Product.everyone_ne X B hb (fun i _ => hn i) h) hb
  intro i
  exact le_mul_of_one_le_right (hb i) (Real.one_le_exp (mul_nonneg ha (by positivity)))

/-- Complete log coefficients (incl inverse factorial) priced before testing V.
-/
def logPrice (b : ι → ℝ) (i : Clusters ι) := clusters (blocked X) b i.2

lemma logPrice_ne {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (i : Clusters ι) : 0 ≤ logPrice X b i := clusters_nonneg (blocked X) hb _

lemma logWeighed {b : ι → ℝ} (hn : ∀ i,(X i).Nonempty)
    {γ a δ q : ℝ} (ha : 0 ≤ a) (h : Ready X B b a γ δ q) :
    Ac.Hit (Z X) B (logPrice X b) a (γ*(1-q)⁻¹) := by
  intro x
  simpa only [logPrice,Z,currency,Nat.zero_le,true_and,pow_zero,mul_one] using
    Ursell.log_hit_tail (blocked X) X B (literal_test X hn) h ha 0 x

lemma log_bound {b u : ι → ℝ} (i : Clusters ι) (hu : ∀ j, ‖u (i.2 j)‖ ≤ b (i.2 j)) :
    ‖Restore.raw X u i‖ ≤ logPrice X b i := by
  rw [Restore.raw, Gas.term_nonneg]
  unfold logPrice clusters
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
  exact prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hu i)

variable (Y I : κ → Support n)

/-- All series in the emitted output equality, and the estimates
at the log stage itself, from per-species prices with strict degree
control. No second threshold necessary on forced to get THIS
finite-volume identity ($c$ can be large; unrooted normalization
and forced sums only checked absolutely at fixed volume). For actual
use at the RG budgets will also want resulting forced *hit* (see `issues`). -/
theorem output {b : ι → ℝ} {f : κ → ℝ} {a γ δ q c : ℝ} (hf : ∀ i, 0 ≤ f i)
    (ha : 0 ≤ a) (h : Ready X B b a γ δ q) (hK : Ac.Hit Y B f a c)
    (hX : ∀ i,(X i).Nonempty) (hY : ∀ i,(Y i).Nonempty) (hI : ∀ i,I i⊆Y i)
    (D : Support n) (u : ι → ℝ) (d : κ → ℝ) (v : Clusters ι → ℝ)
    (hu : ∀ i, Disjoint (X i) D → ‖u i‖ ≤ b i) (hd : ∀ i, ‖d i‖ ≤ f i)
    (hv : ∀ i, ‖v i‖ ≤ logPrice X b i) :
    let g := Restore.good X D u
    let full := gasTerm (both Y X) (onlyL I) D (Sum.elim d g)
    let addi := Restore.good (Z X) D (regular X u v)
    let out := gasTerm (location X Y) (flagsOut X Y I) D (K X Y I D u d v)
    Ac.Hit (Z X) B (logPrice X b) a (γ*(1-q)⁻¹) ∧ Summable (fun i => ‖v i‖) ∧
    Summable (fun i => ‖full i‖) ∧ Summable (fun i => ‖addi i‖) ∧ Summable (fun i => ‖out i‖) ∧
    (∑' i,full i) = Real.exp ((∑' i,v i) - (∑' i,addi i)) * ∑' i,out i := by
  intro g full addi out
  have hb i : 0 ≤ b i := h.2.2.2.2.1 i
  have he := logWeighed X B hX ha h
  have h' := priced_total Y B hf ha hK hY
  have hL := priced_total (Z X) B (logPrice_ne X hb) ha he fun i => Znonempty X hX i
  have hg : Summable (fun i => ‖v i‖) := hL.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) hv
  exact ⟨he,hg,Restore.output_eq X Y I D u d v hX hY hI B ha
    (permit X B h (w:=fun i => ‖g i‖) (fun i => ⟨norm_nonneg _,good_norm X D u i hb (hu i)⟩))
    (h'.2.1.of_nonneg_of_le (fun _ => norm_nonneg _) hd) hg⟩

/-- Sup costs also on the regrouped merged K. No orientation or transport
claim on an expression assembled with inputs that break the symmetry (in
particular at fixed tag outcomes). Sup is unscaled; B paid with support.
-/
def tag (b : ι → ℝ) (f : κ → ℝ) (i : Out X Y) :=
  Multiple.manyW (Sum.elim f (logPrice X b)) i.val.val

lemma tag_ne {b : ι → ℝ} {f : κ → ℝ} (hb : ∀ i,0≤b i) (hf : ∀ i, 0 ≤ f i) (i : Out X Y) :
    0 ≤ tag X Y b f i :=
  Multiple.manyW_nonneg (w:=Sum.elim f (logPrice X b)) (fun i => by rcases i with i|i; exact hf i; exact logPrice_ne X hb i) _

lemma caps {b : ι → ℝ} {f : κ → ℝ} (D : Support n) (u : ι → ℝ) (d : κ → ℝ) (v : Clusters ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hd : ∀ i, ‖d i‖ ≤ f i) (hu : ∀ i, Disjoint (X i) D → ‖u i‖ ≤ b i)
    (hv : ∀ i, ‖v i‖ ≤ logPrice X b i) (i : Out X Y) : ‖K X Y I D u d v i‖ ≤ tag X Y b f i := by
  have hp z : ‖takeBack X D u v z‖ ≤ logPrice X b z := by
    unfold takeBack; split
    next he =>
      rw [norm_neg]
      exact log_bound X _ fun j => hu _ (Finset.disjoint_left.mpr fun x hx h =>
        Finset.disjoint_left.mp he (Zcontains X z _ hx) h)
    next he => rw [norm_neg]; exact hv z
  let r := i.val.val
  have he := tag_ne X Y hb (fun i => (norm_nonneg _).trans (hd i)) i
  unfold K Attach.merged Attach.bill
  split
  · split
    · rw [manyW_norm]
      change Multiple.manyW _ r ≤ Multiple.manyW (Sum.elim f (logPrice X b)) r
      exact prod_le_prod (fun _ _ => div_nonneg (pow_nonneg (norm_nonneg _) _) (by positivity))
        (fun j _ => div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (by
          rcases j with ⟨j|j,hj⟩ <;> dsimp <;> first | exact hd j | exact hp j) _) (by positivity))
    exact norm_zero.trans_le he
  exact norm_zero.trans_le he



end YM.Push.LogIdentity.Price
