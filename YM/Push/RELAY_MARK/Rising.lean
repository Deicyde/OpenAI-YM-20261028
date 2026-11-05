import YM.Next.FOUNDATIONS.JetReads
import YM.Push.RELAY_MARK.Span

/-!
# Truncation, support and triangular pricing

This path to RBin retains the existing t-weighted filtration (factor
number is what orders the `t`-budget), and uses **lex** with that number
first for refining by engineering weight. Higher factor corrections need not
prove vanishing to the same engineering order in this version. Hol projection
itself still reads every engineering weight through d.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set Next.Foundations Wilson Lattice RG Source Source.Drops Labels MvPolynomial
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Pointwise
variable {G : Gauge} {d : ℕ}

def stamp (m : ℕ × ℕ) : ℕ ×ₗ ℕ := toLex (m.2,m.1)




def sector (m : ℕ × ℕ) : Submodule ℂ (Pol G) := MvPolynomial.weightedHomogeneousSubmodule ℂ bidegree m

def weight (a : Key G →₀ ℕ) := Finsupp.weight bidegree a

def rise (m : ℕ × ℕ) : Submodule ℂ (Pol G) := restrictSupport ℂ {a | stamp m ≤ stamp (weight a)}
def above (m : ℕ × ℕ) : Submodule ℂ (Pol G) := restrictSupport ℂ {a | stamp m < stamp (weight a)}

/-- S_R for factor number only (no threshold). -/
def floorSlots (k : ℕ) : Submodule ℂ (Pol G) := rise (0,k)

lemma of_sector (m : ℕ × ℕ) (p : Pol G) : p∈sector m ↔ pureDegree p m.1 m.2 := Iff.rfl

lemma rise_sector (m : ℕ × ℕ) : sector m (G:=G) ≤ rise m := by
  intro p hp; apply (mem_restrictSupport_iff ℂ).2
  intro a ha
  have he : weight a = m := (of_sector _ _).1 hp (mem_support_iff.mp ha)
  change stamp m ≤ stamp (weight a)
  rw [he]

lemma rise_anti {a b : ℕ × ℕ} (h : stamp a ≤ stamp b) : rise b (G:=G) ≤ rise a :=
    restrictSupport_mono ℂ fun _ he => le_trans h he
lemma above_anti {a b : ℕ × ℕ} (h : stamp a ≤ stamp b) : above b (G:=G) ≤ above a :=
    restrictSupport_mono ℂ fun _ he => lt_of_le_of_lt h he
lemma rise_later {a b : ℕ × ℕ} (h : stamp a < stamp b) : rise b (G:=G) ≤ above a :=
    restrictSupport_mono ℂ fun _ he => lt_of_lt_of_le h he

lemma stamp_slots (m : ℕ × ℕ) : stamp (0,m.2) ≤ stamp m := Prod.Lex.le_iff.mpr (Or.inr ⟨rfl,Nat.zero_le _⟩)
lemma slot_sector (m : ℕ × ℕ) : sector (G:=G) m ≤ floorSlots m.2 := le_trans (rise_sector m) (rise_anti (stamp_slots m))
lemma bySlots {a b : ℕ × ℕ} (h : a.2 < b.2) : stamp a < stamp b := Prod.Lex.lt_iff.mpr (Or.inl h)

lemma stamp_monotone {a b : ℕ × ℕ} (he : stamp a ≤ stamp b) : a.2 ≤ b.2 := Prod.Lex.monotone_fst _ _ he

lemma sector_mul {m n : ℕ × ℕ} {p q : Pol G} (hp : p∈sector m) (hq : q∈sector n) : p*q∈sector (m+n) :=
  MvPolynomial.IsWeightedHomogeneous.mul (w:=bidegree) ((of_sector _ _).1 hp) ((of_sector _ _).1 hq)

lemma weight_plus (a b : Key G →₀ ℕ) : weight (a+b)=weight a+weight b := map_add ..
private lemma le_stamp_add (a b m n : ℕ × ℕ) (h : stamp a ≤ stamp b) (e : stamp m ≤ stamp n) : stamp (a+m) ≤ stamp (b+n) := by
  rcases Prod.Lex.le_iff.mp h with h|h <;> rcases Prod.Lex.le_iff.mp e with e|e <;>
    rw [Prod.Lex.le_iff] <;> simp only [stamp, ofLex_toLex, Prod.fst_add, Prod.snd_add] at * <;> omega

private lemma lt_stamp_add (a b m n : ℕ × ℕ) (h : stamp a ≤ stamp b) (e : stamp m < stamp n) : stamp (a+m) < stamp (b+n) := by
  rcases Prod.Lex.le_iff.mp h with h|h <;> rcases Prod.Lex.lt_iff.mp e with e|e <;>
    rw [Prod.Lex.lt_iff] <;> simp only [stamp, ofLex_toLex, Prod.fst_add, Prod.snd_add] at * <;> omega

lemma rise_mul {m n : ℕ × ℕ} {p q : Pol G} (hp : p∈rise m) (hq : q∈rise n) : p*q∈rise (m+n) := by
  classical
  apply (mem_restrictSupport_iff ℂ).mpr
  intro i hi
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hi)
  change stamp (m+n) ≤ stamp (weight (a+b))
  rw [weight_plus]
  exact le_stamp_add _ _ _ _ ((mem_restrictSupport_iff ℂ).mp hp ha) ((mem_restrictSupport_iff ℂ).mp hq hb)

lemma rising_mul {m n : ℕ × ℕ} {p q : Pol G} (hp : p∈rise m) (hq : q∈above n) : p*q∈above (m+n) := by
  classical
  apply (mem_restrictSupport_iff ℂ).mpr
  intro i hi
  obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hi)
  change stamp (m+n) < stamp (weight (a+b))
  rw [weight_plus]
  exact lt_stamp_add _ _ _ _ ((mem_restrictSupport_iff ℂ).mp hp ha) ((mem_restrictSupport_iff ℂ).mp hq hb)

lemma slots_mul {m n : ℕ} {p q : Pol G} (hp : p∈floorSlots m) (hq : q∈floorSlots n) : p*q∈floorSlots (m+n) := by
  unfold floorSlots; rw [show (0,m+n) = ((0,m)+(0,n) : ℕ × ℕ) from rfl]
  apply rise_mul (m:=(0,m)) (n:=(0,n)) hp hq

lemma slots_error {m n : ℕ} {p q u v : Pol G} (hp : p∈floorSlots m) (hq : q∈floorSlots n)
    (he : u-p∈floorSlots (m+1)) (hf : v-q∈floorSlots (n+1)) :
    u*v - p*q ∈ floorSlots (m+n+1) := by
  have hu : u ∈ floorSlots m := by
    rw [← sub_add_cancel u p]
    exact Submodule.add_mem _ ((rise_anti (by exact (bySlots (Nat.lt_succ_self m)).le)) he) hp
  rw [show u*v - p*q=u*(v-q)+(u-p)*q by ring]
  apply Submodule.add_mem
  · rw [add_assoc]; exact slots_mul hu hf
  rw [add_right_comm]; exact slots_mul he hq

lemma sector_limited (m : ℕ × ℕ) (h : m.1 ≤ d) : sector (G:=G) m ≤ limited G d := by
  intro p hp
  apply (mem_restrictSupport_iff ℂ).2
  intro i hi
  change height i ≤ _
  apply le_trans (b:=m.1) _ h
  have he := (of_sector _ _).1 hp (mem_support_iff.mp hi)
  rw [weight_slot] at he
  exact le_of_eq (congr_arg Prod.fst he)

def capping (G : Gauge) (d : ℕ) : Pol G →ₗ[ℂ] Pol G := ∑ i ∈ Finset.range (d+1), tier i
lemma cap_is (p : Pol G) (d : ℕ) : capRead d p=capping G d p := by simp [capping,capRead]
lemma cap_sub (d : ℕ) (p q : Pol G) : capRead d (p-q)=capRead d p-capRead d q := by simp only [cap_is,map_sub]
lemma cap_preserves (d : ℕ) {p : Pol G} {S : Set (Key G →₀ ℕ)} (h : p ∈ restrictSupport ℂ S) : capRead d p ∈ restrictSupport ℂ S := by
  classical
  apply (mem_restrictSupport_iff ℂ).mpr
  intro i hi
  apply (mem_restrictSupport_iff ℂ).mp h
  apply mem_support_iff.mpr
  have he := mem_support_iff.mp hi
  rw [coeff_capRead] at he
  split at he
  · exact he
  simp at he

/- Truncating any factor does not affect capRead of products. -/



end YM.Push.Mark
