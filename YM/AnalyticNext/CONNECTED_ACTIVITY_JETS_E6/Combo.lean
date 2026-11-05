import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Trail
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# Along one spelling

Block price. Use dependent contact tape as input (no dependent casts when
integrating parameters). Includes all position combinations and true
multiplicity. `tape` number of hops. Value of chain already a matrix on
color. Trace over colors at one link/root eventually.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals  Window Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι κ : Type} {c f : Side} {S : StepData c f} {G : Gauge}

namespace Itinerary
variable {n : ℕ}

abbrev Mat (f : Side) (G : Gauge) := Matrix (Tubular f G) (Tubular f G) ℝ
def restrict (A : Mat f G) (i j : Bond f) := A.submatrix (Prod.mk i) (Prod.mk j)

def product {f : Side} {G : Gauge} : (n : ℕ) → (ℕ → Mat f G) → Mat f G
  | 0,_ => 1
  | n+1,f => f 0*product n (fun i => f (i+1))
def tally {n : ℕ} (l : ℕ→ℝ) : ℝ := n.rec (motive:=fun _=>ℝ) 1 (fun n a => l n*a)
lemma count_mul (n : ℕ) (l : ℕ→ℝ) : tally (n:=n+1) l=l 0*tally (n:=n) (fun m => l (m+1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change l (n+1)*tally (n:=n+1) l=l 0*(l (n+1)*tally (n:=n) (fun m => l (m+1)))
    rw [ih]; ring
lemma count_pos {n : ℕ} (l : ℕ→ℝ) (h : ∀ i : ℕ,i<n→0≤l i) : 0≤tally (n:=n) l := by
  induction n generalizing l with
  | zero => exact zero_le_one
  | succ n ih => rw [count_mul]; exact mul_nonneg (h 0 (by omega)) (ih _ (fun i hi => h _ (by omega)))

def combo (i : Bond f) : {n : ℕ} → Itinerary f n → (ℕ → Mat f G) → Matrix G.ColorIndex G.ColorIndex ℝ
  | 0,_,_ => 1
  | _+1,l,P => restrict (P 0) i (next l)*combo (next l) (after l) (fun k => P (k+1))

lemma filtered (S : StepData c f) (d : ℕ) (i : Bond f) : ∀ {n : ℕ} (l : Itinerary f n), ¬Armed S d i l →
    ∀ (P : ℕ→Mat f G), (∀ k<n, Thin (along S) (along S) (P k) d) → combo i l P=0
  | 0,_,h,_,_ => (h trivial).elim
  | n+1,l,h,P,hP => by
    rw [combo]; by_cases H : hop S d i (next l)
    · rw [filtered S d (next l) (after l) (fun hp => h ⟨H,hp⟩) _ (fun k hk => hP _ (by omega)),mul_zero]
    have hg : restrict (P 0) i (next l) = 0 := by
      ext k j; exact hP 0 (by omega) _ _ (lt_of_not_ge (fun e => H (hop_ok S _ _ e)))
    rw [hg,zero_mul]

lemma multiply (_S : StepData c f) (v : Bond f) {n : ℕ} (P : ℕ → Mat f G) (w : Bond f) (p q) :
    (product n P) (v,p) (w,q) = ∑ i : Itinerary f n, if arrive v i=w then combo v i P p q else 0 := by
  induction n generalizing v p P with
  | zero =>
    let b : Itinerary f 0 := ()
    rw [Finset.sum_eq_single b]
    · rw [combo,arrive,product]; by_cases he : v=w
      · rw [he]; simp [Matrix.one_apply]
      simp [he]
    · intro i _ hi; exact (hi (Subsingleton.elim (α:=Unit) _ _)).elim
    simp
  | succ n ih =>
    let Q : ℕ→Mat f G := fun i=>P (i+1)
    rw [product,Matrix.mul_apply,sum_components,Fintype.sum_prod_type]; refine sum_congr rfl fun j _ => ?_
    calc
      _ = ∑ k : G.ColorIndex,∑ l : Itinerary f n, (if arrive j l=w then P 0 (v,p) (j,k)*(combo j l Q k q) else 0) := by
        refine sum_congr rfl fun k _ => ?_; rw [ih j (fun i => P (i+1)),Finset.mul_sum]
        refine sum_congr rfl fun l _ => ?_; split
        next ht => rfl
        next ht => exact mul_zero _
      _ = _ := by
        rw [sum_comm]; refine sum_congr rfl fun l _ => ?_
        simp only [arrive,combo,next_bank,after_bank]
        split
        next h => rw [Matrix.mul_apply]; rfl
        next h => simp

lemma pricingEntries (_S : StepData c f) (P : ℕ → Mat f G) (l : ℕ→ℝ) (v : Bond f) {n : ℕ} (i : Itinerary f n)
    (h : ∀ x<n, ∀ j k, |P x j k| ≤ l x) (hf : ∀ i<n,0≤l i) : ∀ j k, |combo v i P j k| ≤
      (Fintype.card G.ColorIndex:ℝ)^n * tally (n:=n) l := by
  induction n generalizing v P l with
  | zero =>
    intro j k; rw [combo]; change |(1:Matrix ..) j k| ≤ _^ (0:ℕ)*1
    by_cases he : j=k
    · subst k; simp
    simp [he]
  | succ n ih =>
    let j := next i; let L := after i
    let Q (k) : Mat f G := P (k+1); let u (k : ℕ) := l (k+1)
    let C := Fintype.card G.ColorIndex
    let E := combo j L Q
    have hE (v w) : |E v w| ≤ (C:ℝ)^n*tally (n:=n) u := ih Q u j L (fun x hx => h _ (by omega)) (fun x hx => hf _ (by omega)) v w
    intro x y
    rw [combo]
    change |(restrict (P 0) v j * E) x y| ≤ _
    rw [Matrix.mul_apply]; apply (Finset.abs_sum_le_sum_abs ..).trans
    refine le_trans (Finset.sum_le_sum (g:=fun _ => l 0 *((C:ℝ)^n * tally (n:=n) u)) (fun k _ => ?_)) ?_
    · rw [abs_mul]; exact mul_le_mul (h 0 (by omega) _ _) (hE k y) (abs_nonneg _) (hf 0 (by omega))
    rw [sum_const,nsmul_eq_mul,card_univ,count_mul,pow_succ]; unfold C u; exact le_of_eq (by ring)

lemma combo_continuous (v : Bond f) {n : ℕ} (i : Itinerary f n) (P : ℝ→ℕ→Mat f G) (X : Set ℝ)
    (h : ∀ j<n, ContinuousOn (fun t => P t j) X) : ContinuousOn (fun t => combo v i (P t)) X := by
  induction n generalizing P v with
  | zero => simp_rw [combo]; exact continuousOn_const
  | succ n ih =>
    simp only [combo]
    refine ContinuousOn.mul (fun x hx => ?_) (ih (next i) (after i) (fun t j => P t (j+1)) (fun j hj => h (j+1) (by omega)))
    have he : Continuous (fun x : Mat f G => restrict x v (next i)) := Continuous.matrix_submatrix continuous_id _ _
    exact he.continuousAt.comp_continuousWithinAt (h 0 (by omega) x hx)

end Itinerary
end YM.ConnectedActivityE6.Pulse
