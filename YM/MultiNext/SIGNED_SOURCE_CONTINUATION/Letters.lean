import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Hear
import YM.Next.BOUNDARY.Coordinates

set_option warningAsError false

/-!
# Sum *individual* response prices and integrate

Here slicing an incoming pure remainder into ordinary integrands.
This way the RG producer can try to fill requests on just one H occurrence
(on its weighted jet & sign data), or one K occurrence (on its flag
bucket with the witness and exp/div price), not universality on their
combos nor on differences equalized at terminal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Body Multi Push.RelayDifference
variable {G : Gauge} {n : Side} {e : ℕ} {F : Frame G e} {R : Rep G n} {o : Site n}
variable {A : Hol G} {U : GridU n} {D : Body F n} {κ r a b c d w : ℝ}

section Incoming
variable (R) (U) (D) (x : Config G n)
def eat (i : ℕ) : ℂ := (R.eval x:ℂ)*masked R.p.threshold (U i) (payload D i) x
def flash (i : ℕ) : ℂ := punch R x (Pi.single (Pack.ofAddress R.activities i) (flag D i x))

section
variable {R D} (T : Tally o R U D κ r)
include T



lemma eat_bound (i) : ‖eat R U D x i‖ ≤ ‖R.eval x‖ * T.seed i := by
  unfold eat
  rw [norm_mul, Complex.norm_real]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  by_cases he : Healthy R.p.threshold (U i) x
  · rw [masked_eq _ _ _ _ he]; exact (T.sexp i).2 x he [] (by simp) (by simp)
  rw [masked_ne _ _ _ _ he,norm_zero]; exact (T.sexp i).1

end

private lemma ignite (S : Finset (Pack n)) (f : Config G n → ℂ) (t : ℝ) (he : Envelope f) :
    Envelope fun x : Config G n => if S∈Pack.clears (flags t x) then f x else 0 := by
  obtain ⟨p,hp⟩:=he.cost
  have hm : MeasurableSet {x : Config G n | S∈Pack.clears (flags t x)} := Pack.neighborhood S t
  have he' : ∀ x : Config G n,‖(if S∈Pack.clears (flags t x) then f x else (0:ℂ))‖ ≤ max p 0 := fun x => by
    split
    · exact (hp _).trans (le_max_left ..)
    rw [norm_zero]; exact le_max_right ..
  exact ⟨he.meas.ite hm measurable_const,max p 0,he'⟩

private lemma illuminate (m : Finset (Pack n) → Config G n → ℂ) (t : ℝ) (H : ∀ i,Envelope (m i)) :
    Envelope (fun x => ∑ i∈ Pack.clears (flags t x),m i x) := by
  let f (i : Finset (Pack n)) x := if i∈Pack.clears (flags t x) then m i x else (0:ℂ)
  have hx x : (∑ i∈ Pack.clears (flags t x),m i x)=
      ∑ i : Finset (Pack n), f i x := by unfold f; rw [← Finset.sum_filter]; simp
  rw [show (fun x : Config G n => ∑ i ∈ Pack.clears (flags t x),m i x)=(fun x => ∑ i : Finset (Pack n), f i x) from funext hx]
  exact Leaf.amounts _ f fun i => ignite _ _ t (H i)
lemma lamp (H : R.Lawful a b c d w) (q : Pack n) : Envelope (fun x : Config G n => (Real.exp (R.exponent x):ℂ) * ∑ i∈ Pack.clears (flags R.p.threshold x),∑ j∈i,(Pi.single q (1:ℂ) : Pack n→ℂ) j * ∏ v∈i.erase j,incumbent R x v) := by
  have ht : Envelope (fun x : Config G n => (Real.exp (R.exponent x):ℂ)) := by
    obtain ⟨hh,B,hB⟩:=(R.exponentEnv H).exp
    exact ⟨Complex.continuous_ofReal.measurable.comp hh,B,fun x => by
      rw [Complex.norm_real]; exact hB x⟩
  let E (q : Pack n) (x) := incumbent R x q
  have he q : Envelope (E q) := by
    obtain ⟨y,hy,hY⟩:=Activities.K_total H.labels.boundK
    exact ⟨(incumbent_legible R q H.labels.forced).borel,_,fun x => collects_bound R y (fun i => (R.activities.K i x:ℂ))
      hy (fun j => by rw [Complex.norm_real]; exact (hY j).2 _) _⟩
  have hE (S : Finset (Pack n)) : Envelope (fun x => ∏ i∈S,E i x) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Leaf.atom _
    | insert i S hi ih => simp only [Finset.prod_insert hi]; exact Leaf.multiply (he i) ih
  let m (S : Finset (Pack n)) (x) :=
    ∑ i∈S, (Pi.single q (1:ℂ) : Pack n → ℂ) i * ∏ v ∈ S.erase i,E v x
  change Envelope (fun x : Config G n => (Real.exp (R.exponent x):ℂ) * ∑ i∈Pack.clears (flags R.p.threshold x),m i x)
  refine Leaf.multiply ht (illuminate m R.p.threshold fun i => Leaf.amounts _ _ fun j => Leaf.multiply (Leaf.atom _) (hE _))

lemma lights : ∀ q : Pack n, R.Lawful a b c d w → Envelope (fun x : Config G n => punch R x (Pi.single q 1)) := by
  intro q H
  exact lamp R H q

lemma sparkle (H : R.Lawful a b c d w) : ∃ L : ℝ, 0 ≤ L ∧ ∀ (q : Pack n),
    Measurable (fun x : Config G n => punch R x (Pi.single q 1)) ∧ ∀ x,‖punch R x (Pi.single q 1)‖ ≤ L := by
  choose h A hA using fun i =>
    show Measurable _ ∧ ∃ _, _ from ⟨(lights R i H).meas,(lights R i H).cost⟩
  obtain ⟨L,hL,hV⟩:=((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun i : Pack n => eventually_ge_atTop (A i))).exists
  exact ⟨L,hL,fun i => ⟨h i,fun x => (hA i x).trans (hV i)⟩⟩
lemma blink (i) : flash R D x i = flag D i x*punch R x (Pi.single (Pack.ofAddress R.activities i) 1) := by
  unfold flash
  let q := Pack.ofAddress R.activities i; let z := flag D i x
  have he : Pi.single q z=z • (Pi.single q (1:ℂ) : Pack n→ℂ) := by funext l; by_cases h : l=q <;> simp [h]
  rw [he,map_smul]; rfl
lemma flash_env (H : R.Lawful a b c d w) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ (i:ℕ), ∀ B' : ℝ, 0 ≤ B' → (∀ u, ‖flag D i u‖ ≤ B') →
      (∀ u, ‖flash R D u i‖ ≤ B*B') ∧ (Measurable (flag D i) → Measurable fun u => flash R D u i) := by
  obtain ⟨K,hK,h⟩:=sparkle R H
  refine ⟨K,hK,fun i b hb hv => ⟨fun u => ?_, fun he => ?_⟩⟩
  · rw [blink,norm_mul,mul_comm]; exact mul_le_mul ((h _).2 u) (hv u) (norm_nonneg _) hK
  simp_rw [blink]; exact he.mul (h _).1
end Incoming

section Integrate
variable {m : Side} (S : StepData m n) (β : ℝ)




end Integrate

section Receipt
variable {κ r a b c d w : ℝ} (X : SectionData F)
variable (H : R.Lawful a b c d w) (T : Tally o R U D κ r)

include H T

variable {m : Side} (S : StepData m n) {β : ℝ}

theorem funds (h : Ok o A R U D) :
    let H i (u : Config G n) := eat R U D u i; let J i (u : Config G n) := flash R D u i
    (Dominated H ∧ Dominated J) ∧ ∀ i : ℕ, Measurable (H i) ∧ Measurable (J i) := by
  intro h1 h2
  obtain ⟨hu,C,hC⟩ := R.envelope H
  obtain ⟨B,hB,hb⟩:=flash_env R D H
  have ha (i) := hb i (T.stamp i) ((T.tag i).1) ((T.tag i).2)
  refine ⟨⟨⟨_,T.bare_cost.1.2.1.mul_left C,fun i x => ?_⟩,⟨_,T.bare_cost.2.2.1.mul_left B,fun i u => (ha i).1 u⟩⟩,
    fun i => ⟨?_, (ha i).2 (h.borel i)⟩⟩
  · exact (eat_bound U x T i).trans (mul_le_mul_of_nonneg_right (hC x) (T.sexp i).1)
  unfold h1 eat; exact (Complex.continuous_ofReal.measurable.comp hu).mul (masked_measurable _ _ _ (h.smooth i).borel)


end Receipt
end YM.MultiNext.SignedSource
