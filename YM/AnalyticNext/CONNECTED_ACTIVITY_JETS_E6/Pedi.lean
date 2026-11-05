import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.StreamsA

/-!
# Sharp log stamp jets for each Arm (finite joint interpolants)

Not dropping test constraints before paying Hull. After this can use
geometric marks not assuming smooth Log branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Pulse Itinerary
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
open Brush Foramen    Vine Tablet Metric
variable {v z r Q s y η γ : ℝ} {j m n d : ℕ} {U : E → Config G c} {x : E}

lemma canon (A : E → ℕ→ Mat f G) (v : ℕ → ℝ) (h : ∀ k<n,∀ i l,Brush j (v k) z (fun x=> A x k i l) x)
    (hs : 0 ≤ z) (p : Itinerary f n) (l : Bond f) (i u : G.ColorIndex) :
    Brush j ((Fintype.card G.ColorIndex:ℝ)^n*tally (n:=n) v) (n*z) (fun x=>combo l p (A x) i u) x := by
  induction n generalizing A l i v with
  | zero => unfold combo Itinerary.tally; simp only [pow_zero,Nat.cast_zero,zero_mul]
            apply (Brush.certified le_rfl _).climb _ le_rfl
            by_cases hh:i=u <;> simp [Matrix.one_apply,hh]
  | succ n ih =>
    let b:= Pulse.Itinerary.next p; let g x i:= A x (i+1)
    have he i' := ih g (fun j=>v (j+1)) (fun j hj=> h _ (by omega)) (Pulse.Itinerary.after p) b i'
    simp only [combo, Matrix.mul_apply]; refine (Brush.spree _ _ (fun _=> v 0*((Fintype.card G.ColorIndex:ℝ)^n*Itinerary.tally (n:=n) (fun j=>v (j+1)))) (by positivity : 0≤z+n*z) (fun x _=>?_)).climb ?_ ?_
    · exact (h 0 (by omega) (l,i) (b,x)).paints (he _)
    · rw [sum_const,nsmul_eq_mul,card_univ,count_mul]; exact le_of_eq (by ring)
    push_cast; linarith

lemma smooth_combo (A : E → ℕ→ Mat f G) (h : ∀ k<n,∀ i l, ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun x=> A x k i l) x)
    (p : Itinerary f n) (l : Bond f) (i u : G.ColorIndex) : ContDiffAt ℝ (↑j : WithTop ℕ∞)
    (fun x=>combo l p (A x) i u) x := by
  induction n generalizing A l i with
  | zero => exact contDiffAt_const
  | succ n ih =>
    exact per_entry _ _ x i u (fun k=> h 0 (by omega) (l,i) ((Pulse.Itinerary.next p),k))
      (fun j=> ih (fun x i=> A x (i+1)) (fun i hi=> h (i+1) (by omega)) (Pulse.Itinerary.after p) _ j)

-- Use prices with *nonnegative* costs for spin entries.
lemma plurality [FiniteDimensional ℝ E] (A : E → ℝ→ℕ→ Mat f G) (v : ℕ → ℝ) (hv : ∀ i<n, 0≤v i) (h : ∀ s ∈ Set.Icc (0:ℝ) 1,
    ∀ i<n,∀ j' l, Brush j (v i) z (fun x=> A x s i j' l) x ∧ ContDiffAt ℝ (↑j : WithTop ℕ∞) (fun u : E×ℝ=> A u.1 u.2 i j' l) (x,s))
    (hl : ∀ x y, ∀ k<n, Thin (along S) (along S) (A x y k) d) (hs : 0 ≤ z) (i : Bond f) (p : Itinerary f n) :
    Brush j (if Armed S d i p then (Fintype.card G.ColorIndex:ℝ)^(n+1)* tally (n:=n) v else 0) (n*z)
      (fun x => stamp (A x) i p) x := by
  split
  next hg =>
    let c : ℝ:= Fintype.card G.ColorIndex
    have he := count_pos v hv
    have hh : 0≤ (n:ℝ)*z := by positivity
    have hp (j' : G.ColorIndex) : Brush j (c^n*tally (n:=n) v) (n*z) (fun x=>checkIn (A x) i p j') x := by
      unfold checkIn; split_ifs
      next ht =>
        exact yogic (U:=fun x y=>combo i p (A x y) j' j') (fun s hs=> smooth_combo (fun x=> A (x:E×ℝ).1 x.2)
          (fun j hj i l=> (h s hs j hj i l).2) p i j' j') (fun s hr=> canon (fun x=>A x s) v (fun j hj i l=>
          (h s hr j hj i l).1) hs p i j' j')
      simp_rw [intervalIntegral.integral_zero]
      exact (Brush.certified hh 0).climb (by unfold c; rw [norm_zero]; positivity) le_rfl
    refine (Brush.spree _ _ _ hh (fun j (_:j∈univ)=> hp j)).climb ?_ le_rfl
    rw [sum_const,nsmul_eq_mul,card_univ]; unfold c; exact le_of_eq (by ring)
  next hg =>
    unfold stamp checkIn; simp_rw [filtered S d i p hg _ (hl _ _)]; simp only [Matrix.zero_apply,ite_self, intervalIntegral.integral_zero, sum_const_zero]
    exact (Brush.certified (by positivity) _).climb (by simp) le_rfl
end YM.ConnectedActivityE6.Blaze
