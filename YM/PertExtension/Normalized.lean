import YM.PertExtension.OrbExpansion

/-! Normalized Wilson series quotient and exact finite patch-independence.
Includes a version starting with Haar on every (inversion-paired) edge, for
observables invariant under even gauges. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.PertExtension.Orb
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory
open scoped ContDiff Topology Classical BigOperators ENNReal
open Chart Series Series.Radial Series.Tested
variable {G : Gauge}{n : Side}
local notation "W" => tangent G (Cotree n)

private lemma coeff0 {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{f K : E→ℝ}(u : E) : integrandSeries f K 0 u=K 0 := by
  have hh:(Finset.antidiagonal 0 : Finset (ℕ×ℕ))={((0,0):ℕ×ℕ)}:= by ext ⟨x,y⟩; simp only [Finset.mem_antidiagonal,Finset.mem_singleton,Prod.mk.injEq];omega
  simp [integrandSeries,Zone.mul,hh,expsum,Zone.TaylorPow]

variable (P : ChartRatio G)
lemma one_accounting : accountingWith P (n:=n) 1 0=jacobian P (U:=Cotree n) 0 := by unfold accountingWith;simp
lemma rows_zero (O : Observable G n) : rowsWith P O 0 = jacobian P (U:=Cotree n) 0 * O 1 * (∫ u, kernel fiscal u ∂W) := by
  have ha : expLinks G (Cotree n) 0=1:= by funext i;simp [expLinks]
  unfold rowsWith Radial.moment normTerm; simp_rw [coeff0 (K:=accountingWith P O), accountingWith,← integral_const_mul,ha]

variable {P}
lemma ker_integrable (even : Even n.val): Integrable (kernel fiscal) W := by
  obtain ⟨c,hc,h⟩:=coercion (G:=G) even
  refine (bill_integrable W 0 hc).mono' (by unfold kernel;exact (Real.continuous_exp.comp (continuous_neg.comp (Smooth.continuousJet fiscal 2))).aestronglyMeasurable) (Eventually.of_forall fun x=>?_)
  specialize h x
  unfold bill; rw [pow_zero,one_mul,Real.norm_eq_abs,abs_of_nonneg (kernel_pos.le : 0≤kernel fiscal x),kernel];gcongr;linarith

lemma pivot (even : Even n.val)(R : LocalRatio P) : 0<rowsWith P (n:=n) 1 0 := by
  rw [rows_zero,Pi.one_apply,mul_one]
  apply mul_pos (Finset.prod_pos fun i _=>(show 0<fee P 0 from lt_max_of_lt_left (by rw [R.anchored,mul_one];exact R.scale)))
  exact integral_exp_pos (ker_integrable even)

theorem finite_formula (even : Even n.val)(R : LocalRatio P){O : Observable G n}(h : LocalTest O):
    Aspiration (expectation O) (diagonalWith P O) := by
  intro k
  obtain ⟨C,hC,H⟩:= (laplace even R h).quotient (laplace even R (one_test)) (pivot even R).ne' k
  refine ⟨C,hC,?_⟩; filter_upwards [H,Tested.eventually_pos] with t ht hp
  change ‖numerator O t/numerator (G:=G) (n:=n) 1 t-_‖≤_
  change ‖scaledNum O t / scaledNum (G:=G) (n:=n) 1 t-peval (diagonalWith P O) k t‖ ≤_ at ht
  unfold scaledNum at ht;rw [mul_div_mul_left ..] at ht
  · exact ht
  positivity

theorem chart_independent (even : Even n.val){P' : ChartRatio G}(R : LocalRatio P)(R' : LocalRatio P'){O : Observable G n}(h : LocalTest O):
    diagonalWith P O=diagonalWith P' O ∧ rowsWith P O=rowsWith P' O :=
     ⟨(finite_formula even R h).unique (finite_formula even R' h),(laplace even R h).unique (laplace even R' h)⟩
lemma numerator_pos (t) : 0 < numerator (G:=G) (n:=n) 1 t :=
  (integral_pos_iff_support_of_nonneg (f:=entries (n:=n) (G:=G) 1 t) (fun x=> show 0≤ (1:ℝ)*_ from mul_nonneg zero_le_one (Real.exp_pos _).le) (entries_integrable one_test.boundedness t)).2 (by rw [Set.eq_univ_of_forall (s:=Function.support (entries (G:=G) (n:=n) 1 t)) (fun x=>by simp [entries])];simp)
-- orbifold rule before tree reduction

def restrictedO (O : Config G n→ℝ) : Observable G n:=fun v=>O (links 1 v)
def preDensity (t) (x:Config G n) := Real.exp (-(energy x/2) / t^2)
def preNum (O : Config G n→ℝ) (t:ℝ):=
   ∫ v, O (liftLinks v)*(preDensity t (liftLinks v)) ∂physical G (OEdge n)
def preExpectation (O : Config G n→ℝ) := fun (t:ℝ)=>preNum O t/ preNum (G:=G) (n:=n) 1 t
lemma preNum_eq (O : Config G n→ℝ) (t : ℝ) (even : Even n.val)(h : Continuous O)
    (hG : ∀ u : Site n → G.El, (∀ x,u (-x)=u x) → ∀ x, O (gauge u x)=O x) : preNum O t = numerator (restrictedO O) t := by
   have hc : Continuous (preDensity (G:=G) (n:=n) t) := Real.continuous_exp.comp (((energy_cont.div_const 2).neg).div_const (t^2))
   have hu : ∀ u : Site n→G.El, (∀ x,u (-x)=u x) → ∀ x,(O * preDensity (G:=G) (n:=n) t) (gauge u x)=(O * preDensity (G:=G) (n:=n) t) x := fun u hu x=>by simp [hG u hu,preDensity,energy_gauge]
   exact average_eq G (O * preDensity (G:=G) (n:=n) t) (h.mul hc) even hu

structure PreTest (O : Config G n→ℝ) : Prop where
  gauge : ∀ u : Site n→G.El, (∀ x,u (-x)=u x) → ∀ x, O (Lattice.gauge u x)=O x
  curved : LocalTest (restrictedO O)
  continuous : Continuous O

lemma preNum_one_pos {t} (even : Even n.val) :0<preNum (G:=G) (n:=n) 1 t := by rw [preNum_eq 1 t even continuous_const (by simp [Pi.one_apply])];exact numerator_pos _

theorem before_tree_formula (even: Even n.val)(R : LocalRatio P){O : Config G n→ℝ}(h : PreTest O):
    Aspiration (preExpectation O) (diagonalWith P (restrictedO O)):= by
  have he: preExpectation O = expectation (restrictedO O):=by
    funext t
    change preNum O t / preNum (G:=G) (n:=n) 1 t = numerator (restrictedO O) t / numerator (G:=G) (n:=n) 1 t
    rw [preNum_eq O t even h.continuous h.gauge, preNum_eq (O:=(1:Config G n→ℝ)) t even continuous_const (fun _ _ _=>rfl)]; rfl
  rw [he]; exact finite_formula even R h.curved

end YM.PertExtension.Orb
