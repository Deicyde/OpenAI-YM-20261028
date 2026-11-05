import YM.Further.CURVED_GAUSSIAN_JETS.Engine
import YM.Further.CURVED_GAUSSIAN_JETS.TailJets
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Stadium
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques

/-!
# Prices of the ordered vertex-functions up to their integrated or Z use

Same basepoint derivatives on full entry functions and shared-tag window
calculations for every inserted factor. Cost-payment extends to every
principal submatrix with its own windows. `ticket` includes exponent slack
on each jump and each step, ready for hit pricing independently of V.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Tracks
open Matrix Function Filter Jets Lattice Wilson RG Precision Set MeasureTheory Push.Uniform SectorNext.Vacuum
open scoped Matrix.Norms.Frobenius BigOperators Classical Topology ContDiff
variable {I : Type*} [Fintype I] [DecidableEq I] {G : Gauge} {c n : Side}
    {a : I → Site n} {s : Jets.Weights a} {Q : Directions G c → Prop} {P : Prices} {V : Config G c} {M K u : ℝ} {k N : ℕ} {W : Windows I} {A : Jets.Field G c I}

structure Fuel (P : Prices) (s : Jets.Weights a) (k : ℕ) (M K : ℝ) : Prop where
  valid : 0≤M
  one : 1≤K
  base : s.pay k*M ≤ K
  column : s.pay k*column_cost P s k M ≤ K
  defect : s.pay k*defect_cost P s k M ≤ K
  line : s.pay k*line_cost P s k M ≤ K

variable (W A) in
def shifted (d : ℕ) (u : ℝ) : Fin (d+2) → Jets.Field G c I := Fin.cons (Jets.probe W A u) fun _=>fun x=> -(err W A u x)
variable (W A) in
def twist (d : ℕ) : Fin (d+1) → Jets.Field G c I := fun _=> fun x=> -(coeff W A x)
variable (W A) in
def extended (d : ℕ) : Fin (d+2) → Jets.Field G c I := Fin.snoc (twist W A d) A

lemma fare_path (p : ℕ) (i j : I) : Jets.path W A p u V i j = ∑ z, ends i j z (fare z fun b=>shifted W A p u b V) := by
  rw [← engine_entries,engine_next,shifted,Fin.cons_zero,show (Fin.tail fun i => Fin.cons (α:=fun _=>Jets.Field G c I) (Jets.probe W A u) (fun _=>fun v => -(err W A u v)) i V) = fun _ : Fin (p+1) => -(err W A u V) by funext; simp [Fin.tail], engine_pow]; rfl

lemma fare_extended (d : ℕ) (i j : I) : (((-(coeff W A V))^(d+1))*A V) i j = ∑ z, ends i j z (fare z fun b=>extended W A d b V) := by
  rw [← engine_entries,engine_rear,extended,show (Fin.init fun i=>Fin.snoc (α:=fun _=>Jets.Field G c I) (twist W A d) A i V)=(fun _ : Fin (d+1)=> -(coeff W A V)) by funext; simp [Fin.init,twist], engine_pow,Fin.snoc_last]

variable (h : Street P s k Q A V M)
include h
lemma shifted_good (d : ℕ) (i : Fin (d+2)) (hu : 0≤u) : Good (shifted W A d u i) k V := by induction i using Fin.cases <;> simp only [shifted, Fin.cons_zero,Fin.cons_succ]; exacts [h.probe W hu,(h.err W hu).neg]
lemma shifted_flow (d : ℕ) (i : Fin (d+2)) : Flow (fun u=>shifted W A d u i) V k := by induction i using Fin.cases <;> simp only [shifted, Fin.cons_zero,Fin.cons_succ]; exacts [h.column_flow W,(h.defect_flow W).neg]
lemma twist_good (d : ℕ) (i : Fin (d+1)) : Good (twist W A d i) k V := (h.coeff W).neg
lemma extended_good (d : ℕ) (i : Fin (d+2)) : Good (extended W A d i) k V := by induction i using Fin.lastCases <;> simp only [extended,Fin.snoc_castSucc,Fin.snoc_last]; exact h.good; exact twist_good h _ _

variable (hf : Fuel P s k M K) (hx : W.Includes a N)
include hf hx

variable (P N) in
def wage := Real.exp (-spare P*N)
omit h hf hx in
lemma positive (P : Prices) (N : ℕ) : 0<wage P N := Real.exp_pos _
variable (a P K N) in
def ticket (d : ℕ) {m : ℕ} (p : Run I m) := K^m * wage P N^(d+1) * decay a (spare P) p
variable (P s K N) in
def asking (d : ℕ) {m : ℕ} (p : Run I m) (j : ℕ) := ticket a P K N d p * s.τ (p 0)^j

def daily (P : Prices) (N d : ℕ) (u : ℝ) (s : Jets.Weights a) (k : ℕ) (M : ℝ) : Fin (d+2) → ℝ := Fin.cons (column_cost P s k M/(1+u)) fun _=> defect_cost P s k M * wage P N/(1+u)

lemma shift_price (d : ℕ) (p : Run I (d+2)) (hu : 0≤u) : Cash s (spare P) k Q V (reserved p (shifted W A d u)) (ticket a P K N d p * Line.bell u) := by
  let F := daily P N d u s k M
  obtain ⟨hC,hD,hS,hL⟩ := cost_pos P s k hf.valid
  have hE := positive P N; have hK := zero_le_one.trans hf.one
  have hF (i : Fin (d+2)) : 0≤F i := by induction i using Fin.cases <;> simp only [F,daily,Fin.cons_succ,Fin.cons_zero] <;> positivity
  have hp : 2*spare P ≤ 3*spare P := by linarith only [spare_pos P]
  refine (reserved_cash p (M':=shifted W A d u) (C':=F) (fun i => ?_) (fun i=> shifted_good h d i hu) hF h.room).mono le_rfl ?_
  · induction i using Fin.cases <;> simp only [shifted,F,daily,Fin.cons_zero,Fin.cons_succ]; exacts [(columns_pay W h hu).mono hp le_rfl,(defect_pay W h hx hu).neg]
  unfold F daily ticket; rw [Fin.prod_univ_succ]; simp only [Fin.cons_succ,Fin.cons_zero,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [mul_right_comm _ (decay a _ p), ← mul_div_assoc, ←mul_div_assoc, ←mul_assoc (s.pay k)]
  refine mul_le_mul_of_nonneg_right ?_ (decay_strict _).le
  let E := wage P N
  calc
    _ ≤ K/(1+u)*((K*E)/(1+u))^(d+1) := by have hs := s.pay_pos k; gcongr <;> (first | positivity | exact hf.column | exact hf.defect)
    _ = (K*((K*E)^d*(K*E)))/( (1+u)^d * ((1+u)^2)) := by rw [div_pow,pow_succ,pow_succ]; field_simp
    _ ≤ _ := by unfold Line.bell; rw [one_div,←div_eq_mul_inv,mul_pow, show K^(d+2)*wage P N^(d+1) = K*(K^d*E^d*(K*E)) by unfold E; ring]
                gcongr; exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by linarith))

lemma twist_price (hA : ∀ᶠ u in 𝓝 V,(A u).IsHermitian) (d : ℕ) (p : Run I (d+1)) : Cash s (spare P) k Q V (reserved p (twist W A d)) (ticket a P K N d p) := by
  let E := wage P N; have hE : 0<E := Real.exp_pos _; have hm := (cost_pos P s k hf.valid).2.2.2
  refine (reserved_cash p (fun _=> (coeff_pay W h hx hA).neg) (fun i=>twist_good h d i) (fun _=>show 0≤line_cost P s k M*E by positivity) h.room).mono le_rfl ?_
  unfold ticket; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← mul_pow,← mul_assoc (s.pay k)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (s.pay_pos k).le hm) hE.le) (mul_le_mul_of_nonneg_right hf.line hE.le) _) (decay_strict p).le
lemma extended_price (hA : ∀ᶠ u in 𝓝 V,(A u).IsHermitian) (d : ℕ) (p : Run I (d+2)) : Cash s (spare P) k Q V (reserved p (extended W A d)) (ticket a P K N d p) := by
  let E := wage P N; let F : Fin (d+2)→ℝ := Fin.snoc (fun _=>line_cost P s k M * E) M
  have hE : 0<E := Real.exp_pos _; have hm := (cost_pos P s k hf.valid).2.2.2; have hK := zero_le_one.trans hf.one
  have hF i : 0 ≤ F i := by induction i using Fin.lastCases <;> simp [F]; exact hf.valid; positivity
  refine (reserved_cash p (C':=F) (M':=extended W A d) (fun i=> ?_) (fun i=>extended_good h d i) hF h.room).mono le_rfl ?_
  · induction i using Fin.lastCases <;> simp only [F,extended,Fin.snoc_castSucc,Fin.snoc_last]
    exacts [h.cash.mono (by linarith only [four_spare P,spare_pos P]) le_rfl,(coeff_pay W h hx hA).neg]
  unfold ticket; rw [Fin.prod_univ_castSucc]; simp only [F,Fin.snoc_last,Fin.snoc_castSucc,Finset.prod_const, Finset.card_univ,Fintype.card_fin]; rw [←mul_assoc (s.pay k)]
  calc
    _ ≤ (((K*E)^(d+1))*K)*decay a (spare P) p := by gcongr <;> (first | exact hf.line | exact hf.base | exact mul_nonneg (s.pay_pos k).le hf.valid | exact mul_nonneg (mul_nonneg (s.pay_pos k).le hm) hE.le | exact (decay_strict _).le)
    _ = _ := by rw [mul_pow,pow_succ K]; ring
end YM.Further.CurvedGaussianJets.Tracks
