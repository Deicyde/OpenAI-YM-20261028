import YM.MergeProof.Newell
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Clock


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac Menu Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I : Type} [Fintype V][DecidableEq V]{B:Census V}{G:Gauge}{n:Side} {e f t u v: ℝ}{r: V→ℝ}
variable {A:Rep G n}{F: V→ Config G n→ℂ}{g:V→ Box n→ Config G n→ℂ}{X: Config G n→ Poly B}{o:V→Site n}{a x y l Λ σ C:ℝ}
local notation "P!"=> A.p
lemma hove (hr:∀ i,0<r i)(hx:Served A F g X o r e f)(h:A.Lawful σ C Λ t u)(hg:0 ≤ A.beta) (hv:Vault r F g x y)(he:0 ≤ e)(U): Poly.price r (X U) ≤ Real.exp (A.scalar + Bands.fine (Fintype.card V) A x y (2*f) 1 C Λ t u):=by
   refine (steer hr hx h.labels hv he U).trans (Real.exp_monotone ?_)
   unfold Bands.fine; linarith only [Rep.exponent_hi A h hg U]
-- qualitative definite from path.q any f 
lemma sail (hr:∀ i,0<r i)(hx:Served A F g X o r e f)(h:A.Lawful σ C Λ t u)(hg:0 ≤ A.beta) (hv:Vault r F g x y)(he:0 ≤ e)(T:B.Mode)(hi:Integrable X (prior G n))(s:ℝ)(hp:0<s)(hf:s≤(P!).threshold)(hA:∀ U,0 ≤ A.eval U):
   ‖(∫ U,(X U).part T ∂prior G n)‖/(∫ U,A.eval U∂prior G n)*Poly.toll r T ≤ Real.exp (Bands.finalBill (Fintype.card V) A s x y (2*f) 1 C Λ t u):=by
   let p:= B.Mode; let k:= Real.exp (A.scalar + Bands.fine (Fintype.card V) A x y (2*f) 1 C Λ t u); let X'(U):=(X U).part T
   have hv' :Integrable X' (prior G n):= ((Poly.get T).restrictScalars ℝ).integrable_comp hi
   have hV : ‖(∫ U,X' U ∂prior G n)‖ ≤ k / Poly.toll r T:=by
      apply (norm_integral_le_integral_norm _).trans; calc
       _ ≤ ∫ _ : Config G n,k/Poly.toll r T ∂prior G n := integral_mono hv'.norm (integrable_const _) (fun U=> (le_div_iff₀ (Poly.worth hr _)).mpr (le_trans (le_of_eq (mul_comm ..)) ((Poly.member hr ..).trans (hove hr hx h hg hv he U))))
       _ = _:=by simp
   have ht := A.denominator h hg s hp hf hA; rw [div_mul_eq_mul_div,div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) ht)]; apply ((le_div_iff₀ (Poly.worth hr _)).mp hV).trans
   apply le_trans _ (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le); rw [← Real.exp_add]; apply le_of_eq; unfold k Bands.fine Bands.finalBill; congr 1; rw [show Fintype.card (Edge (Site n))=Fintype.card (Site n)*4 by simp [Edge,Axis]]; push_cast; ring
variable (A: RG.History G)(B:Census V)(N p k:ℕ)
    (T:V → Config G (A.S.side N p)→ℂ)
local notation "R"=> A.rep N p
local notation "P"=> A.levels.budget
local notation "Z"=> A.S
variable {X:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→ Poly B}
  (h:∀ i:ℕ,k ≤ i → ∀ hi:i<N,X i hi.le=(A.levels.clock.op i p).push ((A.rep N p (i+1)).beta) (X (i+1) hi))
  (hx:X N le_rfl=birth B (A.rep N p N) T) (hv: Integrable (X N le_rfl) (prior G (A.S.side N p)))
   (hh:A.Selected)
include h hx hv hh
local notation "K"=> Fintype.card V
set_option quotPrecheck false
-- any ballot
lemma vista {F:V→ Config G (A.S.side k p)→ℂ} {g: V→ Box (A.S.side k p) → Config G (A.S.side k p)→ℂ}{o:V→Site (A.S.side k p)} (hk:k≤N) (s:B.Mode)(ht:Integrable (fun U => ∏ i∈s.val,T i U) (law G (A.S.side N p) (A.β N p N)))
   (he:Served (R k) F g (X k hk) o r e f)(hS:Vault r F g x y)(hr:∀ i,0 < r i)(hz: 0≤ e) : ‖moment (A.β N p N) (fun U=> ∏ i∈ s.val,T i U)‖* Poly.toll r s ≤
      Real.exp (Fintype.card (Site (A.S.side k p))* Vac.treasury A.levels k+ Fintype.card V*(x+y+2*f)):=by
   let n:=Z|>.side k p; let N':=(Z)|>.side N p
   let c:=A.levels.clock
   have hb:=hh.represents N p k hk; have h':0<c.hatCoupling k:= inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans (A.levels.fits.delayed k)))
   let Y i hi (U:Config G (A.S.side i p)):=(X i hi U).part s
   have hp := hb.band
   have hy (i:ℕ)(hi:k ≤ i)(hh:i≤N):Integrable (X i hh) (prior G (A.S.side i p)):=by
      induction hh using Nat.decreasingInduction with
      | self=>exact hv
      | of_succ j hj ih=> rw [h j hi hj]; exact StepData.push_integrable (A.levels.transition_mass ..) _ (ih (hi.trans j.le_succ))
   have he' : c.hatCoupling k ≤ (R k).p.threshold:=by
      rw [hb.vac]; exact le_mul_of_one_le_right h'.le (Real.one_le_exp (sq_nonneg _))
   let T' (U):=∏ i∈s.val,T i U; let φ:=moment (A.β N p N) T'
   have hg := (sail hr he hb.good (Overlay.beta_positive hh hk).le hS hz s (hy k le_rfl hk) _ h' he' (History.nonnegative A hh N p k hk)).trans (Real.exp_monotone (Vac.suffices_bill hh hk K ..)) -- syntax edit
   have hT i (hi:k ≤ i)(h':i≤N): (∫ U,Y i h' U∂prior G (A.S.side i p))=(Wilson.partition G N' (A.β N p N):ℂ)* φ:=by
       induction h' using Nat.decreasingInduction with
       | self =>
          unfold Y; rw [hx]; unfold φ; rw [moment_formula _ T' ht,mul_inv_cancel_left₀ _ (_:ℂ)]; -- names
          · simp_rw [birth, (hh.starts N p).2,Poly.part_smul,Mach, Extra.Trajectories.pass_fire]; rfl
          exact Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
       | of_succ j hj ih=>
          have hx' : Y j hj.le= (A.levels.clock.op j p).push (A.β N p (j+1)) (Y (j+1) hj) := by
              unfold Y; rw [h j hi hj]; exact push_get (A.levels.transition_mass ..) (hy (j+1) (hi.trans j.le_succ) hj) s
          rw [hx',StepData.push_integral (A.levels.transition_mass ..)  (Y (j+1) hj) (((Poly.get s).restrictScalars ℝ).integrable_comp (hy (j+1) (hi.trans j.le_succ) hj)),ih (hi.trans j.le_succ)] -- coerc
   rw [show (∫ U,(X k hk U).part s∂prior G _) = (Wilson.partition G _ (A.β N p N):ℂ)*φ from hT k le_rfl hk,History.partition_eq A hh N p k hk,norm_mul,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le,mul_comm (Wilson.partition ..),mul_div_cancel_right₀ _ (partition_pos _).ne',mul_one] at hg; exact hg
end YM.MergeProof.Accent
