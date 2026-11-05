import YM.Push.GRID_APPROXIMATION.Joint
import YM.OPE.Columns.Accounts
import YM.Push.GRID_APPROXIMATION.Many
import YM.Next.WARD_BIN.Spin
import YM.Cells.Embedded
import YM.RG.Push
/-!
# The unselected HISTORY law at effective level

Fixed cutoff, represented with same coupling, normalized using original
partition and prior Haar.Want to measure canonical Gram across meso windows
at arbitrary positions in that hierarchy.

It does not assert sign preservation or locality of
arbitrary appointments of the gas away from the eligibility scopes.

Compare the conditional observable to cut time with the *exact* shared kernels; no witness
reselection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm
open Function Filter Set MeasureTheory Lattice Wilson RG Next.Extract Push.GridApprox Cells WardBin.Wheels
open scoped ENNReal Topology BigOperators Classical
variable {G:Gauge} {H:History G}(Y:H.Selected){k i m N p:ℕ} {τ s:ℝ}
local notation "n" j => H.S.side j p
local notation "β" => H.β N p N
local notation "Q" j => H.rep N p j
local notation "η" j => prior G (H.S.side j p)
local notation "ℤ∞" => partition G (H.S.side N p) (H.β N p N)

def dose (i:ℕ) (U : Config G (H.S.side i p)) (N:ℕ) := (H.rep N p i).eval U / partition G (H.S.side N p) (H.β N p N)
variable {Y}

def scene (H:History G)(N p i:ℕ) := (prior G (H.S.side i p)).withDensity (fun U => ENNReal.ofReal (dose (H:=H) (p:=p) i U N))
variable (Y)
local notation "μ" j => scene H N p j
include Y
lemma dose_positive (h:i≤N) (U:Config G (n i)) : 0<dose (H:=H) (p:=p) i U N:= div_pos (gravity Y h _) (partition_pos _)
lemma dose_env (h:i≤N) : Envelope (fun U=> dose (H:=H) (p:=p) i U N):=by
   simpa only [dose,div_eq_mul_inv] using! Envelope.mul ((Q i).envelope (Y.represents _ _ _ h).good) (Envelope.const ℤ∞⁻¹)
lemma probability (h:i ≤ N) : IsProbabilityMeasure (μ i):= by
   let f(U):=dose (H:=H) (p:=p) i U N
   refine ⟨?_⟩; rw [scene,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,← ofReal_integral_eq_lintegral_ofReal ((dose_env Y h).integrable (η i)) (Eventually.of_forall (fun U=>(dose_positive Y h U).le))]; simp_rw [dose]; rw [integral_div,H.partition_eq Y N p i h,div_self (partition_pos _).ne',ENNReal.ofReal_one]
lemma account (h:i ≤ N) {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (f:Config G (n i) → X) : (∫ U,f U∂(μ i)) = (∫ U, dose (H:=H) (p:=p) i U N • f U∂(η i)):= by
   unfold scene; rw [integral_withDensity_eq_integral_toReal_smul (dose_env Y h|>.meas.ennreal_ofReal) (Eventually.of_forall fun _=> ENNReal.ofReal_lt_top)]; simp_rw [ENNReal.toReal_ofReal (dose_positive Y h _).le]
lemma scenery (h:i ≤ N) (f:Config G (n i) → ℝ) : (∫ U,f U∂(μ i)) = (∫ U,(Q i).eval U * f U∂(η i)) / ℤ∞:= by
   rw [account Y h,← integral_div]; simp only [dose,smul_eq_mul,div_mul_eq_mul_div]
lemma violet (h:i ≤ N) (f:Config G (n i) → ℂ) : (∫ U,f U∂(μ i)) = (∫ U, ((Q i).eval U:ℂ) * f U∂(η i)) / (ℤ∞:ℂ):= by
   rw [account Y h,← integral_div]; simp_rw [dose,Complex.real_smul,Complex.ofReal_div,div_mul_eq_mul_div]
lemma invoice (h:i ≤ N) (f:Config G (n i) → ℂ): (∫ U, ((Q i).eval U:ℂ) * f U∂(η i))=(ℤ∞:ℂ)* ∫ U,f U∂(μ i):=by rw [violet Y h, mul_div_cancel₀]; exact_mod_cast (partition_pos _).ne'
lemma onstage (f:Config G (n N)→ ℂ) (h:Integrable f (law G (n N) β)): (∫ U,f U∂(μ N)) = moment β f:= by rw [violet Y le_rfl,moment_formula _ _ h,(Y.starts N p).2,div_eq_mul_inv,mul_comm]
lemma retune (t:Signed)(b:Site (n i))(h:i≤N) (f:Config G (n i)→ ℝ):
    (∫ U,f (pull t b U)∂ (μ i))=∫ U,f U∂(μ i):=by
   rw [account Y h, account Y h]; unfold dose; conv_lhs => arg 2; ext x; rw [← (rep_spins t Y h x b)]
   exact (prior_pull t b).integral_comp (embedding_pull t b) (fun U=> ((Q i).eval U / ℤ∞) • f U)
-- via Push back.Local
lemma enact (q:k ≤ i) (hi:i ≤ N) : pushTo H N p q (fun U=> ((Q i).eval U:ℂ)) = (fun U=> ((Q k).eval U:ℂ)):=by
    induction i, q using Nat.le_induction with
    | base=> simp
    | succ i q ih =>
      let V:= (H.levels.clock.op i p); let g(x:Config G (n (i+1))):= ((Q (i+1)).eval x:ℂ)
      rw [pushTo_next H N p q]; have he: V.push (H.β N p (i+1)) g = (fun U => ((Q i).eval U:ℂ)):=by
           funext P; have ht:=Y.steps N p i hi|>.1; rw [ht]; unfold StepData.push; rw [← integral_complex_ofReal]; apply integral_congr_ae (Eventually.of_forall fun v=>?here); case here=> unfold g V; simp [Complex.real_smul]
      rw [show _= _ from he,ih (le_trans i.le_succ hi)]
lemma retro (q:k ≤ i) (hi:i ≤ N) (f:Config G (n k)→ ℂ) (he:Envelope f):
    (∫ U,backTo H N p q f U∂(μ i))=∫ U,f U∂(μ k):=by
   rw [violet Y hi,violet Y (q.trans hi),← pushTo_dual H N p q he (fun U=>((Q i).eval U:ℂ)) (((Q i).envelope (Y.represents N p i hi).good).integrable (η i)).ofReal, enact Y q hi]
local notation "P*" => H.levels
lemma repeated (h:i≤ k) (he:k≤N) (f:Config G (n k)→ ℂ) (d:ℕ) (hg:Interior (window 0 d) f) (hp:room H.levels i k d) :
    let M:= tilesAt H.S p h
    ‖∫ U,f U∂ (μ k)‖ ^ Fintype.card M.Cell ≤ ‖∫ U, M.fullAt (fun _=> f) U∂(μ k)‖:=by
    intro M; let T:= tilesAt H.S p (h.trans he); let g:=backTo H N p he f
    have hx:T.chamber 0=(center H.S p (h.trans he) 0).chamber 0:=rfl
    have hi: Interior (T.chamber 0) g:=by
        have hv := backTo_local H N p h he 0 d (F:=f)
        apply Interior.enlarges (hv ?_) (room_fits p (P*) d h he hp 0)
        rw [anchor, ← Ratio.root_embed,map_zero]; exact hg
    have ht : Seam G (n N) β := laws _ _ _ (by
      refine le_trans ?_ (Y.represents N p N le_rfl).band.1; have hh:= H.levels.fits.delayed N
      linarith only [hh])
    have hR: backTo H N p he (M.fullAt fun _=> f) = (T.fullAt fun _=>g) := backTo_copies H N p h he Finset.univ f d hg hp
    have hh := T.planted (ι:=Unit) ht (fun _ => (0:T.Cell)) (injective_of_subsingleton _) (fun _ => g) (fun _ => hi)
    simp only [Fintype.prod_unique,Tiling.copy_zero] at hh
    rw [← retro Y he le_rfl f (cylinder_env hg),onstage Y _ (hi.integrable _), ← retro Y he le_rfl (M.fullAt (fun _=> f)) (Joint.incoming_env H p h (cylinder_env hg) Finset.univ), hR,onstage Y _ (T.manyIntegral β _ fun _=>hi)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hh (Fintype.card T.Cell)).trans_eq (T.powering β g)
end YM.OPE.Therm
