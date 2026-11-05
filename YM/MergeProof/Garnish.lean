import YM.Extra.MULTISOURCE_BOUNDS.Root
import YM.MergeProof.Accent
import YM.MergeProof.Tongue


set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Local  Source Extra.Multi
variable {t d c e : ℝ} {o:V→ Site n}
variable (ψ:V→MergeProof.Response G n)
structure Garnish (P:BudgetPoint)(o:V→Site n)(ψ:V→MergeProof.Response G n)(w:V→ℝ) (e v:ℝ):Prop where
   yes i p: Local.Attaches P.threshold p (ψ i p)
   tracks i p: ψ i p ≠ 0 → o i∈p
   fee i:∃ f: Support n→ℝ, (∀ j,0≤f j∧ ∀ U, ‖ψ i j U‖≤ f j)∧ (∑ j,Real.exp ((e+1)*coverNumber P.B j)* (w i*f j)) ≤ v
-- Need marks B not Track for zeros.
def conviction (B:Census V)(j:V×Support n)(U:Config G n): Poly B:= Poly.send (B.fire j.1) (ψ j.1 j.2 U)
-- even quiet support ∅
variable {w:V→ℝ}{P:BudgetPoint}
lemma satin (F: Y→ℂ) (k:B.Mode)(b:ℝ)(hb:0 ≤ b)(h:∀ i,‖F i‖ ≤ b): Loci w (fun U=> Poly.send k (F U)) (Poly.toll w k*b):=by
   let p(i:B.Mode):= if i=k then b else 0; refine ⟨p,fun i=> ?_,fun U i=>?_,?_⟩
   · change 0 ≤ p i; unfold p; split;exact hb;rfl
   · rw [Poly.part_send]; unfold p;split; exact h _; simp
   simp [wordsPrice,p,mul_ite]
variable [Fintype V]
variable (B:Census V)
local notation "Λ" => conviction ψ B
def kelp (U:Config G n):=∑ j, conviction ψ B j U
variable (h:Garnish P o ψ w e c)
include h
lemma dresses (j:V×Support n) : Borne o j.2 (conviction ψ B j) P.threshold:=by
   let u:= ψ j.1 j.2; let b:= B.fire j.1; let hp:= h.yes j.1 j.2
   refine ⟨fun U V hx ht=>congr_arg (_root_.YM.Marker.Poly.send b) (hp.sites _ _ hx ht),fun g U=>congr_arg (Poly.send b) (hp.symmetry g U),fun i=>?_,fun U=>?_⟩
   · simp_rw [conviction,Poly.part_send]; split;exact hp.borel; exact measurable_const
   by_cases hv:u=0
   · change Scoped _ (Poly.send b (u U)); rw [hv,show (0: Config G n→ℂ) U=0 from rfl,Poly.send_zero]; exact fun _ _=> rfl
   apply scope_send; exact fun i hi=> (Finset.mem_singleton.mp hi).symm ▸ h.tracks _ _ hv
omit [Fintype V] in
lemma husk (j: V × Support n) (U) : conviction ψ B j U≠0 → ¬ Healthy P.threshold j.2 U:=fun he hv=> he (by unfold conviction; rw [(h.yes j.1 j.2).healthy_zero U hv,Poly.send_zero])
lemma stock {N:ℕ}(hv:∀ i,0 < w i)(hh:Occupancy o N)(ht:0 ≤ c): Towed w Prod.snd (conviction ψ B) P.B e (N*siteFactor P.B*c):=by
   choose f hf he using h.fee
   let X(j:V×Support n):= j.2; let r(i:V)(j:Support n):= if o i∈j then f i j else 0; let u(j: V ×Support n):= w j.1*r j.1 j.2
   have hp i j: 0≤ r i j:=by unfold r;split;exact (hf ..).1; rfl
   let m(j:V×Support n):= (B.fire j.1).val
   refine ⟨u,Summable.of_finite,root_hit (X:=X) (mode:=m) hh (fun j=>mul_nonneg (hv _|>.le) (hp ..)) ht ?_ ?_,fun j=>?_⟩
   · intro j hz; refine ⟨j.1,Finset.mem_singleton_self _,?_⟩; by_contra hn; unfold u r at hz; rw [if_neg (show o j.1 ∉ j.2 from hn),mul_zero] at hz; linarith
   · intro i; let w' j:= if o i∈j then u (i,j) else 0
     have hk := he i; refine ⟨fun i=> ?_,Summable.of_finite,le_trans ?_ hk⟩
     · dsimp only; split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hv _|>.le) (hp ..)); rfl
     rw [tsum_fintype,Fintype.sum_prod_type,sum_eq_single i];
     · refine Finset.sum_le_sum fun j _=> ?_; refine (if_pos (show i∈m (i,j) from Finset.mem_singleton_self _)|>.trans_le ?_)
       exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (show r i j ≤ f i j from by unfold r; split; rfl; exact (hf ..).1) (hv _|>.le)) (Real.exp_pos _).le
     · intro j _ hj; exact sum_eq_zero fun q _=> if_neg (fun he=> hj (Finset.mem_singleton.mp he|>.symm))
     simp
   have he:∀ U, ‖ψ j.1 j.2 U‖≤ r j.1 j.2:=by
      intro U; unfold r; split; exact (hf ..).2 _; next he=> rw [not_not.mp (mt (h.tracks j.1 j.2) he)]; simp
   simpa only [Poly.solo_toll] using! satin (ψ j.1 j.2) (B.fire _) _ (hp ..) (w:=w) he
end YM.MergeProof.Accent
