import YM.TraceExtension.Pills.Light
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pills
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine Fen Kits
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} (P:ℕ→Wo G) (L:Finset ℕ) {A a:ℝ}
private lemma epoll {f:ℕ→ℝ}(h: HasSum f 0) {w:ℕ→ℝ} (hp:SumBudget (fun i=> if i∈L then 0 else w i) A)(hx:∀ i,|f i| ≤ w i): |∑ i∈L,f i| ≤ A:=by
    let g(i):= if i∈L then f i else 0; have he: HasSum g (∑ i∈ L,f i):=by rw [show (∑ i∈L,f i)=∑ i∈L,g i from Finset.sum_congr rfl (fun i hi=> by simp [g,hi])]; exact hasSum_sum_of_ne_finset_zero (fun i hi=> if_neg hi)
    have ht:= h.sub he
    have hh(i): ‖f i-g i‖≤ (if i∈L then 0 else w i):=by unfold g; split <;> simp[hx i]
    rw[zero_sub] at ht; rw [← abs_neg, ← ht.tsum_eq]; apply le_trans (norm_tsum_le_tsum_norm ht.summable.norm); exact (Summable.tsum_le_tsum hh ht.summable.norm hp.2.1).trans hp.2.2
def biete(G:Gauge)(A:ℝ):ℝ:= Fintype.card Colour*(Fintype.card (Cards G)*(A+4*A))
lemma washM (h:Silent P) (hp:SumBudget (fun i=>if i∈L then 0 else (P i).budget a * (1+(P i).length)) A)(ha:0<a):
    let c:= biete G A; (∑ i:Colour,(ink L P i).magnitude)≤c:=by
    intro c; let g(i):=(P i).budget a*(1+(P i).length); have he(w:Flop)(x:Cards G)(i:ℕ):|charge (P i) w x|≤ (P i).budget a:=by
        apply le_trans ?_ ((P i).lower_budget a ha); unfold charge; split_ifs; · exact coeff_le ..
        rw[abs_zero]; unfold Atom.magnitude; positivity
    have hA := Cost.nonneg hp; let M:ℝ:=A+4*A
    have hP(i):0 ≤ (P i).budget a:=by unfold Atom.budget Atom.magnitude; positivity
    have hv(w:Flop)(x:Cards G): |strum L P w x| ≤ A:= epoll L (h w x).1 (w:=g) hp (fun i=> (he w x i).trans (le_mul_of_one_le_right (hP i) (by simp)))
    have hz(w:Flop)(x:Cards G)(v:Axis):|thud L P w v x| ≤ A:=by
        apply epoll L ((h w x).2 v) (w:=g) hp
        intro i; rw[abs_mul]; apply mul_le_mul (he w x i) ?_ (abs_nonneg _) (hP i)
        have ht: (delta (P i) v).natAbs ≤ (P i).length:= (single_le_sum (f:=fun j=> (delta (P i) j).natAbs) (fun j _=>Nat.zero_le _) (mem_univ v)).trans (delta_size (P i))
        have he: |((delta (P i) v:ℤ):ℝ)| ≤ (P i).length:=by exact_mod_cast (show |delta (P i) v| ≤ ↑(P i).length by rw [← Int.natCast_natAbs]; exact_mod_cast ht)
        linarith
    have hx(w:Colour)(v:Cards G): |(ink L P w).coeff v| ≤ M:=by
       unfold M ink; cases h':w.2
       · change |- _ + (∑ i,thud L P w.1 i) v| ≤ _; rw[Finset.sum_apply]; refine (abs_add_le ..).trans (add_le_add ((abs_neg _).trans_le (hv w.1 v)) ((Finset.abs_sum_le_sum_abs ..).trans (le_trans (Finset.sum_le_sum (fun j _=> hz _ _ _)) ?_))); simp[Axis]
       rename_i i; change |-(thud L P w.1 i v)|≤_; refine ((abs_neg _).trans_le (hz w.1 v i)).trans (le_add_of_nonneg_right (by positivity))
    apply (sum_le_sum (fun i (_:i∈univ)=>Finset.sum_le_sum (fun v _=> hx i v))).trans; simp [c,M,biete,mul_add]
lemma washR {n:Side}(R:Rep G n)(σ A B q:ℝ)(r:ℕ)(hp:R.path.Bounds R.clip σ A B)(hq:0<q): ∀ᶠ L:Finset ℕ in atTop,
    let P:=R.path.loop; let Q:=spikes R loopF L r; ∑ i:Colour,(ink Q P i).magnitude≤ biete G (q+Real.exp (-(σ/4)*r)*(momentPrice 1 (σ/2)*B)):=by
    filter_upwards [coatout R loopF 1 r B q hp.width (offloop R hp) hq] with L hL
    intro V Q; apply washM V Q (silent_of_bounds hp) (a:=σ/4) _ (by have h:=hp.width; positivity)
    convert! hL using 1; ext i
    by_cases h:i∈ L ∧ rowL R loopF i≤r
    · rw[if_pos (show i∈Q from mem_filter.mpr h),if_pos h]
    rw [if_neg (show _ from fun he:i∈Q=>h (mem_filter.mp he)), if_neg h,pow_one]; rfl
end YM.Trace.Pills
