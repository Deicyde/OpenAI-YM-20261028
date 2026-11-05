import YM.MultipleContact.Center.Fixture
import YM.MultipleContact.Center.Ray
/-! Test a single untruncated internal packet (or a predictor) against fixed determination probes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace YM.MultipleContact.Centered
open Set Filter Function Table Extraction Spec Drama Script Scene ScheduleRow Bunching
open March Joins
open scoped Classical ContDiff Topology BigOperators
lemma common_radii {ι:Type*}[Fintype ι](r:ι→ℝ)(he:∀i,0<r i):∃ δ:ℝ,0<δ∧∀i,δ≤ r i:=by
      have h(i:ι):∀ᶠ δ:ℝ in 𝓝[>] 0,δ ≤ r i:= Eventually.filter_mono (nhdsWithin_le_nhds) (by exact (gt_mem_nhds (he i)|>.mono fun δ (h:δ∈ Set.Iio (r i))=>le_of_lt h)) -- invalid maybe
      exact ((show ∀ᶠ δ:ℝ in 𝓝[>] 0,0<δ from self_mem_nhdsWithin).and (eventually_all.mpr h)).exists
      -- alternative any λ in punctured near0; eventually. Use nonempty eventually. (No placeholders)
variable {G:Gauge}{L:Register G}{S:Table L}{n h:ℕ}[Inhabited (Fin n)]
variable (V:Fin n→ S.Tag)(N:Lattice.Side)(D:Detector S h)
def GapF (ρ:ℝ)(x:Fin n→E4):=(∀i j,i≠j → ρ/4<‖x i-x j‖)∧∀i,‖x i‖ < 2*N.val*ρ
def Nearish (p:March S) (ρ:ℝ)(x:Fin n→E4):=p.allow N ρ x ∧ GapF N ρ x
def picketOps (p:March S)(e:Exterior L):Fin (e.n+1)→ March S:=Fin.cons (α:=fun _=> March S) p (fun t=> .field (e.letter t).1)
def probeData (p:March S)(q:p.Data)(e:Exterior L):∀i:Fin (e.n+1),(picketOps p e i).Data:=Fin.cases q fun i:Fin e.n=> S.project _ (e.letter i).2
lemma fullEquation {p:March S}(x:Fin n→E4)(e:Exterior L)(q:p.Data):
    work (n:=fun _=>n) (picketOps p e) (fun (_:Fin (e.n+1))=>V) e.point (fun _=>x) (probeData p q e) = (p.payload V (e.point 0) x q) * prospect S e:= by
       unfold work; rw [Fin.prod_univ_succ]; congr 1
variable (ε:ℝ) (p:March S)(q:p.Data)
lemma point_load (e:Exterior L)(ρ:ℝ): plainLoad (S:=S) (n:=fun _=>n) (picketOps p e) (fun (_:Fin (e.n+1)) =>V) ε (fun _=>ρ) (probeData p q e) = p.credit V ε ρ q *∏ j:Fin e.n,max 1 ‖S.project _ (e.letter j).2‖:=by
       unfold plainLoad; rw [Fin.prod_univ_succ]; congr 1; refine Finset.prod_congr rfl fun i _=>?_
       exact show ρ ^ (0:ℝ) * max 1 ‖S.project _ (e.letter i).2‖ = _ from by rw [Real.rpow_zero,one_mul]
lemma exists_clear (e:Exterior L): ∃κ:ℝ,0<κ∧ ∀i j:Fin (e.n+1),i≠ j → κ ≤ ‖e.point i-e.point j‖:= by
        let r:Fin (e.n+1)× Fin (e.n+1)→ ℝ:=fun (i,j)=>if i=j then 1 else ‖e.point i-e.point j‖
        have hr(u):0<r u:= by rcases u with ⟨a,b⟩; change 0<(if a=b then (1:ℝ) else _); split_ifs with h; exact zero_lt_one; simpa only [norm_pos_iff,sub_ne_zero] using! e.clear.ne h
        obtain ⟨κ,hκ,hu⟩:=common_radii r hr; exact ⟨κ,hκ,fun i j h=> by simpa [r,h] using hu (i,j)⟩
omit V q ε in
lemma picket_space (e:Exterior L){κ:ℝ}(h:0<κ)(hu:Close e.point.ofLp κ)(u r:ℝ)(hf:0<u)(x:Fin n→E4)(h':Nearish N p u x)(hx:u < min r (κ/(2*N.val))):
      Permit (picketOps p e) (n:=fun _=>n) κ r N (fun (_:Fin (e.n+1))=> u) e.point (fun _=>x) ∧ joint e (points x)∈ conf _:=by
        have hr:u<r:= hx.trans_le (min_le_left ..); refine ⟨⟨hu,fun _=>⟨hf,hr⟩,?_⟩,joint_clear e (fun i=>hu i.succ 0 (Fin.succ_ne_zero i)) _ ?_ ?_⟩
        · exact Fin.cases h'.1 fun i=> True.intro
        · have hp:u*(2*N.val)<κ:= (lt_div_iff₀ (by positivity : 0<(2*N.val:ℝ))).1 (hx.trans_le (min_le_right ..))
          intro i; exact (h'.2.2 i).trans (by linarith only [hp])
        exact fun i j h=>by_contradiction (fun hu'=> by have hv:=h'.2.1 i j hu'; change x i=x j at h; exact hv.not_ge (by rw [h,sub_self,norm_zero];positivity)) -- shadow h'
omit q
lemma estimatePicket {h:ℕ}(p:March S)(f: (Fin n→ E4)→ S.Field h){t:ℝ}(H:S.Hierarchy) (D : Detector S h) (hp:∀e∈D.probes, ∃K r:ℝ,0<K ∧ 0<r ∧ ∀ρ:ℝ,(0<ρ ∧ ρ<r)→ ∀x:Fin n→E4,Nearish N p ρ x → joint e (points x) ∈ conf _ →
 ‖evaluation S ((Scene.packet S V x (e.point 0)-insertion S (e.point 0) (f x))*prospect S e)‖ ≤ K*ρ^t):
  ∃K r:ℝ,0<K ∧ 0<r ∧ ∀ρ:ℝ,(0<ρ ∧ ρ<r) →∀x:Fin n→E4,Nearish N p ρ x → ‖D.apply V (points x)-f x‖≤K*ρ^t:=by
        choose K R hk hk' husing using fun i:D.probes=>hp i i.property
        choose κ hk₀ hκ using fun i:D.probes=>exists_clear i.val
        obtain ⟨r,hr,hrel⟩:=common_radii (fun i:D.probes=>min (R i) ((κ i)/(3*N.val))) (fun i=>lt_min (hk' i) (div_pos (hk₀ i) (by positivity)))
        obtain ⟨A,ha⟩:=Finite.bddAbove_range (α:=ℝ) K
        let A0:=max 1 A; let B:= (LinearMap.toContinuousLinearMap D.decode); let B':=max 1 ‖B‖
        have he(i):K i≤ A0:=(ha (Set.mem_range_self _)).trans (le_max_right ..)
        have hA:0<A0:=lt_max_of_lt_left zero_lt_one; have hB:0<B':=lt_max_of_lt_left zero_lt_one
        refine ⟨B'*A0,r,mul_pos hB hA,hr,fun ρ hρ x hx=>?_⟩
        let g (i:D.probes):ℂ:=raw S V (points x) i.val - response S h i (f x)
        have hEq : D.apply V (points x) - f x=B g:=by unfold Detector.apply; nth_rw 1 [← D.fixes (f x)]; exact Eq.symm (B.map_sub _ _)
        rw [hEq]
        suffices H0 : ‖g‖ ≤ A0*ρ^t by refine (B.le_opNorm _).trans ((mul_le_mul (le_max_right ..) H0 (norm_nonneg _) hB.le).trans_eq (by ring))
        refine (pi_norm_le_iff_of_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hρ.1.le _))).2 fun i=>?_
        have hProbe:= (hrel i).trans (min_le_left (R i) _)
        have hS:(κ i)/(3*N.val)≤κ i/(2*N.val):= by gcongr <;> try first | exact (hk₀ i).le | norm_num
        have hh:= (picket_space N p i.val (hk₀ i) (hκ i) ρ _ hρ.1 x hx (hρ.2.trans_le (hrel i|>.trans (min_le_min_left (R i) hS)))).2
        let T:=H.laws.toSymmetric
        have h0: g i = evaluation S ((packet S V x (i.val.point 0)-insertion S (i.val.point 0) (f x))*prospect S i.val):= (by rw [sub_mul,map_sub,strict_packet S T _ _ _ hh,prospect_cost S T])
        exact (congr_arg (‖·‖) h0).trans_le ((husing i ρ ⟨hρ.1,hρ.2.trans_le hProbe⟩ x hx hh).trans (mul_le_mul_of_nonneg_right (he i) (Real.rpow_nonneg hρ.1.le _))) -- norm mismatch
end YM.MultipleContact.Centered
