import YM.TraceExtension.Det.Chide
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{I J:Type}[Fintype I][Fintype J]{k m n:ℕ}{α τ A C D E:ℝ}
variable {l:I→Site f}{d:J→Site f}{F:Rays I→ℝ}{V:Rays J→ Rays I}
lemma drive_elem (h: Drive d l V k A)(hz:0≤A)(a:ℝ)(i:I) : Pet d (l i) (fun z=> V z i) a A k:=by
    let L: Rays I→L[ℝ] ℝ:= ContinuousLinearMap.proj i
    refine ⟨L.contDiff.contDiffAt.comp _ h.side,fun j hj q=>?_⟩
    by_cases hx: entry (fun z=> V z i) 0 q=0
    · rw[hx,norm_zero];positivity
    have hh:= h.dut i j hj q hx; unfold spanSites; simp_rw [hh,separation_self,sum_const_zero]; simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one]; exact h.quote i j hj q
lemma Pet.weighted {α:Type}{s:Finset α}{F:α→Rays J→ℝ}{D:α→ℝ}(x:Site f)(h:∀ i∈s, Pet d x (F i) τ (D i) m) {C:ℝ}(he:∑ i∈s,D i ≤ C): Pet d x (fun z=>∑ i∈s,F i z) τ C m:=⟨ContDiffAt.sum fun i hi=> (h i hi).1, (beacon_sum (fun i hi=> (h i hi).2) (fun i hi=>(h i hi).1)).mono he⟩
def castoff (m K:ℕ)(C A:ℝ):= K*((2:ℝ)^m * ‖ContinuousLinearMap.mul ℝ ℝ‖ * (C*lodge m (1+A*K))*A)
lemma Drive.laced {K:ℕ}(h:Drive d l V (m+1) A)(hV:V 0=0)(hf:ContDiffAt ℝ ω F 0)(hp:Scatter l α (m+1) F 0 C)(hα:0 ≤ α)(ha:0 ≤ A)(hc:0≤C)(hk:Multiplicity l K)(i:J): Pet d (d i) (fun z=> fderiv ℝ (F ∘ V) z (bolt i)) (α/(m+1:ℝ)) (castoff m K C A) m:=by
    let g j(z:Rays J):= V z j
    let B (j:I)(x:Rays I):= fderiv ℝ F x (bolt j)
    let D (j:I)(x:Rays J):=fderiv ℝ (g j) x (bolt i)
    have hx : (fun z=> fderiv ℝ (F ∘ V) z (bolt i))=ᶠ[𝓝 0] fun z=>∑ j:I,B j (V z)*D j z:=by
       have he: Tendsto V (𝓝 0) (𝓝 0):= hV ▸ h.side.continuousAt.tendsto
       filter_upwards [h.side.eventually (by simp), he.eventually (hf.eventually (by simp))] with x hx hv
       rw[fderiv_comp x (hv.differentiableAt (by simp)) (hx.differentiableAt (by simp))]
       let A:= fderiv ℝ F (V x); let M:= fderiv ℝ V x (bolt i)
       have hM : M=∑ i:I,M i • bolt i:=by ext i; rw[Finset.sum_apply];simp [bolt,Pi.single_apply]
       have ht(j:I): M j=D j x:=by
           let L:Rays I→L[ℝ] ℝ:=ContinuousLinearMap.proj j
           unfold D;rw[show g j=L ∘ V from rfl,fderiv_comp _ L.differentiableAt (hx.differentiableAt (by simp)), L.fderiv];rfl
       change A M=_; rw[hM,map_sum]; apply sum_congr rfl; intro j _; rw[map_smul,ht j,smul_eq_mul,mul_comm]
    have hD: Drive d l V m A:=⟨h.side, fun j b p=>h.quote j b (p.trans (Nat.le_succ _)),fun j b p=>h.dut j b (p.trans (Nat.le_succ _))⟩
    let L:=α/(m+1:ℝ)
    let Z:ℝ:=C*lodge m (1+A*K); have hz:0≤Z:=mul_nonneg hc (lodge_n (by positivity)); have hL:0≤L:=by unfold L; positivity
    have hv(j:I): Pet d (l j) (B j ∘ V) L Z m:=by
       refine Pet.rein (D:=d) ?_ hD hV ha hc hα hk
       refine ⟨(hf.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const,fun i hi q=>?_⟩
       let p:Fin (i+1)→ I:= Fin.snoc q j
       have hn:=hp (i+1) (by omega) p (Fin.last i)
       unfold B; rw[← entry_d hf q]; unfold p spanSites at hn; simp only [Fin.snoc_last,Fin.sum_univ_castSucc, Fin.snoc_castSucc,separation_self,add_zero] at hn; exact hn
    let P:ℝ:= (2:ℝ)^m * ‖ContinuousLinearMap.mul ℝ ℝ‖*Z*A; have hP:0≤P:=by unfold P; positivity
    have ht (j:I): Pet d (d i) (D j) L (if l j=d i then A else 0) m:=by
        have h':= (drive_elem h ha L j).halp i; split; next e => rw [e, Decay,separation_self] at h'; simp only[Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at h';exact h'
        next e =>
           refine ⟨h'.1,fun a ha q=>?_⟩; rw[zero_mul, norm_le_zero_iff]; unfold D g; rw[← entry_d (drive_elem h (show 0≤_ from by assumption) L j).1 q]; by_contra he; apply e; obtain hr:= h.dut j (a+1) (by omega) (Fin.snoc q i) he (Fin.last a); simp only[Fin.snoc_last] at hr;exact hr.symm
    have hh (j:I): Pet d (d i) (fun z=> B j (V z)*D j z) L (if l j=d i then P else 0) m:=by
        by_cases h₀:l j=d i
        · have hx:= ht j; rw[if_pos h₀] at hx ⊢; exact Pet.bins (ContinuousLinearMap.mul ℝ ℝ) (h₀ ▸ hv j) hx hz ha
        have hx:=ht j; rw[if_neg h₀] at hx ⊢; let U:= ContinuousLinearMap.mul ℝ ℝ
        have hp:= Pet.bins U ((hv j).switch hz (d i) hL) hx (by positivity) le_rfl; rw [mul_zero] at hp; exact hp
    refine (Pet.weighted (d i) (fun j _=>hh j) ?_).grows hx.symm
    rw[← Finset.sum_filter, Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le (α:=ℝ) |>.mpr (hk (d i))) hP
-- global rows
abbrev Leg {r:ℕ} (x:Lines G f r):=x.1
def Park {r b:ℕ}(V:WildM G f r b)(α C:ℝ)(m:ℕ): Prop:= ∀ i j, Pet Prod.fst i.1 (fun z=> V z i j) α (C*Decay α i.1 j.1) m
lemma H_park (G:Gauge)(p:Clip)(m:ℕ)(hc:0<α)(A:ℝ):∃ η D, 0<η∧0≤D∧∀ (n:Side)(R:PathData G)(D':ℝ), R.Bounds p α A D'→ Park (flare p R ∘ input G n) η D m:=by
    obtain ⟨a,C,ha,hC,H⟩:= lone_spread p G α A hc (m+2); obtain ⟨Z,hZ,h⟩:= speak G (m+2)
    refine ⟨_,_,show 0 < a/((↑(m+1):ℝ)+1) by positivity, show 0≤ castoff (m+1) (Fintype.card (Loc G 1)) C Z by unfold castoff; have hp:=lodge_n (m:=m+1) (A:=1+Z*Fintype.card (Loc G 1)) (by positivity); positivity,fun n R D' hp i j=>?_⟩
    let F:= intended (m:=n) p R; let X:= bchip G n; let U(z):=mainTerm p R (splitp G n z)
    obtain ⟨hx,he⟩:= H R D' hp n
    have hu := Drive.laced (m:=m+1) (h n) (show X 0=0 by unfold X bchip; rw[splitp_0,content_one]) hx he ha.le hZ hC (pay_gate G n) (.inr i)
    let W(t:Acr G n):= fderiv ℝ (F ∘ X) t (bolt (Sum.inr i)); let L:= fun t=> fderiv ℝ W t (bolt (.inr j))
    have hf : U=ᶠ[𝓝 0] F ∘ X:=by filter_upwards [(show Tendsto (splitp G n) (𝓝 0) (𝓝 1) from splitp_0 ▸ splitp_n.cont.tendsto).eventually content_encodes] with x hx; exact congr_arg (mainTerm p R) hx.symm
    have hh:ContDiffAt ℝ ω U 0:= Work.F02.mainTerm_contDiffAt hp splitp_n
    have hw: W =ᶠ[𝓝 0] fun z=> fderiv ℝ U z (bolt (.inr i)):=by filter_upwards [EventuallyEq.fderiv (𝕜:=ℝ) hf] with v hv; exact DFunLike.congr_fun hv.symm _
    refine (((hu.grows hw).halp (Sum.inr j)).compL (taken G n)).grows ?_
    filter_upwards [soft_hx U hh] with z hz
    simp only[Function.comp_apply]
    have ht:=damage_symm (pocket (Lines G n 1)) (F:=burn p R (input G n z)) (burn_cov _ hp)
    change (flare p R (input G n z)).transpose=flare p R (input G n z) at ht
    have hr: snip U z= burn p R (input G n z):=funext (fun v: Link G n=>by simp [snip,U,splitp,burn,aright,aleft])
    rw[← hz j i, hr, bockat,bockat, ← burn_p (input G n z) p R]
    exact congr_arg (fun H:Matrix (Lines G n 1) (Lines G n 1) ℝ=>H i j) ht
end YM.Trace.Det
