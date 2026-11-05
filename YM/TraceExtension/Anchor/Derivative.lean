import YM.TraceExtension.Anchor.Persist
import Mathlib.Analysis.Calculus.Taylor

/-!
# Reading a derivative via anchor seats
Use summation by parts on the calibration. A deliberately **high order** centered stencil for
this step so the axes-mixing estimates with coarse reference labels may employ the crude upper
bound *with* possible large unit part. No convergence claim at neighboring points of the
original Wilson top.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Pull
open Function Filter Set MeasureTheory Analysis Extraction Around Table Ward Cells Lattice Wilson Next.UVStress
open Asymptotics Finset Work.A01
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book} {d : ℕ}

-- center weights, nonzero offsets both sides
def steps (i:Fin 4):ℕ:= i.val+1
def cash : Fin 4 → ℝ:= ![4/5,-1/5,4/105,-1/280]
lemma credit (k:ℕ)(h:k≤8) : ∑ i : Fin 4, cash i*(((steps i):ℝ)^k-(-↑(steps i) : ℝ)^k)=(if k=1 then 1 else 0):= by interval_cases k<;> rw [Fin.sum_univ_four,show cash 0=4/5 from rfl,show cash 1= - (1/5:ℝ) from by change -1/5 = -(1/5:ℝ); ring,show cash 2=4/105 from rfl,show cash 3= -(1/280:ℝ) from by change -1/280= -(1/280:ℝ); ring] <;> norm_num [steps]
def dTap {A:Type*}[AddCommGroup A][Module ℝ A] (f:ℤ→ A) (l:ℤ):=∑ j : Fin 4, cash j • (f (l+steps j)-f (l-steps j))
variable (HE:S.Hierarchy)
section
variable (I:Watch C)(a:Axis)

private def spin (d:ℕ)(v:S.Field d) (t:ℝ) := plant I S d (t • basis a) v
lemma spin_home (v:S.Field d) : spin I a d v 0 = I.tester S d v:=by simp [spin,tester_home]
include HE
lemma spin_smooth {x:ℝ}(hv: rows I (x • basis a)∈conf _) (v:S.Field d) : ContDiffAt ℝ ∞ (fun t:ℝ=> plant I S d (t • basis a) v) x:= by
   simp_rw [plant,front_eval]; exact (smooth_cons _ HE.smooth _ _ hv).comp x (f:=fun t:ℝ=> t • basis a) (by fun_prop)

variable (W:DiffPlan S)(hw:W.Derivatives S)
include hw
private lemma stepD (t r x:ℝ)(hx: rows I ((x+t*r) • basis a)∈conf _) (v:S.Field d) : HasDerivAt (fun t:ℝ=>spin I a d v (x+t*r))
        (r • spin I a (d+1) (W.deriv d a v) (x+t*r)) t:= by
   simp_rw [spin,plant,front_eval,rows]
   let g:ℝ→ E4:= fun z=> (x+z*r) • basis a; have hG: HasDerivAt g (r • basis a) t:=by unfold g; exact (by simpa only [one_mul] using! ((((hasDerivAt_id' t).mul_const r).const_add x).smul_const (basis a)))
   rw [← show Analysis.D (basis a) (fun y=>disc (Fin.cons ⟨d,v⟩ (S.classTokens ∘ I.q)) (Points.cons y (Points.tail I.held))) (g t)=_ from D_cons HE.smooth W hw v _ hx a]
   unfold Analysis.D; rw [← map_smul]
   exact ((((smooth_cons _ HE.smooth _ _ hx).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt _ hG)

private def higher (W:DiffPlan S)(d:ℕ)(a:Axis): (m:ℕ) → S.Field d →ₗ[ℂ] S.Field (d+m)
  | 0=> LinearMap.id
  | i+1=> (W.deriv (d+i) a).comp (higher W d a i)
private lemma spinIter {q:ℝ} (hq:0<q) (v:S.Field d) (x r:ℝ)(hx:∀ t∈Icc (0:ℝ) q,rows I ((x+t*r) • basis a) ∈ conf _) (i:ℕ) (t:ℝ)(ht : t∈Icc (0:ℝ) q):
    iteratedDerivWithin i (fun s=> spin I a d v (x+s*r)) (Icc 0 q) t = r^i • spin I a (d+i) (higher W d a i v) (x+t*r):=by
   induction i generalizing t with
   | zero=> simp [higher]
   | succ i IH=>
     rw [iteratedDerivWithin_succ]
     let Q:= higher W d a i v
     let f(z:ℝ):=spin I a (d+i) Q (x+z*r)
     have he: iteratedDerivWithin i (fun s=> spin I a d v (x+s*r)) (Icc 0 q) =ᶠ[nhdsWithin t (Icc 0 q)] r^i • f:= by filter_upwards [self_mem_nhdsWithin] with z hz; exact IH z hz
     have hv := (((stepD HE I a W hw _ r x (hx t ht) Q).const_smul (r^i)).hasDerivWithinAt).congr_of_eventuallyEq he (IH t ht)
     rw [hv.derivWithin (uniqueDiffOn_Icc hq t ht),smul_smul,pow_succ]; rfl

omit hw in
lemma spin_cont {r:ℝ}(ht: rows I (r • basis a)∈conf _): ContinuousAt (fun z:ℝ=> (plant I S d (z • basis a)).toContinuousLinearMap) r:=by
   have hz (v:S.Field d) := (spin_smooth HE I a ht v).continuousAt
   exact YM.Dash.fit_plane _ _ hz
private lemma taylor_sum {q:ℝ}(hq:0<q)(n:ℕ)(hl:1 ≤ n)(hn:n≤8) (v:S.Field d) (x:ℝ)(h:∀ (j:Fin 4)(t:ℝ),t∈Set.Icc (0:ℝ) q→ rows I ((x+t*↑(steps j)) • basis a)∈conf _ ∧ rows I ((x+t*(-↑(steps j):ℝ)) • basis a)∈conf _ ) (t:ℝ) :
    let T (r:ℝ):= taylorWithinEval (fun s=>spin I a d v (x+s*r)) n (Set.Icc 0 q) 0 t
    ∑ j :Fin 4,cash j • (T ↑(steps j)- T (-↑(steps j)))=t • spin I a (d+1) (W.deriv d a v) x:=by
   intro T; let R:=Finset.range (n+1)
   let u(i:ℕ):= ((i.factorial:ℝ)⁻¹*t^i) • spin I a (d+i) (higher W d a i v) x
   have ht (r:ℝ)(hp:∀ z:ℝ,z∈Set.Icc (0:ℝ) q→ rows I ((x+z*r) • basis a)∈conf _) : T r= ∑ i∈R,r^i • u i:=by
      unfold T; rw [taylor_within_apply]; refine Finset.sum_congr rfl fun i hi=> ?_
      rw [spinIter HE I a W hw hq v _ _ hp _ _ (Set.left_mem_Icc.mpr hq.le)]; simp only [u,sub_zero,zero_mul,add_zero]; exact smul_comm ..
   let r(j:Fin 4):ℝ:= steps j
   simp_rw [show ∀ j,(cash j) • (T ↑(steps j)-T (-↑(steps j)))= ∑ i∈R,(cash j*(r j^i-(-r j)^i)) • u i from fun j=>by rw [ht _ (fun z hz=>(h j z hz).1),ht _ (fun z hz=>(h j z hz).2), ← Finset.sum_sub_distrib, Finset.smul_sum]; simp only [mul_smul,sub_smul, r]]
   rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul]; rw [sum_eq_single 1]
   · rw [show ∑ i : Fin 4,cash i * (r i^ (1:ℕ)- _)=(1:ℝ) from (credit 1 (by omega)).trans (if_pos rfl)]; unfold u; simp [higher]
   · intro i hZ hh; rw [Finset.mem_range] at hZ; rw [credit i (by omega),if_neg hh,zero_smul]
   exact fun hp=>False.elim (hp (Finset.mem_range.mpr (by omega)))

/-- Once the stencil width is fixed, the differentiation estimates on compact shape
probes are uniform over reference labels (explicit norm factor). -/
lemma axis_advance : ∃ c q C':ℝ,0<c ∧ 0<q ∧∀ l:ℤ,∀ x:ℝ,0<x→x ≤ q→ |(l:ℝ)*x| ≤ c → ∀ v:S.Field d,
      ‖x⁻¹ • dTap (fun j:ℤ=> plant I S d (((j:ℝ)*x) • basis a) v) l - plant I S (d+1) (((l:ℝ)*x) • basis a) (W.deriv d a v)‖ ≤ C' * ‖v‖ * x^8:=by
   obtain ⟨r,hr,hδ⟩:= screen I; let c:= r/2; let q:=r/8; have hc:0<c:=half_pos hr; have hq:0<q:= div_pos hr (by norm_num)
   let P(z:ℝ): S.Field (d+9)→L[ℂ] ℂ:= (plant I S (d+9) (z • basis a)).toContinuousLinearMap
   let Y:=Set.Icc (-r) r
   have hY(z:ℝ)(hz : z∈Y): rows I (z • basis a)∈conf _:=generic_conf _ (hδ _ (by simpa [norm_smul] using (abs_le.mpr hz)))
   have hPV : ContinuousOn P Y := fun z hz=> (spin_cont HE I a (d:=d+9) (hY z hz)).continuousWithinAt
   let E:= S.Field (d+9) →L[ℂ] ℂ; have hn : Continuous (fun p : E => ‖p‖):= continuous_norm (E:=E)
   obtain ⟨A,hA⟩:= (isCompact_Icc.image_of_continuousOn (hn.comp_continuousOn hPV)).bddAbove
   let U:= higher W d a 9; let D:ℝ:=A*4^9*‖U.toContinuousLinearMap‖; have hA' : 0≤A:= (norm_nonneg (P 0)).trans (show ‖P 0‖ ≤ A from hA ⟨_,show 0∈Y from ⟨neg_nonpos.mpr hr.le,hr.le⟩,rfl⟩)
   let H' :ℝ:=∑ i, ‖cash i‖*2*D/(8:ℕ).factorial
   refine ⟨c,q,H',hc,hq,fun l x hx hh hy v =>?_⟩
   let y:ℝ:= (l:ℝ)*x; let T:= fun R:ℝ=>taylorWithinEval (fun s=>spin I a d v (y+s*R)) 8 (Set.Icc 0 q) 0 x
   have hV(z R:ℝ)(hz:z∈Set.Icc (0:ℝ) q)(hR:|R|≤4): y+z*R∈Y:=by
      suffices ht : |y+z*R| ≤ r from abs_le.mp ht
      apply (abs_add_le ..).trans; rw [abs_mul z R, abs_of_nonneg hz.1]; exact (add_le_add (show |y|≤ c from hy) (mul_le_mul hz.2 hR (abs_nonneg _) hq.le)).trans (le_of_eq (by unfold c q; ring))
   have h(R:ℝ)(hR:|R|≤4): ‖spin I a d v (y+x*R)-T R‖ ≤ D*‖v‖*x^9/(8:ℕ).factorial:=by
      let L:=fun s=>spin I a d v (y+s*R)
      have he : ContDiffOn ℝ (8+1:ℕ) L (Set.Icc 0 q) := fun z hz=> ((spin_smooth HE I a (hY _ (hV z R hz hR)) v).comp (f:=fun s=> y+s*R) z (by fun_prop)|>.of_le (show (↑(8+1:ℕ):ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
      have hf z (hz:z∈Set.Icc 0 q) : ‖iteratedDerivWithin 9 L (Set.Icc 0 q) z‖ ≤ D*‖v‖:=by
         rw [show iteratedDerivWithin 9 L (Set.Icc 0 q) z=_ from spinIter HE I a W hw hq v y R (fun z hz=> hY _ (hV z R hz hR)) 9 z hz,norm_smul, norm_pow]; change ‖R‖^9*‖P _ (U v)‖ ≤ _
         have h' : ‖P (y+z*R) (U v)‖ ≤ A*(‖U.toContinuousLinearMap‖*‖v‖):=( (P (y+z*R)).le_opNorm _).trans (mul_le_mul (hA ⟨_,hV z R hz hR,rfl⟩) (U.toContinuousLinearMap.le_opNorm _) (norm_nonneg _) hA')
         exact (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hR _) h' (norm_nonneg _) (by norm_num)).trans_eq (by unfold D; ring)
      simpa only [sub_zero] using (taylor_mean_remainder_bound (n:=8) hq.le (by convert he; norm_cast) ⟨hx.le,hh⟩ hf)
   let k(i:Fin 4):ℝ:= steps i
   have he(i):|k i|≤4:=by unfold k steps; fin_cases i <;> norm_num
   let f (i:ℤ):= plant I S d (((i:ℝ)*x) • basis a) v
   have hU : x • plant I S (d+1) (y • basis a) (W.deriv d a v) = ∑ j:Fin 4,cash j • (T (k j)-T (-k j)):= (taylor_sum HE I a W hw hq 8 (by decide) le_rfl v y (fun i z hz =>⟨hY _ (hV z _ hz (he i)),hY _ (hV z _ hz (by rw [abs_neg]; exact he i))⟩) x).symm
   let p:= plant I S (d+1) (y • basis a) (W.deriv d a v)
   change ‖x⁻¹ • dTap f l-p‖ ≤ _
   nth_rw 1 [← inv_smul_smul₀ hx.ne' p]
   rw [← smul_sub,hU,dTap, ← sum_sub_distrib,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hx).le]; refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr hx.le)) ?_
   let B:=D*‖v‖*x^9/(8:ℕ).factorial; refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun j=>‖cash j‖*(B+B)) (fun j _=> ?_)) (inv_nonneg.mpr hx.le)) ?_
   · rw [← smul_sub,norm_smul,show f (l+steps j)=spin I a d v (y+x*k j) by unfold f spin y k; push_cast; ring_nf,show f (l-steps j)=spin I a d v (y+x*(-k j)) by unfold f spin y k; push_cast; ring_nf, sub_sub_sub_comm]
     exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (h _ (he _)) (h _ (by rw [abs_neg]; exact he _)))) (norm_nonneg _)
   unfold H' B; rw [Finset.mul_sum,Finset.sum_mul,Finset.sum_mul]; refine Finset.sum_le_sum fun i _=> le_of_eq ?_; field_simp; ring
end
end YM.Trace.Pull
