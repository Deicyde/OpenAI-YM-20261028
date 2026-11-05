import YM.TraceExtension.Lamp.Card
import Mathlib.Analysis.Calculus.Taylor
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z] {F H:W→ X→ Y}{L:Filter W}

def neap (k:ℕ)(F:X→Y)(x p:X) := (k.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ k F x (fun _=> p)
lemma neap0 (F:X→Y)(x p:X): neap 0 F x p=F x:=by simp[neap,iteratedFDeriv_zero_apply]
lemma neap1 (F:X→Y)(x p:X): neap 1 F x p=fderiv ℝ F x p:=by simp[neap,iteratedFDeriv_one_apply]
lemma neap2 (F:X→Y)(x p:X): neap 2 F x p=(1/2:ℝ) • (fderiv ℝ (fderiv ℝ F) x p p):=by
    unfold neap; rw[iteratedFDeriv_two_apply];norm_num[Nat.factorial]
lemma norm_neap {F:X→Y}{x p:X}(h: Allows n F x C) (hk:k≤n) : ‖neap k F x p‖ ≤ (k.factorial:ℝ)⁻¹ * C * ‖p‖^k:=by
    unfold neap; rw[norm_smul,Real.norm_of_nonneg (by positivity), mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity); refine le_trans (ContinuousMultilinearMap.le_opNorm ..) ?_; rw [Finset.prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (h.norm_le _ hk) (pow_nonneg (norm_nonneg _) _)
lemma neap_tide (F:X→Y)(k:ℕ)(x p:X)(c:ℝ): neap k F x (c • p)= c^k • neap k F x p:=by
    unfold neap; rw [show iteratedFDeriv ℝ k F x (fun _=> c • p)=_ from (iteratedFDeriv ℝ k F x).toMultilinearMap.map_smul_univ (fun _=>c) (fun _=> p)];simp only[prod_const,card_univ,Fintype.card_fin]; exact smul_comm ..

lemma chord_h {F:X→Y}(o:X)(y:X)(c:ℝ) (h:Allows k F (o+c • y) A)(ht:‖y‖≤b)(hp:1≤b): Allows k (fun s:ℝ=> F (o+s • y)) c (A*b^k):=by
    let L:ℝ→L[ℝ] X:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ..) y
    have hL(s): L s=s • y:=rfl
    have hv : ‖L‖ ≤ b:= L.opNorm_le_bound (zero_le_one.trans hp) (fun z=> by rw[hL,norm_smul,mul_comm];exact mul_le_mul_of_nonneg_right ht (norm_nonneg z))
    have hh : Allows k (fun x:X=> F (o+x)) (L c) A:=⟨ContDiffAt.comp (g:=F) (f:=fun x:X=> o+x) _ h.analytic (by fun_prop),fun p _=> ?_⟩
    · exact pullAll hh hv hp
    rw[iteratedFDeriv_comp_add_left]; exact h.norm_le p (by assumption)
lemma chord_n {F:X→Y}(o:X)(p:X)(k:ℕ)(h:ContDiffAt ℝ ω F o):
    neap k (fun s:ℝ=>F (o+s • p)) 0 1=neap k F o p:=by
    let L:ℝ→L[ℝ] X:= ContinuousLinearMap.smulRight (ContinuousLinearMap.id ..) p
    let f(x:X):=F (o+x)
    have hf:ContDiffAt ℝ ω f (L 0):=ContDiffAt.comp (g:=F) (f:=fun x:X=>o+x) _ (by rw[map_zero,add_zero];exact h) (by fun_prop)
    unfold neap;rw[show (fun s:ℝ=>F (o+s • p))= f ∘ L from rfl,iter_lin_at (hf.of_le le_top),ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
    unfold f;rw[iteratedFDeriv_comp_add_left,add_zero]; simp[L]
lemma warm (F:ℝ→Y)(d:ℝ)(hd:0<d)(t:ℝ)(ht:t∈Set.Icc 0 d)(j:ℕ)(h:∀ t∈Set.Icc 0 d,Allows (j+1) F t C):
    ‖F t-∑ i∈range (j+1),t^i • neap i F 0 1‖ ≤ C*t^(j+1)/(j.factorial:ℝ):=by
    let I:= Set.Icc 0 d;have hi: (0:ℝ)∈I:= Set.left_mem_Icc.mpr hd.le
    have hh: ContDiffOn ℝ (↑(j+1:ℕ):ℕ∞ω) F I:= fun x hx=> ((h x hx).analytic.of_le le_top).contDiffWithinAt
    have hp x (hx:x∈I) (i : ℕ): iteratedDerivWithin i F I x= iteratedFDeriv ℝ i F x (fun _=>1):=by
       rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hd) ((h x hx).analytic.of_le le_top) hx]
    rw [show (∑ i∈range (j+1),t^i • neap i F 0 1)=taylorWithinEval F j I 0 t from ?_]; swap
    · rw[taylor_within_apply]; apply Finset.sum_congr rfl; intro i _; rw[sub_zero,hp 0 hi]; unfold neap; rw[mul_smul]; exact smul_comm ..
    have hv: ∀ x∈I, ‖iteratedDerivWithin (j+1) F I x‖ ≤ C:=by
       intro x hx; rw[hp x hx]; refine le_trans (ContinuousMultilinearMap.le_opNorm ..) ?_; simp; exact (h x hx).norm_le _ le_rfl
    simpa only [sub_zero] using taylor_mean_remainder_bound (n:=j) hd.le (by convert hh; norm_cast) ht hv

structure Wilt (L:Filter W)(x:W→ℝ) : Prop where
    pos (w:W): 0<x w
    void:Tendsto x L (𝓝 0)
omit [NormedSpace ℝ X] in
abbrev DashQ (L:Filter W)(F:W→X) : Prop:=∃ C:ℝ,0≤C∧∀ᶠ x in L,‖F x‖≤ C
abbrev Rose (L:Filter W)(F H:W→X) := Tendsto (F-H) L (𝓝 0)
omit [NormedSpace ℝ X] in
lemma Rose.const (F:W→X): Rose L F F :=by unfold Rose; rw [sub_self];exact tendsto_const_nhds
omit [NormedSpace ℝ X] in
lemma Rose.inc {F H U V:W→X}(h:Rose L F H)(hv:Rose L U V): Rose L (F+U) (H+V):=by
    unfold Rose;rw[add_sub_add_comm]; convert h.add hv using 1
    · rfl
    simp
omit [NormedSpace ℝ X] in
lemma Rose.dec {F H U V:W→X}(h:Rose L F H)(hv:Rose L U V): Rose L (F-U) (H-V):=by
    unfold Rose; rw[sub_sub_sub_comm]; convert h.sub hv using 1
    · rfl
    simp
omit [NormedSpace ℝ X] in
lemma Rose.chain {F H U:W→X}(h:Rose L F H)(hp:Rose L H U): Rose L F U:=by
    unfold Rose;rw[← sub_add_sub_cancel F H U]; convert h.add hp using 1
    · rfl
    simp
omit [NormedSpace ℝ X] in
lemma Rose.side {F H:W→X}(h:Rose L F H): Rose L H F:=by
    unfold Rose;rw [← neg_sub];convert h.neg using 1
    · rfl
    simp
omit [NormedSpace ℝ X] in
lemma DashQ.near {F H:W→X}(h: Rose L F H)(hx:DashQ L H) : DashQ L F:=by obtain ⟨M,hM,hx⟩:= hx; refine ⟨1+M,by linarith,?_⟩; filter_upwards [h.eventually (Metric.ball_mem_nhds 0 zero_lt_one),hx] with x hx ht; rw [← sub_add_cancel (F x) (H x)]; apply (norm_add_le ..).trans (add_le_add (le_of_lt _) ht); simpa [Metric.mem_ball] using hx
omit [NormedSpace ℝ X] in
lemma DashQ.inc {F H:W→X}(h:DashQ L F)(he:DashQ L H): DashQ L (F+H):=by obtain ⟨M,hM,h⟩:=h;obtain ⟨N,hN,p⟩:=he; exact ⟨M+N,by positivity,h.mp (p.mono fun w hw hf=>(norm_add_le ..).trans (add_le_add hf hw))⟩
omit [NormedSpace ℝ X] in
lemma Rose.skip {F H:W→X}(h: F=ᶠ[L] H): Rose L F H:= (tendsto_const_nhds (x:=0)).congr' (h.mono fun _ hx=>(sub_eq_zero.mpr hx).symm)
omit [NormedSpace ℝ X] in
lemma DashQ.rose {F:W→X}{x:X}(t:Tendsto F L (𝓝 x)): DashQ L F :=by
    refine ⟨‖x‖+1,by positivity,t.norm.eventually (ge_mem_nhds (by linarith))⟩
lemma CohX {f g:W→ X}{Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](B:X→L[ℝ]Y)(h:Rose L f g): Rose L (fun i=> B (f i)) (fun i=> B (g i)):=by unfold Rose;rw [show (fun i=> B (f i))-(fun i=> B (g i))=B ∘ (f-g) from funext fun i=> (map_sub ..).symm]; exact (show Tendsto B (𝓝 0) (𝓝 0) from by simpa using B.continuous.tendsto 0).comp h
lemma roseRate (c:ℂ){f g:W→ℂ}(h:Rose L f g): Rose L (fun i=> c*f i) (fun i=>c*g i):=CohX (ContinuousLinearMap.mul ℝ ℂ c) h
lemma coh (f g:W→ ℂ)(h: Tendsto f L (𝓝 0))(he:DashQ L g) : Tendsto (f*g) L (𝓝 0):=by
    obtain ⟨D,hD,hg⟩:=he; have hz:Tendsto (fun i:W=> ‖f i‖* D) L (𝓝 0):=by simpa using (h.norm.mul (tendsto_const_nhds (x:=D)))
    refine squeeze_zero_norm' ?_ hz; filter_upwards[hg] with i hi; rw [Pi.mul_apply,norm_mul]; exact mul_le_mul_of_nonneg_left hi (norm_nonneg _)
lemma Rose.prod {f g u v:W→ℂ}(h:Rose L f g)(hp:Rose L u v)(hg:DashQ L g)(hv:DashQ L v): Rose L (f*u) (g*v):=by
    unfold Rose; rw [show f*u-g*v=(f-g)*u+(u-v)*g by ring]; convert (coh _ _ h (DashQ.near hp hv)).add (coh _ _ hp hg) using 1
    · rfl
    simp
lemma DashQ.prod {f g:W→ℂ}(h:DashQ L f)(he:DashQ L g): DashQ L (f*g):=by obtain ⟨M,hM,f⟩:=h;obtain ⟨N,hN,g⟩:=he; refine ⟨M*N,by positivity,?_⟩; filter_upwards[f,g] with v hf hg; rw[Pi.mul_apply,norm_mul]; exact mul_le_mul hf hg (norm_nonneg _) hM
end YM.Trace.Lamp
