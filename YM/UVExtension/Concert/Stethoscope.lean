import YM.UVExtension.Concert.Germ
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quotes
import YM.Push.LOCAL_SPLITTING.Calculus

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Concert
open Filter Function Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 Blaze March Push Push.AbsoluteSums Lamppost AnalyticBridge VerifiedReset Quotes Next.Foundations
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge} {n: Side} (p:BudgetPoint) {Z A D X : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {T:Opening D Z}
    {k:ℕ} {t : ℝ}
structure Tap (p:BudgetPoint) (G:Gauge) (o:Site n) (Y:Support n) where
    view : Config G n
    live : Healthy p.threshold Y view
    poll : List (Directions G n)
    card : poll.length≤p.order
    innerP : ∀ x∈poll, p.dirBound o x
variable {p} {Y:Support n} {o:Site n}
def Tap.read (x:Tap p G o Y) {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g:Config G n→ F): F:= leftDerivs g x.poll x.view
lemma tap_bound {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f:Config G n→ F}{c:ℝ} : p.supBounds o Y f c ↔ 0≤ c∧∀ x:Tap p G o Y,‖x.read f‖≤c:= by
  constructor
  · exact fun h=> ⟨h.1,fun x=> h.2 x.view x.live x.poll x.card x.innerP⟩
  exact fun h=> ⟨h.1,fun v hv l hl hs=> h.2 ⟨v,hv,l,hl,hs⟩⟩
variable (s:Finset X) (a:X→ℝ)(f:X→ Config G n→ℝ)
lemma brigade (h:∀ i∈s,p.Regular Y (f i)): p.Regular Y (∑ i∈s, a i • f i):=by
  let Z':= ∑ i∈s,a i • f i
  have he (U) (hu:Healthy p.threshold Y U): Local.Chart p.order Z' U:= by
    unfold Local.Chart; unfold Z'; simp_rw [Function.comp_def,Finset.sum_apply]; apply ContDiffAt.sum; intro i hi; exact ((h i hi).smooth U hu).const_smul (a i)
  refine ⟨fun U V hu=>?_ ,  ?_,fun g U=>?_,he,fun U hu A l hl=> left_has A hl (he U hu)⟩
  · simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> congr_arg (a i*·) ((h i hi).sites U V hu)
  · rw [show (∑ i∈s, a i • f i)=(fun x=> ∑ i∈s,(a i) • f i x) from funext fun x=> Finset.sum_apply ..]; exact Finset.measurable_sum _ fun i hi=> (h i hi).borel.const_smul (a i)
  simp_rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> congr_arg (a i*·) ((h i hi).symmetry _ _)
lemma Tap.staves (x:Tap p G o Y)(h:∀ i∈s,p.Regular Y (f i)) : x.read (∑ i∈s,a i • f i)=∑ i∈s,a i*x.read (f i):=by
  unfold Tap.read; have he (i)(hi:i∈s):Local.Chart p.order (f i) x.view:= (h i hi).smooth _ x.live
  rw [Local.left_sum _ _ _ _ (fun i hi=>show Local.Chart p.order (a i • f i) x.view from ((h i hi).smooth _ x.live).const_smul (a i)) x.card]; exact Finset.sum_congr rfl fun i hi=> Local.left_linear (a i • ContinuousLinearMap.id ℝ ℝ) x.poll (he i hi) x.card

-- Oracle tests for gala. normalize multilinear product by explicit division including zeros
structure Handle (G:Gauge)(U:Config G n)(k:ℕ)(u:ℝ) where
  E : Type
  [group : NormedAddCommGroup E]
  [space : NormedSpace ℝ E]
  [small : FiniteDimensional ℝ E]
  chart : E→ Config G n
  x : E
  atX : chart x=U
  arc : Mode chart x k u
  j : ℕ
  lengthC : j≤k
  v : Fin j→ E
attribute [instance] Handle.group Handle.space Handle.small
variable (g: D→ Config G n→ ℝ) {v b : ℝ} {U:Config G n}
namespace Handle
variable (r:Handle G U k v) {F:Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
def partialR (f:r.E→F): F:= (∏ i,‖r.v i‖)⁻¹ • (iteratedFDeriv ℝ r.j f r.x r.v)
def seat (f:Config G n→ ℝ) := r.partialR (f ∘ r.chart)
-- multilinear integral estimates in Type*
lemma solves (b:ℝ) {f:r.E→F}(hb:0≤ b): ‖r.partialR f‖ ≤ b ↔ ‖iteratedFDeriv ℝ r.j f r.x r.v‖ ≤ b*∏ i, ‖r.v i‖:= by
  let P:=(∏ i, ‖r.v i‖)
  by_cases hx:P=0
  · have he:‖iteratedFDeriv ℝ r.j f r.x r.v‖ ≤ ‖iteratedFDeriv ℝ r.j f r.x‖ * P := ContinuousMultilinearMap.le_opNorm ..
    rw [hx,mul_zero] at he; simp only [partialR,show (∏ i,‖r.v i‖)=_ from hx,_root_.inv_zero,zero_smul,norm_zero,mul_zero]; exact ⟨fun _=>he,fun _=>hb⟩
  have he:0<P:= lt_of_le_of_ne (prod_nonneg (fun i _=> norm_nonneg _)) (Ne.symm hx)
  unfold partialR; simp_rw [norm_smul]; rw [norm_inv,Real.norm_of_nonneg (prod_nonneg (fun i _=> norm_nonneg _)),inv_mul_eq_div]; exact div_le_iff₀ he

lemma chords (hz:∀ i∈s, ContDiffAt ℝ (↑r.j) (f i ∘ r.chart) r.x) : -- h drop
    r.seat (∑ i∈s,a i • f i)=∑ i∈s,a i*r.seat (f i):=by
  unfold seat partialR; simp_rw [Function.comp_def,Finset.sum_apply,Pi.smul_apply]
  simp_rw [Function.comp_def] at hz
  rw [iteratedFDeriv_fun_sum_apply (n:=r.j) (fun i hi=> (hz i hi).const_smul (a i)),_root_.sum_apply,Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi=>?_
  rw [iteratedFDeriv_const_smul_apply' (hz i hi)]; simp only [_root_.smul_apply,smul_eq_mul]; ring
lemma rock {g:Config G n→ℝ} (h: ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p:E→ Config G n)(τ:E), p τ=U→Mode p τ k v→ ContDiffAt ℝ (↑k) (g∘p) τ) (hb:0≤ b)(hp:∀ r:Handle G U k v, ‖r.seat g‖≤b): Ore U g v b k:= by
  intro E G1 P t Y τ ht hv
  refine ⟨h E Y τ ht hv,zero_le_one,fun i hi=>?_⟩; rw [one_pow,mul_one]; apply ContinuousMultilinearMap.opNorm_le_bound hb
  intro w; let r:Handle G U k v:= {E:=E,chart:=Y, x:=τ,atX:=ht, arc:=hv, j:=i, lengthC:=hi, v:=w}
  exact r.solves _ hb|>.1 (hp r)
end Handle

-- pointwise (one germ read). funding B may depend on z; reads migrate via REAL linear theorem
lemma conduct {c Y' F:ℝ} (L:Sailor G p.threshold c k) (hc:0≤c) (hp: k*c≤v) (hz:p.order≤k) (hl:∀ i,p.Regular Y (g i))
    (w: Tap p G o Y) (f: Z→ ℝ) (hh : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p:E→ Config G n)(τ:E), p τ=w.view→Mode p τ k v→ ∃ g', Twist T τ k (fun d=>g d∘p) g' ∧ ∀ z ∈T.span,Brush k (f z) 1 (g' z) τ)
    (hx : ∀ x∈Y,1+(separation x o:ℝ)≤Y') (ht:1≤Y') (hm:∀ z∈T.span,0≤f z∧ f z ≤ F)(hF:0≤ F) :
    ∃ H:Z→ℂ,Bumps T.span H∧ (∀ d,H (T.call d)= ↑(w.read (g d)))∧∀ z∈T.span,‖H z‖≤ 2*(Y'^(p.power*k))* f z := by
  let R:=Handle G w.view k v; choose g' H hh' using fun i:Handle G w.view k v => hh i.E i.chart i.x i.atX i.arc
  let p'(z:Z)(i:Handle G w.view k v): ℂ:= i.partialR (g' i z)
  refine bloom (M:=Y'^(p.power*k)) (U:=F) (x:=T.call) (src:=fun d (i:Handle G w.view k v)=> i.seat (g d)) (f:=p') T.within (fun i s p hs hm hh=> ?_) (fun i k=>?_) (fun d=> w.read (g d)) ?_ (pow_nonneg (zero_le_one.trans ht) _) (fun z hz=> ⟨(hm z hz).1,⟨(hm z hz).2,hF⟩,fun i=>?_⟩) hF
  · exact ((H i).past s p hs hm hh|>.order i.j i.lengthC i.v).const_smul _
  · unfold p' Handle.seat Handle.partialR; rw [(H k).read k.j k.lengthC k.v i]; exact (Complex.ofRealCLM.map_smul ..).symm
  · intro s a x hx' hV; rw [← w.staves _ _ _ (fun i _=> hl i)]
    let f₀:= ∑ i∈s,a i • g i
    let hR:= brigade s a g (fun i _=> hl i)
    have he: Ore w.view f₀ v x k := by
      apply Handle.rock _ hx'
      · intro i; specialize hV i; rw [← Handle.chords s a g i] at hV
        exact hV
        exact fun j _=> ((H i).smooth j).of_le (by exact_mod_cast i.lengthC)
      intro E A B _ p τ hτ ha
      obtain ⟨e,hE,-⟩:= hh E p τ hτ ha
      unfold f₀; simp_rw [Function.comp_def,Finset.sum_apply,Pi.smul_apply]; exact ContDiffAt.sum fun i _=> (hE.smooth i).const_smul _
    apply (costsD hR.sites L hc o x hp he hx ht w.poll (w.card.trans hz) w.innerP) -- no apply? expected
  apply (i.solves _ (hm z hz).1).2
  refine ContinuousMultilinearMap.le_opNorm .. |>.trans (mul_le_mul_of_nonneg_right ?_ (prod_nonneg (fun i _=> norm_nonneg _)))
  simpa only [one_pow,mul_one] using (hh' i z hz).order i.j i.lengthC
end YM.UVExtension.Concert
