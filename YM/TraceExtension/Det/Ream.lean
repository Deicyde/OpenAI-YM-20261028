import YM.TraceExtension.Perfect.Zippy
import YM.TraceExtension.Perfect.Tumul
import YM.TraceExtension.Det.Mica

/-!
# Exponential derivative weights per-period, ROOT packets. Explicit some radii for later use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{J K I:Type}[Fintype J][Fintype I]
variable {X Y Z:Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z]
    {l:J→Site f}{o:Site f}{F H:Rays J→ X}{m n:ℕ}{α β C D A:ℝ}

def Pet (l:J→Site f) (x:Site f)(F:Rays J→X)(α:ℝ)(C:ℝ)(m:ℕ): Prop:= ContDiffAt ℝ ω F 0 ∧ Beacon l α m F x 0 C
lemma Pet.tilt (h:Pet l o F α C m)(hv:C≤D)(hp:β≤α)(he:n ≤ m): Pet l o F β D n:=by
    refine ⟨h.1,fun k hk q=>?_⟩
    have hC:0 ≤ C:=by
       have hx:= h.2 0 (Nat.zero_le m) Fin.elim0; have ht:= (norm_nonneg _).trans hx; simpa [spanSites] using ht
    apply (h.2 _ (hk.trans he) q).trans; apply mul_le_mul hv (Real.exp_monotone _) (Real.exp_pos _).le (hC.trans hv); exact mul_le_mul_of_nonneg_right (neg_le_neg hp) (by positivity)
lemma entry_tide (he:F =ᶠ[𝓝 0] H) (x:Fin m→J): entry F 0 x=entry H 0 x:=by unfold entry; rw[(he.iteratedFDeriv ℝ m).eq_of_nhds]
lemma Pet.grows (h:Pet l o F α C m)(he:F =ᶠ[𝓝 0] H): Pet l o H α C m:=⟨h.1.congr_of_eventuallyEq he.symm, fun i hi p=>entry_tide he p ▸ h.2 i hi p⟩
omit [Fintype J] in
lemma span_shift (l:J→Site f)(x y:Site f)(p: Fin m→J): spanSites l x p ≤ m*separation x y+spanSites l y p:=by
    unfold spanSites; apply (Finset.sum_le_sum fun j (_:j ∈ univ)=> separation_triangle x y (l (p j))).trans; simp [Finset.sum_add_distrib]
lemma Pet.switch (h:Pet l o F α C m)(hv:0≤C)(y:Site f)(he:0≤α): Pet l y F α (C*Real.exp (α*(m:ℝ)*separation y o)) m:=by
    refine ⟨h.1,fun i hi q=>?_⟩
    rw [mul_assoc, ← Real.exp_add]; refine (h.2 i hi q).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) hv)
    have hp:= (span_shift l y o q).trans (add_le_add_left (Nat.mul_le_mul_right (separation y o) hi) _)
    have hs: (spanSites l y q:ℝ) ≤ m*(separation y o:ℝ)+spanSites l o q:=by exact_mod_cast hp
    linarith only [mul_le_mul_of_nonneg_left hs he]
lemma entry_d (hf: ContDiffAt ℝ ω F 0)(q:Fin n→J)(j:J): entry F 0 (Fin.snoc q j)= entry (fun z=> fderiv ℝ F z (bolt j)) 0 q:=by
    unfold entry; rw[iteratedFDeriv_succ_apply_right]; simp only [Fin.snoc_last]
    let L:=ContinuousLinearMap.apply ℝ X (bolt j)
    have hp:= L.iteratedFDeriv_comp_left (hf.fderiv_right (m:=ω) (by simp)) (show (n:WithTop ℕ∞)≤ω from le_top)
    rw [show Fin.init (fun i:Fin (n+1)=>bolt (Fin.snoc (α:=fun _=>J) q j i))=(fun i=>bolt (q i)) from funext (fun i=>by simp [Fin.init])]; exact congr($(hp.symm) (fun i=> bolt (q i)))
lemma Pet.halp (h:Pet l o F α C (m+1))(j:J): Pet l o (fun z=> fderiv ℝ F z (bolt j)) α (C*Decay α o (l j)) m:=by
    refine ⟨(h.1.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const,fun i hi q=> ?_⟩
    rw [← entry_d h.1 q]; apply (h.2 (i+1) (by omega) (Fin.snoc q j)).trans_eq
    simp only [spanSites,Fin.sum_univ_castSucc]; simp only [Fin.snoc_last,Fin.snoc_castSucc,Nat.cast_add,mul_add,Real.exp_add,Decay]; ring
lemma Pet.compL {p:I→J}{N:Rays I→L[ℝ] Rays J}(h:Pet l o F α C m)(hv:∀ i,N (bolt i)=bolt (p i)):Pet (l∘p) o (F ∘ N) α C m:=by
    refine ⟨ContDiffAt.comp 0 ((map_zero N).symm ▸ h.1) N.contDiff.contDiffAt, fun i hi q=>?_⟩
    rw[show entry (F ∘ N) 0 q=entry F 0 (p ∘ q) from ?_]; exact h.2 i hi (p∘q)
    unfold entry; rw[iter_lin_at ((map_zero N).symm ▸ h.1.of_le le_top),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp_rw [hv]; rfl
lemma Pet.plus (h: Pet l o F α C m)(hp:Pet l o H α D m): Pet l o (fun x=>F x+ H x) α (C+D) m:=⟨h.1.add hp.1,h.2.add h.1 hp.1 hp.2⟩
lemma Pet.monoL (h:Pet l o F α C m)(L:X→L[ℝ]Y): Pet l o (L ∘ F) α (‖L‖*C) m:=by
    refine ⟨L.contDiff.contDiffAt.comp _ h.1, fun k hk q=>?_⟩
    unfold entry; rw [L.iteratedFDeriv_comp_left h.1 le_top]; exact (L.le_opNorm _).trans ((mul_le_mul_of_nonneg_left (h.2 k hk q) (norm_nonneg _)).trans_eq (mul_assoc ..).symm)
lemma Pet.minus (h: Pet l o F α C m)(hp:Pet l o H α D m): Pet l o (fun x=> F x-H x) α (C+D) m:=by
    refine ⟨h.1.sub hp.1,fun i hi q=>?_⟩
    unfold entry; rw [show (fun x=> F x-H x)=F-H from rfl,iteratedFDeriv_sub_apply (h.1.of_le le_top) (hp.1.of_le le_top),add_mul,_root_.sub_apply]; exact (norm_sub_le ..).trans (add_le_add (h.2 i hi _) (hp.2 i hi _))
lemma Pet.pair {G:Rays J→Y}(h:Pet l o F α C m)(hp:Pet l o G α D m) : Pet l o (fun x=> (F x,G x)) α (C+D) m:=by
    refine ⟨h.1.prodMk hp.1,fun i hi q=>?_⟩
    have he: entry (fun x=> (F x,G x)) 0 q= (entry F 0 q,entry G 0 q):=by unfold entry; rw[iteratedFDeriv_prodMk h.1 hp.1 le_top];rfl
    rw [he,Prod.norm_def]; apply le_trans (max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))) _
    rw[add_mul]; exact add_le_add (h.2 i hi q) (hp.2 i hi q)
lemma Pet.seven [Fintype K]{G:Rays J→ K→X}(he:0≤C)(h:∀ i,Pet l o (fun x=> G x i) α C m): Pet l o G α C m:=by
    have hv: ContDiffAt ℝ ω G 0:= contDiffAt_pi.mpr (fun i=> (h i).1); refine ⟨hv,fun j hj q => ?_⟩
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg he (Real.exp_pos _).le)).mpr
    intro i; let L: (K→X) →L[ℝ] X:= ContinuousLinearMap.proj i
    rw [show entry G 0 q i= entry (L ∘ G) 0 q from ?_]; exact (h i).2 j hj q
    unfold entry; rw [L.iteratedFDeriv_comp_left hv le_top]; rfl
lemma Pet.sink {g:X →Y}(h:Pet l o F α C m)(hp:0 ≤ C)(he:Allows m g (F 0) A): Pet l o (g ∘ F) α ((∑ i∈Finset.range (m+1),(Fintype.card (OrderedFinpartition i):ℝ))* (A*(1+C)^m)) m:=⟨he.analytic.comp _ h.1,Beacon.comp (g:=g) h.1 h.2 hp he⟩
-- Leibniz in entry
private lemma beamLinMix (L:X→L[ℝ] Y→L[ℝ] Z){g:Rays J→Y}(x:Rays J)(h:ContDiffAt ℝ ω F x)(hp:ContDiffAt ℝ ω g x)(y:Rays J):
    fderiv ℝ (fun z=> L (F z) (g z)) x y = L (F x) (fderiv ℝ g x y) + L (fderiv ℝ F x y) (g x):=by
    have hp' : DifferentiableAt ℝ (L ∘ F) x:= (L.contDiff.contDiffAt.comp _ h).differentiableAt (by simp); change fderiv ℝ (fun z=> (L ∘ F) z (g z)) _ _=_; rw[fderiv_clm_apply hp' (hp.differentiableAt (by simp)), fderiv_comp _ L.differentiableAt (h.differentiableAt (by simp)),L.fderiv]; rfl
lemma Pet.bins (L:X→L[ℝ] Y→L[ℝ] Z){g:Rays J→Y}(hf:Pet l o F α C m)(hg:Pet l o g α D m)(hc:0≤C)(hd:0≤D): Pet l o (fun x=> L (F x) (g x)) α (2^m*‖L‖*C*D) m:=by
    induction m generalizing C D F g with
    | zero=>
       refine ⟨(L.contDiff.contDiffAt.comp _ hf.1).clm_apply hg.1, fun i hi q=>?_⟩; obtain rfl: i=0:=by omega
       have hF:= hf.2 0 hi q; have hG:= hg.2 0 hi q
       simp [entry,spanSites,iteratedFDeriv_zero_apply] at hF hG ⊢
       exact ((L (F 0)).le_opNorm _).trans (mul_le_mul ((L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hF (norm_nonneg _))) hG (norm_nonneg _) (by positivity))
    | succ i ih=>
       have hp:= ih (F:=F) (g:=g) (hf.tilt le_rfl le_rfl (by omega)) (hg.tilt le_rfl le_rfl (by omega)) hc hd
       refine ⟨hp.1,fun n hn q=>?_⟩
       by_cases h:n ≤ i
       · have hv:=pow_le_pow_right₀ (show 1 ≤ (2:ℝ) by norm_num) (Nat.le_succ i)
         exact hp.tilt (by gcongr) le_rfl le_rfl|>.2 _ h q
       obtain rfl : n=i+1:=by omega
       let j:= q (Fin.last i); let v:= Fin.init q
       let A(z):= fderiv ℝ F z (bolt j); let B(z):= fderiv ℝ g z (bolt j)
       have hs := (show 0≤Decay α o (l j) from (decay_pos ..).le)
       have ht:= ih (F:=F) (g:=B) (hf.tilt le_rfl le_rfl (by omega)) (hg.halp j) hc (mul_nonneg hd hs)
       have hh:= ih (F:=A) (g:=g) (hf.halp j) (hg.tilt le_rfl le_rfl (by omega)) (mul_nonneg hc hs) hd
       let M(x):= L (F x) (B x)+L (A x) (g x)
       have hu: (fun z=> fderiv ℝ (fun z=> L (F z) (g z)) z (bolt j)) =ᶠ[𝓝 0] M:=by filter_upwards[hf.1.eventually (by simp),hg.1.eventually (by simp)] with z hf hg; exact beamLinMix L z hf hg _
       rw[show entry _ 0 q= entry M 0 v from ?_]; apply ((ht.plus hh).2 i le_rfl v).trans_eq; conv_rhs=> rw [show q=Fin.snoc v j from (Fin.snoc_init_self q).symm]
       · simp only [spanSites, Fin.sum_univ_castSucc, Fin.snoc_last,Fin.snoc_castSucc, Decay,Nat.cast_add,mul_add,Real.exp_add]; ring
       rw[show entry _ 0 q= entry (fun x=> L (F x) (g x)) 0 (Fin.snoc v j) from congr_arg (fun q=> entry (fun x=> L (F x) (g x)) 0 q) (Fin.snoc_init_self q).symm, entry_d hp.1, entry_tide hu]
-- sparse composition. Ehs(k,len≥1)
structure Drive (l : I→Site f) (d:J→ Site f)(N:Rays I→ Rays J)(K:ℕ)(A:ℝ) : Prop where
    side : ContDiffAt ℝ ω N 0
    quote : ∀ j i,i≤K → ∀ h:Fin i→ I, ‖entry (fun x=>N x j) 0 h‖≤A
    dut (k) (j) (hj:j≤K) (x:Fin j→I): entry (fun x=> N x k) 0 x ≠ 0 → ∀ i,l (x i)=d k
def lodge (s:ℕ)(a:ℝ):= ∑ i∈range (s+1),(Fintype.card (OrderedFinpartition i):ℝ)*a^s
lemma lodge_n (h:0≤A): 0≤lodge m A:=sum_nonneg fun _ _=>by positivity
lemma locate_pull {l:J→ Site f}{d:I→Site f}{g:Rays I→Rays J}{c:OrderedFinpartition n}(hc:0≤C)(h:Beacon l α m F o 0 C)(hg:Drive d l g m A)(hn:n≤ m)(x:Fin n→ I)(ha:0≤A)(hp:0≤α){M:ℕ}(he:Multiplicity l M) :
    let Λ(i:Fin c.length):=entry g 0 (x ∘ c.emb i)
    ‖iteratedFDeriv ℝ c.length F 0 Λ‖ ≤ C*(1+A*M)^m*Real.exp (-(α/(m+1:ℝ))*spanSites d o x):=by
    intro Λ
    have hL (i:Fin c.length)(j:J): Λ i j=entry (fun x=>g x j) 0 (x ∘ c.emb i):=by
        let L: Rays J→L[ℝ]ℝ:= ContinuousLinearMap.proj j
        exact congr($((L.iteratedFDeriv_comp_left hg.side (i:=c.partSize i) (by exact le_top)).symm) (fun v=> bolt (x (c.emb i v))))
    let B(v:Fin c.length→J):= ∏ i, Λ i (v i)
    let ht i: Fin (c.partSize i):= ⟨0,c.partSize_pos i⟩
    let w(i):=d (x (c.emb i (ht i))); let J' (v:Fin c.length → J):ℝ:= ∏ i:Fin c.length,(if l (v i)=w i then 1 else 0)
    let K:= Real.exp (-(α/(m+1:ℝ))*spanSites d o x)
    rw [many c]; apply (norm_sum_le ..).trans; refine (sum_le_sum (g:=fun v=> J' v*A^c.length*C*K) ?_).trans ?_
    · intro v _; rw [norm_smul]; by_cases h₀: B v=0
      · rw[show ∏ i:Fin c.length,Λ i (v i)=0 from h₀,norm_zero,zero_mul]; have hx : 0 ≤ J' v:=Finset.prod_nonneg fun i _=>by split <;> norm_num
        unfold K; positivity
      have hV(i j) : d (x (c.emb i j))=l (v i):=by
         apply hg.dut _ _ ((c.partSize_le i).trans hn) (x ∘ c.emb i) _ j; rw [← hL]; exact fun h=> h₀ (Finset.prod_eq_zero (mem_univ i) h)
      have hx:J' v=1:=by unfold J'; rw [prod_eq_one]; intro i _; rw[if_pos (hV i (ht i)).symm]
      have hy: ‖B v‖ ≤ A^c.length :=by
        unfold B; rw[norm_prod]; refine (prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>?_)).trans_eq (by simp: (∏ _i:Fin c.length, A)=_)
        rw [hL]; exact hg.quote _ _ ((c.partSize_le i).trans hn) _
      rw [hx,one_mul,mul_assoc]; apply mul_le_mul hy ((show ‖bank (iteratedFDeriv ℝ c.length F 0) v‖≤ _ from h c.length (c.length_le.trans hn) v).trans ?_) (norm_nonneg _) (by positivity)
      have hv : spanSites d o x ≤ (m+1)*spanSites l o v:=by
          unfold spanSites; rw [← c.sum_sigma_eq_sum (fun i=> separation o (d (x i))),Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_
          simp_rw[hV]; simp only[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; exact Nat.mul_le_mul_right _ ((c.partSize_le i).trans (hn.trans (Nat.le_succ _)))
      apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hc
      have hv':(spanSites d o x:ℝ) ≤ (m+1:ℝ)*(spanSites l o v : ℝ):=by exact_mod_cast hv
      have hx := mul_le_mul_of_nonneg_left hv' (show 0 ≤ α/(m+1:ℝ) by positivity); rw [← mul_assoc, div_mul_cancel₀ _ (by positivity: (m+1:ℝ)≠0)] at hx; linarith
    have hh : ∑ i:Fin c.length→J, J' i≤ (M:ℝ)^c.length:=by
      let f (i:Fin c.length)(j:J):ℝ:= if l j=w i then 1 else 0
      have hx(i:Fin c.length): ∑ j:J,f i j≤ M:=by unfold f; rw[← Finset.sum_filter]; simpa using (Nat.cast_le (α:=ℝ) |>.mpr (he (w i)))
      rw [← Fintype.prod_sum f]; refine (prod_le_prod (fun i _=> Finset.sum_nonneg fun j _=>by unfold f; split<;>norm_num) (fun i _=>hx i)).trans_eq (by simp)
    rw [← sum_mul,← sum_mul,← sum_mul]; change _≤ _*K; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (pow_nonneg ha _)) hc).trans; rw [mul_comm _ C,mul_comm ((M:ℝ)^c.length)]
    apply mul_le_mul_of_nonneg_left _ hc; rw[← mul_pow]; have hn': 0 ≤ A*M:=by positivity
    exact (pow_le_pow_left₀ hn' (show A*M ≤ 1+A*M by linarith) c.length).trans (pow_le_pow_right₀ (by linarith) (c.length_le.trans hn))
lemma Pet.rein {D:I→Site f}{g:Rays I→Rays J}(h:Pet l o F α C m)(hg:Drive D l g m A)(hx:g 0=0)(ha:0≤A)(hc:0≤C)(hp:0≤α){M:ℕ}(he:Multiplicity l M): Pet D o (F ∘ g) (α/(m+1:ℝ)) (C*lodge m (1+A*M)) m:=by
    have hv:ContDiffAt ℝ ω F (g 0):=hx.symm ▸ h.1
    refine ⟨ContDiffAt.comp _ hv hg.side,fun i hi q=>?_⟩
    unfold entry; rw [iteratedFDeriv_comp hv hg.side le_top, FormalMultilinearSeries.taylorComp, _root_.sum_apply]
    apply le_trans (norm_sum_le ..)
    let K:= Real.exp (-(α/(m+1:ℝ))*spanSites D o q); let Q:=1+A*M; have hK:0 ≤ K:=(Real.exp_pos _).le; have hQ:0≤Q:=by unfold Q; positivity
    refine (sum_le_sum (g:=fun i' :OrderedFinpartition i=> C*(1+A*M)^m*K) ?_).trans ?_
    · intro j _; change ‖iteratedFDeriv ℝ j.length F (g 0) (fun b=> entry g 0 (q ∘ j.emb b))‖ ≤ _; rw [hx]; exact locate_pull hc h.2 hg hi q ha hp (c:=j) he
    rw [sum_const,card_univ,nsmul_eq_mul]; rw [← mul_assoc,mul_left_comm (Fintype.card (OrderedFinpartition i):ℝ) C]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f:=fun j=> (Fintype.card (OrderedFinpartition j):ℝ)*Q^m) (fun _ _=>by positivity) (mem_range.mpr (Nat.lt_succ_of_le hi))) hc) hK
end YM.Trace.Det
