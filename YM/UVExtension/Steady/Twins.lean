import YM.UVExtension.Steady.Platoon

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady
open Filter Function Metric Set ConnectedActivityE6 Blaze
open scoped Topology Classical ContDiff BigOperators
-- universe equal Type, enough for our FD motion calculus (used for compositions)
variable {ι : Type*} {F G E D : Type} [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup E]
 [NormedSpace ℝ F] [NormedSpace ℝ E] [NormedSpace ℝ G] [NormedAddCommGroup D] [NormedSpace ℝ D]
variable (v: Filter ι)
structure Walt (x:ι→ E) (k:ℕ) (f:ι→ Bool→ E→F):Prop where
    smooth : ∀ᶠ i in v,∀ b,ContDiffAt ℝ (↑k) (f i b) (x i)
    jets : ∀ j≤k,Together v (fun i b=> iteratedFDeriv ℝ j (f i b) (x i))
namespace Walt
variable {v} {x:ι→ E}{j k:ℕ} {f g:ι→ Bool→ E→F}{h:ι→Bool→ E→G}
lemma cap (p:Walt v x k f): ∃ u:ℝ, 0 ≤ u∧ ∀ᶠ n in v,∀ i, Brush k u 1 (f n i) (x n):=by
   choose u hu using fun i : Fin (k+1)=> (p.jets i (Nat.le_of_lt_succ i.2)).1; let Z:= ∑ i, |u i|; refine ⟨Z,by unfold Z; positivity,?_⟩
   filter_upwards [eventually_all.mpr hu,p.smooth] with b hb hx n
   refine ⟨hx n,zero_le_one,fun i hi=>?_⟩; rw [one_pow,mul_one]; exact (hb (⟨i,Nat.lt_succ_of_le hi⟩:Fin (k+1)) n).trans ((le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (u j)) (Finset.mem_univ _)))
lemma hem (p:Walt v x k f)(ε:ℝ)(he:0<ε): ∀ᶠ n in v, Brush k ε 1 (fun y=> f n true y-f n false y) (x n):=by
  have ht:= eventually_all.mpr (?_ : ∀ i: Fin (k+1), ∀ᶠ n in v,‖iteratedFDeriv ℝ (i:ℕ) (f n true) (x n)-iteratedFDeriv ℝ (i:ℕ) (f n false) (x n)‖≤ ε)
  · filter_upwards [ht,p.smooth] with n ht hx; refine ⟨(hx _).sub (hx _),zero_le_one,fun j hj=>?_⟩
    unfold normJ; rw [one_pow,mul_one]
    change ‖iteratedFDeriv ℝ j (f n true-f n false) (x n)‖ ≤ _; rw [iteratedFDeriv_sub_apply ((hx _).of_le (Nat.cast_le.mpr hj)) ((hx _).of_le (Nat.cast_le.mpr hj))]; exact ht ⟨j,Nat.lt_succ_of_le hj⟩ -- hi cast
  exact fun i=> (p.jets i (Nat.le_of_lt_succ i.2)).cap ε he
lemma earns (F : ι→ Bool→ E→G)(r:ℝ) (h:∀ᶠ n in v,∀ i, Brush k r 1 (F n i) (x n))(hr:∀ ε:ℝ, 0<ε→∀ᶠ n in v,Brush k ε 1 (fun a=>F n true a-F n false a) (x n)): Walt v x k F:=by
  refine ⟨h.mono fun n hn i=> (hn i).smooth, fun i hi=> Together.of_cap _ ⟨r,h.mono fun n hn j=>?_⟩ (fun ε he=>?_)⟩
  · simpa only [one_pow,mul_one] using (hn j).order i hi
  filter_upwards [h,hr ε he] with n hx hh
  rw [← iteratedFDeriv_sub_apply ((hx _).smaller hi).smooth ((hx _).smaller hi).smooth]; simpa only [one_pow,mul_one] using! hh.order i hi
lemma thin (p:Walt v x k f) (h: j≤ k): Walt v x j f:= ⟨p.smooth.mono fun n hn i=> (hn i).of_le (by exact_mod_cast h), fun i hi=> p.jets i (hi.trans h)⟩
lemma same (p:Walt v x k f)(h:∀ᶠ n in v,∀ i,g n i=ᶠ[𝓝 (x n)] f n i): Walt v x k g:=by
   refine ⟨(p.smooth.and h).mono fun n hn i=> (hn.1 i).congr_of_eventuallyEq (hn.2 i),fun j hj=>(p.jets j hj).shimmy ?_⟩
   filter_upwards [h] with n hn; exact funext fun i=> (((hn i).iteratedFDeriv ℝ j).eq_of_nhds).symm
lemma excuse (p:Walt v x k f)(a:ι→Prop): Walt (apart v a) x k f:= ⟨inf_le_left (b:=𝓟 {n|a n}) p.smooth, fun i hi=> (p.jets i hi).finely inf_le_left⟩
lemma split (r:ι→Prop)(p:Walt (apart v r) x k f)(q:Walt (apart v (fun n=>¬r n)) x k f): Walt v x k f:= ⟨(gathered v p.smooth q.smooth).mono fun _ h=> by_cases h.1 h.2,fun i hi=> (Together.split r (p.jets i hi) (q.jets i hi))⟩
lemma twin (u d:ℝ) (p : ∀ᶠ n in v, Brush k u d (f n true) (x n) ∧ f n true=f n false): Walt v x k f:=by
   refine ⟨p.mono fun n hx i=>?_,fun i hi=> ⟨⟨u*d^i,p.mono fun n hx j=>?_⟩,(tendsto_const_nhds (x:=0)).congr' ?_⟩⟩
   · cases i; rw [← hx.2]; exact hx.1.smooth; exact hx.1.smooth
   · cases j; dsimp only; rw [← hx.2]; exact hx.1.order i hi; exact hx.1.order i hi
   filter_upwards [p] with n hx; simp only [hx.2,dist_self]
lemma stamp {f:ι→Bool→G}(p:Together v f) : Walt v x k (fun n b _=> f n b):=by
   refine ⟨Eventually.of_forall fun n i=> contDiffAt_const,?_⟩; rintro (_|i) hi
   · exact p.scalar ((continuousMultilinearCurryFin0 ℝ E G).symm.toLinearIsometry.toContinuousLinearMap)
   simpa only [iteratedFDeriv_succ_const, Pi.zero_apply] using! Together.steady (v:=v) (0:E [×(i+1)]→L[ℝ] G)
lemma ready (a:F): Walt v x k (fun _ _ _=> a):= stamp (Together.steady a)
lemma sums (p: Walt v x k f)(q: Walt v x k g): Walt v x k (fun n b y=>f n b y+g n b y):=by
   refine ⟨(p.smooth.and q.smooth).mono fun n hn i=> (hn.1 i).add (hn.2 i),fun i hi=> ((p.jets i hi).add (q.jets i hi)).shimmy ?_⟩
   filter_upwards [(p.thin hi).smooth,(q.thin hi).smooth] with n hn hm; exact funext fun b=> (iteratedFDeriv_add_apply (hn b) (hm b)).symm
lemma leaf (p: Walt v x k f)(L:F→L[ℝ] G): Walt v x k (fun n b y=>L (f n b y)):=by
    refine ⟨p.smooth.mono fun n hn i=> L.contDiff.contDiffAt.comp _ (hn _),fun i hi=> ((p.jets i hi).scalar ?_).shimmy ?_⟩
    · exact ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ F G L
    filter_upwards [p.smooth] with n hn; exact funext fun i=> (L.iteratedFDeriv_comp_left (hn i) (by exact_mod_cast hi)).symm
lemma twin_bill (p:Walt v x k f)(q:Walt v x k h)(Z:F→L[ℝ] G→L[ℝ] D): Walt v x k (fun n b i=> Z (f n b i) (h n b i)):=by
  obtain ⟨a,ha,hv⟩:= p.cap; obtain ⟨b,hb,hG⟩:= q.cap
  have hm {f:E→D} {u:ℝ} {x:E} (h: Brush k u (1+1) f x): Brush k (u*2^k) 1 f x:=by
    refine ⟨h.smooth,zero_le_one,fun i hi=>(h.order i hi).trans ?_⟩; rw [one_pow,mul_one, one_add_one_eq_two]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hi) h.nonneg
  refine earns _ ((‖Z‖*(a*b))*2^k) ((hv.and hG).mono fun i h b=>hm ((h.1 b).twins (h.2 b) Z)) (fun ε he=>?_)
  let r:=(1+‖Z‖)*(a+b+1)*2^k; have hr:0<r:=by unfold r; positivity
  let d:=ε/r; have hd: 0<d:=div_pos he hr
  filter_upwards [hv,hG,p.hem d hd,q.hem d hd] with n hp hb' hu hV
  have he' := hm ((hu.twins (hb' true) Z).gathering ((hp false).twins hV Z)); refine (he'.climb ?_ le_rfl).shimmy (Eventually.of_forall (fun i=> ?_))
  · calc
      _ = d*(‖Z‖*(b+a)*2^k):=by ring
      _ ≤ d*((1+‖Z‖)*(a+b+1)*2^k):= mul_le_mul_of_nonneg_left (by apply mul_le_mul_of_nonneg_right _ (by positivity); exact mul_le_mul (by linarith) (by linarith) (add_nonneg hb ha) (by positivity)) hd.le
      _ = _ := div_mul_cancel₀ _ hr.ne'
  dsimp only; rw [map_sub,map_sub]; simp only [_root_.sub_apply]; abel
lemma derivative (p:Walt v x (k+1) f): Walt v x k (fun n b=> fderiv ℝ (f n b)):=by
    refine ⟨p.smooth.mono fun n hn i=> (hn i).fderiv_right ?_,fun i hi=>?_⟩
    · norm_cast
    refine ((p.jets (i+1) (by omega)).scalar (continuousMultilinearCurryRightEquiv' ℝ i E F).toLinearIsometry.toContinuousLinearMap).shimmy ?_
    filter_upwards with n; ext1 b; rw [iteratedFDeriv_succ_eq_comp_right]; simp
lemma atProbe (p:Walt v x k f): Together v (fun n b=>f n b (x n)):=by
    refine ((p.jets 0 (Nat.zero_le _)).scalar ((continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.toContinuousLinearMap)).shimmy ?_
    filter_upwards with i; ext1 b; rfl
lemma company {K:Set F}(h:IsCompact K){Z:F→G}(hz:∀ i∈K,ContDiffAt ℝ (↑k) Z i)(p:Walt v x k f) (hf:∀ᶠ n in v,∀ b,f n b (x n)∈ K): Walt v x k (fun n b y=> Z (f n b y)):=by
    induction k generalizing G with
    | zero =>
      have he := Together.compact h p.atProbe hf (fun x hx=> (hz x hx).continuousAt.continuousWithinAt)
      refine ⟨(p.smooth.and hf).mono fun n hn i=> (hz _ (hn.2 i)).comp _ (hn.1 _),fun i hi=>?_⟩
      obtain rfl : i=0:=by omega
      exact (stamp (x:=x) (k:=0) he).jets _ (le_refl _)
    | succ k ih =>
      let g i b y:= Z (f i b y)
      have he : ∀ᶠ n in v, ∀ b, fderiv ℝ (g n b) =ᶠ[𝓝 (x n)] (fun y=> (fderiv ℝ Z (f n b y)).comp (fderiv ℝ (f n b) y)):=by
        filter_upwards [p.smooth,hf] with i hi hp b
        filter_upwards [(hi b).eventually (by simp), (hi b).continuousAt ((hz _ (hp b)).eventually (by simp))] with y hy ht
        change ContDiffAt ℝ (↑(k+1:ℕ)) Z (f i b y) at ht; exact fderiv_comp y (ht.differentiableAt (by norm_cast)) (hy.differentiableAt (by norm_cast))
      have hx := p.thin (le_refl k|>.trans (Nat.le_succ _)); have hQ := ih (Z:=fderiv ℝ Z) (fun i hi=> (hz i hi).fderiv_right (by norm_cast)) hx
      have hD:= hQ.twin_bill p.derivative (ContinuousLinearMap.compL ℝ E F G); have ht: Walt v x k (fun i b=> fderiv ℝ (g i b)):=hD.same he
      refine ⟨(p.smooth.and hf).mono fun i hi b=> (hz _ (hi.2 b)).comp _ (hi.1 b),fun i hi=>?_⟩
      cases i with
      | zero => exact (ih (fun i hi=>(hz i hi).of_le (Nat.cast_le.mpr (Nat.le_succ _))) hx).jets 0 (Nat.zero_le _)
      | succ i =>
        refine ((ht.jets i (by omega)).scalar (continuousMultilinearCurryRightEquiv' ℝ i E G).symm.toLinearIsometry.toContinuousLinearMap).shimmy (Eventually.of_forall fun n=> funext fun b=>?_ )
        rw [iteratedFDeriv_succ_eq_comp_right]; rfl
lemma plant [FiniteDimensional ℝ F] (p:Walt v x k f){Z:F→G}(h:ContDiff ℝ (↑k) Z) : Walt v x k (fun n b y=> Z (f n b y)):=by
   obtain ⟨d,hd⟩:= p.atProbe.1; apply company (isCompact_closedBall 0 d) (fun z _=> h.contDiffAt) p; filter_upwards [hd] with i hi b; exact mem_closedBall.mpr (by rw [dist_zero_right]; exact hi b)
end Walt
end YM.UVExtension.Steady
