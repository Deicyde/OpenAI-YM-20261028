import YM.TraceExtension.Perfect.Equate

/-! # UV price constancy on arbitrary world, finite-order receipts. Use varying labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {W: Type*} {I:W→Type} [∀ w,Fintype (I w)][∀ w,DecidableEq (I w)]
   {Y Z:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z]
   {f h:∀ w,Rays (I w)→ Y}{D:∀ w,I w→ℕ}{m:ℕ}

structure Calm (D:∀ w,I w→ℕ)(f:∀ w,Rays (I w)→ Y)(m:ℕ): Prop where
    velvet w: ContDiffAt ℝ ω (f w) 0
    shape: ∃ α C:ℝ,0 < α ∧ 0 ≤ C ∧ ∀ w k,k ≤ m→ cost (D w) α 0 0 (leaf (f w) 0 k) ≤ C

lemma Calm.near (hp: Calm D f m)(ht:∀ w,f w=ᶠ[𝓝 0] h w): Calm D h m:=by
 refine ⟨fun a=> (hp.velvet a).congr_of_eventuallyEq (ht a).symm,?_⟩
 obtain ⟨α,C,c,y,p⟩:=hp.shape; exact ⟨α,C,c,y,fun w m h=> by rw [leaf,← (ht w|>.iteratedFDeriv ℝ m).eq_of_nhds]; exact p w m h⟩

lemma Calm.perching (hp: Calm D f m) : ∃ α C:ℝ, 0<α ∧ 0≤C∧ ∀ β, 0≤β→ β≤α → ∀ w k,k ≤ m→ cost (D w) β 0 0 (leaf (f w) 0 k) ≤ C:=by
 obtain ⟨a,C,ha,hc,h⟩:=hp.shape; exact ⟨a,C,ha,hc, fun b hb hk w n hn => (cost_tiny _ _ _ _ _ _ _ hb hk le_rfl).trans (h _ _ hn)⟩

variable {X : Type} [Fintype X][DecidableEq X]
open Finset OrderedFinpartition Planned.PrimaryIntegral295.Cases
omit [DecidableEq X] in
private lemma cost_mix (D:X→ℕ)(b c: OrderedFinpartition m)
    (p : (i:Fin c.length)→(Fin (c.partSize i)→ X)→ Y)(H : ContinuousMultilinearMap ℝ (fun _: Fin c.length=> Y) Z)
    (α :ℝ)(h:0≤α) : cost D α 0 0 (fun v:Fin m→X=> H (fun i=>p i (scheme c v i))) ≤ ‖H‖* ∏ i:Fin c.length,cost D α 0 0 (p i):=by
 unfold cost; refine le_trans ?_ (le_of_eq (by rw [← splitSum c (fun i v=> spot α 0 0 (limitN D v) * ‖p i v‖)]))
 rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_
 dsimp only; rw [Finset.prod_mul_distrib]; refine le_trans (mul_le_mul (splitN D α _ 0 c i h le_rfl) (H.le_opNorm (fun j => p j (scheme c i j))) (norm_nonneg _) (prod_nonneg (fun j _=> (spot_pos ..).le))) (le_of_eq ?_); exact mul_left_comm ..
lemma leaf_mix {F : Rays X→ Y}{K:Y→ Z}{α:ℝ}{D:X→ℕ}(h:ContDiffAt ℝ ω F 0)(hp:ContDiffAt ℝ ω K (F 0))(hh:0≤α):
    cost D α 0 0 (leaf (K∘F) 0 m) ≤ ∑ i:OrderedFinpartition m, ‖iteratedFDeriv ℝ i.length K (F 0)‖* ∏ j:Fin i.length,cost D α 0 0 (leaf F 0 (i.partSize j)):=by
 let Y (i:OrderedFinpartition m)(x:Fin m→X):= caseRead i K F 0 (desk ∘ x)
 rw [show leaf (K∘F) 0 m=fun x=>∑ i,Y i x from funext fun x=> compReads hp h (by simp) _]
 apply le_trans (cost_sum ..); refine Finset.sum_le_sum fun i _=> cost_mix D i i (fun j=> leaf F 0 (i.partSize j)) (iteratedFDeriv ℝ i.length K (F 0)) α hh
lemma Calm.forward (hp:Calm D f m)(k:Y→ Z) (p:∀ w,ContDiffAt ℝ ω k (f w 0))(a:Y)(hh:∀ w,f w 0=a): Calm D (fun w=> k∘f w) m:=by
 obtain ⟨α,C,c,H,u⟩:= hp.shape
 let t (n:ℕ):=∑ i:OrderedFinpartition n, ‖iteratedFDeriv ℝ i.length k a‖*C^i.length; have h n:0≤t n:= Finset.sum_nonneg fun _ _=> mul_nonneg (norm_nonneg _) (pow_nonneg H _)
 refine ⟨fun w=>(p w).comp _ (hp.velvet w),α,∑ n∈Finset.range (m+1),t n,c,sum_nonneg (fun _ _=>h _),fun w n hn=>?_⟩
 apply le_trans (leaf_mix (hp.velvet w) (p w) c.le)
 apply le_trans _ (Finset.single_le_sum (fun i _=>h i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))
 rw [hh]; refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); refine (prod_le_prod (fun i _=> cost_nn ..) (fun j _ => u w _ ((i.partSize_le j).trans hn))).trans_eq ?_
 simp
lemma Calm.prop (hp:Calm D f m){a : Y}(k:Y→ Z) (hx:ContDiffAt ℝ ω k a) (hh:∀ w,f w 0=a): Calm D (fun w=> k∘f w) m:= hp.forward k (fun w=> hh w |>.symm ▸ hx) a hh
lemma duo_cost (p:(Fin m→ X)→Y)(q:(Fin m→ X)→Z)(D α) : cost D α 0 0 (fun x=>(p x,q x)) ≤ cost D α 0 0 p+cost D α 0 0 q:=by
 unfold cost; rw [← sum_add_distrib]; refine Finset.sum_le_sum fun i _=>?_ ; rw [← mul_add]; refine mul_le_mul_of_nonneg_left ?_ (spot_pos ..).le; rw [Prod.norm_def]; exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
lemma Calm.duo (hp:Calm D f m){e:∀ w,Rays (I w)→ Z}(hx:Calm D e m) : Calm D (fun w x=>(f w x,e w x)) m:=by
 obtain ⟨α,C,hα,hC,h⟩:=hp.perching; obtain ⟨b,F,hb,hF,H'⟩:= hx.perching; have hh:=lt_min hα hb
 refine ⟨fun w=>(hp.velvet w).prodMk (hx.velvet w),min α b,C+F,hh,by positivity,fun w n hn=>?_⟩
 let T:=leaf (f w) 0;let V:=leaf (e w) 0
 rw [show leaf (fun x=>(f w x,e w x)) 0 n=fun x=>(leaf (f w) 0 n x,leaf (e w) 0 n x) from funext (fun x=> by unfold leaf bank; rw [iteratedFDeriv_prodMk (hp.velvet w) (hx.velvet w) le_top]; rfl)]
 exact (duo_cost ..).trans (add_le_add (h _ hh.le (min_le_left ..) w n hn) (H' _ hh.le (min_le_right ..) w n hn))
lemma Calm.heater {D':∀ w,I w→ℕ}(hp:Calm D f m)(M:ℕ)(h:∀ w i,D' w i ≤ D w i+M): Calm D' f m:=by
 obtain ⟨a,C,c,H,hy⟩:=hp.shape; refine ⟨hp.velvet,a,C*Real.exp (a*M),c,by positivity,fun w n ht=>?_⟩
 apply le_trans ?_ (mul_le_mul_of_nonneg_right (hy w n ht) (Real.exp_pos _).le); unfold cost; rw [sum_mul]; refine Finset.sum_le_sum fun x _=> ?_
 rw [mul_right_comm]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
 have he : limitN (D' w) x≤ limitN (D w) x+M:= (limitN_le ..).2 fun i=> (h w (x i)).trans (Nat.add_le_add_right (limitN_ge _ _ _) _)
 apply le_trans (spot_mono a _ _ c.le he); simp [spot,shelter]; rw [max_eq_right (by positivity : (0:ℝ) ≤ ↑(limitN (D w) x)+M),mul_add,Real.exp_add]

lemma Calm.maps (hp:Calm D f m)(L:Y→L[ℝ] Z) : Calm D (fun w=> L∘ f w) m:=by
 obtain ⟨a,C,ha,hC,H⟩:=hp.shape; refine ⟨fun i=>L.contDiff.contDiffAt.comp _ (hp.velvet i),a,‖L‖*C,ha,mul_nonneg (norm_nonneg _) hC,fun i j hj=>?_⟩
 apply le_trans ?_ (mul_le_mul_of_nonneg_left (H i _ hj) (norm_nonneg L))
 unfold cost leaf; rw [L.iteratedFDeriv_comp_left (hp.velvet i) le_top,Finset.mul_sum]; refine Finset.sum_le_sum fun y _=> ?_
 rw [mul_left_comm ‖L‖]; exact mul_le_mul_of_nonneg_left (L.le_opNorm _) (spot_pos ..).le
lemma Calm.over (hp:Calm D f m)(hℓ: Calm D h m): Calm D (fun w x=> f w x + h w x) m:= by
 let L: Y × Y→L[ℝ] Y:= ContinuousLinearMap.fst _ _ _ + ContinuousLinearMap.snd _ _ _
 exact (hp.duo hℓ).maps L
lemma Calm.from {V: Type*}(g: V→ W)(hp:Calm D f m): Calm (fun i:V=> D (g i)) (fun i=> f (g i)) m:=by
 obtain ⟨a,C,c,y,H⟩:=hp.shape; exact ⟨fun i=>hp.velvet _,a,C,c,y,fun w n hn=> H _ _ hn⟩
lemma Calm.assemble {ι : Type*}(o : Finset ι){P : ι→ W→ Prop}(h : ∀ w,∃ i∈o,P i w)(hp:∀ i∈o, Calm (fun w: {w:W// P i w}=> D w.val) (fun w=> f w.val) m) : Calm D f m:=by
 classical
 choose a C c y v using fun i : o => (hp i.val i.property).perching
 by_cases Hh : Nonempty (↥o)
 · let A:=univ.inf' (by exact (@Finset.univ_nonempty o _ Hh)) a
   have hc:0 < A:=by unfold A; exact (lt_inf'_iff _).mpr (fun i _ => c i)
   refine ⟨fun i=>?_,A,∑ i,C i,hc,sum_nonneg (fun i _ => y i),fun w n hn=>?_⟩
   · obtain ⟨k,hk,hv⟩:= h i; exact (hp k hk).velvet ⟨i,hv⟩
   obtain ⟨i,hp,H⟩:=h w; let t:o:=⟨i,hp⟩
   exact (v t A hc.le (inf'_le _ (mem_univ _)) ⟨w,H⟩ n hn).trans (single_le_sum (fun i _=>y i) (mem_univ t))
 have he(w:W):False:=by obtain ⟨i,hz,h⟩:=h w; exact Hh ⟨⟨i,hz⟩⟩
 exact ⟨fun w=> (he w).elim, 1,1,zero_lt_one,zero_le_one,fun w=> (he w).elim⟩
lemma zero_price (A α t r)(v : Rays X → Y): cost A α t r (leaf v 0 0)= spot α t r 0 * ‖v 0‖:= by
 unfold cost leaf bank; simp [iteratedFDeriv_zero_apply,limitN,Unique]
lemma Calm.frozen (A:∀ w,I w→ℕ)(u:Y): Calm A (fun _ _=>u) m:=by
 refine ⟨fun _=>contDiffAt_const,1,‖u‖,zero_lt_one,norm_nonneg _,fun w n hn=>?_⟩
 cases n with
 | zero=> rw [zero_price,show spot 1 0 0 0=1 from by simp [spot,shelter],one_mul]
 | succ n=> unfold cost leaf bank; rw [sum_eq_zero]; exact norm_nonneg _; intro i _; rw [iteratedFDeriv_const_of_ne (by simp)]; simp
lemma Calm.piP (p:(w:W) → Rays (I w) → X → Y)(h:∀ i,Calm D (fun w v=> p w v i) m): Calm D p m:=by
 classical
 let f i: (w:W)→ Rays (I w)→ X → Y:= fun w x=> (ContinuousLinearMap.single (R:=ℝ) (φ:=fun _:X=> Y) i) (p w x i)
 suffices he :∀ s:Finset X,Calm D (fun w x=>∑ i∈s,f i w x) m by
     apply (he univ).near; intro w; exact Eventually.of_forall fun x=> by ext i; dsimp only; rw [Finset.sum_apply]; simp [f,Pi.single_apply]
 intro s; induction s using Finset.induction with
 | empty=> simp_rw [sum_empty];exact Calm.frozen D _
 | insert a l hl ih=> simp_rw [sum_insert hl];exact ((h a).maps (ContinuousLinearMap.single (R:=ℝ) (φ:=fun _:X=>Y) a)).over ih
end YM.Trace.Perfect

namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {W:Type*}{I J: W→Type}[∀ w,Fintype (I w)][∀ w,DecidableEq (I w)][∀ w,Fintype (J w)][∀ w,DecidableEq (J w)]
    {X Y:Type}[Fintype X][DecidableEq X][NormedAddCommGroup Y][NormedSpace ℝ Y]{D:∀ w,I w→ℕ}{f g:∀ w,Rays (I w)→Y}{n:ℕ}
open Finset
lemma Calm.pick (D:∀ w,I w→ℕ)(i:∀ w,I w) (k :ℕ)(he:∀ w,D w (i w) ≤ k): Calm D (fun w x=> x (i w)) n:=by
 let V (w:W):Rays (I w)→L[ℝ]ℝ:= ContinuousLinearMap.proj (φ:=fun _:I w=>ℝ) (i w)
 have hv :∀ w x,V w x=x (i w):=fun _ _=>rfl
 refine ⟨fun w=> (V w).contDiff.contDiffAt,1,spot 1 0 0 k,zero_lt_one,(spot_pos ..).le,fun w n hn=>?_⟩
 change cost _ _ _ _ (leaf (V w) 0 n) ≤_
 match n with
 | 0 => rw [zero_price,map_zero,norm_zero,mul_zero]; exact (spot_pos ..).le
 | 1 =>
    let v := fun (_:Fin 1)=>i w
    have hL (y : Fin 1 → I w): leaf (V w) 0 1 y=if y=v then 1 else 0:=by
       unfold leaf bank; rw [iteratedFDeriv_one_apply,(V w).fderiv];
       change desk (y 0) (i w)=_; split
       · subst y; simp [v,desk]
       next he => unfold desk; rw [Pi.single_eq_of_ne]; intro h; apply he; ext1 i; fin_cases i; exact h.symm
    unfold cost; simp_rw [hL]; rw [sum_eq_single v,if_pos rfl,norm_one,mul_one,show limitN (D w) v=D w (i w) from by simp [limitN,v]]
    · exact spot_mono _ _ _ zero_le_one (he w)
    · intro b _ h; rw [if_neg h,norm_zero,mul_zero]
    simp
 | n+2 =>
    unfold cost leaf bank; rw [Finset.sum_eq_zero]; exact (spot_pos ..).le; intro i _; rw [iteratedFDeriv_succ_apply_right,show fderiv ℝ (V w)=(fun _=> V w) from funext fun _=>(V w).fderiv, iteratedFDeriv_const_of_ne (by omega)]; simp
lemma Calm.trim {δ:W→Prop} [DecidablePred δ] (hp:Calm (fun w:{x//δ x}=>D w.val) (fun w=> f w.val) n)(he: ∀ w,¬δ w→ f w = 0): Calm D f n:=by
 refine Calm.assemble (Finset.univ:Finset Bool) (P:=fun b x=> decide (δ x)=b) (fun w=> ⟨_,mem_univ _,rfl⟩) (fun y _=>?_); cases y
 · refine ((Calm.frozen _ (0:Y)) : Calm (fun w:{x// decide (δ x)=false}=>D w.val) (fun _ _=>(0:Y)) n).near (fun v=>?_); rw [he _ (by simpa using v.property)]; rfl
 exact hp.from (fun v:{x// decide (δ x)=true}=>⟨v.val,by simpa using v.property⟩)
lemma cell_move [CompleteSpace Y] (p:∀ w,J w≃ I w)(A:∀ w,J w→ℕ) (h:Calm D f n) (L:∀ w,Rays (J w)→L[ℝ]Rays (I w))(ht:∀ w b, L w (desk b)=desk (p w b)) (hx:∀ w b,A w b=D w (p w b)):
    Calm A (fun w=> f w ∘ L w) n:=by
 obtain ⟨a,C,c,y,H⟩:=h.shape; refine ⟨fun w=>(show ContDiffAt ℝ ω (f w) (L w 0) from by rw [map_zero]; exact h.velvet w).comp _ (L w).contDiff.contDiffAt,a,C,c,y,fun w n hn=>?_⟩
 refine le_trans (le_of_eq (b:=cost (D w) a 0 0 (leaf (f w) 0 n)) ?_) (H _ _ hn)
 let E:= Equiv.arrowCongr (Equiv.refl (Fin n)) (p w)
 have hu b : limitN (A w) b=limitN (D w) (E b):=by unfold limitN; change Finset.sup univ _=Finset.sup univ _; congr 1; funext i;exact hx w _
 unfold cost; rw [← E.sum_comp]; refine sum_congr rfl fun i _=>?_; rw [hu]; unfold leaf bank; rw [wired (L w) (by rw [map_zero]; exact (h.velvet w).analyticAt),map_zero]; congr! 3;ext1 j; exact ht w _
end YM.Trace.Perfect
