import YM.TraceExtension.Lamp.Gate
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Lamp
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform Det MeasureTheory
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r l:ℕ}{α σ μ a b c τ A C D:ℝ}
variable {W:Type*} {g:W→Side}{X:Type} [NormedAddCommGroup X][NormedSpace ℝ X]{L:Filter W} {F H: Peat G f}
lemma hearth (h: Cleric F)(V:X → Config G f)(hv:Army V 0)(hp:V 0=1)[FiniteDimensional ℝ X][CompleteSpace X]:
    ∀ᶠ z in 𝓝 0,ContDiffAt ℝ ω (bal (V z) F) 0:=by
    let G'(t:X × Link G f):= input G f t.2*V t.1
    have he: ContDiffAt ℝ ω (F ∘ G') 0:= h.put _ ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (hv.comp (g:=V) (w:=Prod.fst) contDiffAt_fst)) (by unfold G'; simp[hp])
    filter_upwards [(show Tendsto (fun x:X=> (x,(0:Link G f))) (𝓝 0) (𝓝 0) from tendsto_id.prodMk_nhds tendsto_const_nhds).eventually (he.eventually (by simp))] with z hz; exact hz.comp (f:=fun x=> (z,x)) 0 (by fun_prop)
abbrev sailM (p:Clip)(M:PathData G)(μ:ℝ)(F:Peat G f)(x:Link G f):= (shellB p M μ (input G f x)*beamH F (input G f x)).trace
lemma hearth_m (h:Cleric F): Memo (beamH F ∘ input G f) 0:=by
    let V(z:Onus G f):= input G f z.2*input G f z.1
    have he:= h.put (U:=V) ((Army.powL (v:=Prod.snd) contDiffAt_snd).mul (Army.powL contDiffAt_fst)) (show V 0=1 by simp[V]); exact memo_damage _ (F:=fun x=> bal (input G f x) F) he
lemma hearth_s (h:Cleric F)(hp:Memo (shellB p M μ ∘ input G f) 0): ContDiffAt ℝ ω (sailM p M μ F) 0:=by
    exact ContDiffAt.sum (f:=fun i x=> (shellB p M μ (input G f x)*beamH F (input G f x)) i i) (fun i _=>Memo.cross hp (hearth_m h) i i)
lemma hearth_trans (h:Cleric F)(s:Site f) (hp:M.Bounds p α C D)(hh:0 < μ)(he:(stock p M μ (1:Config G f)).det≠0):
    sailM p M μ (rj s F)=ᶠ[𝓝 0] sailM p M μ F ∘ rideC s:=by
    let V:=input G f; let X:=rideC (G:=G) s; let W:= V ∘ X
    have hm: Army V 0:=Army.powL (v:=id) contDiffAt_id; have hW:Army W 0:=Army.powL (v:=X) X.contDiff.contDiffAt
    filter_upwards [hearth h W hW (by simp[W,V]),gate_n hp hh he (V:=V) hm (input_zero ..)] with z hz hv
    rw [Function.comp_apply, show sailM _ _ _ _ _=_ from rfl]; unfold sailM; rw[r_imp]; apply shell_get_s s _ hv ?_ hp
    rw [← r_imp];exact hz
lemma arm_sail_c(t:ℝ) (h:Cleric F) : sailM p M μ (t • F)=ᶠ[𝓝 0] t • sailM p M μ F:=by
    filter_upwards[hearth h (input G f) (Army.powL (v:=id) contDiffAt_id) (input_zero ..)] with z hz
    have hx: beamH (t • F) (input G f z) = t • beamH F (input G f z):=by ext i j; rw[Matrix.smul_apply,beam_p,beam_p,show bal (input G f z) (t • F)=t • bal (input G f z) F from rfl,iteratedFDeriv_const_smul_apply (hz.of_le le_top)];rfl
    rw[sailM,hx,Matrix.mul_smul, Matrix.trace_smul];rfl
lemma arm_sail_a (h:Cleric F)(hv:Cleric H): sailM p M μ (F+H)=ᶠ[𝓝 0] sailM p M μ F+sailM p M μ H:=by
    let V:=input G f; have hp:Army V 0:=Army.powL (v:=id) contDiffAt_id
    filter_upwards [hearth h V hp (input_zero ..), hearth hv V hp (input_zero ..)] with z hz hh
    have hx: beamH (F+H) (V z)=beamH F (V z)+beamH H (V z):=by ext i j;rw[beam_p,Matrix.add_apply,beam_p,beam_p,show bal (V z) (F+H)=bal (V z) F+bal (V z) H from rfl,iteratedFDeriv_add_apply (hz.of_le le_top) (hh.of_le le_top)];rfl
    unfold V at hx; rw [sailM,hx,Matrix.mul_add,Matrix.trace_add];rfl
lemma arm_sail_s (h:Cleric F)(hv:Cleric H): sailM p M μ (F-H)=ᶠ[𝓝 0] sailM p M μ F-sailM p M μ H:=by
    have hp: Cleric (-H):= (clergy G f).neg_mem hv
    rw[sub_eq_add_neg]; apply EventuallyEq.trans (arm_sail_a h hp); have hx:= arm_sail_c (p:=p) (M:=M) (μ:=μ) (-1) hv; rw[neg_one_smul,neg_one_smul] at hx; rw [sub_eq_add_neg];exact EventuallyEq.add EventuallyEq.rfl hx
lemma arm_sail_t {I:Type}(s:Finset I){A:I→ Peat G f}(h:∀ i∈s,Cleric (A i)): sailM p M μ (∑ i∈s,A i) =ᶠ[𝓝 0] ∑ i∈s,sailM p M μ (A i):=by
    induction s using Finset.induction with
    | empty=> simp only[sum_empty]; refine Eventually.of_forall fun x=> ?_
              unfold sailM;rw[show beamH (0:Peat G f) (input G f x)=0 from ?_]; simp
              ext i j; rw[beam_p]; rw [show bal (input G f x) (0:Peat G f)=(fun _=>0) from rfl]; simp
    | insert i s hi ih=>
       have hx(j)(hj:j∈s):= h j (mem_insert_of_mem hj); rw [sum_insert hi,sum_insert hi]; exact (arm_sail_a (h _ (mem_insert_self ..)) (show Cleric _ from (clergy G f).sum_mem hx)).trans (EventuallyEq.add EventuallyEq.rfl (ih hx))
lemma elm_cleric (V:Site f→ Peat G f)(a:Axis)(h:∀ i,Cleric (V i))(x): Cleric (elm a V x):=by
    unfold elm Pull.dTap; exact (clergy G f).sum_mem fun i _=> (clergy G f).smul_mem _ ((clergy G f).sub_mem (h _) (h _))
lemma arm_sail_e (V:Site f→Peat G f)(a:Axis)(h:∀ i,Cleric (V i))(x):
    sailM p M μ (elm a V x)=ᶠ[𝓝 0] elm a (sailM p M μ ∘ V) x:=by
    unfold elm Pull.dTap; apply (arm_sail_t _ ?_).trans; swap; · intro i _; exact (clergy G f).smul_mem _ ((clergy G f).sub_mem (h _) (h _))
    -- concat 4
    have hh{I:Type}[Fintype I]{X Y:I→Maze G f}(h:∀ i, X i =ᶠ[𝓝 0] Y i): (∑ i,X i) =ᶠ[𝓝 0] ∑ i,Y i:=by
        filter_upwards[eventually_all.mpr h] with z hz; simp only[Finset.sum_apply];exact sum_congr rfl fun i _=>hz i
    apply hh
    intro i; apply (arm_sail_c _ (show Cleric _ from (clergy G f).sub_mem (h _) (h _))).trans
    have ht(A B: Link G f→ℝ)(hp:A=ᶠ[𝓝 0] B): Pull.cash i • A=ᶠ[𝓝 0] Pull.cash i • B:=hp.mono (fun x hx=>congr_arg (fun x:ℝ=> Pull.cash i • x) hx)
    apply ht;exact arm_sail_s (h _) (h _)
lemma t_cleric (J:Site f→ Maze G f)(a:Axis)(h:∀ i,ContDiffAt ℝ ω (J i) 0)(x): ContDiffAt ℝ ω (elm a J x) 0:=by
    unfold elm Pull.dTap; rw[show ∀ p:Fin 4→ Maze G f,∑ i,p i=fun x=>∑ i,p i x from fun p=> funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum fun i _=> ((h _).sub (h _)).const_smul (Pull.cash i)
-- physical germ braid
lemma bra_pick {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{F H:X→ℝ}(h:braid F H 0 (k+1))(hv:ContDiffAt ℝ ω F 0)(hp:ContDiffAt ℝ ω H 0)(x:X): braid (fun z=> fderiv ℝ F z x) (fun z=> fderiv ℝ H z x) 0 k:=by
    intro i hi; let T:= ContinuousLinearMap.apply ℝ ℝ x; have hx: iteratedFDeriv ℝ i (fderiv ℝ F) 0=iteratedFDeriv ℝ i (fderiv ℝ H) 0:=by
        ext1 v; ext1 z; let p: Fin (i+1)→ X:=Fin.snoc v z; have he := DFunLike.congr_fun (h (i+1) (by omega)) p; rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_succ_apply_right] at he; unfold p at he; simpa using he
    change iteratedFDeriv ℝ i (T ∘ fderiv ℝ F) 0= iteratedFDeriv ℝ i (T ∘ fderiv ℝ H) 0; rw [T.iteratedFDeriv_comp_left (hv.fderiv_right (m:=ω) (by simp)) le_top,T.iteratedFDeriv_comp_left (hp.fderiv_right (m:=ω) (by simp)) le_top,hx]
lemma braceM (h:(F,H)∈wing f G) : ∀ i j, braid (fun z=>beamH F (input G f z) i j) (fun z=>beamH H (input G f z) i j) 0 2:=by
    obtain ⟨hc,ht,h⟩:=h; change Cleric F at hc; change Cleric H at ht
    intro i j
    let P(z):=input G f z
    let A(Z:Peat G f):=Z ∘ splitp G f; let X(Z:Peat G f): Acr G f→ℝ:=fun z=> fderiv ℝ (fun x=> fderiv ℝ (A Z) x (bolt (Sum.inr j))) z (bolt (Sum.inr i))
    have hv(Z: Peat G f)(h:Cleric Z): (fun z=>beamH Z (P z) i j)=ᶠ[𝓝 0] X Z ∘ takea G f:=by
        filter_upwards [soft_hx (A Z) (h.put _ splitp_n splitp_0)] with z hz; rw [Function.comp_apply]; unfold X; rw [← hz, beam_p, bockat,bockat]; congr 1
    have hy : ∀ Z, A Z =ᶠ[𝓝 0] (Z∘ input G f) ∘ bchip G f:= fun Z=> by filter_upwards [(show Tendsto (splitp G f) (𝓝 0) (𝓝 1) from splitp_0 ▸ splitp_n.cont.tendsto).eventually content_encodes] with z hz;exact congr_arg Z hz.symm
    have he:bchip G f 0=0:=by rw[bchip,splitp_0,content_one]
    have hx: braid (A F) (A H) 0 4:= braid.trans (braided (hy F)) (braid.trans (wove (w:=bchip G f) (he.symm ▸ h) (he.symm ▸ hc.dye) (he.symm ▸ ht.dye) (bchip_A ..)) (braided (hy H|>.symm)))
    have hh(Z: Peat G f)(h:Cleric Z): ContDiffAt ℝ ω (fun x=> fderiv ℝ (A Z) x (bolt (.inr j))) 0:= ((h.put (splitp G f) splitp_n splitp_0).fderiv_right (by simp)).clm_apply (g:=fun _=>bolt (Sum.inr j)) contDiffAt_const
    let T:= takea G f; have hz:=bra_pick (bra_pick (k:=3) hx (hc.put _ splitp_n splitp_0) (ht.put _ splitp_n splitp_0) (bolt (.inr j))) (k:=2) (hh F hc) (hh H ht) (bolt (.inr i)); have hf(Z: Peat G f)(h: Cleric Z): ContDiffAt ℝ ω (X Z) (T 0):=by rw [map_zero]; exact ((hh Z h).fderiv_right (by simp)).clm_apply (g:=fun _=> bolt (Sum.inr i)) contDiffAt_const
    exact braid.trans (braided (hv _ hc)) (braid.trans (wove (w:=T) (show braid (X F) (X H) (T 0) 2 by rw [map_zero]; exact hz) (hf _ hc) (hf _ ht) T.contDiff.contDiffAt) (braided (hv _ ht|>.symm)))
-- sailM F= G at second Hess after multiply
lemma braid_twice {F H:X→ℝ}(he:braid F H 0 2){i:X}: F 0=H 0∧ fderiv ℝ F 0 i=fderiv ℝ H 0 i:=by
    constructor
    · simpa [iteratedFDeriv_zero_apply] using DFunLike.congr_fun (he 0 (by omega)) Fin.elim0
    simpa [iteratedFDeriv_one_apply] using DFunLike.congr_fun (he 1 (by omega)) ![i]
lemma stiff (hp:(F,H)∈wing f G)(h: Memo (shellB p M μ ∘ input G f) 0): iteratedFDeriv ℝ 2 (sailM p M μ F) 0=iteratedFDeriv ℝ 2 (sailM p M μ H) 0:=by
    let X:= beamH F ∘ input G f;let Y:=beamH H∘ input G f
    have he : ∀ i j, braid (fun z=> X z i j) (fun z=> Y z i j) 0 2:=braceM hp
    obtain ⟨ht,hx,_⟩:= hp
    have hm:= hearth_m (F:=F) ht; have hv:= hearth_m (F:=H) hx
    let V:= shellB p M μ ∘ input G f; let U(z):= V z* X z; let T (z):= V z*Y z
    have hX:Memo U 0:= Memo.cross h hm; have hY:Memo T 0:= Memo.cross h hv
    suffices hz:∀ i j, iteratedFDeriv ℝ 2 (fun z=> U z i j) 0= iteratedFDeriv ℝ 2 (fun z=> T z i j) 0 by
       rw[show sailM p M μ F=∑ i:Lines G f 1, fun z=> U z i i from funext (fun v=> by rw[Finset.sum_apply];rfl),show sailM p M μ H=∑ i:Lines G f 1, fun z=> T z i i from funext (fun v=> by rw[Finset.sum_apply];rfl), iteratedFDeriv_sum_apply (fun i _=>(hX i i).of_le le_top),iteratedFDeriv_sum_apply (fun i _=>(hY i i).of_le le_top)]; exact sum_congr rfl (fun i _=> hz i i)
    intro i j; ext1 q; let u:=q 0; let v:=q 1
    have ht : directionM X 0 =directionM Y 0:=by funext x; ext i j; exact (braid_twice (i:=x) (he i j)).2
    have hx: bendM X 0 u v=bendM Y 0 u v:=by ext i j;exact DFunLike.congr_fun ((he i j) 2 le_rfl) (![u,v])
    have hd : X 0=Y 0:=by ext i j; exact (braid_twice (i:=0) (he i j)).1
    rw[show q=![u,v] from funext fun i=>by fin_cases i<;>rfl]; suffices hm' : bendM U 0 u v=bendM T 0 u v from congr_arg (fun X:Funds (Lines G f 1)=> X i j) hm'
    rw[← coins_M hX, ← coins_M hY]
    have hzX(K:WildM G f 1 1)(hK:Memo K 0):(fun z=> directionM (fun z=> V z*K z) z v)=ᶠ[𝓝 0] fun z=>directionM V z v*K z+V z*directionM K z v:=by filter_upwards [eventually_memo hK,eventually_memo h] with z hz hx;exact direction_prod hx hz v
    change Memo X 0 at hm; change Memo Y 0 at hv; change Memo V 0 at h
    rw [directions_congr (M:=fun z=> directionM U z v) (hzX _ hm), directions_congr (M:=fun z=>directionM T z v) (hzX _ hv)]
    change directionM ((fun z=> directionM V z v*X z) + (fun z => V z*directionM X z v)) 0 u= directionM ((fun z=>directionM V z v*Y z)+(fun z=>V z*directionM Y z v)) 0 u
    rw [direction_add ((memo_corner h v).cross hm) (h.cross (memo_corner hm v)), direction_add ((memo_corner h v).cross hv) (h.cross (memo_corner hv v))]
    simp_rw [direction_prod (memo_corner h v) hm, direction_prod (memo_corner h v) hv,direction_prod h (memo_corner hm v), direction_prod h (memo_corner hv v),coins_M hm,coins_M hv,hx,hd,ht]
end YM.Trace.Lamp
