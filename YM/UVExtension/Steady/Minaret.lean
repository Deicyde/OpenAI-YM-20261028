import YM.UVExtension.Steady.Scout
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Ink
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Arms
/-! Uniform gaps at *fixed* period. Finite-trajectory arcs of stamp, carrying
    all repeated labels (no spectral cutoff). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Steady.Minaret
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Laurent Tree Matrix MeasureTheory
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat AnalyticBridge.RelativeLogdet
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f:Side}{S:StepData c f} {ι α β κ J:Type} {v:Filter ι} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
section algebra
variable [Fintype J]
def Town (d:ℝ)(x:ℝ): Set (Matrix J J ℝ):= closedBall 0 d ∩ {X|X.IsHermitian}∩{X|Bottom X x}
lemma suburbs (d x:ℝ):IsCompact (Town (J:=J) d x):=by
    have hZ:IsClosed {X:Matrix J J ℝ| X.IsHermitian}:=isClosed_eq continuous_id.matrix_conjTranspose continuous_id
    have hf:IsClosed {X:Matrix J J ℝ|Bottom X x}:=by
      change IsClosed {M|∀ v:J→ℝ, x*dotProduct v v≤ dotProduct v (M *ᵥ v)}
      rw [setOf_forall]; apply isClosed_iInter; intro v; apply isClosed_le continuous_const ?_; unfold Matrix.mulVec dotProduct; fun_prop
    exact ((isCompact_closedBall _ _).inter_right hZ).inter_right hf
variable {d r:ℝ}
lemma certified {X:Matrix J J ℝ}(h: X∈ Town d r) (hr:0<r): X.PosDef:= definite h.1.2 h.2 hr
variable {a:J→ Site c}{B:ℕ} (D: Window a B)
lemma clm {X: E→ Matrix J J ℝ}{A' B':Type} [Fintype A'][Fintype B'] (r:A'→J)(s:B'→ J){x:E}{k:ℕ}(hp:ContDiffAt ℝ (↑k) X x): ContDiffAt ℝ (↑k) (fun i:E=> (X i).submatrix r s) x:=by
   let T : Matrix J J ℝ→ₗ[ℝ] Matrix A' B' ℝ :=
     { toFun := fun M=> M.submatrix r s
       map_add' := fun M N=> rfl
       map_smul' := fun M N=> rfl }
   exact T.toContinuousLinearMap.contDiff.contDiffAt.comp x hp
variable [DecidableEq J]
lemma refer {A:Matrix J J ℝ}(h:A.PosDef) (k : ℕ): ContDiffAt ℝ (↑k) (D.pad) A:=by
    have hh j: ContDiffAt ℝ (↑k) (fun X=> (D.principal X j)⁻¹) A:=by
       have hv := (Push.Loops.inv_contDiffAt (D.principal A j) (isUnit_iff_ne_zero.mpr ((h.submatrix (Embedding.subtype _).injective).det_pos.ne'))).of_le (show (↑k:ℕ∞ω) ≤ ω from le_top)
       exact hv.comp A (clm _ _ (X:=fun M=>M) contDiffAt_id)
    -- reconstruct all coord by summing
    have he i j: ContDiffAt ℝ (↑k) (fun X=>D.pad X i j) A:=by
       by_cases he : i∈ D.take j
       · let v: (D.take j):= ⟨i,he⟩; let w:D.take j:= ⟨j,D.here j⟩
         let T : Matrix (↥(D.take j)) (↥(D.take j)) ℝ →ₗ[ℝ] ℝ:=
           { toFun := fun M=> M v w
             map_add' := fun M N=> rfl
             map_smul' := fun M N=> rfl }
         simp_rw [Window.pad,Matrix.of_apply, dif_pos he]; exact T.toContinuousLinearMap.contDiff.contDiffAt.comp A (hh j)
       simp_rw [D.outside _ i j he]; exact contDiffAt_const
    let N :(J→J→ℝ)→ₗ[ℝ]Matrix J J ℝ :=
      { toFun:= Matrix.of
        map_add' := fun M N=> rfl
        map_smul' := fun M N=> rfl }
    have hp : ContDiffAt ℝ (↑k) (fun M i j=>D.pad M i j : Matrix J J ℝ→J→J→ℝ) A:= contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr (he i)
    exact N.toContinuousLinearMap.contDiff.contDiffAt.comp A hp
lemma youth {A:Matrix J J ℝ}(h:A.PosDef) (k:ℕ):ContDiffAt ℝ (↑k) (D.frameMean) A ∧ ContDiffAt ℝ (↑k) (D.flawed) A:=by
    let T : Matrix J J ℝ →ₗ[ℝ] Matrix J J ℝ:=
       { toFun:=Matrix.transpose
         map_add' := fun M N=>rfl
         map_smul':= fun M N=>rfl }
    have hp:= refer D h k
    have hh : ContDiffAt ℝ (↑k) (D.frameMean) A:=ContDiffAt.const_smul (c:=((1:ℝ)/2)) (hp.add (T.toContinuousLinearMap.contDiff.contDiffAt.comp A hp))
    exact ⟨hh,(contDiffAt_id.mul hh).sub contDiffAt_const⟩
lemma archP {A:Matrix J J ℝ}(h: A.PosDef) (v:ℝ)(hv: v∈ Ink.interval): (glide A v).PosDef:=by
  obtain ⟨hx,ht⟩:= hv; by_cases hz:v=0; · rw [hz,glide_start]; exact PosDef.one
  have he:= h.smul (hx.lt_of_ne (Ne.symm hz)); rw [Window.affine]; exact PosDef.posSemidef_add ((Matrix.PosSemidef.one (R:=ℝ)).smul (sub_nonneg.mpr ht)) he
end algebra
variable {B':ℕ}(D: Window (along (G:=G) S) B') -- B edit
lemma orbit (A: Matrix (Tubular f G) (Tubular f G) ℝ)(h:A.PosDef)(k:ℕ): ∀ i t,t∈ Ink.interval → ContDiffAt ℝ (↑k) (fun v:Mat f G×ℝ=> aSeq D v.1 v.2 i) (A,t) ∧ ContDiffAt ℝ (↑k) (fun v:Mat f G×ℝ=> sSeq D v.1 v.2 i) (A,t):=by
  intro i t ht
  have hp: ContDiffAt ℝ (↑k) (fun v:Mat f G×ℝ=> glide v.1 v.2) (A,t):=contDiffAt_const.add (contDiffAt_snd.smul (contDiffAt_fst.sub contDiffAt_const))
  have hg:= (refer D (archP h t ht) k).comp (A,t) hp
  have hb := ((youth D h k).2).comp (A,t) contDiffAt_fst
  match i with
  | 0=> exact ⟨contDiffAt_fst.sub contDiffAt_const,hb⟩
  | 1=> exact ⟨hg, (contDiffAt_snd.smul hb).neg⟩
  | _+2=> exact ⟨((hp.mul hg).sub contDiffAt_const).neg,(contDiffAt_snd.smul hb).neg⟩
private def pickM {J:Type}[Fintype J](i:J): Matrix J J ℝ→L[ℝ] ℝ :=
    ({ toFun := fun M=> M i i, map_add' := fun _ _=> rfl, map_smul' := fun _ _=> rfl } : Matrix J J ℝ→ₗ[ℝ] ℝ).toContinuousLinearMap
lemma lengths {X: Mat f G}(j : Bond f)(P:ℝ→ Mat f G→ ℕ→ Mat f G) (k:ℕ)(h : ∀ n t,t∈ Ink.interval → ContDiffAt ℝ (↑k) (fun v: Mat f G ×ℝ=> P v.2 v.1 n) (X,t)) {u:ℕ}(l:Itinerary f u): ContDiffAt ℝ (↑k) (fun v=> stamp (fun t=> P t v) j l) X:=by
    unfold stamp; apply ContDiffAt.sum; intro i hi
    let K (v:Mat f G ×ℝ):= if arrive j l=j then combo j l (P v.2 v.1) i i else 0
    have hm : Ink.Arc K k X:=by
       by_cases hx:arrive j l=j; swap; · intro t ht; unfold K; simp only [if_neg hx]; exact contDiffAt_const
       unfold K; intro t ht; simp only [if_pos hx] -- unfold `Ink.Arc` may not here
       suffices hh: ContDiffAt ℝ (↑k) (fun v:Mat f G×ℝ=> combo j l (P v.2 v.1)) (X,t) from (pickM i).contDiff.contDiffAt.comp (X,t) hh
       clear hx K; induction u generalizing j P with
       | zero => simp only [combo]; exact contDiffAt_const
       | succ u ih=> simp_rw [combo]; exact (clm _ _ (h 0 t ht)).mul (ih _ (fun t b j=> P t b (j+1)) (fun n=>h (n+1)) (after l))
    apply hm.writes.congr_of_eventuallyEq; filter_upwards with v; unfold checkIn; rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc] -- inspect
lemma mature {A: Mat f G}(h:A.PosDef)(k:ℕ) : (∀ p,ContDiffAt ℝ (↑k) (fun M=>ArmA D M p) A) ∧ (∀ p,ContDiffAt ℝ (↑k) (fun M=>ArmS D M p) A) ∧ ∀ i, ContDiffAt ℝ (↑k) (fun M=> Batch.joint M D i) A:=by
    refine ⟨fun _=> lengths _ (fun t M=> aSeq D M t) k (fun v t hx=>(orbit D A h k v t hx).1) _,fun _=> lengths _ (fun t M=> sSeq D M t) k (fun v t hx=>(orbit D A h k v t hx).2) _,fun i=>?_⟩
    unfold Batch.joint; apply ContDiffAt.sum; intro v hv
    let L (k:Mat f G×ℝ):= intensity D k.1 k.2 0 (i,v) (i,v); have ht : Ink.Arc L k A:=by
       intro t ht; let M:Mat f G ×ℝ:= (A,t)
       have hp := orbit D A h k 1 t ht|>.1
       suffices he: ContDiffAt ℝ (↑k) (fun q:Mat f G ×ℝ=> intensity D q.1 q.2 0) M from (pickM (i,v)).contDiff.contDiffAt.comp M he
       unfold intensity; simp only [pow_zero,mul_one]; exact (contDiffAt_fst.sub contDiffAt_const).mul hp
    apply ht.writes.congr_of_eventuallyEq; filter_upwards with i
    change (∫ t in (0:ℝ)..1, L (i,t))= _; rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
end YM.UVExtension.Steady.Minaret
