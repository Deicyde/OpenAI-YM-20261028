import YM.FullVolume.Spiral.Dome
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint.Tower
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations Rank
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n m:Side}{Y:Hol G}
open MergeProof MergeProof.Matric FullVolume.Ray Jams Luna
variable {i:ℕ}{F:Labels.Frame G i}{B:BudgetPoint}{q t v a b s c u:ℝ}{p:sun→ Coefficient F n}{P:Desk G n}{y:F.Coeff}
local notation "A_"=> P.orient
set_option maxHeartbeats 380000
open Forum
open Extra.Histories.InputColumn
open UniformSpace FullVolume.Amp
local notation "I"=> Extra.Histories.InputColumn.Listing
open Beam
namespace PaidBeam
section
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
lemma static (x:X):PaidBeam (fun _=>x) ‖x‖:=⟨arm x,(armN x).le,fun i=>(armL i x).symm⟩
lemma field (f:sun→ X→Y) (h:∀ t u v, f t (u-v)= f t u-f t v)(hv:0≤v)(hp:∀ y,PaidBeam (fun i=> f i y) (v*‖y‖))(x:sun→X)(hx:PaidBeam x a): PaidBeam (fun i=> f i (x i)) (v*a):=by
   obtain ⟨P,hP,hB⟩:=hx.arrives; obtain ⟨Q,hQ,h⟩:= Beam.listen (ContinuousLinearMap.id ℝ X) isometry_id denseRange_id f h hv (fun x=> (hp x).arrives) P x hB; exact ⟨Q,hQ.trans (mul_le_mul_of_nonneg_left hP hv),h⟩
lemma transit (f:X→Y)(h:∀ u v,f (u-v)=f u-f v) (hv:0≤v) (hp:∀ y,‖f y‖≤v*‖y‖)(x:sun→X)(hx:PaidBeam x a): PaidBeam (fun i=> f (x i)) (v*a):=field (fun _=> f) (fun _=>h) hv (fun y=> (static (f y)).larger (hp y)) x hx
-- Neumann at charge.f.TRACK without choosing complex algebra structure. real fixed point common radius.
lemma origin (f:sun→ X≃ₗ[ℝ] X)(T:X≃ₗ[ℝ] X)(hv:0≤v)(hb:0≤b)(ht:∀x,‖T.symm x‖≤b*‖x‖) (h:v*b ≤ 1/2)(hP:∀ x,PaidBeam (fun s=>f s x-T x) (v*‖x‖)) {U:sun→X}(hs:PaidBeam U a): PaidBeam (fun s=> (f s).symm (U s)) (2*b*a):=by
   let f'(s:sun)(x:X):= f s x-T x; obtain ⟨P,hq,hz⟩:=(hs.arrives)
   let q(s:sun)(x:X):= T.symm (U s-f' s x);
   have he(x:Beam X):∃ A:Beam X,‖A‖≤ b*(a+v*‖x‖) ∧∀ i:sun,q i (read _ i x)=read _ i A:=by
       let Z:=fun i:sun=>read _ i x
       have hZ: PaidBeam Z ‖x‖:=⟨x,le_rfl,fun _=>rfl⟩
       have hh:= field f' (fun s x y=> by unfold f'; rw [map_sub,map_sub]; abel) hv hP Z hZ
       have hn:= transit (fun z:X=>-z) (fun x y=>by abel) zero_le_one (fun x=>le_of_eq (by rw [norm_neg,one_mul])) _ hh
       rw [one_mul] at hn; let u:= fun i=> U i-f' i (read _ i x); have h' :PaidBeam u (a+v*‖x‖):= (hs.plus hn).stamp (fun s=>sub_eq_add_neg ..)
       exact (transit _ (map_sub T.symm) hb ht u h').arrives
   choose Ψ hΨ hU using he; have hy : ContractingWith ⟨b*v, mul_nonneg hb hv⟩ Ψ:=by
        refine ⟨NNReal.coe_lt_coe.mp ?_, LipschitzWith.of_dist_le_mul fun x y=>?_⟩; · change b*v<1; nlinarith
        rw [dist_eq_norm,dist_eq_norm]; let V:=x-y
        have ht':= field f' (fun s x y=> by unfold f'; rw [map_sub,map_sub]; abel) hv hP (fun i=> read _ i (x-y)) (a:=‖V‖) ⟨x-y,le_rfl,fun _=>rfl⟩
        obtain ⟨Q,hQ,hB⟩:= (transit (fun x=> -(T.symm x)) (fun u v=>by rw [map_sub]; abel) hb (fun x=> (norm_neg _).trans_le (ht x)) _ ht').arrives
        have he : Ψ x- Ψ y=Q:=by
             apply soul;intro i; change read _ i (Ψ x-Ψ y)=read _ i Q; rw [map_sub, ←hB i, ← hU,←hU]; unfold q f'; simp_rw [map_sub]; abel -- check
        rw [he]; exact hQ.trans_eq (mul_assoc b v _).symm
   let k:= hy.fixedPoint Ψ; have he:k= Ψ k:= hy.fixedPoint_isFixedPt.symm
   refine ⟨k,?_ ,fun i=>?_⟩
   · have hx : ‖k‖ ≤ b*(a+v*‖k‖):= calc
        _=‖Ψ k‖:=congr_arg _ he
        _≤ _:=hΨ k
     nlinarith [norm_nonneg k]
   let y:= read X i k; have he':y=T.symm (U i-f' i y):= Eq.trans (congr_arg (read X i) he) (hU k i).symm; apply (f i).injective; rw [(f i).apply_symm_apply]; change _= f i y; apply eq_of_sub_eq_zero;
   have hh:T y= U i-(f i y-T y):= Eq.trans (congr_arg T he') (T.apply_symm_apply _); nth_rw 1 [eq_add_of_sub_eq hh.symm]; abel -- check
end
end PaidBeam
end YM.FullVolume.Paint.Tower
