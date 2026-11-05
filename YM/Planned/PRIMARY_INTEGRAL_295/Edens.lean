import YM.Planned.PRIMARY_INTEGRAL_295.Gala
/-!
# Compatibility re choosing forecast row W.Stamp.Page

Doesn't assume present W[A0] tangent from arbitrary trajectory. Proves equality of
exact physical d1-unweighted composite on actual torus under Suffices;
keeps arbitrary kept A0 everywhere and shadow in `Page` using Canonical.A0
with all actually MEASURED fields unchanged. Never changing Family, kernel,
β reps/paths/tag histories, Rotor.C, etc. Holds may not be authenticated.All. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Edens
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Streets Laurent Next.Free
open Work.F08
open Triumph   Warehouse  Next.Foundations Extra.Histories Input
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical NNReal
variable {G:Gauge} {c f:Side} {S:StepData c f}

section Solve
variable {U: Matrix (Body 2 f) (Body 2 f) ℝ} {x:Clip}{A:Bed}{a b:ℝ}
variable {W W': Matrix (Body 1 f) (Body 1 c) ℝ} {B D:Matrix (Body 2 c) (Body 2 c) ℝ}
lemma burns (hp:Precision.K (A.metric.acts f)=Precision.K U) (h:Precision.Floor A x f a b) (he:0<a)
    (hw: Inputs S W (A.metric.acts f) B)(hq:Inputs S W' U D): mean S*W= mean S*W' ∧ d 1 f*W=d 1 f*W' ∧
      Precision.K B=Precision.K D :=by
    let L:= mean S; let P:= A.metric.acts f; let U':=Precision.K P; let k:= S.kernel.penalty; have hκ:=S.kernel.penalty_pos
    let Δ:=W-W'; let Y:= Precision.K B - Precision.K D
    have hY: U'*Δ=L.transpose*Y:=by
      have ht:Precision.K P*W'=L.transpose*Precision.K D :=by rw [hp,hq.primal]
      unfold Δ Y; rw [Matrix.mul_sub,Matrix.mul_sub, show U'*W= _ from hw.primal,ht]
    have hL: L*Δ= - k⁻¹ • Y:=by -- parentheses negative before
        have h: k⁻¹ • Y=k⁻¹ • Precision.K B - k⁻¹ • Precision.K D:=smul_sub _ _ _
        unfold Δ; rw [Matrix.mul_sub,show L*W=_ from hw.dual,show L*W'= _ from hq.dual,neg_smul,h]; abel -- replace
    let Z:= d 1 f
    have hc(X: Body 1 c→ℝ): (L*Δ).mulVec X=0∧(Z*Δ).mulVec X=0 :=by
       let v:= Δ *ᵥ X; let y:= Y *ᵥ X; let u:=Z*ᵥv
       have hf: L*ᵥ v= -k⁻¹ • y:= by unfold y v; rw [mulVec_mulVec,hL,Matrix.smul_mulVec]
       have hh:(u ⬝ᵥ (P*ᵥ u)) = -k⁻¹*(y ⬝ᵥ y):=calc
           _ = v ⬝ᵥ (U'*ᵥ v):=by unfold u U' Precision.K; rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec v,vecMul_transpose]
           _ = v ⬝ᵥ (L.transpose *ᵥ y):=by unfold v y; rw [mulVec_mulVec,hY,mulVec_mulVec]
           _ = _ :=by rw [dotProduct_mulVec,vecMul_transpose,hf,smul_dotProduct]; rfl
       have ha: 0≤u⬝ᵥ u:= Finset.sum_nonneg (fun i _=> mul_self_nonneg _)
       have hy: 0≤y⬝ᵥ y:= Finset.sum_nonneg (fun i _=>mul_self_nonneg _)
       have hκ:0<k⁻¹:=inv_pos.mpr hκ
       have hr:= (h.uniform.1 u).1; rw [hh] at hr; -- defeq?
       have hW : y ⬝ᵥ y=0 ∧ u ⬝ᵥ u=0:=by constructor <;> nlinarith
       have h1:y=0:= dotProduct_self_eq_zero.mp hW.1
       have h2:u=0:= dotProduct_self_eq_zero.mp hW.2
       rw [h1,smul_zero] at hf; exact ⟨(Matrix.mulVec_mulVec X ..).symm.trans hf,(Matrix.mulVec_mulVec X ..).symm.trans h2⟩ -- args
    have hz : L*Δ=0∧Z*Δ=0:=by
       constructor
       · apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; rw [map_zero]; exact (hc x).1
       apply Matrix.toLin'.injective; apply LinearMap.ext; intro x; rw [map_zero]; exact (hc x).2
    refine ⟨?_,?_,?_⟩
    · exact sub_eq_zero.mp (Matrix.mul_sub L W W'|>.symm.trans hz.1)
    · exact sub_eq_zero.mp (Matrix.mul_sub Z W W'|>.symm.trans hz.2)
    have hh :=hL.symm.trans hz.1; exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr (inv_ne_zero hκ.ne')))
end Solve

section Stay
variable (B:Levels G) (V:Horizon B) {T:MapPrices}(ht:V.Suffices T) (N:ℕ)

def predic (i p:ℕ):Matrix (Body 2 (B.S.side i p)) (Body 2 (B.S.side i p)) ℝ := (pink B.clock.kernel.penalty (location B N i)).acts (B.S.side i p)

private lemma ideal(k:ℝ) (hk:0<k) (j:ℕ)(hj:4≤j)(n:Side): (pink k (Train.top j)).acts n=1:=by
    -- Whole via heart
    let v:=Train.top j; have hh:Whole (pink k v):= by
      -- heart_true Witness cost
      exact (heart_saves k hk hj (fun _:Unit=>v)).1.whole ()
    have he := Whole.eq_on hh (Whole.coin (TypeFace 2)) (fun p hp => Eq.trans ((heart_true k hk hj v).1.echo _ hp) ((top_metric k hk j (base_subset_realCube zone_pos hp)).2.trans (read_unit _ p).symm)) n
    exact he.trans (acts_unit n)

private lemma english (i p:ℕ)(h:i<N) : let S:=B.clock.op i p; let L:=B.clock.kernel.penalty; let P:=destination B N i; let X:= linesOf P L
    Inputs S (installed S.ratio X) (predic B N (i+1) p) (predic B N i p):=by
    intro S L P X
    have he := (Flight.tangent P B.clock.kernel (B.clock.adm i) (show ((B.S.side (i+1) p).val)=(B.S.side i p).val*P.L.val from S.sizes))
    unfold predic; rw [loc_land B N i h]; exact he.1

include ht
lemma ontario (i p:ℕ)(h:i≤N):Precision.K ((V.H N i).metric.acts (B.S.side i p))=Precision.K (predic B N i p):=by
    induction h using Nat.decreasingInduction with
    | self =>
       unfold predic Precision.K; rw [loc_top,ideal _ B.clock.kernel.penalty_pos _ (B.clock.adm _),Matrix.mul_assoc,(ht.all N N le_rfl (B.S.side N p)).same,ht.top]; simp
    | of_succ i hi ih=>
       have hp:= ht.all N (i+1) hi (B.S.side (i+1) p)
       exact (burns ih hp (T.eta_pos _) (ht.crossings N i p hi).trial (english B N i p hi)).2.2
lemma laureates (i p:ℕ) (h:i<N): let S:=B.clock.op i p; let L:=B.clock.kernel.penalty; let P:=destination B N i; let X:=
       {(V.towers N i) with A0:=linesOf P L}; let a:=V.H N (i+1); let b:=V.H N i
    Towers.Roll S a b X (B.params (i+1)).clip (B.params i).clip ∧ Towers.Diagonal S a b X ∧ Bid.Sworn b (B.S.side i p) G:=by
   intro S L P X a b
   have hp := ontario B V ht N _ p h
   have hS:=ht.crossings N i p h; have hK:= ht.stack N i p h
   obtain ⟨hA,hD,hP⟩:=burns hp (ht.all N (i+1) h (B.S.side _ p)) (T.eta_pos _) hS.trial (english B N i p h)
   refine ⟨?_,?_,?_⟩
   · refine ⟨hK.m,hK.n,?_,hK.nPart,hK.oPart,hK.orthogonal⟩
     have hm:=hK.fPart; rw [Matrix.mul_assoc ((V.H N (i+1)).full _ _),hD,←Matrix.mul_assoc _ (d 1 (B.S.side (i+1) p))] at hm; exact hm
   · have hh:= (english B N i p h)
     refine ⟨⟨?_,?_⟩,hS.transport,?_⟩
     · rw [show Precision.K (a.metric.acts _)=_ from hp, show Precision.K (b.metric.acts _)=_ from hP]; exact hh.primal
     · rw [show Precision.K (b.metric.acts _)=_ from hP]; exact hh.dual
     have he := hS.stays; rw [Matrix.mul_assoc (a.diagonal.acts _),hD,←Matrix.mul_assoc] at he; exact he
   intro s x y; unfold Bid.gaugeFiscal; rw [show Precision.K (b.metric.acts _)=_ from hP]
   apply Finset.sum_congr rfl
   intro j _; rw [pigment,pigment]; exact apply_bill s L B.clock.kernel.penalty_pos (B.clock.adm _) (location B N i) _ _ _
end Stay
end YM.Planned.PrimaryIntegral295.Edens
