import YM.TraceExtension.Fen.Sets
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Numbers
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side} (R:Rep G n){I:Type} (b:I→Barley) {k:ℕ}{σ A C:ℝ}
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] {x:X}
lemma armsP (k:ℕ)(G:Gauge) (A:ℝ)(ha:0 ≤ A):∃ D:ℝ,0≤ D∧∀ (n:Side)(v: Link G n),‖v‖≤ A→∀ i,Allows k (fun y:Link G n=>G.mat (input G n y i)) v D:=by
    let M: (G.ColorIndex→ℝ)→L[ℝ] G.Color:=(WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearMap
    let B:= 1+A; let D:= ‖M‖ * B; have hB:0≤ D:=by positivity
    obtain ⟨E,hE,H⟩:= exists_allows (f:= G.mat ∘ G.lieExp) (s:=Metric.closedBall 0 D) (ProperSpace.isCompact_closedBall 0 D) (fun x _=> G.exp_jet.contDiffAt) k
    refine ⟨composeCost k E D,by unfold composeCost; positivity,fun n v hv i=>?_⟩
    have hu(t:G.ColorIndex): Allows k (fun y:Link G n=> edgeColor y i t) v B:=by
        let L:=ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Lines G n 1=>ℝ) (i.1,coord i.2,t)
        apply allows_linear (L:=L) ((L.opNorm_le_bound zero_le_one (fun j=>by rw[one_mul];exact norm_le_pi_norm j _)).trans (le_add_of_nonneg_right ha)); exact ((norm_le_pi_norm v _).trans hv).trans (le_add_of_nonneg_left zero_le_one)
    have hz: Allows k (fun y:Link G n=>edgeColor y i) v D:= (allows_pi (f:=fun y:Link G n=>fun t=>edgeColor y i t) (C:=B) (by positivity) hu).linear M le_rfl
    exact ((H _ (show edgeColor v i ∈ _ from (by simpa using hz.value))).comp (f:=fun y=>edgeColor y i) hz).germ (Eventually.of_forall fun x=> (congr_arg G.mat (input_color x i)).symm)
lemma pie_roll (G:Gauge)(k:ℕ)(A:ℝ)(ha:0 ≤ A):∃ D:ℝ,0≤ D ∧ ∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X]{n:Side}(U:X→ Config G n)(x:X),(∀ i,Allows k (fun y=>G.mat (U y i)) x A)→
   ∀ i,Allows k (fun p:X× Link G n=>G.mat ((input G n p.2 * U p.1) i)) (x,0) D:=by
    obtain ⟨B,hB,H⟩:=armsP k G 0 le_rfl
    refine ⟨2^k*B*A,by positivity,?_⟩; intro X _ _ n U x h i
    let L:=ContinuousLinearMap.snd ℝ X (Link G n); have hz : ‖L‖ ≤ 1:= L.opNorm_le_bound zero_le_one (fun z=>by rw [one_mul]; exact norm_snd_le ..)
    have ht : Allows k (fun p:X× Link G n=>G.mat (input G n (L p) i)) (x,0) B:= pre_short L (H n (L (x,0)) (by simp[L]) i) hz
    exact ht.times (f:=fun p=>input G n (L p) i) (g:=fun p=> U p.1 i) (allows_first_var (f:=fun y=>G.mat (U y i)) (p:=(x,(0:Link G n))) (h i))
abbrev Tar (p:Seat n×I):= metal R b p
def seatP (p:Seat n×I): Peat G n:=fer R p.1 (b p.2)
def outD (F:Peat G n)(i:Lines G n 1): Peat G n:=fun U=> fderiv ℝ (fun y=>F (input G n y * U)) 0 (bolt i)
def upLand (e:Lines G n 1)(j:Seat n×I):=ite (e.1∈Tar R b j) (port R (b j.2)) 0
lemma out_home {F:Peat G n}(i:Lines G n 1){U:Config G n}(hW:DifferentiableAt ℝ (fun y=>F (input G n y * U)) 0)(P:Support n)(he:LocalOn P F)(hi:i.1∉P): outD F i U=0:= by
    unfold outD; let L:=Push.side (fun y:Link G n=> F (input G n y*U)) hW (bolt i)
    refine (L.congr_of_eventuallyEq (f₁:=fun _=>F U) ?_).unique (hasDerivAt_const ..)
    apply Eventually.of_forall fun t=> he _ _ (fun e hh hx=>?_); rw [Pi.mul_apply,input_color,map_smul,Pi.smul_apply]
    rw [show edgeColor (bolt i) e=0 from ?_,smul_zero,G.mat_lieExp_zero,one_mul]
    ext j; change bolt (ι:=Lines G n 1) i (e.1,coord e.2,j)=0; simp [bolt,Pi.single_apply,show (e.1,coord e.2,j) ≠ i from fun he=> hi (congr_arg Prod.fst he ▸ hh)]
lemma lick (p:Seat n×I)(U:X→ Config G n)(x:X)(h:Army U x): ContDiffAt ℝ ω (seatP R b p ∘ U) x:=by
    let Z(e:Edge (Site n)):=G.mat (U x e)
    obtain ⟨f,hf,H⟩:= black G G.colorScale 0 (G.colorScale_pos.le)
    refine (H X R U x ?_ p.1 (b p.2)).analytic
    intro i; refine ⟨h i,fun k hk=>?_⟩; obtain rfl:k=0:=by omega
    rw [norm_iteratedFDeriv_zero]; exact (SectorAffine.mat_paid ..).le
lemma licks (p:Seat n×I)(U:Config G n): DifferentiableAt ℝ (fun y=>seatP R b p (input G n y*U)) 0:= ((licksW p U)).differentiableAt (by simp) where
  licksW(p:Seat n×I)(U:Config G n):ContDiffAt ℝ ω (fun y=>seatP R b p (input G n y*U)) 0:=lick _ _ _ _ _ ((Army.powL (v:=id) contDiffAt_id).mul (Army.park U _))
lemma peach (G:Gauge)(A:ℝ)(k:ℕ)(ha:0 ≤ A):∃ f:ℕ→ℝ,MarksP f ∧ ∀ (X:Type)[NormedAddCommGroup X][NormedSpace ℝ X](I:Type)(b:I→Barley){n:Side}(R:Rep G n)(hB:2 ≤ R.p.B)(U:X→ Config G n)(x:X),(∀ i,Allows (k+1) (fun y=>G.mat (U y i)) x A)→∀ (i:Seat n×I)(e:Lines G n 1), Allows k (outD (seatP R b i) e ∘ U) x (upLand R b e i*f (mote R (b i.2))):=by
    obtain ⟨D,hD,H⟩:= pie_roll G (k+1) A ha
    obtain ⟨f,hf,Hf⟩:= black G D (k+1) hD
    refine ⟨f,hf,?_⟩; intro X _ _ I b n R hB U x h i e
    by_cases hx:e.1 ∈ Tar R b i
    · rw [upLand,if_pos hx]; let V(s:X×Link G n):= input G n s.2* U s.1
      exact priced_partial (f:=seatP R b i ∘ V) (Hf (X × Link G n) R V _ (H X U x h) i.1 (b i.2)) _ (norm_bolt e).le
    unfold upLand; rw [if_neg hx,zero_mul]; apply (allows_const (n:=k) x (v:=(0:ℝ)) ((norm_zero (E:=ℝ)).le)).germ
    exact Eventually.of_forall fun y=> (out_home e (licks R b i (U y)) _ (ferLocal R _ _ hB) hx).symm
end YM.Trace.Fen
