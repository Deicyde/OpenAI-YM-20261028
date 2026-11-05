import YM.TraceExtension.Shepherd.Spindle
import YM.TraceExtension.Cask.Votive
import YM.Next.RANK.Stretch
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory Cells
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{n:Side}(R:Rep G n)(x:Site n)(d:Axis)(ν:G.El→ G.El) (J:Config G n→ G.El →ℂ) {P:Support n}
    {σ A v δ u:ℝ}(h:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent) (m:ℕ) {D:ℝ} (hJ: ProofC R x J ν P D)
local notation "a"=>posDir d
local notation "r!"=> rink R x (posDir d) m J ν
def lensF (U:Config G n):= ∫ j:G.El,rink R x (posDir d) m J ν U j-J U j∂ G.probHaar
def pierSize (p:BudgetPoint) (m l:ℕ):= (l+m)*(4*p.B+2)+10*p.B
lemma meetP {i o z:Site n}{P:Support n}{l:ℕ}(hp:coverNumber R.p.B P ≤ l) (h:z∈P)(ho:o∈P)(hm:i∈ inspected (bluff R (fun _:Unit=>z) (fun _=> P) m ())): separation i z≤ pierSize R.p m l:=by
   obtain ⟨v,hv,ht⟩:=halo_spec.mp (Next.Rank.Thirst.inspect _ hm); unfold pierSize; have he:= R.p.B_pos
   have hz(S)(hv':v∈S)(hs:z∈S)(x:ℕ)(hx:coverNumber R.p.B S≤ x):separation i z ≤ x*(4*R.p.B+2)+2*R.p.B+8:=by
       have h1:= Corona.extent _ R.p.B hv' hs; rw[separation_comm] at ht; have ht:=separation_triangle i v z; have h2:=Nat.mul_le_mul_right (4*R.p.B+2) hx; omega
   rcases mem_union.mp hv with hf|hf; apply (hz _ hf h _ hp).trans; rw[add_mul]; omega
   obtain ⟨g,hg,hv⟩:=mem_biUnion.mp hf; exact (hz _ hv g.property.1 m g.property.2).trans (by rw [add_mul]; omega)
lemma bluffP (v:V)(x:V→Site n)(P:V→Support n): bluff R x P m v=bluff R (fun _:Unit=> x v) (fun _=> P v) m ():=rfl
include h H hv he hJ
lemma panel (hP : x ∈ P) (k:ℕ) (hK:coverNumber R.p.B P ≤ k) (hU:0∈P): Interior (Push.GridApprox.window 0 (2*pierSize R.p m k)) (lensF R x d ν J m):=by
   let o:Unit↪ Site n:= ⟨fun _=>x,fun i j _=> Subsingleton.elim _ _⟩; let Q:= bluff R (fun _:Unit=> x) (fun _=>P) m ()
   have hx : Palace R (fun _:Unit=>x) (fun _=>a) ν o (fun _=> P) (fun _=>J) m D:= ⟨fun _=> hJ,hJ.turns,hJ.borel,fun _=>hP,fun _=>hP,fun _ _ _=>Subsingleton.elim _ _,fun _ _ _ _ hz=> False.elim (hz (Subsingleton.elim ..))
     ⟩
   obtain ⟨hh,ht⟩:= extraCred R h H hv he m hx ()
   let Y:=fun U j=>r! U j-J U j; have hh' : Envelope (uncurry Y):= envUsub hh hJ.env
   have hz:Envelope (lensF R x d ν J m):= sealM G.probHaar (f:=Y) hh'
   have he: Interior (inspected Q) (lensF R x d ν J m):=by
       refine ⟨fun k U=>?_,hz.meas,fun U V hu=>?_,hz.cost⟩
       · have hV(A:Config G n)(g:Site n→G.El): field R m (Lattice.gauge g A)=field R m A:=by unfold field; apply congr_arg₂ (·+·) rfl (sum_congr rfl (fun i _=>(stock_pay R h i.val hv).2.1 _ _))
         have hu(j:G.El):Y (Lattice.gauge k U) (k x*j)=Y U j:=by
           unfold Y rink; rw[diary R x (posDir d) J ν hJ,hJ.gear]; unfold aura; rw[gazeP R x (posDir d) J ν hJ,hV,hV]
         refine ((integral_mul_left_eq_self (μ:=G.probHaar) (Y (Lattice.gauge k U)) (k x)).symm.trans ?_); simp_rw[hu]; rfl
       refine congr_arg (fun f:G.El→ℂ=>∫ j,f j∂G.probHaar) (funext fun j=> congr_arg₂ (·-·) (ht j U V hu) ((hJ.eye j) U V (agrees_mono hu (by intro x hp; exact mem_union_left _ (mem_union_left _ hp)))))
   refine he.enlarges (fun i hi=>?_); have hy := (separation_triangle i x 0).trans (add_le_add (meetP R m hK hP hU hi) (show separation x 0≤ _ from (separation_comm ..).trans_le (meetP R m hK hP hU (i:=0) (Finset.mem_union_left _ (Finset.mem_union_left _ hU)))))
   let D:= pierSize R.p m k; have hm:pdist i ≤ 2*D:= by
          simpa only[separation, sub_zero,two_mul] using hy
   refine ⟨lift i, box_test.mpr ⟨fun i'=> ?_,fun i' => ?_⟩,by simp⟩
   all_goals (have hx : (lift i i').natAbs ≤ 2*pierSize R.p m k:= (component_le i i').trans hm; omega)
end YM.Trace.Shepherd
