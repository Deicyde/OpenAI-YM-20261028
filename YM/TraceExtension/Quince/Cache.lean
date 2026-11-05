import YM.TraceExtension.Quince.Creel
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice RG Pressure Pressure.Tube Wilson Finset
open ConnectedActivityE6 Push Push.AbsoluteSums Gas Ursell Extra.Histories
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open JointLoad JointLoad.Heir Roof Daisy Charity Rain Roost Lotus Blush Mallow
open Extra.Histories Extra.Histories.Doors Next.Foundations YM.Planned.GuardedAtom Labels
open Graces Cub Malachite Circlet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}(P0 P1: Stage)(d:ℕ)(L:Side)
set_option quotPrecheck false
-- final sprite lead after all pay <= y. Includes energy weights mare (Q). maybe overchoose.
def chief {d:ℕ}(G:Gauge)(X:ℝ)(p: Local.Probe G d) := Push.Local.partPrice (hol G) p*(Cub.gaugeMeter d * (X* (2+2)))+ X*(1+1)
-- both real fees. + common far note. choose y arbitrarily small after routines.
structure Bunk (G:Gauge)(P0 P1: Stage)(d:ℕ)(L:Side)(u v y:ℝ): Prop where
  cycle (p:Local.Probe G d): p∈Local.tests ((Labels.frames G).level d) → chief G (d:=d) ((L.val:ℝ)^d) p*v ≤ u
  reg: Motion.orbitCost ((Labels.frames G).level d) * (Local.testPrice ((Labels.frames G).level d)*u+ Local.readPrice (hol G) ((Labels.frames G).level d) * ((L.val:ℝ)^d*(v+v))) ≤ y
  huge: Motion.orbitCost ((Labels.frames G).level d) *(Local.readPrice (hol G) ((Labels.frames G).level d) * ((L.val:ℝ)^d*(v+v)) + Local.readPrice (hol G) ((Labels.frames G).level d) *((L.val:ℝ)^d*(v+v))) ≤ y
  main: Motion.orbitCost ((Labels.frames G).level d) * (Local.testPrice ((Labels.frames G).level d)*v+ Local.readPrice (hol G) ((Labels.frames G).level d) * ((L.val:ℝ)^d*(2*v* credibility G P1.supportExponent P1.order P1.power))) ≤ y
lemma foton (G:Gauge) (y:ℝ)(h:0<y):∃ u v,0<u ∧ 0<v ∧ Bunk G P0 P1 d L u v y:=by
    let H:=Local.readPrice (hol G) ((Labels.frames G).level d); let W:=Local.testPrice ((Labels.frames G).level d); let T:=Motion.orbitCost ((Labels.frames G).level d)
    let K:=∑ p∈Local.tests ((Labels.frames G).level d),‖chief G ((L.val:ℝ)^d) p‖
    have hp: 0≤ K:= sum_nonneg (fun _ _=> norm_nonneg _)
    let g(u:ℝ):= (1+K)*u; let a:ℝ:= (L.val:ℝ)^d; let b:=credibility G P1.supportExponent P1.order P1.power
    have ht(r:ℝ→ℝ)(hr:Continuous r)(he:r 0=0): ∀ᶠ u in nhdsWithin 0 (Set.Ioi 0), r u≤ y:= (hr.continuousAt.eventually (ge_mem_nhds (by rw[he];exact h))).filter_mono nhdsWithin_le_nhds
    have hb:∀ᶠ u:ℝ in nhdsWithin 0 (Ioi 0), Bunk G P0 P1 d L (g u) u y:=by
         filter_upwards [self_mem_nhdsWithin, ht (fun u=>T*(W*g u+ H*(a*(u+u)))) (by unfold g;fun_prop) (by simp[g]), ht (fun u=> T*(H*(a*(u+u))+H*(a*(u+u)))) (by fun_prop) (by simp), ht (fun u=> T*(W*u+H*(a*(2*u*b)))) (by fun_prop) (by simp)] with u hu hv ht he
         refine ⟨fun i hi=>mul_le_mul_of_nonneg_right ?_ (show 0≤u from (show 0<u from hu).le),hv,ht,he⟩
         exact ((le_abs_self _).trans (Finset.single_le_sum (f:=fun p=> |chief G a p|) (fun _ _=>abs_nonneg _) hi)).trans (le_add_of_nonneg_left zero_le_one)
    obtain ⟨x,(hx:0<x),h⟩:= (Eventually.and (show ∀ᶠ x:ℝ in nhdsWithin 0 (Ioi 0),0<x from self_mem_nhdsWithin) hb).exists; exact ⟨_,_,mul_pos (by positivity) hx,hx,h⟩
end YM.PhysicalNext.Repeat.Quince
