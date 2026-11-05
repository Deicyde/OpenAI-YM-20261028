import YM.RG12.Spins.Valley
import YM.RG12.Spins.Comet
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Pressure Next.Fluctuations Next.SectorChange Push.SectorMeasure Labels
open WardBin.Lies Planned.PrimaryIntegral295 PPX Next Next.Free
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{M:Metals G}(D:Rolls M.p)
protected def Dove (j i e:ℕ)(L:Side)(x:ℝ)(k:ℝ): Prop :=∀ d:ℕ, d+3≤ i →∀ (p:Push.Local.Probe G d),p∈ Push.Local.tests ((Labels.frames G).level d)→ ∀ a: ((Labels.frames G).level d).Index,∀ (c f:Side)(S:StepData c f)(T:Tube G S)(K : Flight j i),S.ratio.count=K.L→K.L=L→ HEq T.R.A0 (Carrier.linesOf K k)→ ∀ (w y),∀ hB:Blend 2 w y, 2*Heir.reach x<c.val→
      ∀ (hk: 4≤ i)(hu:d ≤ j)(hv:0< k), let R':=localSection G d; let F:=(Labels.frames G).level d; let u:=ocean T (Push.Local.presented R' (0:Site f) w (Place.copy F a)) x; let V:= (hol G).testLinks d 0 (y • p.1); let Z:=Seal.donne R' (sound G d) hv hk (Next.Foundations.valuation G d) K hu hB
      ‖(L.val:ℝ)^d • iteratedDeriv p.2.val (u ∘ (V: ℝ → Config G c)) 0 - Push.Local.runProbe F p (Z.leads L (Place.copy F a))‖ ≤ (x^e)⁻¹
def raft (e:ℕ){θ:Protection D}(W:Delays θ):Prop:= ∀ j x,W.betaEntry j ≤ x → ∀ i, StepStages j i → M.p.first ≤ i → Legato.Dove (G:=G) j i e (D.L j) x M.p.kernel.penalty
lemma soaring (e:ℕ){θ:Protection D}(W:Delays θ):∃ W':Delays θ,DelayLe W W'∧∀ X:Delays θ,DelayLe W' X→ raft D e X:=by
   have h(j i)(h:StepStages j i)(hi:M.p.first ≤ i):∀ᶠ x in atTop, Legato.Dove (G:=G) j i e (D.L j) x M.p.kernel.penalty:=by
      have he :4 ≤ i:=by have hx:=M.p.cut; omega
      have hj :4 ≤ j:=he.trans h.1
      have ha(d:ℕ)(hu:d≤j)(p:Push.Local.Probe G d):= eventually_all.mpr (fun a:((Labels.frames G).level d).Index=>Cub.Wild.starlight p (localSection G d) (hol G) (sound G d) (Next.Foundations.valuation G d) M.p.kernel.penalty_pos hj he hu a (D.L j) e)
      have hα (d:Fin (j+1)):= (Push.Local.tests ((Labels.frames G).level d)).eventually_all.mpr (fun i _=> ha d (by have := d.isLt; omega) i)
      filter_upwards [eventually_all.mpr hα] with x H d hd p hp a c f S T K hS hK hT t p₁ hA hX hh hh' hH
      exact H ⟨d,(Nat.lt_succ_of_le hh')⟩ p hp a _ _ _ _ _ hS hK hT t p₁ hA hX
   obtain ⟨A,_,hA,H⟩:=collect_upper W.betaEntry (fun j x=>∀ i, StepStages j i → M.p.first ≤ i → Legato.Dove (G:=G) j i e (D.L j) x M.p.kernel.penalty) (fun j=> eventually_transitions j _ _ (fun i hv=> by
       by_cases hV:M.p.first ≤ i; swap; · exact Eventually.of_forall fun x h'=>False.elim (hV h')
       exact (h j i hv hV).mono (fun x hx _=> hx)))
   exact ⟨{W with betaEntry:=A},⟨hA,le_rfl,le_rfl,le_rfl⟩,fun _ h j x hv=> H j x ((h.beta j).trans hv)⟩
end YM.PhysicalNext.Repeat.Legato
