import YM.TraceExtension.Quince.Sol
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Arcs
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Summer
/-! # Stochastic minus route at reference phase. one more derivative than order being sampled. In a genuine Neighborhood. -/
set_option autoImplicit false
-- adaptation Cub.Summer, expanded radius.
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular MultiNext.SignedSource WardBin.Lies Foliage
open JointLoad JointLoad.Heir Lyre
open Cub
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {F : Forest S.ratio}
    {P B : BudgetPoint} {X : Support f} {Y : Support c} {t r x τ : ℝ} {I : Type}
    {A : Stores S} {n j l : ℕ} {D' : Slab G c l} {u : ℝ} {q : Chi} {d : ℝ} {f' : Config G f → ℝ}
    {o : Site f}{C : Libretto G n}{D : Record}
variable (h : Plays C D P B Pt T x)

open Folio
variable (Y)
structure Until {c f:Side}{G:Gauge}{n:ℕ}(C: Libretto G n)(D:Record)(P B:BudgetPoint) (S:StepData c f) (o:Site f) (X: Support f) (Y:Support c)(m:ℕ)(x:ℝ): Prop where
    low:0 ≤ loom P m C.C
    small:D.Q*loom P m C.C ≤ 1
    normP:loom P m C.C < D.r
    tall:reach x ≤ m
    feasible : ∀ y∈Y,separation (S.ratio.parent o) y ≤ m
    widths : ∀ i:Bond f,Mom.needed X i→Lyre.width B o i ≤ 1
variable {Y}
section diagram
variable {m:ℕ} (hu: Until C D P B S o X Y m x)
variable [Fintype I](a:Museum F x A X Y I)(U:Config G f)(w:Prices G I)(hs:‖a.extra (1:Site c→G.El) u w‖≤loom P (reach x) C.C)
local notation "V₀"=> (1:Config G c)
local notation "G₀"=> (1:Site c→G.El)
include h hu hs
lemma depictedW(l:ℕ)(b:Slab G c l) : let v := enters V₀ (S.ratio.parent o) m G₀ b (a.extra G₀ u w); let Z:=journey V₀ l b
    ∀ᶠ y in 𝓝 (0:Panels l), Agrees (inspected X) (increment 1 (display T F x k true (v y))) (Lattice.gauge (fun i=> G.lieExp (φ T F true (v y).1 i)) (Lattice.gauge ((1:Site c→G.El) ∘ S.ratio.parent) (a.received k T q d u (Z y) U w))):=by
    intro v Z; let f:=a.extra G₀ u w; have hc:= h.rehearsed; have hT:= h.acts F k; have hE:D.r>0:= D.radius; have hp : v 0=(0,f):=by unfold v; unfold enters; rw [launch_zero _,blankBirth]
    have hh : ‖v 0‖≤ loom P (reach x) C.C := by rw[hp,Prod.norm_def, norm_zero]; exact max_le ((norm_nonneg _).trans hs) hs
    have hv:=posedW (P:=P) (o:= S.ratio.parent o) (r:=m) C.Z
    filter_upwards [(show ∀ᶠ i in 𝓝 0, ‖v i‖< D.r from ((readyEnter (A:=b) (w:=f) hv).continuousAt.norm.eventually (gt_mem_nhds (hh.trans_lt hc.tensions.allows)))),(flowJourney V₀ b).eventually hv.seen] with y hy hz
    rw[hT.represents true _ hy.le]; intro i hi hj
    let p:= S.ratio.parent i.1; have hq:Museum.Station Y x p:= (Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (a.asks i.1 hi)
    apply a.heard _ _ h.bulletin hi hj hq ?_ _ _ _ ?_
    · rw [separation_self]; omega
    intro j he; apply hz j; change separation _ _ ≤ m; exact hu.feasible _ (hq (halo_spec.mpr ⟨p,Finset.mem_singleton_self _,he⟩))
lemma pluckedW (b:Slab G c l) (hU: Healthy B.threshold X (a.received k T q d u V₀ U w)) :
    let v := enters V₀ (S.ratio.parent o) m G₀ b (a.extra G₀ u w)
    let z := display T F x k true (v 0)
    (∀ e, Mom.needed X e → ‖z e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1) ∧ ∀ s∈Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (s • z)) := by
  intro v z; have hc:= h.rehearsed; have hT:=h.acts F k; have hq:=hu; have hx : ‖v 0‖ ≤ loom P (reach x) C.C:=max_le (by change ‖launch _ _ _ _ _ 0‖ ≤ _; rw[launch_zero _,blankBirth,norm_zero];exact (norm_nonneg _).trans hs) hs
  have hb:= hT.toTour; have hh:= display_price hT (show 1≤ n by have he:=P.order_ge;rw [← hc.test];omega) hx hc.tensions.allows.le D.majorant
  have hz : Healthy B.threshold X (increment 1 z) := by
    have ht := (depictedW (q:=q) (d:=d) (k:=k) h hu a U w hs l b).self_of_nhds
    have he := flags_agree B.threshold _ _ X ht
    rw [gauge_flags,gauge_flags,Planned.AtomRegular.Sample.journey_origin _ b] at he
    change Disjoint _ _ at hU ⊢; rwa [Finset.disjoint_iff_inter_eq_empty,he,←Finset.disjoint_iff_inter_eq_empty]
  have hr := hc.tensions.small.trans (min_le_right ..)
  refine ⟨fun e he' => ⟨(norm_le_pi_norm z _).trans (hh.trans hr),hu.widths e he'⟩, (Flair.strings G).choose_spec.2 _ X _ _ z hr ((norm_nonneg _).trans hh) hc.weft.squared
    (fun i _ => (norm_le_pi_norm z _).trans hh) hz⟩
end diagram
end YM.PhysicalNext.Repeat.Quince
