import YM.MergeProof.East.Gran
import YM.MergeProof.North.Bardo

/-! Afford the large calendar-based rank comparison on interiors of whole stages rather than only use `Paid.run` once per stage. Width still depends on the constructed waits. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Dense
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec Supply PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open YM.MergeProof YM.MergeProof.East
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ}
variable {Θ: Sheet G} (B: MapPrices) {L:Rolls Θ}{E:Protection L}{H:Delays E}{Z:Bar H}

structure Thicker (U:Wait Z)(V:Wait Z) : Prop where
   minL : U.minLength ≤ V.minLength
   ready : U.readyHere ≤ V.readyHere
   range : U.window ≤ V.window
lemma Thicker.retain {U V:Wait Z}{A:Levels G}(h:Thicker U V)(hv:Paid V A) : Paid U A :=
   retains_budget h.minL (fun i=>⟨h.ready i,h.range i⟩) hv

-- Backward window at k; the field-observation radius for the returned Wheel will be `gap`, *not* S.a k.
structure Interior (U:Wait Z)(A:Levels G)(k:ℕ) : Prop where
   opens : U.readyHere (A.clock.J k) ≤ A.S.scale k
   old : U.window (A.clock.J k) (A.S.scale k) ≤ k
   stays : ∀ i,k-U.window (A.clock.J k) (A.S.scale k) ≤ i → i≤k → A.clock.J i=A.clock.J k

structure Relay (Θ:Sheet G)(B:MapPrices)(u:ℕ→ℕ):Prop where
   bulletin : ∃ b:ℕ→Finset ℕ, ∃ Y:∀ d,Fin 3→ Tapes.Panel d, (∀ d, ∃ ξ, Checks (Y d 0).arc (Y d 1).arc (Y d 2).arc ξ (trays d) d) ∧
     (∀ d,∀ᶠ i in atTop,d∈b i) ∧ Fortified Θ B trays Y b u
lemma bulletin (X:Sheet G)(B:MapPrices) (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop):∃ k,Relay X B k:=by
   choose a ha hp using fun d=>raises d (trays d)
   obtain ⟨k,N,P,hK,hV,hB⟩:= y_poster X B a ha _ (fun _=> Nat.le_add_left ..) ht
   exact ⟨N,⟨k,P,fun d=>by rw [hV,hV,hV]; exact hp d,hK,hB⟩⟩
variable (O₀ : HaarBudget G) (J₀ : ChartRatio G) (U:Wait Z)
structure StationPort (U:Wait Z) (B:MapPrices) (O₀:HaarBudget G)(J₀:ChartRatio G) where
    panels : ∀ d,Fin 3→Tapes.Panel d
    cost : ℕ→ℝ
namespace StationPort
variable {U}{B}{O₀}{J₀}
def arc (S:StationPort U B O₀ J₀) (d) := (S.panels d 0).arc
structure Certified (S:StationPort U B O₀ J₀) : Prop where
    signs d : ∃ ξ, Checks (S.arc d) (S.panels d 1).arc (S.panels d 2).arc ξ (trays d) d
    reasonable d i : i≤d → Accent.generator G i ≤ S.cost d
    orders (C : Family G) : Paid U C.path.levels →∀ (K:Binding C), K.prices=B → ∀ (hC:C.Makes), ParadeX C → ∀ D,
          ∀ᶠ k in atTop, Interior U C.path.levels k → ∃ T, Poised (S.panels D) K hC O₀ J₀ (trays D) (S.cost D) k T

def clockwork {b : ℕ→Finset ℕ}{u:ℕ→ℕ}{μ:ℕ→ℝ}{p : ℕ→ℕ}{P:∀ d,Fin 3→Tapes.Panel d}
    (φ: ∀ i,Clocked B O₀ J₀ U (fun d=>P d i) μ p b)
    (h:∀ i,∀ᶠ j in atTop, i∈b j)
    (he: ∀ (A:Levels G),Paid U A→ ∀ i, U.readyHere (A.clock.J i) ≤ A.S.scale i→ wheel A i ≤ A.clock.monitor i) :
    ∀ (C:Family G),Paid U C.path.levels→ ∀ (K:Binding C), K.prices=B→ ∀ d,
      ∀ᶠ i in atTop, Interior U C.path.levels i → Cutouts K O₀ μ p J₀ P d i := by
   intro C hA K hK d
   filter_upwards [C.path.levels.fits.deep.eventually_gt_atTop Θ.first, C.path.levels.fits.deep.eventually (h d),
     eventually_all.mpr (fun α=> (φ α).rent C hA K hK)] with k hF hb h hx
   exact ⟨he C.path.levels hA k hx.opens,fun i=> h i hF hx.opens hx.old hx.stays d hb⟩
end StationPort
open StationPort

lemma next_wait_for (hG:G.Simple) {u:ℕ→ℕ} (hR:Relay Θ B u) (hu:∀ i,u i ≤ (L.L i).val)(hJ : LocalRatio J₀) :
    ∃ (W:Wait Z),Thicker U W ∧ ∃ S:StationPort W B O₀ J₀,S.Certified := by
   obtain ⟨b,P,ht,hP,hK⟩:= hR.bulletin
   let z j:= ∑ i∈Finset.range (j+1),Accent.generator G i
   have ho(i):0 ≤ Accent.generator G i:=by unfold Accent.generator; positivity
   obtain ⟨V,P',hm,hr,h0,hT,hθ,hE⟩:= y_tour B O₀ J₀ hG hK (H:=fun j=>show 0≤z j from Finset.sum_nonneg fun _ _=> ho _) (hx:=fun _=>Nat.le_add_left 2 _) hu hJ U
   obtain ⟨W,hv,hw,hp,he⟩:= w_bound V hG
   let S:StationPort W B O₀ J₀:=⟨P',z⟩
   refine ⟨W,⟨hm.trans hv,hr.trans hw,h0.trans hp⟩,S,⟨?_,?_,?_⟩⟩
   · intro i; simp only [StationPort.arc,S,← hT]; exact ht i
   · intro i j h; exact Finset.single_le_sum (f:=Accent.generator G) (fun _ _=> ho _) (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
   intro C hA B₀ hB hC hu d
   have h := clockwork (B:=B) (p:=trays) (μ:=z) (U:=W) (u:=u) (fun i=>printL B O₀ J₀ (hE i) W hv hw hp) hP he C hA B₀ hB d
   have hl:= (staging (n:=trays d) (z:=z d) (P' d) B₀ hC O₀ J₀ hG 0 hu (hθ d 0))
   filter_upwards [h, hl] with k hK hL hx
   exact hL (hK hx).limit (hK hx).aisle

end YM.Pert.Dense
