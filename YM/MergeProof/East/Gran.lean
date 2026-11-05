import YM.MergeProof.East.Largo
import YM.MergeProof.West.Commerce
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open PhysicalNext.Repeat.Legato.Bandage
open Org Spec Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
lemma raises (d n:ℕ): ∃ c:Fin 3→ℝ, (∀ i,d+6 ≤ c i) ∧ ∃ ξ,Checks (c 0) (c 1) (c 2) ξ n d:=by
    -- b-e=gap1; b-c offset arc σ
    let x : ℝ := 7*d*n+1
    let y := 6+x
    let a:ℝ:= 10 + d + x + ((y*d)*n)+y+7
    let l : Fin 3→ℝ:=![a,a-7,a-y]; have hL:0<x:=by positivity
    refine ⟨l,fun i=> ?_,-x,?_⟩
    · fin_cases i <;> (simp [l]; dsimp only [a,y,x]; nlinarith)
    change Checks a (a-7) (a-y) (-x) n d; refine ⟨by linarith,by linarith,by unfold y; linarith,by unfold x; linarith only,?_⟩; dsimp only [a,y,x]; linarith [Nat.cast_nonneg (α:=ℝ) d, (show 0<x from hL)]
-- Universal supplier preserving stage.

abbrev trays(d:ℕ):= d+2
structure RelayP (X : Supply.Sheet G)(B:MapPrices)(k:ℕ→ℕ) : Prop where
   buys : ∃ b:ℕ→Finset ℕ, ∃ Y:∀ d,Fin 3→ Tapes.Panel d, (∀ d, ∃ ξ, Checks (Y d 0).arc (Y d 1).arc (Y d 2).arc ξ (trays d) d) ∧
     (∀ d,∃ᶠ i in atTop,d∈ b i)∧Fortified X B trays Y b k
lemma posters (X:Supply.Sheet G)(B:MapPrices) (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop):∃ k,RelayP X B k:=by
    choose a ha hp using fun d=>raises d (trays d)
    obtain ⟨k,N,P,hK,hV,hB⟩:= y_poster X B a ha _ (fun _=> Nat.le_add_left ..) ht
    refine ⟨N,⟨k,P,fun i=> ?_,fun i=> (hK i).frequently,hB⟩⟩
    have h := hp i; simp only [hV]; exact h
-- calendaring Ties legit.M.
def CompleteWeak (C : Family G) (F : Extraction.Order):Prop:= ∀ (N D:ℕ) (R:ℝ), 0<R→(standard C).Smooth → ∀ H:(standard C).RealSpin, ∃ W : ℕ → Wheel C D,Granular W F H N R
open Supply Accent
variable {T : Sheet G}{D': Rolls T} {E : Protection D'} {T' : Delays E}{K : Bar T'}
lemma sponsored (hG:G.Simple)(B:MapPrices)(O:HaarBudget G)(J:ChartRatio G)(hx:LocalRatio J) (u:ℕ→ℕ)(h:RelayP T B u) (hu:∀ i,u i ≤ (D'.L i).val) (U:Wait K) :∃ V:Wait K, U.minLength ≤ V.minLength∧U.readyHere ≤ V.readyHere ∧ U.window ≤ V.window ∧ ∀ C:Family G,Paid V C.path.levels→∀ H: Binding C,H.prices=B→ C.Makes→ParadeX C→∀ (W : Worth)(a b c e r L),Scrim C W a b c e (fly C.path.levels) r L→∀ F,CompleteWeak C F:=by
    obtain ⟨b,P,ht,hP,hK⟩:=h.buys
    let Z j:= ∑ i∈Finset.range (j+1),Accent.generator G i
    have he(i):0 ≤ Accent.generator G i:=by unfold Accent.generator; positivity
    have ho i: 2 ≤ trays i:= Nat.le_add_left ..
    obtain ⟨V,P',h1,h2,h3,hC,hA,hB⟩:= y_stead B O J hG hK (μ:=Z) (fun i=>Finset.sum_nonneg fun j _=> he j) ho hu hx U hP
    refine ⟨V,h1,h2,h3,fun C hL H hz hM hu W a b c e r L hE f N D R hR hT hS=>?_⟩
    let d:= max N D
    have he':∀ i≤d,generator G i≤Z d:= fun i hi=>Finset.single_le_sum (fun j _=> he j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    obtain ⟨c',ht⟩:= ht d; rw [hC,hC,hC] at ht
    have hv : ∃ᶠ j in atTop,∃ Y, Poised (P' d) H hM O J (trays d) (Z d) j Y := by
       refine ((hB C hL H hz d).and_eventually (staging (n:=trays d) (z:=Z d) (P' d) H hM O J hG 0 hu (hA d 0))).mono fun i h => h.2 h.1.limit h.1.aisle
    obtain ⟨V,hV⟩:= podium (P' d) H hM hG hE O J _ he' f (ho d) R hR hT hS ht hv
    exact reduce_wave V hS f hV (le_max_right ..) ((le_max_left ..).trans (Nat.le_add_right ..))
end YM.MergeProof.East
