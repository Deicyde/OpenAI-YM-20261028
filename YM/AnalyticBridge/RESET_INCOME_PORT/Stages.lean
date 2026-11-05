import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen


set_option warningAsError false

/-!
# When the order-zero J and log table forecasts can already be paid

Stage gates for these two contributions. Before Bar, after (say)
`Cosmos`. Require the corresponding βEntry prices, or *choose*
anticipatory ones here. NOT payments for the remaining numerical prices
or the Recipe! No assertion the PRICE_COMPILER / canonical issued
Directed at other costs brings these hypotheses, with any desired shifts
of windows. Bills include the explicit Quote/log forecast costs in native
E δ, hence can e.g. choose σ = cost/64 upstream and don't spend these a
second time for a different unissued history.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open Next.Scheduling
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} {q : ResetPrices}

namespace Office
/-- Post-L and pre-*Issued*! Local chart = Z, need the picked d-multiplier
known for the use on the real band beforehand. -/
structure Flow (W : Delays Θ) (K : MapPrices) (H : Sheen.Gloss Z) (a σ : ℕ → ℕ → ℝ) : Prop where
  each (j i : ℕ) : Adj j i → C.first ≤ i → ∃ X : Etcher.Specs,
    ∀ x : ℝ, W.betaEntry j ≤ x → let t := σ j i * Vac.Numbers.Hat x ^ ((11:ℝ)/5)
    let d := a j i * fiery G x (D.L j)
    0 < t ∧ 0 < d ∧ 4*d ≤ H.zone ∧ ∀ {c f : Side} (S : StepData c f), S.patch.L=D.L j → S.patch.J=j →
    100*(1+radiusB x) ≤ c.val → ∀ e : Plate G S, e.x=x → (query C K j i).Funds S e.tube →
      ∀ (A : Stores S), (Fintype.card (Active A e.x e.forest):ℝ)*(H.cents*(4*d)^3) ≤ sites c*t ∧
        ∀ (V : Config G c), e.matched A V → ∀ u, let q := Etcher.forecast X e (radiusB x) A V u
        q.Pays e A V u ∧ q.tip ≤ sites c*t



/-- Just these two (partial) currencies through every required stage
before picking any qualifying Directed. Radius multiplier here requested
by Cosmos. Preserve Ringing and prior β/Cosmos bills. -/
theorem stamp (W : Delays Θ) (H : Sheen.Gloss Z) {g a E : ℕ → ℕ → ℝ} (hh : Ringing K g W) (hG : Cosmos Z K W g a E)
    (σ : ℕ → ℕ → ℝ) (hs : ∀ j i, 0<σ j i) : ∃ W' : Delays Θ,
      Boost W W' ∧ Ringing K g W' ∧ Cosmos Z K W' g a E ∧ Flow W' K H a σ := by
  have h (j i) (ha : Adj j i ∧ C.first ≤ i) :
      ∃ (X : Etcher.Specs) (u : ℝ), ∀ x : ℝ, u ≤ x → let t := σ j i * Vac.Numbers.Hat x ^ ((11:ℝ)/5)
      let d := a j i * fiery G x (D.L j)
      0<t ∧ 0<d ∧ 4*d ≤ H.zone ∧ ∀ {c f : Side} (S : StepData c f), S.patch.L=D.L j → S.patch.J=j →
      100*(1+radiusB x) ≤ c.val → ∀ e : Plate G S, e.x=x → (query C K j i).Funds S e.tube →
        ∀ (A : Stores S), (Fintype.card (Active A e.x e.forest):ℝ)*(H.cents*(4*d)^3) ≤ sites c*t ∧
          ∀ (V : Config G c), e.matched A V → ∀ u, let q := Etcher.forecast X e (radiusB x) A V u
          q.Pays e A V u ∧ q.tip ≤ sites c*t := by
    let L:= D.L j
    let S : Patch := ⟨L,j,C.cut.trans (ha.2.trans ha.1.1),(D.large j).size,(D.large j).odd⟩
    let T := query C K j i
    have hd := (hG j i ha.1 ha.2).door
    obtain ⟨X,hX⟩ := Etcher.table G S T (C.has S)
    refine ⟨X,eventually_atTop.mp ?_⟩
    filter_upwards [hX, Etcher.accuracy X L G (σ j i) (hs j i),Sheen.luster L H (σ j i) (a j i) (hs j i) hd,
      eventually_gt_atTop (1:ℝ)] with x hx ht hw hu
    intro t d
    have hz : 0<Vac.Numbers.Hat x := by unfold Vac.Numbers.Hat; positivity
    refine ⟨mul_pos (hs _ _) (Real.rpow_pos_of_pos hz _), hw.1,hw.2.1,?_⟩
    intro c f S' hl hj he e hh hg A
    have ho : S'.patch=S := by
      rcases heq : S'.patch with ⟨L',j',hc',hf',hj'⟩; rw [heq] at hl hj
      change L' = D.L j at hl; change j'=j at hj; subst_vars; rfl
    refine ⟨?_,fun V h u => ?_⟩
    · rw [hh]; exact hw.2.2 _ hl e.forest A
    exact ⟨hx S' e ho he hg hh A V h u _,ht S' e hh hl A V u⟩
  -- Collect along adjacent finite choices per j
  classical
  choose X p hp using h
  let f (j i : ℕ) := if h : Adj j i ∧ C.first ≤ i then p j i h else 0
  let V : Delays Θ := { W with betaEntry := fun j => max (W.betaEntry j) (max (f j j) (f j (j-1))) }
  have hB : Boost W V := ⟨fun j => le_max_left ..,le_rfl,le_rfl,le_rfl⟩
  refine ⟨V,hB,Bid.recheck hB.beta hh,fun j i ha hj => ?_,⟨fun j i ha hj => ?_⟩⟩
  · obtain ⟨hr,ht,hz⟩ := hG j i ha hj
    exact ⟨hr,ht,fun x hx => hz x ((hB.beta _).trans hx)⟩
  refine ⟨X j i ⟨ha,hj⟩,fun x hx => hp j i ⟨ha,hj⟩ _ (le_trans ?_ hx)⟩
  change _ ≤ max (W.betaEntry j) (max (f j j) (f j (j-1)))
  rw [← show f j i = p j i ⟨ha,hj⟩ from dif_pos ⟨ha,hj⟩]; apply le_max_of_le_right
  rcases ha.cases_back with e|e <;> subst i
  · exact le_max_left ..
  exact le_max_right ..

variable {g a σ : ℕ → ℕ → ℝ} {H : Sheen.Gloss Z} (B : Directed G I Z K P)
private lemma meter (m n : ℕ) : fiery G (B.a.clock.hatBeta m) ((B.a.clock.op m n).patch.L) = B.a.clock.threshold (m+1) := by
  have hl : B.a.clock.hatBeta (m+1)=betaF G (B.a.clock.hatBeta m) ((B.a.clock.op m n).patch.L) := by
    unfold Calendar.hatBeta betaF
    rw [Schedule.scale_succ]; change _ = _ + _ * Real.log (B.a.S.block m).val; unfold Levels.S; ring
  change temp _ = temp _; rw [hl]

/-- Convert only at the bought uf. H here must be the SAME
ChartRatio chosen by the Directed/plate (`b` has z fixed). -/
theorem current {N m p : ℕ} (hh : Flow W K H a σ) (hm : m < N) (F χ u k') :
    let j := B.a.clock.J (m+1); let i := B.a.clock.J m
    let t := (sites (B.a.S.side m p)) * (σ j i * B.a.clock.allowance m)
    let e := assigned B N m p g a F χ u k'
    0<t ∧ 0<e.d ∧ 4*e.d ≤ H.zone ∧ ∃ X : Etcher.Specs, ∀ A : Stores (B.a.clock.op m p),
      Sheen.bloom e H A ≤ t ∧ ∀ V : Config G _, e.matched A V → ∀ k,
        let q := Etcher.forecast X e (radiusB e.x) A V k
        q.Pays e A V k ∧ q.tip ≤ t := by
  intro j i t e
  have ha : Adj j i:=Deployment.adj B.a _
  have hc : C.first ≤ i := by rw [← B.valid.firstZero]; exact B.a.fits.mono (Nat.zero_le m)
  obtain ⟨X,hX⟩ := hh.each j i ha hc
  obtain ⟨hr,hl,ht,hp⟩ := hX _ (B.valid.pays m)
  let S:=B.a.clock.op m p
  have hL : S.patch.L = D.L j := (B.a.fits.sameFactor m).symm.trans (congr_fun B.valid.lengths _)
  have hn : 100*(1+radiusB e.x) ≤ (B.a.S.side m p).val := by rw [add_comm]; exact B.a.fits.sizeT m p
  have he : fiery G (B.a.clock.hatBeta m) (D.L j)= B.a.clock.threshold (m+1) := by rw [← hL]; exact meter B ..
  rw [he] at hl ht hp
  refine ⟨mul_pos (sites_pos _) hr,hl,ht,X,fun A => ?_⟩
  exact hp S hL rfl hn e rfl (Pressure.Testing.proceeds B N m p hm) A
end Office
end YM.AnalyticBridge.ResetIncome
