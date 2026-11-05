import YM.Next.SCHEDULE.Layers
import YM.Work.F06
import YM.Work.F07
import YM.Work.F08
import YM.Work.F09

/-!
# Repinning on forecasts

The actual `profile` of the Sheet is used by the call to pinning. Some of its
fields may *need the pinned map prices* before they are known! Use a Sheet with
smaller price requests, and an explicit retargeting proof. Only the DIRECT
coefficient of the Clip is needed. No change to history/towers due to raising
the reserves. (Doesn't prove Rack.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling

open Filter RG RG.Supply Bid Precision Function Craft

/-- Sufficient (not necessary) to repin. -/
structure Refining {G : Gauge} (P Q : Sheet G) : Prop where
  kernel : Q.kernel=P.kernel
  direct j : (Q.profile j).clip.direct=(P.profile j).clip.direct
  bigger j :
    let a:=P.profile j; let b:=Q.profile j
    a.paths ≤ b.paths ∧ b.width ≤ a.width ∧ a.columns ≤ b.columns ∧
      a.clip.relaxation ≤ b.clip.relaxation ∧ a.supportExponent ≤ b.supportExponent
  drifts j : (P.profile j).drift ≤ (Q.profile j).drift

/-- universal quote lemma for initial X, usable without knowing the actual
Roll. -/
def Pinned {G : Gauge} (P : Sheet G) (X K : MapPrices) := ∀ a : Levels G,
  a.clock.stage=P.profile → a.clock.kernel=P.kernel → ∀ B : Horizon a,
    Rack a X B → ∃ T : Horizon a, Retained T B ∧ T.Suffices K

variable {G : Gauge}

private lemma roll_exchange {c f : Lattice.Side} {p q p' q' : Clip} {s : StepData c f}
    {H H' : Bed} {t : Towers s.patch.L}
    (r : Towers.Roll s H H' t p q) (hp : p.direct = p'.direct) (hq : q.direct = q'.direct) :
    Towers.Roll s H H' t p' q' := by
  have hu : Bed.full H p f=Bed.full H p' f := by simp [Bed.full,hp]
  have hv : Bed.full H' q c=Bed.full H' q' c := by simp [Bed.full,hq]
  obtain ⟨r,r1,r2,r3,r4,r5⟩ := r
  rw [hv] at r1 r2 r3 r4; rw [hu] at r2 r5
  exact ⟨r,r1,r2,r3,r4,r5⟩

private lemma floor_exchange {n : Lattice.Side} {H : Bed} {x y : ℝ} {p p' : Clip}
    (r : Floor H p n x y) (h : p.direct=p'.direct) : Floor H p' n x y := by
  have he : Bed.full H p n=Bed.full H p' n := by simp [Bed.full,h]
  obtain ⟨r1,r2,r3,r4,r5,r6,r7⟩ := r; rw [he] at r3; exact ⟨r1,r2,r3,r4,r5,r6,r7⟩

lemma Pinned.later {P Q : Sheet G} {X K : MapPrices} (h : Pinned P X K) (hv : Refining P Q) :
    Pinned Q X K := by
  intro a ha he B H
  let S : Calendar G := { a.clock with stage := P.profile }
  have hl (m) : 0 ≤ Real.log (a.S.block m).val := Real.log_nonneg (by
    have hz := a.S.block_large m; exact_mod_cast (show 1 ≤ (a.S.block m).val by omega))
  have hf : S.Fits :=
    { mesh := a.fits.mesh
      sameFactor := a.fits.sameFactor
      monotoneL := a.fits.monotoneL
      mono := a.fits.mono
      stepSlow := a.fits.stepSlow
      deep := a.fits.deep
      deepOrder := P.orders.comp a.fits.mono
      deepPower := P.powers.comp a.fits.mono
      deepExp := P.prices.comp a.fits.mono
      delayed := a.fits.delayed
      smallField := a.fits.smallField
      sizeT := a.fits.sizeT
      fitsPatch := a.fits.fitsPatch
      thetaRange := a.fits.thetaRange
      thetaMono := a.fits.thetaMono
      driftSmall m := by
        refine le_trans ?_ (a.fits.driftSmall m)
        refine div_le_div_of_nonneg_right ?_ (hl m)
        change (P.profile _).drift ≤ (a.clock.stage _).drift
        rw [ha]; exact hv.drifts _
      logCost m := by
        let t := S.params (m+1); let u := a.params (m+1)
        have ht := t.paths_pos
        have hU := t.columns_ge
        have hw := t.width_pos
        have hy := t.price_pos
        have hb := t.clip.radius_pos
        have hcu : t.paths ≤ u.paths ∧ u.width ≤ t.width ∧ t.columns ≤ u.columns ∧
            t.clip.relaxation ≤ u.clip.relaxation ∧ t.supportExponent ≤ u.supportExponent := by
          dsimp only [S,t,u,Levels.params,Calendar.params]; rw [ha]; exact hv.bigger _
        intro t'
        apply le_trans _ (a.fits.logCost m)
        apply div_le_div_of_nonneg_right _ (hl m)
        apply Real.log_le_log
        · change 0 < 1+t.paths+t.width⁻¹+t.columns+t.clip.relaxation+t.supportExponent
          have hn : 0 < t.columns := lt_of_lt_of_le zero_lt_one hU
          positivity
        change 1+t.paths+t.width⁻¹+t.columns+t.clip.relaxation+t.supportExponent ≤
          1+u.paths+u.width⁻¹+u.columns+u.clip.relaxation+u.supportExponent
        obtain ⟨h1,h2,h3,h4,h5⟩ := hcu
        have hp := inv_anti₀ u.width_pos h2; linarith }
  let b : Levels G := ⟨S,hf,fun m p ↦ ⟨(a.blocks m p).branches,(a.blocks m p).symmetric,(a.blocks m p).gauge⟩⟩
  let M : Horizon b := ⟨B.H,B.towers⟩
  have eqd (i) : (a.params i).clip.direct=(b.params i).clip.direct := by
    change (a.clock.stage _).clip.direct = (P.profile _).clip.direct; rw [ha]; exact hv.direct _
  have hg : Rack b X M := ⟨H.covers,fun n i hi j => floor_exchange (H.traces n i hi j) (eqd i), H.oath,H.top,H.legs,H.crosses,H.creak⟩
  obtain ⟨T,hT,Hs⟩ := h b rfl (he.trans hv.kernel) M hg
  let N : Horizon a := ⟨T.H,T.towers⟩
  exact ⟨N,⟨hT.1,hT.2⟩,Hs.rows,
    fun n i hi j => floor_exchange (Hs.all n i hi j) (eqd i).symm,
    Hs.costs,Hs.crossings,fun n m p hi => roll_exchange (Hs.stack n m p hi) (eqd _).symm (eqd _).symm,Hs.top⟩

/-- Acquire the committed `MapPrices` already on the provisional sheet. They
will work for *every* refinement. -/
theorem commit (P : Sheet G) (X : MapPrices) : ∃ K : MapPrices, Pinned P X K :=
  Bid.pinning Work.F06.answer Work.F07.answer Work.F08.answer Work.F09.answer P X
end YM.Next.Scheduling
