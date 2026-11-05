import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Bonfire
/-!
# Cauchy dust accounts on these exact Heaters
Adapt stage-1 reward with film on whitened P. Do NOT apply BodyGrant on
that P alone! Here use the mixed identity and projected envelopes proved
for that. Remaining costs literally named stage-1 constructions of choir/ramp.
Do not change any support predicates on the raw Audience.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Filter MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid SectorNext.Vacuum Precision Display Display.Docking Station Thirst
open scoped Topology BigOperators Classical ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f}
    {x τ σ w e l m n r : ℝ} {L : Lantern G S} {T : Tube G S} {A : Stores S} {P : Teller G}
    {W ι κ α φ : Type} [Fintype W] [DecidableEq W] {θ : W → Site f} {u : W → Site c}
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold)
    (K : κ → Lifted G θ R.p.threshold) [Fintype κ]
    (H : α → Flake S G x L.park u R'.p.threshold) (ht : Boosted T P x) {Wg : ℕ} (hs : 25*radiusB x+30 ≤ Wg) (hv : u=S.ratio.parent ∘ θ) {o m1 Λ δ v : ℝ} (hR : Tissue R o m1 Λ δ v)
    [Fintype ι] [Fintype α] [Fintype φ] {D : Allocation G S x w} {J : ChartRatio G}
local notation "P0"=> white R
local notation "J0"=> Gel.freezeKey K
local notation "Q" => picture R R' p J0 H ht hs hv
local notation "v'" => fun _ : W => r
local notation "B'" => R'.p.B
lemma so_mat (B) (Ω : φ→ SourceAt G θ) (hg : Envelope (Value.dust R Ω K)) (hK : Background R K)
    (hΩ : audition R R' H (T:=T) Ω) {Λ'} (h : BodyGrant T R L D J R'.p.threshold p Λ') (hp : ReturnTrip P0 R' p ht hs hv hR.status Λ' B)
    (hc : Coupler T L J D R.beta) (hX : earns_layout Q T): Matric B (bequeath Q ht) (S.push R.beta (Value.dust R Ω K)):= by
  obtain ⟨hI,hE⟩:= Film.rituals ht _ (auditioned P0 R' p K H ht hs hv hR.status hK) (clicked P0 R' p K H ht hs hv) _ hp.pays hp.rolls
  apply Eq.mp _ (in_bulk B _ _ (bequeath Q ht) (show Flux.Intervals B Λ' (germ Q ht) from hI) (show Nonempty (Flux.Embedded B.f (bequeath Q ht)) from hE)); congr 1; funext i; rw [← brigade ht R' Q]
  apply Eq.symm (rendered Q hg (dustMoves R Ω K hR) ht hc _ hX i)
  have ht : Value.dust R Ω K=Value.dust R Ω J0:= by funext U; unfold Value.dust; rw [Gel.all_keys K U]
  intro V A H; rw [ht]; exact stage_gain R R' p J0 _ _ _ _ _ hΩ h _ H
variable (C : α→Prop) (Y : φ→ SourceAt G θ)
theorem v_reward {Z} {σY Tz : ℝ} {E : Config G c → ℂ}
    (hp : Coupler T L J D R.beta) (he : BodyGrant T R L D J R'.p.threshold p E) (hX : ReturnTrip P0 R' p ht hs hv hR.status E Z)
    (hr : 0<r) (hl : 1≤l) (hm : 1≤ m)
    {δ y a γ k η σ ψ} {g : ℕ} (hf : Light R Y K v' σY γ η) (hg : Background R K) (hη : 0≤η)
    (ha : audition R R' H (T:=T) Y) (hy : Parachute S R.p R'.p e σY Wg Tz) (hσ : 0 ≤ σY)
    (hx : Pertains u g) (hB : Holdings R' p T m l e δ)
    (hZ : Spot R' H C T l v' e a) (hn : 0≤ a) (hN : Reparations u R' Z v' e l k ψ)
    (hk : δ+wilt B'*((Fintype.card (Site S.patch.L):ℝ)*(Tz*η))+wilt B'*(g*a)≤ σ)
    (hH : Real.exp σ-1+k ≤ ψ) (hd : Risible B' σ) (h0 : Tz*η+a ≤ y) :
    Matric Z (bequeath Q ht) (S.push R.beta (Value.dust R Y K)) ∧
      rawRadii Z (bequeath Q ht) (Glaze R R' p J0 H ht hs hv C) r e m l ψ y := by
  obtain ⟨z,hz,h⟩:= hB.prices
  obtain ⟨p',hp',hK⟩ := Gel.earned R.p K _ (fun i=>hr) hf.forced
  obtain ⟨w',hw,hw',hw'',hβ⟩:= hZ.balance
  let f (i):=penny (J0 i).extent R.p σY (p' i)
  have hz': LetterCost R R' p J0 H ht hs hv C z f w' l m (fun _=>r) :=
    ⟨hz,fun i=> penny_nn _ _ (hp' i).1,hw,fun i U A k y _=>bond_cost R _ ht L Wg hs _ _ hv U A k y _ (hp' i),fun i U A k y=> hw' i A U k y,hw''⟩
  refine ⟨so_mat R R' p K H ht hs hv hR Z Y (dustEnvelope R Y K hR (fun _=>hr) hσ hf hg) hg ha he hX hp
    (fun i U h k=> (refund R R' p J0 H ht hs hv C z f w' hz' (fun _=>hr) hl hm i U k h).1), finances R R' p J0 H ht hs hv C z f w' Z hz' hl hm hr hN hy.tallies ?_ hd hH ?_⟩
  · intro i; rw [Flux.locus, Flux.locus]; -- nested
    exact (add_le_add (add_le_add (h i) (packs_lift S (J0) p' (fun i=>(hp' i).1) hy le_rfl hη hK i)) (accum (H:=H) hw hx hn hβ i)).trans hk
  let k1:=ucap e+1
  intro i; rw [Flux.locus, Flux.locus]; apply le_trans ?_ h0
  let F(j:ι):Prop:=i∈(Glyph.quiet W).val
  change strike (fun i=>(p i).zone) z R'.p F k1+strike (fun i=> wings S Wg (J0 i).extent) f R'.p (fun j=> i∈(J0 j).fires.val) k1+strike (fun i=>(H i).space) w' R'.p (fun j=>i∈(H j).notes.val) k1≤ _
  rw [show strike (fun i=>(p i).zone) z R'.p F k1=0 by unfold strike; simp [F,Glyph.quiet,Census.quiet],zero_add]; refine add_le_add (price_lift S J0 p' (fun i=>(hp' i).1) hy (show k1≤Docking.increment _ by unfold Docking.increment k1; linarith only) hK i) (le_trans ?_ (hβ i));
  apply Finset.sum_le_sum; intro j _; unfold alarm; gcongr; exact hw j; unfold k1 Docking.increment; linarith only
end YM.PhysicalNext.InteractingRank.Soft
