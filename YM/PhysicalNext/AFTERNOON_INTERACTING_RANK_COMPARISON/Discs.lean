import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Iced
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Necklace
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Patron
/-!
# Earn the normalization holes on THIS actual step

`commissioned` & `interval_earns`: Opacity pays for logs on all these
unmarked letters. `in_boxes`: Resin gives the ONE scalar VACUUM
comparison (whole volume, all fields). Now recover for any region of
holes. Issue on every marker stencil, SAME normalization. No
compatibilities assumed on Lifted K'. Still to check cap for
actual resulting R'.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst Docking
     Flux Bid SectorNext.Vacuum Precision Baler
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S}
    {P : Teller G} {W V ι κ α β : Type} [Fintype W] [DecidableEq W]
    [Fintype ι] [Fintype α]
/-- arithmetic (L preloaded in Warm); no dependence on cert prop. -/
structure Lease (S : Side) (P Q : BudgetPoint) (e M L d y v : ℝ) : Prop where
  coin : 0≤e
  bright : 1 ≤ M
  lamps : 1 ≤ L
  upper : Towering S P Q (e+1) P.supportExponent
  sparks : wilt Q.B*((Fintype.card (Site S):ℝ)*(salary (e+1)*v)) ≤ d
  inferno : Risible Q.B (2*d)
  small : Real.exp (2*d)-1 ≤ 1-Real.exp (-(16*d))
  volume : (16*d)*ReLog.roof Q.B ≤ 1
  enough : 16*d ≤ 1
  patches : L*2*(16*d)≤ y/4
  fees : Real.exp (2*d)-1+(y/4) ≤ y
  due : d ≤ y/16
  output : Q.supportExponent ≤ e+1
  resumes : Tickets Q y
  cap : 0≤d
  interest : 0≤v

variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η β s M l k m σ e y w : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Opacity R R' p A hs hR ν (D:=D) (J:=J) e M l σ)
local notation "X0"=> unmarked R R' p A hs (blink S) hR
local notation "G0"=> germ X0 A
local notation "Q"=> germinates R R' p A hs hR E
local notation "V0"=> courtyard R R' p A hs hR E
variable (θ : W→Site f) (u : W→Site c) (hθ : u=S.ratio.parent∘θ)
local notation "X"=> unmarked R R' p A hs hθ hR
local notation "H"=> germ X A
local notation "F"=> gruel X A (callsQuiet R R' p A hs hR hθ)
local notation "Vb"=> carves R R' p A hs hR E he θ u hθ
local notation "R0"=> Gel.archived R θ hR
local notation "EQx"=> (Empty.elim : Empty→Flake S G x L.park u R'.p.threshold)
local notation "wk"=> (Empty.elim : Empty→Prop)
local notation "wp"=> (Empty.elim : Empty→ℝ)
variable (Ly : Lease S.patch.L R.p R'.p e M l σ y η)
local notation "Φ" z:max v:max r:max => (LetterCost R R' p R0 EQx A hs hθ wk z v wp l M r)
local notation "B"=> R'.p
local notation "Z" => unmarked R Q p A hs hθ hR
include he Ly
lemma commissioned (r : W→ℝ) (_hr : ∀ i,0 < r i) : ∃ z v, Φ z v r ∧ Hits (zones X) (bid z v wp) B (ucap (e+1)+1) (2*σ):= by
  obtain ⟨a,hA,h⟩:= sticker R θ hR r
  obtain ⟨k,hk,hV⟩:=he.cash.prices
  let b i:= penny (R0 i|>.extent) R.p R.p.supportExponent (a i)
  have hb : Φ k b r:= { paid:=fun i U N k v _=> bond_cost R _ A L _ hs _ _ hθ U N k v _ (hA i), charged:=hk,
                         stellar:=fun i=> penny_nn _ _ (hA i).1,
                         favorable:=fun i=>i.elim, illumined:=fun i=>i.elim, shaded:=fun i=>i.elim }
  refine ⟨k,b,hb,fun i=>?_⟩
  rw [Flux.locus,Flux.locus]; unfold strike; rw [show (Finset.univ : Finset Empty)=∅ by rfl, filter_empty,Finset.sum_empty, add_zero]
  exact (add_le_add (hV i) ((packs_lift S R0 a (fun i=>(hA i).1) (Docking.Towering.covers _ Ly.upper) le_rfl Ly.interest h i).trans Ly.sparks)).trans (by linarith only)
set_option maxHeartbeats 300000 in
lemma interval_earns (r : W→ℝ) (hr : ∀ i,0<r i) :
    let f i:= (H i).extent; let g i a:= ((H i).value a).re
    ∃ c',ReLog.Tags f B g c' ∧ ReLog.Fund f R'.p.B (ucap e) (16*σ) (Real.exp (2*σ)-1) c' := by
  intro f g; obtain ⟨z,w',hC,hS⟩:=commissioned R R' p A hs hR he θ u hθ Ly r hr
  let Y:=bid z w' wp; let c' (i:Exe X):=∏ j∈i.val.val,Y j
  have hv i:0 ≤ Y i:= incomes _ _ _ _ _ _ _ _ _ _ _ _ hC i; have ht i:0≤c' i:=prod_nonneg fun i _=>hv i
  refine ⟨c', start_local H B c' (fun i U=> ?_),⟨mul_nonneg (by norm_num) Ly.cap,?_,Ly.volume,Ly.small,ht,?_⟩⟩
  · have hx:= learned_club _ _ _ _ _ _ _ _ _ _ _ _ hC Ly.lamps Ly.bright hr i.val U
    change _ * Poly.price r (proceeds X T i.val U) ≤ _ at hx
    rw [← (parch X A i).2.2 U,CoverReads.covets,show ((H i).glow R'.p.threshold).fires=quiet W from (parch X A i).1] at hx
    rw [send_price] at hx; exact (le_mul_of_one_le_left (norm_nonneg _) (tune_safe R R' p R0 EQx A hs hθ wk Ly.lamps Ly.bright i.val)).trans hx
  · unfold Flux.ucap; linarith only [Ly.coin]
  have hh': ucap (e+1)=ucap e+1:= by unfold ucap; ring
  have hx:=inks X Y B (fun i=> ¬promotes X i) (e:=ucap e+1) (by rw [hh'] at hS; exact hS) Ly.inferno hv (by unfold ucap; linarith only [Ly.coin])
  intro i; have hw : Ac.Hit f R'.p.B c' (ucap e+1) (Real.exp (2*σ)-1) := by
    refine quotas f c' B ht ?_; convert! hx using 1
  apply Eq.mp _ (hw i); congr 1; funext i'; split_ifs <;> first |rfl| exact mul_comm ..
variable (hp : Resin R R' p A hs hR ν E e y)
include hp in
-- existence of exact *Lamprad* from funded schedule
lemma in_boxes (r : W→ℝ) (hr : ∀ i,0<r i) :
    ReturnTrip R Q p A hs hθ hR (fun x=>↑(ν x)) Vb ∧ Reparations u Q Vb r e l (y/4) y:= by
  obtain ⟨j,hj,hZ⟩:=interval_earns R R' p A hs hR he θ u hθ Ly r hr
  have hh:∀ i U,(H i).value U= _:= fun i U=> (show Sound ((H i).value U) from worth_real R R' p A hs hR he θ u hθ i.val U)
  refine ⟨⟨⟨fun i=> (parch X A i).1,fun D U=> ?_⟩,⟨(show Flux.Embedded F (bequeath X A) from ⟨Embedding.refl _,fun i=> held_guests ..,fun i _=>⟨i,rfl⟩⟩)⟩⟩,?_⟩
  · let J:=Vb
    have hv:= reclamation H B j hj hZ D U
    -- payroll expression ON V
    let r i:= (E i).letter U
    let f:= scalar W; let C:= ∏ i,(r i+1)
    have hc : deemed J U=f C := by
      unfold deemed C; rw [map_prod]; change (∏ i:α,((J.pay i).covets U+1))=_
      apply prod_congr rfl; intro i hi; exact (map_add f (r i) 1).symm |> fun h=>Eq.trans (by rw [map_one]; rfl) h
    change (↑(ν U):ℂ) • backgroundU H ((B).threshold) D U=((↑(Real.exp (R'.exponent U)):ℂ) • deemed J U)* reclaimed J U D
    have hm: ν U*realGas H B ∅ U= Real.exp (R'.exponent U)* C:= by rw [← (growth R R' p A hs hR (blink S) hθ hR).root]; exact hp.each U
    rw [hc, evening_table H B (fun i=> (parch X A i).1) hh,hv]
    rw [Algebra.smul_def, Algebra.smul_def]; change f _ * (f _ * _)=f _ * f _ * _; rw [← mul_assoc,← map_mul,hm,map_mul]; rfl
  obtain ⟨z',h,z,hx⟩:=patch_paid H B j hj hZ Ly.enough l (zero_le_one.trans Ly.lamps)
  obtain ⟨γ,H₁,H₂,H₃⟩:=hp.guards
  let V:=Vb; change Reparations u _ V _ _ _ _ _; refine ⟨z',γ,h,H₁,fun i U=> ?_,fun i U=>?_,fun i=> (hx i).trans Ly.patches,H₃⟩
  · change l*Poly.price r (Poly.send (quiet _) (((scroll H i).glow R'.p.threshold).value U)) ≤ _; rw [send_price]; exact z i U
  change Poly.price r (Poly.send (quiet W) ↑((E i).letter U)) ≤ _; rw [send_price, Complex.norm_real]; exact H₂ i U
end YM.PhysicalNext.InteractingRank.Display.Sew
