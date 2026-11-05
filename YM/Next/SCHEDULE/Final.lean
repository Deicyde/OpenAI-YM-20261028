import YM.Next.SCHEDULE.Postal
import YM.Next.SCHEDULE.Stadium

/-!
# Issuing one schedule paying the gates

Use `Survey.openRun` then `activate`. Provision Recall etc. on its SAME
Sheet & MapPrices. Quantifier order explicit (including boosting window and
even post W). Pure arithmetic outputs and test portions unconditional.
Actual calls to transmit energy (Ringing contests) operate in the variant
with PreGrant (conditional, see `before`). Extra Delays/Wait charges in the
types to enable joined schedules not by weakening Quantifier at D. See the
more precise `Levels`,`Calling`,`Postal`,`Stadium` lugs for what *does*
follow at all these choices. Many other estimates necessary and NOT IMPLIED
by acquiring this schedule. This is neither the whole feasibility of YU nor
proof of it.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter Function RG RG.Supply Bid Pressure Precision Weak

variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {v : ℕ → ℕ}
variable {D : Rolls (s.paper q v)}

/-- After-Θ goals incl work stretches, not YU. All numbers `F j i`, etc
independent of Bar and delay etc, so can price on both entrances (including
i=j) not a posteriori evaluation on some physical history. Use `Loaded.waits`
to conclude meets at one Wait. -/
structure Loaded (B : Beam K D) {T : Protection D} (V : Delays T)
    (e : ℕ → ℕ → Exchange) (F : ℕ → ℕ → Postage) (k : ℕ → ℕ) (f : ℕ → Focus) : Prop where
  taxed : Regime B e F V
  marks : Marked e F k V
  beta j : T.theta j ≤ (f j).thin

lemma Loaded.waits (Gsimple : G.Simple) {B : Beam K D} {T : Protection D} {V : Delays T}
    {F k f} (h : Loaded B V e F k f) (b : ℝ) : ∃ Y : Bar V, b ≤ Y.value ∧ ∀ W : Wait Y,
      ∃ I : Wait Y, Behind W I ∧ Billed I e f ∧ ∃ a : Levels G,Paid I a := by
  obtain ⟨Y,hY⟩:=Bar.exists_above V b
  refine ⟨Y,hY,fun W => ?_⟩
  obtain ⟨I,hw,H⟩:=Billed.ahead Gsimple W e f h.beta
  exact ⟨I,hw,H, Wait.ready I Gsimple⟩

lemma Loaded.later {B : Beam K D} {T : Protection D} {V W : Delays T}
    {F k f} (h : Loaded B V e F k f) (hx : Boost V W) : Loaded B W e F k f :=
  ⟨h.taxed.carry hx,Marked.carry hx h.marks,h.beta⟩

/-- Use PreGrant *only* when needed post-L, calling on the selected K. Choose the
Radios BEFORE these F etc to use strengths accounting. Not assuming Grants (if
needed, they enter `before`). `extra` another theta ceiling, can include
requirements depending on adjacent indices. `V` arbitrary earlier requests on
threshold/barrier/geometric period floors BEFORE the Bar. Either variant does
not presuppose an operating trajectory or any proofs on a Directed object.
-/
theorem activate (Gsimple : G.Simple) (h : Prepaid s K q e v) (D : Rolls (s.paper q v)) :
    ∃ B : Beam K D, ∀ (F : ℕ → ℕ → Postage) (k : ℕ → ℕ) (f : ℕ → Focus) (extra : ℕ → ℝ),
      (∀ i,0 < extra i) → ∃ T : Protection D, T.theta ≤ extra ∧ ∀ V : Delays T,
        (∃ W, Boost V W ∧ Loaded B W e F k f) ∧
          ∀ R : Radios K D, ∃ W, Boost V W ∧ Loaded B W e F k f ∧ Transmitting R W := by
  obtain ⟨B⟩:=Beam.alight K D
  refine ⟨B,fun F k f g hg => ?_⟩
  obtain ⟨T,ht,he⟩:=temper D (fun i ↦ min ((f i).thin) (g i)) (fun i => lt_min ((f i).tp) (hg i))
  have hp (j) : T.theta j ≤ (f j).thin := le_trans (he j) (min_le_left ..)
  refine ⟨T,fun i => (he i).trans (min_le_right ..),fun V => ?_⟩
  obtain ⟨V',hv,H⟩:=Marked.raise F k V e
  constructor
  · obtain ⟨W,hw,hW⟩:= Regime.issue Gsimple B F ht V' h
    exact ⟨W,hv.chain hw,hW, Marked.carry hw H,hp⟩
  intro R; obtain ⟨W,hw,hW,hR⟩:= R.transmit Gsimple B F ht h V'
  exact ⟨W,hv.chain hw, ⟨hW, Marked.carry hw H,hp⟩,hR⟩

/-- Initial survey can actually be made given the potential charge numbers (not proving
estimates here), relative to ordinary primary source data. -/
theorem Authorities.survey (A : Authorities G) (f0 : ℕ) (hf : 4 ≤ f0)
    (X : MapPrices) (a w : ℕ → Need) (floorL : ℕ → ℕ) (d b : ℕ → ℝ) (h1 : ∀ i,0 < d i)
    (h2 : ∀ i,d i ≤ 1) (h3 : ∀ i,0 < b i) (h4 : ∀ i,b i < d i / 16) :
    ∃ S : Survey G,S.B=A ∧ S.X=X ∧ S.first=f0 ∧ S.floorL=floorL ∧ S.direct=d ∧ S.linear=b ∧ S.requests=a ∧
      ∀ i,(w i).order ≤ S.o.k i ∧ (w i).power ≤ S.o.P i ∧ ((w i).exponent : ℝ) ≤ S.o.A i := by
  obtain ⟨o,ho⟩:=Rungs.available a w
  exact ⟨⟨A,a,o,d,b,h1,h2,h3,h4,X,f0,hf,floorL⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,ho⟩

theorem Survey.openRun (Gsimple : G.Simple) (s : Survey G) :
    ∃ K : MapPrices, ∀ (q : Quote) (e : ℕ → ℕ → Exchange),
     (∃ f : ℕ → ℕ, ∀ v ≥ f,
      Nonempty (Rolls (s.metals q K v).p) ∧ Prepaid s K q e v) ∧
     ((∀ i j,Teller.Grants (Testing.query (s.paper q s.floorL) K i j)) →
        ∃ f : ℕ → ℕ, ∀ v ≥ f, Nonempty (Rolls (s.metals q K v).p) ∧
          Prepaid s K q e v ∧ PreGrant (s.metals q K v).p K) := by
   obtain ⟨K,hK⟩:= before s
   refine ⟨K,fun q e => ?_⟩; obtain ⟨⟨k,hk⟩,hh⟩:= hK q e
   exact ⟨⟨k,fun v hv => ⟨Rolls.exists_rolls _ Gsimple,hk v hv⟩⟩,fun he => by
     obtain ⟨k,hk⟩:=hh he
     exact ⟨k,fun v hv => ⟨Rolls.exists_rolls _ Gsimple,hk v hv⟩⟩⟩


end YM.Next.Scheduling
