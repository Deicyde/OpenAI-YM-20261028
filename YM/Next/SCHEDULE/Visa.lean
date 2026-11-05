import YM.Next.SCHEDULE.Apron
import YM.Next.SCHEDULE.Markets


/-!
# Before boundary

A recommended invocation for THESE scheduling gates together. Also
inhabitation sanity checks for numerical requests (not a cure for
missing ESTIMATES projecting to those requests). Still quantifies Lens
costs as data not known at period. Further downstream R requirements
need more scheduling results, don't apply to arbitrary YU procedures.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling
open Filter RG RG.Supply Bid Precision Pressure Weak

variable {G : Gauge} {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange}
variable {v : ℕ → ℕ} {D : Rolls (s.paper q v)} {T : Protection D}

lemma Routed.after {u} {V W : Delays T} (h : Boost V W) (hw : Routed e u V) : Routed e u W :=
    fun j i ht b hh => hw j i ht b ((h.beta j).trans hh)

/-- Quintuple of upgrades at fixed θ THEN cutoff choices. Transmit any
Ringing coming in on selected pre/post V. No changing estimates after
hearing which periods the clock issued. -/
lemma topLedger (hG : G.Simple) {V : Delays T} {B : Beam K D} {F k f} (h : Loaded B V e F k f)
    (d u : ℕ → ℕ) (c : ℕ → ℝ) : ∃ W : Delays T,
    Boost V W ∧ Loaded B W e F k f ∧ (Extent d c W ∧ Routed e u W ∧ Bumper e W) ∧
    (∀ R : Radios K D, Transmitting R V → Transmitting R W ∧ Testing.Ringing K R.W W) ∧
    ∀ r : ℝ,∃ Y : Bar W, r ≤ Y.value ∧ ∀ J : Wait Y,∃ I : Wait Y, Behind J I ∧
      Billed I e f ∧ ∃ a : Levels G,Paid I a := by
  obtain ⟨V',hw,Hv⟩:=Routed.ready e u V
  obtain ⟨W,hW,H,b,g,hT⟩:=combined hG (h.later hw) d c
  have hx:=hw.chain hW
  refine ⟨W,hx,H,⟨g,Routed.after hW Hv,b⟩,fun R hl => ?_,fun r => H.waits hG r⟩
  have hh:Transmitting R W:=fun i j hj => (hl i j hj).trans (hx.beta i)
  exact ⟨hh,hh.ringing⟩

/-- Pre and post-L end-to-end (use those K values AFTER primaries
surveyed). Pure price variant without Gt.E assumption is `before` +
`activate`; here exhibit optional request for Energy IF using a proof
of Grants on the required profiles (not available for free). -/
theorem funded_prices (hG : G.Simple) (s : Survey G) :
    ∃ K : MapPrices, ∀ (q : Quote) (e : ℕ → ℕ → Exchange),
      -- actual Pressure premises pre-L, not Energy post an observed path
      (∀ i j, Teller.Grants (Testing.query (s.paper q s.floorL) K i j)) →
      ∃ f : ℕ → ℕ, ∀ v ≥ f,
        Nonempty (Rolls (s.metals q K v).p) ∧ Prepaid s K q e v ∧
        ∀ D : Rolls (s.paper q v), ∀ extraW : ℕ → ℕ → ℝ,
          ∃ (B : Beam K D) (R : Radios K D), (∀ i j,extraW i j ≤ R.W i j) ∧
            -- these further post-L bills can be valued now
            ∀ (F : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus)
              (extra : ℕ → ℝ), (∀ i,0 < extra i) → ∃ T : Protection D,T.theta ≤ extra ∧
              ∀ V : Delays T, ∀ c d u, ∃ W : Delays T, Boost V W ∧ Loaded B W e F m f ∧
                Extent d c W ∧ Routed e u W ∧ Bumper e W ∧
                Transmitting R W ∧ Testing.Ringing K R.W W ∧
                ∀ r : ℝ,∃ Y : Bar W,r ≤ Y.value ∧ ∀ J : Wait Y,
                  ∃ I : Wait Y, Behind J I ∧ Billed I e f ∧ ∃ a : Levels G,Paid I a := by
  obtain ⟨K,hK⟩:=s.openRun hG
  refine ⟨K,fun q e ha => ?_⟩
  obtain ⟨f,hf⟩:=(hK q e).2 ha
  refine ⟨f,fun v hv => ?_⟩
  obtain ⟨hn,hp,hT⟩:=hf v hv
  refine ⟨hn,hp,fun D eW => ?_⟩
  obtain ⟨R,hR⟩:=hT D eW; obtain ⟨B,hB⟩:=activate hG hp D
  refine ⟨B,R,hR,fun F m f extra he => ?_⟩
  obtain ⟨T,hT,H⟩:=hB F m f extra he
  refine ⟨T,hT,fun V c d u => ?_⟩
  obtain ⟨V',hV,Hv,Hr⟩:=(H V).2 R
  obtain ⟨W,h,H,⟨G0,G1,G2⟩,hg,w⟩:=topLedger hG Hv d u c
  exact ⟨W,hV.chain h,H,G0,G1,G2,(hg R Hr).1,(hg R Hr).2,w⟩

lemma quote_ne : Nonempty Quote := by
  let s : Strips:=⟨fun _ => 1,fun _ _=> 1,fun _ _=>1,by simp,by simp,by simp⟩
  let f : Figures := ⟨fun _ => 2,fun _ _=>2,by simp,by simp⟩
  let t : Finish:= ⟨fun _ => 12,fun _ _=>2,fun _ _=>2,worth (fun _ => 1),fun _=>1,by simp,by simp⟩
  exact ⟨⟨s,f,t⟩⟩




end YM.Next.Scheduling
