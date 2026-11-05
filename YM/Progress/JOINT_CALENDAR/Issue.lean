import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Tails
import YM.Next.FLUCTUATIONS.Bare
import YM.Next.FOUNDATIONS.SU2
import YM.Next.FREE_KERNELS.Calendar
import YM.Next.SCHEDULE.Visa


/-!
# One kernel and book of rates for linear and interacting calculations

Glue over `YM.Next.Free` and `YM.Next.Scheduling`.

A common **pre-L** issue, post-L issuance, and actual linear
construction on the paid Levels.

NOT construction of interacting path
corrections, Wilson density transfer, or any continuum limit.

Further
numerical/analytic requirements must be anticipated at the right binder
(e.g. all requests in a `Quote` or `Exchange` used here before all `Rolls`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.Joint
open RG Precision RG.Supply Bid Next Next.Scheduling Next.Scheduling.Weak Pressure Filter

variable {G : Gauge}

/-- General repinning with EXACTLY the comparison from `Free.before_paid`
(not e.g. componentwise bigger everywhere). For full `Pinned` one has to
carry even an arbitrary caller's Rack back to the quoting Sheet first. -/
theorem pin_willing {P Q : Sheet G} {X K : MapPrices} (hq : Pinned P X K)
    (hk : Q.kernel = P.kernel) (hw : ∀ i, Free.Willing (P.profile i) (Q.profile i)) : Pinned Q X K := by
  intro a ha he M g
  have h (i : ℕ) : Free.Willing (P.profile i) (a.clock.stage i) := by rw [ha]; exact hw i
  let A := Free.usingPrices P a h
  let B : Horizon A := ⟨M.H, M.towers⟩
  have hd i := Free.direct_retarget P a h i
  have hB : Craft.Rack A X B := ⟨g.covers,
    fun N i hi n => Free.floor_direct (hd i).symm (g.traces N i hi n), g.oath,g.top,g.legs,g.crosses,g.creak⟩
  obtain ⟨U,hu,H⟩ := hq A rfl (he.trans hk) B hB
  exact ⟨Free.recopy P a h U, hu,H.rows,
    fun N i hi n => Free.floor_direct (hd i) (H.all N i hi n), H.costs,H.crossings,
    fun N i p hi => Free.roll_direct (hd (i+1)) (hd i) (H.stack N i p hi), H.top⟩

/-- Linear output, no fall-back horizon selected at application time with a
new price list. `M,H` differ only as allowed by `Retained`. -/
def Built (a : Levels G) (X K : MapPrices) (l : ℕ → ℝ) := ∃ M H : Horizon a,
    Craft.Rack a X M ∧ Free.Present a M l ∧ Bid.Retained H M ∧ H.Suffices K ∧ Free.Present a H l ∧
      ∀ N i n, i ≤ N → Bid.Sworn (H.H N i) n G

theorem pinned_builds {X K : MapPrices} {p : Sheet G} {l γ : ℕ → ℝ} {b : ℕ → ℕ}
    (hn : Pinned p X K) (hc : Free.Catalog p.kernel X l γ b)
    {a : Levels G} (he : a.clock.kernel = p.kernel) (hs : a.clock.stage = p.profile)
    (h : Free.Credit a γ b) : Built a X K l := by
  obtain ⟨M,hM,hP⟩ := Free.shelves a X l γ b (by rwa [he]) h
  obtain ⟨H,hH,hK⟩ := hn a hs he M hM
  exact ⟨M,H,hM,hP,hH,hK,Free.retained_presents a X M H hP hM hH⟩



/-- Exactly the post-L portion of `Scheduling.funded_prices`. F, m, f may
look at D,B,R, *not* V,W,a. Teller.Grants are discharged here, not the
applicability of live tests to a physical calculation. -/
def Events (s : Survey G) (K : MapPrices) (q : Quote) (e : ℕ → ℕ → Exchange)
    (v : ℕ → ℕ) := ∀ D : Rolls (s.paper q v), ∀ extraW : ℕ → ℕ → ℝ,
    ∃ (B : Beam K D) (R : Radios K D), (∀ i j,extraW i j ≤ R.W i j) ∧
      ∀ (F : ℕ → ℕ → Postage) (m : ℕ → ℕ) (f : ℕ → Focus) (extra : ℕ → ℝ),
      (∀ i,0 < extra i) → ∃ T : Protection D,T.theta ≤ extra ∧
        ∀ V : Delays T, ∀ c d u, ∃ W : Delays T, Boost V W ∧ Loaded B W e F m f ∧
          Extent d c W ∧ Routed e u W ∧ Bumper e W ∧
          Transmitting R W ∧ Testing.Ringing K R.W W ∧
          ∀ r : ℝ,∃ Y : Bar W,r ≤ Y.value ∧ ∀ J : Wait Y,
            ∃ I : Wait Y, Behind J I ∧ Billed I e f ∧ ∃ a : Levels G,Paid I a

/-- Include a free supply on **each such** Levels (even on other paid
Levels with the same Sheet). One K for both branches. -/
structure Package (s : Survey G) (K : MapPrices) (q : Quote) (e : ℕ → ℕ → Exchange)
    (v : ℕ → ℕ) (l γ : ℕ → ℝ) (b : ℕ → ℕ) : Prop where
  starts : Nonempty (Rolls (s.metals q K v).p)
  prices : Prepaid s K q e v
  afterL : Events s K q e v
  serves (D : Rolls (s.paper q v)) {T : Protection D} {W : Delays T} {Y : Bar W} {I : Wait Y} {a : Levels G} :
    Paid I a → Free.Credit a γ b ∧ Built a s.X K l

variable {s : Survey G} {K : MapPrices} {q : Quote} {e : ℕ → ℕ → Exchange} {l γ : ℕ → ℝ} {b : ℕ → ℕ}

theorem join_bills (hc : Free.Catalog s.B.kernel s.X l γ b)
    (hd : ∀ i,s.first ≤ i → s.direct i ≤ γ i)
    (h : ∃ f : ℕ → ℕ, ∀ v ≥ f,
        Nonempty (Rolls (s.metals q K v).p) ∧ Prepaid s K q e v ∧ Events s K q e v) :
    ∃ f : ℕ → ℕ, ∀ v ≥ f, Package s K q e v l γ b := by
  obtain ⟨f,h⟩ := h
  refine ⟨fun i => max (f i) (b i),fun v hv => ?_⟩
  obtain ⟨hg,hp,hE⟩ := h v (fun i => (le_max_left ..).trans (hv i))
  refine ⟨hg,hp,hE,fun D _ _ _ _ _ ha => ?_⟩
  have hγ := Free.credit_from_sheet ha γ b hd (fun i _ => (le_max_right ..).trans (hv i))
  exact ⟨hγ,pinned_builds hp.pins hc ha.kernel ha.stage hγ⟩



/-- Version of `funded_prices` that takes a previously pinned K on the
final profile. `Prepaid.floors` for an auxiliary quote only used for its
*numeric* floors, then before PreGrant/activate replace its `.pins` by the
actual early quote. (No auxiliary Rolls ever run.) -/
theorem pinned_events (hG : G.Simple) (e : ℕ → ℕ → Exchange) (hK : Pinned (s.paper q s.floorL) s.X K) :
    ∃ f : ℕ → ℕ, ∀ v ≥ f,
        Nonempty (Rolls (s.metals q K v).p) ∧ Prepaid s K q e v ∧ Events s K q e v := by
  obtain ⟨K₀,hK₀⟩ := commit s.sheet s.X
  obtain ⟨f,hf⟩ := Prepaid.floors s K₀ hK₀ q e
  obtain ⟨u,hu⟩ := PreGrant.joint (s.paper q s.floorL) K (fun _ _ =>
    YM.Integrated.pressure_grants YM.Next.Fluctuations.bare _)
  refine ⟨fun i => max (f i) (u i), fun v hv => ?_⟩
  have H := hf v (fun i => (le_max_left ..).trans (hv i))
  have hs : Prepaid s K q e v := ⟨hK,H.higher,H.each,H.cash⟩
  have hr : PreGrant (s.paper q v) K := hu v (fun i => (le_max_right ..).trans (hv i))
  refine ⟨Rolls.exists_rolls _ hG,hs,fun D eW => ?_⟩
  obtain ⟨R,hR⟩ := hr D eW
  obtain ⟨B,hB⟩ := activate hG hs D
  refine ⟨B,R,hR,fun F m f extra he => ?_⟩
  obtain ⟨T,hT,H⟩:=hB F m f extra he
  refine ⟨T,hT,fun V c d u => ?_⟩
  obtain ⟨V',hV,Hv,Hr⟩:=(H V).2 R
  obtain ⟨W,h,H,⟨G0,G1,G2⟩,hg,w⟩:=topLedger hG Hv d u c
  exact ⟨W,hV.chain h,H,G0,G1,G2,(hg R Hr).1,(hg R Hr).2,w⟩

theorem shared_pin (hG : G.Simple) {P : Sheet G} {X : MapPrices} (hc : Free.Catalog P.kernel X l γ b)
    (hp : Pinned P X K) (e : ℕ → ℕ → Exchange) (hk : s.B.kernel=P.kernel) (hX : s.X=X)
    (hw : ∀ i, Free.Willing (P.profile i) (s.melt q i)) (hd : ∀ i,s.first ≤ i → s.direct i ≤ γ i) :
    ∃ f : ℕ → ℕ, ∀ v ≥ f, Package s K q e v l γ b := by
  have h : Pinned (s.paper q s.floorL) s.X K := hX.symm ▸ pin_willing hp hk hw
  exact join_bills (by rwa [hX,hk]) hd (pinned_events hG e h)



/-! ## Constructive realization of the PRE-L layer as well -/

/-- Stage rates here only used to issue T; drift and logCost are the gates
in `Willing`. In particular direct is small but the SAME as later. No
commitment to all future nonlinear bills/scales before getting T. -/
def startSheet (B : Authorities G) (b : ℕ → ℕ) (d : ℕ → ℝ) (h : ∀ i,0<d i) : Sheet G where
  profile i := ⟨⟨d i,d i/32,12,h _, by have := h i; positivity,by have := h i; linarith,by norm_num⟩,
    6,2,1,1,1,0,1, by omega,by omega,one_pos,one_pos,one_pos,by norm_num,le_rfl,le_rfl⟩
  first := 4
  cut := le_rfl
  orders := fun _ _ _ => le_rfl
  powers := fun _ _ _ => le_rfl
  prices := fun _ _ _ => le_rfl
  kernel := B.kernel
  has := B.has
  floorL := b

structure Desk (B : Authorities G) where
  X : MapPrices
  l : ℕ → ℝ
  γ : ℕ → ℝ
  b : ℕ → ℕ
  catalog : Free.Catalog B.kernel X l γ b
  direct : ℕ → ℝ
  pos i : 0 < direct i
  cap i : direct i ≤ 1
  small i : direct i ≤ γ i
  T : MapPrices
  pins : Pinned (startSheet B b direct pos) X T





variable {B : Authorities G} (O : Desk B) {r w : ℕ → Need}

def Desk.menu (first : ℕ) (hf : 4 ≤ first) (o : Rungs r) : Survey G :=
  ⟨B,r,o,O.direct,fun i => O.direct i /32,O.pos,O.cap,fun i => by have := O.pos i; positivity,
   fun i => by have := O.pos i; linarith,O.X,first,hf,O.b⟩

lemma Desk.willing {q : Quote} (he : s.direct=O.direct) (i : ℕ) : Free.Willing
    ((startSheet B O.b O.direct O.pos).profile i) (s.melt q i) := by
  refine ⟨congr_fun he.symm _, (s.melt q i).drift_ge,?_⟩
  unfold Free.numericBasis
  apply Real.log_le_log
  · norm_num [startSheet]
  change 1+1+(1:ℝ)⁻¹+1+12+1 ≤ 1+q.classicalCost.cap i+(q.widths.width i)⁻¹ + s.columns q i + Survey.change q i + s.o.A i
  have h1 := q.classicalCost.cp i
  have h2 := inv_anti₀ (q.widths.wp i) (show q.widths.width i ≤ 1 from min_le_left ..)
  have h3 := s.factorial q i
  change ↑(Nat.factorial (s.o.k i)) ≤ s.columns q i at h3
  have h3' : (2:ℝ) ≤ ↑(Nat.factorial (s.o.k i)) := by
    have := Nat.factorial_le (by have := s.o.six i; omega : 2 ≤ s.o.k i)
    exact_mod_cast (show 2 ≤ Nat.factorial (s.o.k i) from this)
  have h4 := Survey.change_ge q i
  linarith [s.o.pos i]

lemma Desk.pay (hG : G.Simple) {s : Survey G} (hq : s.B=B) (he : s.direct=O.direct) (hs : s.X=O.X)
    (q : Quote) (e : ℕ → ℕ → Exchange) : ∃ f : ℕ → ℕ, ∀ v ≥ f, Package s O.T q e v O.l O.γ O.b := by
  have hγ i : s.direct i ≤ O.γ i := by rw [he]; exact O.small _
  exact shared_pin hG O.catalog O.pins e (congr_arg Authorities.kernel hq) hs (O.willing he) (fun i _ => hγ i)






end YM.Progress.Joint
