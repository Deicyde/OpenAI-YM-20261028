import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Period
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Denarii
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Diana
import YM.Progress.CLASSICAL_KIN_RECURSION.Freight
import YM.Progress.CLASSICAL_KIN_RECURSION.Tent
import YM.Push.RELAY_DIFFERENCE.Rolling
/-!
# Follow-through to Rank trial billing and Purchases

Keep readings on named data. `Next/RANK` argument (Screen etc.) with weaker
Ferm terms and the new determinant proof. Adapt even its private helpers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson RG Next.Rank Tapes Value Perch Filter Set Function Marker Glyph Extraction Market Ship Cells Read Price Dock Camp Station Peak Atlas
open scoped Topology BigOperators Classical
section
variable {G : Gauge} {n : Side} {m k p N v : ℕ} {Z : Demand}
variable {C : Family G} {S : Table C.book} {b : ℝ}

section
variable (hi : k ≤ N) {x : Points v}
variable (Y : Course C N p k) (P : (u : ℕ) → Rep G (C.side u p))
variable (D : Era)
variable (B : Fin v→ (standard C).Tag) (t : Fin v→ C.book.Token)
variable (ho : Fit C.path.levels b k x)

theorem v_conditioned (a : Allowed C.path.levels b k) (h : Path_ Y P hi b) (hh : Tally (wheel C.path.levels k) (C.path.levels.clock.hatBeta k) D m)
    (hw : ∀ u, width C.path.levels b k ≤ u → u ≤ middle C.path.levels b k →
      C.path.levels.clock.hatBeta u ∈ Icc (C.path.levels.clock.hatBeta k/2) (C.path.levels.clock.hatBeta k))
    (hp : Instance hi Y P D B t ho m) (hm : v≤ m) (hr : sufficiently C B b x k) :
    Ship.estimate (P (width C.path.levels b k)) Y hi x (invoice B t ho N p) D.coast.e 1 1 (Ship.allowance C.path.levels m k) := by
  let A := C.path.levels
  let l := middle A b k
  let y : l ≤ N := (before A b k).trans hi
  let T := Ship.yard C b hi p
  let M := D.coast
  let s := A.clock.hatBeta k
  let q := A.clock.hatBeta l
  have hc := h l (wider A b k) le_rfl
  have hu := hh.stops _ (hw _ (wider A b k) le_rfl)
  let J := Peak.Meter C.path.levels hc.budget hu
  obtain ⟨α,β,bα,bβ,H,K,W,hK,hb,hP,hW⟩ := hp.1 hc.budget hu
  have ht : Aurora J D.coast.Q Y hi t B ho := by
    refine ⟨α,β,bα,bβ,H,K,W,?_,hK,hb,hP⟩
    refine Peak.warming hu hc.budget hm (fun i => (hW i).2.1) (fun i => (hW i).1) (fun i => (hW i).2.2) (hr ho p N hi)
  have hl := Peak.launched J M.Q Y hi t B ho a hm ht (hc.budget ▸ hu.span) (hc.budget ▸ hu.space)
  apply Perch.covers Y P b x m hi hp.2 a hh hw
  have he : spouse s D (l-l)=J.output := by dsimp only [spouse]; rw [Nat.sub_self,pow_zero,one_mul]; rfl
  apply Perch.follows hl
  · exact he.symm.le
  exact hu.reserve.trans_eq (congr_arg (·*w q) he.symm)
end

variable (O : HaarBudget G) {d : ℕ} (X : Columns C S d)

/-- `Instance` for finitely many requests at comparison window.

Requires true
readout (e.g.

Doesn't stipulate global moment/root estimates.

Quantifiers retain
which lifts at all p. -/
def Factory_ (P : Representatives C X) (b : ℝ) (D : Era) (k : ℕ) :=
    let A := C.path.levels
    C.ref d ≤ k → (∀ i, Fit A b k (X.row i).expected) →
      ∀ᶠ N : ℕ in atTop, ∃ hN : k ≤ N, ∀ p : ℕ,
        ∃ (M : C.label d →ₗ[ℂ] C.label d), Tested C d k N p M ∧
          ∃ (Y : Course C N p k) (R : (u : ℕ) → Rep G (C.side u p)), Path_ Y R hN b ∧
            ∀ v, Names C P (Station.mag A b k) k N p M v → ∀ i (h : Fit A b k (X.row i).expected) j,
              Instance hN Y R D (roles X i j) (Ship.ranksheet X v i j) h 2

def Turning_ (P : Representatives C X) (b : ℝ) (D : ℕ → Era) := ∃ᶠ k : ℕ in atTop,
    let A := C.path.levels
    let era := D (A.clock.J k)
    Charge A b k 2 O era ∧ Factory_ X P b era k


-- eventual allocation from all votes tied path
variable (D : ℕ→ Era) (P : Representatives C X)
theorem v_culminates (b : ℝ) (h : G.Simple) (hb : 0<b) (H : C.Makes) (hV : saves C d+3 ≤ b) (deg : ℕ) (he : s_empire O D X P b deg) :
    Turning_ O X P b D := by
  let Y:= C.path.levels
  have hP := eventually_all.mpr fun i => eventually_all.mpr fun j => pedalling b (uses X P.rep i j) deg _ h H hb hV (generic_conf _ (X.row i).probes)
  refine (he.and_eventually hP).mono ?_
  rintro k ⟨⟨hs,hK⟩,hp⟩
  refine ⟨hs,fun hv hf => (hK hv hf).mono ?_⟩
  rintro N ⟨hn,hN⟩; refine ⟨hn, fun p => ?_⟩
  obtain ⟨Y₀,M,M',c,R,hR,H,W⟩ := hN p
  refine ⟨M',H.span,c,R,hR, fun v H1 i h2 j => ?_⟩
  rw [← actual X P]; obtain ⟨Hx,Hs⟩ := (W i h2).2 v H1 j
  exact ⟨crushed b Y₀ M c R (uses X P.rep i j) deg (hp i j) h2 H _ hn (fun s => H1 _) (W i h2).1 _ _ Hx, Hs⟩
end
variable {G : Gauge} {d N p k : ℕ}
variable {C : Family G} {S : Table C.book} (O : HaarBudget G) {X : Columns C S d} (p' : Representatives C X) (b : ℝ)

def Quota_ (k : ℕ) := C.ref d ≤ k → (∀ i, Fit C.path.levels b k (X.row i).expected) →
    ∀ᶠ N : ℕ in atTop, ∃ hN : k ≤ N, ∀ p : ℕ,
      let A := C.path.levels
      ∃ (read : C.label d→ₗ[ℂ] C.label d), Tested C d k N p read ∧
        ∃ (Y : Course C N p k) (P : Rep G (C.side (width A b k) p)),
          Ferm P Y (((wider A b k).trans (before A b k)).trans hN) ∧
            ∀ v, Names C p' (mag A b k) k N p read v → Bill b X P Y hN v

/-- Over sufficient stations on **this** calendar (See also `Paid`
and sublinear use). -/
def Offers_ : Prop := ∃ᶠ k : ℕ in atTop, Allocated C.path.levels 2 k O b ∧ Quota_ p' b k

include O in
lemma v_pay_all (h : G.Simple) (P : Representatives C X) (b' : ℝ) (hb : 0<b') (D : ℕ → Era)
    (T : Turning_ O X P b' D) : Offers_ O P b' := by
  let A := C.path.levels
  have he := eventually_all.mpr fun i => eventually_all.mpr fun j => cough h hb _ (X.row i).probes (roles X i j)
  refine (T.and_eventually he).mono ?_
  rintro k ⟨⟨ha,hF⟩,hp⟩
  refine ⟨ha.allot,fun h hQ => ?_⟩
  filter_upwards [hF h hQ] with N hn
  obtain ⟨hi,hV⟩ := hn; refine ⟨hi,fun p => ?_⟩
  obtain ⟨M,hM,Y,R,hR,H⟩ := hV p; let m := Station.width A b' k; let l := A.clock.J k
  refine ⟨M,hM,Y,R m,(hR _ le_rfl (wider ..)).chand,fun v hv i hi' j => ?_⟩
  refine ⟨(D l).coast.e,(D l).coast.base, v_conditioned hi Y R (D l) _ _ hi' ha.allot.permitted hR ha.tally ha.assured (H v hv i hi' j) ?_ (hp i j)⟩
  have hp := (X.row i).cap; omega

private lemma sold (a : Levels G) (b : ℝ) (j : ℕ) : ∀ᶠ k in atTop, Allowed a b k → j < width a b k := by
  filter_upwards [a.fits.deep.eventually (eventually_gt_atTop (a.clock.J j))] with k hk hp
  by_contra! he
  exact not_lt_of_ge ((hp.plateau _ le_rfl ((wider a b k).trans (before a b k))) ▸ a.fits.mono he) hk

-- Include lifts explicit even for later usage/ancestry compatibility beyond Purchases scope.

structure Travels_ (Z : X.Trials) : Prop where
  occupied (i : ℕ) : Allocated C.path.levels 2 (Z.depth i) O b
  width (i : ℕ) : Z.width i=Station.width C.path.levels b (Z.depth i)
  testScale (i : ℕ) : Z.scale i=Station.gap C.path.levels b (Z.depth i)
  mark (i j) : Z.mark i j = Station.choose C.path.levels b (Z.depth i) (X.row j).expected
  cost (i : ℕ) : Z.gap i=Ship.budget C.path.levels 2 (Z.depth i)
  fits (i j) : Fit C.path.levels b (Z.depth i) (X.row j).expected
  starts (i : ℕ) : C.ref d ≤ Z.depth i
  name_at (i : ℕ) : ∀ᶠ N in atTop, ∃ hN : Z.depth i≤N, ∀ p,
    let A := C.path.levels; let k := Z.depth i
    ∃ (read : C.label d→ₗ[ℂ] C.label d), Tested C d k N p read ∧ Names C p' (mag A b k) k N p read (Z.lift i N p) ∧
      ∃ (Y : Course C N p k) (P : Rep G (C.side (Station.width A b k) p)),
        Ferm P Y (((wider A b k).trans (before A b k)).trans hN) ∧
          Bill b X P Y hN (Z.lift i N p)

private lemma ticketed (h : C.Makes) (hk : C.ref d≤k) (hc : ∀ i, Fit C.path.levels b k (X.row i).expected)
    (ho : Quota_ p' b k) :
    ∃ x : ℕ → ℕ → Fin (X.dim+1) → C.label d,
      (∃ D : ℝ,∀ N p i, ‖x N p i‖≤D) ∧ (∀ N p,x N p 0=C.refUnit d) ∧ (∀ N p i,star (x N p i)=x N p i) ∧
        ∀ᶠ N : ℕ in atTop, ∃ hN : k ≤ N, ∀ p,
          let A := C.path.levels
          ∃ (read : C.label d→ₗ[ℂ] C.label d), Tested C d k N p read ∧ Names C p' (mag A b k) k N p read (x N p) ∧
            ∃ (Y : Course C N p k) (P : Rep G (C.side (width A b k) p)),
              Ferm P Y (((wider A b k).trans (before A b k)).trans hN) ∧
                Bill b X P Y hN (x N p) := by
  obtain ⟨j,hj⟩ := eventually_atTop.1 (ho hk hc)
  let A := C.path.levels
  have hd : k≤j := (hj j le_rfl).choose
  obtain ⟨C₀,hG⟩:= Price.within C p' (mag A b k) h hk; let D':=max C₀ ‖C.refUnit d‖
  choose w hWp hw hx using fun N p => show ∃ w : Fin (X.dim+1) → C.label d,
    (∀ i,‖w i‖≤ D') ∧ (w 0=C.refUnit d ∧ ∀ i,star (w i)=w i) ∧ ∀ ht : j ≤ N, ∃ read, Tested C d k N p read ∧
      Names C p' (mag A b k) k N p read w ∧ ∃ (Y : Course C N p k) (P : Rep G (C.side (width A b k) p)),
        Ferm P Y (((wider A b k).trans (before A b k)).trans (hd.trans ht)) ∧
          Bill b X P Y (hd.trans ht) w from by
      by_cases ht : j≤N
      · obtain ⟨read,hT,Y,P,hP,hh⟩ := (hj N ht).choose_spec p
        obtain ⟨w,hz,hy,he⟩ := series C p' _ h hk (hd.trans ht) hT
        exact ⟨w,fun i=>(hG N (hd.trans ht) p read hT _ hz i).trans (le_max_left ..),⟨hy,he⟩,fun _ => ⟨read,hT,hz,Y,P,hP,hh _ hz⟩⟩
      exact ⟨fun _ => C.refUnit d, (fun _=> le_max_right ..),⟨rfl,fun _ => C.book.bar_scalar _⟩,fun hh => False.elim (ht hh)⟩
  exact ⟨w,⟨_,hWp⟩,fun N p => (hw N p).1,fun N p => (hw N p).2,(eventually_ge_atTop j).mono fun N h => ⟨hd.trans h,fun p => hx N p h⟩⟩

-- extract useful sequence. keep p' & b & X.

theorem v_obtain_purchases (h : G.Simple) (hc : C.Makes) (hb : 0<b) (he : Offers_ O p' b) : ∃ Z : X.Trials,
    Travels_ O p' b Z ∧ Purchases Z := by
  let A := C.path.levels
  let w := Station.width A b
  let g := Station.gap A b
  let P k := bank O A (w k) ∧ C.ref d ≤ k ∧ Allocated A 2 k O b ∧ Quota_ p' b k ∧ ∀ i,Fit A b k (X.row i).expected
  obtain ⟨r,Hr⟩ := eventually_atTop.mp (banking A O h)
  have hv (i j) (ε : ℝ) (hε : 0<ε) : ∃ k, P k ∧ i < k ∧ j < w k ∧ g k < ε := by
    have hq := (gap_rate A h b).eventually (gt_mem_nhds hε)
    have hf := eventually_all.mpr (fun i => Station.ready h (X.row i).expected (X.row i).probes A hb)
    obtain ⟨k,⟨ha,hB⟩,⟨H₁,⟨H₂,H₃⟩,H₄⟩,H₅⟩ := (he.and_eventually (((sold A b (max r j)).and (((eventually_gt_atTop i).and hq).and hf)).and (eventually_ge_atTop (C.ref d)))).exists
    have H := ha.permitted
    exact ⟨k,⟨Hr _ ((le_max_left ..).trans (H₁ H).le),H₅,ha,hB,fun i => H₄ i H⟩,H₂,(le_max_right r j).trans_lt (H₁ H),H₃⟩
  obtain ⟨i,hi,-⟩ := hv 0 0 1 (by norm_num)
  choose f hf Hf hs K using fun i => hv i (w i) (g i) (gap_pos A b i)
  let U := fun n : ℕ => Nat.rec (motive:=fun _ => ℕ) i (fun _ j => f j) n
  have hU a : P (U a) := by cases a <;> first | exact hi | exact hf _
  let B : Extraction.Sequence := ⟨U,strictMono_nat_of_lt_succ (fun n => Hf (U n))⟩
  let W : Extraction.Sequence := ⟨fun k => w (B k),strictMono_nat_of_lt_succ (fun n => hs (U n))⟩
  choose x hPacu hx he' hT using fun i : ℕ => ticketed p' b hc ((hU i).2.1) ((hU i).2.2.2.2) ((hU i).2.2.2.1)
  let Z : X.Trials := {
    depth := B
    width := W
    window := fun i => ((wider A b (U i)).trans (before ..))
    scale := fun i => g (U i)
    positive := fun i => gap_pos ..
    zoom := (gap_rate A h b).comp B.cofinal
    mark := fun i j => Station.choose A b (U i) (X.row j).expected
    lift := x
    later := fun _ _ => 0
    gap := fun i => Ship.budget A 2 (U i)
    allowed := fun i => (budget_pos ..).le
    small := (diminishes A 2 h (by decide)).comp B.cofinal }
  have ht : Travels_ O p' b Z := ⟨fun i => (hU i).2.2.1,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,
      fun _ => rfl,fun i => (hU i).2.2.2.2,fun i => (hU i).2.1,hT⟩
  refine ⟨Z,ht, ⟨⟨b,hb, ht.testScale⟩,fun i => (ht.occupied i).permitted.plateau,strictAnti_nat_of_succ_lt (fun n => K (U n)),he',hx,hPacu,
    fun i => (tuning A (X.row i).expected h hb).comp B.cofinal, ⟨1/4,by norm_num,fun k i => (ht.fits k i).within⟩,
    fun i j => (ht.fits i j).usable,?_⟩⟩

  intro i
  filter_upwards [ht.name_at i, eventually_all.mpr (fun j => Fit.stencils (ht.fits i j) hc d)] with N hN hX
  obtain ⟨a,L⟩ := hN; refine ⟨a,fun p j z => ?_⟩
  obtain ⟨R,Hr,hw,Y,P,hP,hh⟩ := L p
  obtain ⟨e,hε,hb⟩ := hh j (ht.fits i j) z
  refine ⟨fun u => (hX j).choose_spec p u (Z.lift i N p _),fun q hq => ?_⟩
  exact coupon O (ht.occupied i) (hU i).1 hP _ _ (ht.fits i j) (by have hv := (X.row j).cap; omega) hε le_rfl le_rfl hb q hq
end YM.PhysicalNext.InteractingRank.Soft
