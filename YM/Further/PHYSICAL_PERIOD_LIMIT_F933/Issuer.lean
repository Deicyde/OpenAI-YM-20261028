import YM.Extra.ITERATION_NO_LOSS.Mechanism
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.World

/-!
# Issuing from aligned boundary choice (paths versus sum convention)

Could transmit R. at the actual boundary directly: no reason to supply
Rates.initial on arbitrary unaligned top and hope to return to the custom
path later, or fit Γ's after that change (and then to a path covector
which might have been billed under older U,Λ). In fact T.Ticket is
literally unobtainable on Design.top (test `foreignTop`). However the
existing mathematics of the precursor bids here *do not* need that exact
enumeration (only Attached+charged); use in application. Keep also new
Ticket-shaped receipts we DO establish for this F for future uses (Note:
Continuity/Program, W etc not bought!). Topological billing of zero-coef
labels in subsequent sector methods must still use the literal f
from our conclusion, period etc unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Issuer
open Function Filter Lattice Wilson RG Supply Precision Exterior Pressure Tree Bloch Bid Craft Input Extra.Iteration
  Extra.Iteration.Calibration Extra.Iteration.Inherited WilsonStartup
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical WilsonStartup
variable {G : Gauge} {S : Sheet G} {D : Rolls S} {Θ : Protection D} {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {M : Horizon a} {K : MapPrices} {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts}
    {Q : PostCost D} {O : ChartRatio G} (hc : Before S U A H K) (hw : Warm H W) (hp : Paid I a) (hm : M.Suffices K)
    (hg : GapQuote D K Q) (hO : LocalRatio O) (hB : ∀ N m : ℕ, m ≤ N → ∀ p, Sworn (M.H N m) (a.S.side m p) G)
    (hT : ∀ N m : ℕ, m < N → Harmonic (M.towers N m))



/-- L concurrency order: bulk top reserves in pre-L list. Cubic and loop are even zero here.
Does NOT replace path rows/genuine scalar evaluation by shortest path approximation.
-/
structure Coffers (S : Supply.Sheet G) (R : ClassicalCosts) : Prop where
  credits (J : ℕ) : Charged (Design.top G (S.profile J).clip).cubic (S.profile J).width (R.top J) ∧
    Charged (Design.top G (S.profile J).clip).quartic (S.profile J).width (R.top J)



/-- Exact ancestry and chronological caps. Includes the position *if below top* (e.g. future use in
Rates stage-specific computation), and verifies top shape rather than require
unobtainable correspondence. -/
structure Marking (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (N m : ℕ) (T : PathData G) : Prop where
  stamp : Attached (M.H N m) T
  funded : T.Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m)
  cipher : m<N → Aligned T (M.H N m)
  finished : m=N → T = Design.top G (a.params m).clip
  cube : Charged T.cubic (a.params m).width (A.cap U K (a.clock.J m))
  quartic : Charged T.quartic (a.params m).width (A.cap U K (a.clock.J m))



-- optional reachability invariant needed for new analytical rate forecasts. Only on the actual data for unmasked path
abbrev Passport (_a : Levels G) := ℕ → ℕ → PathData G → Prop

/-- Outstanding RLoops analytical problems. Version from a single
optimized Preis. Unlike original Estimates (and Rates) insist SAME response α,slope and
 **invariant continuation** of path forecast after the correction in χ.
Therefore there isn't a circular call to full assembled YU. If true
uniformly on all Marking, can just use erasure invariant. Using Stamp
without Invariant induces hypotheses potentially stronger (e.g arbitrary
T at input with same paid powers and mass incl quartic but with past route
not optimal remnant powers). We provide the version with client
chosen invariants - those too cannot anticipate changes after calling
extraction. This still should be scrutinized by campaign (whether the implementation
 preserving laws keeps demand at precommitment, especially determinant which must
 fit ALL orders). Does NOT assert solvability. -/
structure Sensors (M : Horizon a) (K : MapPrices) (U : Apertures) (A : ClassicalCosts) (H : QuantumCosts) (Q : PostCost D) (O : ChartRatio G) (X : Passport a) : Prop where
  start N : X N N (Design.top G (a.params N).clip)
  readout (N m : ℕ) (T : PathData G) (ρ : Branch a m) : m<N → Marking M K U A N (m+1) T → OnShell M Q N m T ρ → X N (m+1) T →
    let i := a.clock.J (m+1)
    let j := a.clock.J m
    let r := A.cap U K i
    let L := a.S.block m
    let b := A.fresh i j
    ∃ e d, ∃ (α : ℝ), ∃ l, SymmetricAtoms e ∧ SymmetricAtoms d ∧ SymmetricAtoms l ∧ Silent l ∧
      Charged e (a.params m).width (rem3 b r L) ∧ Charged d (a.params m).width (rem4 b r r L) ∧
      Charged l (a.params m).width (H.det i j*(L.val:ℝ)^4) ∧
      |α + G.slopeConstant * Real.log L.val| ≤ H.slope i j ∧
      (∀ p, ∃ F c, Fresh (S:=a.clock.op m p) F c T
        (bundle (M.H N m) (join e (inherit M N m T.cubic)) (join d (inherit M N m T.quartic)) T.loop)
          (a.params (m+1)).clip (a.params m).clip (ρ p F) e d) ∧
      (∀ p, ∃ F c, FreshDet (S:=a.clock.op m p) F c T (bundle (M.H N m) T.cubic T.quartic l)
        (a.params (m+1)).clip (a.params m).clip (ρ p F) O α (Q.Γ i) (Q.c i)) ∧
      X N m (glue M N m T e d l)

section resumeSeed
variable {N m : ℕ} {F : Horizon a} (T : World.Tour a M F) (hS : Coffers S A) {X : Passport a} (H₀ : Sensors M K U A H Q O X)
local notation "j" => (a.clock.J (m+1))
local notation "k" => (a.clock.J m)
local notation "L" => (a.S.block m)
local notation "η" => U.clear K j k
local notation "σ" => Stage.width (a.params (m+1))

include T hS hp
lemma summitt (hs : ∀ i, WilsonStartup.Design.Suitable G (a.params i)) (n : ℕ) :
    Marking M K U A n n (Design.top G (a.params n).clip) := by
  let i := a.clock.J n
  have he : a.params n=S.profile i := congr_fun hp.stage _
  obtain ⟨h₁,h₂⟩ := he ▸ hS.credits i -- direction?
  refine {
    stamp := T.peak n ▸ Design.attached _
    funded := Design.layout_ready (hs n)
    cipher := fun e => (lt_irrefl _ e).elim
    finished := fun _ => rfl
    cube := h₁.mono le_rfl ?_
    quartic := h₂.mono le_rfl ?_ }
  all_goals
    unfold ClassicalCosts.cap ClassicalCosts.price
    apply le_trans (le_trans (le_max_right ..) (le_max_left ..))
    apply le_mul_of_one_le_left (le_trans one_pos.le (le_trans (le_max_left ..) (le_max_left ..))) (by norm_num)

omit T hS
variable {T : PathData G} (u : m < N) (P : Marking M K U A N (m+1) T)
include hc hm u P
lemma honors : Ticket M K U A N (m+1) (bundle (M.H N (m+1)) T.cubic T.quartic T.loop) :=
    make_ticket hc hm hp.stage _ _ u _ rfl (fun _ => (P.funded.invariant _).1) (fun _ => (P.funded.invariant _).2.1)
      (fun _ => (P.funded.invariant _).2.2) ((silent_of_bounds (W:=T) P.funded)) P.funded.two P.cube P.quartic

include hw hO hT hB hg H₀
lemma customStep (hT' : X N (m+1) T) : ∃ (R : PathData G) (ρ : Branch a m) (α : ℝ), Move M K U A Q O N m T R ρ α ∧ X N m R := by
  have H (p : ℕ) := hg.serves a M N m p (a.clock.J (m+1)) rfl (block_eq hp m).symm hp.kernel
    (larger hw hp m p) u hm (hB N (m+1) u p) T _ _ _ P.funded P.stamp
  choose ρ ht using fun p F => (H p F).2
  have hρ : OnShell M Q N m T ρ := ⟨fun p F => (H p F).1,fun p F => (ht p F).1,fun p F => (ht p F).2.1,fun p F => (ht p F).2.2⟩
  obtain ⟨e,d,α,l,hse,hsd,hsl,hzl,h1,h2,h3,hα,hJu,hJl,hχ⟩ := H₀.readout N m T ρ u P hρ hT'
  let R := glue M N m T e d l
  have ht' : Ticket M K U A N m R := resume hc hw hp hm hT u (honors hc hp hm u P) hse hsd hsl hzl h1 h2 h3
  have hv := provision hc hm hp N m u
  have hJ : 1 ≤ j-2 := by have := a.clock.adm (m+1); omega
  have he := U.clear_pos K j k
  have hs := (a.params (m+1)).width_pos
  have hx := (a.params m).width_pos
  have hfit : η ≤ σ*(L).val := hv.early.fit.trans (by gcongr; linarith)
  have hC := (classical_price hJ he hv.high hv.low hv.tower P.cube (by decide) hfit).mono hv.width le_rfl
  have hD := (classical_price hJ he hv.high hv.low hv.tower P.quartic (by decide) hfit).mono hv.width le_rfl
  have hL := (loop_price hJ he hv.high hv.low hv.tower P.funded.two hv.early.fit).mono hv.width le_rfl
  have Hu (p F) : ClassicalMatch (S:=a.clock.op m p) F (a.params (m+1)).clip (a.params m).clip T R (ρ p F) := by
    obtain ⟨H,e0,hH⟩ := hJu p
    let S := a.clock.op m p
    refine all_forests (larger hw hp m p) hO (hρ.critical p H) (hρ.critical p F) P.funded ht'.funded (Q.price _) (hρ.gap _ H) (hρ.gap _ F) e0 (fun g hu => ?_)
    by_cases hi : g ≤ 2
    · exact lower (M.H N (m+1)) (M.H N m) (larger hw hp m p) P.funded ht'.funded (hm.all N _ u _)
        (hm.all N _ u.le _) P.stamp ht'.rooted.attached (hB N (m+1) u p) (hB N m u.le p) (hρ.critical p H) (hρ.quadratic p H) e0 g hi
    have hv' := classical_match (S:=S) hJ he hv.high hv.low hv.tower (K.eta_pos _) (a.blocks m p).branches
      (hm.all N _ u _) (hB N (m+1) u p) (hm.crossings N m p u) P.cube (by decide) hfit (hρ.critical p H) (hρ.guessed p H) 3 le_rfl
    have hy := classical_match (S:=S) hJ he hv.high hv.low hv.tower (K.eta_pos _) (a.blocks m p).branches
      (hm.all N _ u _) (hB N (m+1) u p) (hm.crossings N m p u) P.quartic (by decide) hfit (hρ.critical p H) (hρ.guessed p H) 4 le_rfl
    exact higher T R ht'.funded rfl rfl h1 hC h2 hD (hρ.critical p H) ⟨hH.three,hH.four⟩ hv' hy g (by omega) hu
  refine ⟨R,ρ,α,⟨ht',hρ,?_,Hu, (fun p F => ?_)⟩,hχ⟩
  · unfold Levels.params Calendar.params; rw [hp.stage]; exact (add_le_add_left hα _).trans (hc.drift _ _ (a.fits.mono (Nat.le_succ m)) (a.fits.stepSlow m))
  obtain ⟨F0,e0,hH⟩ := hJl p
  let S := a.clock.op m p
  have hy := loop_match (S:=S) hJ he hv.high hv.low hv.tower (K.eta_pos _) (a.blocks m p).branches
    (hm.all N _ u _) (hB N (m+1) u p) (hm.crossings N m p u) P.funded.two (silent_of_bounds P.funded) hv.early.fit (hρ.critical p F0) (hρ.guessed p F0) 2 le_rfl
  have hb := determinant_price T (Q.price j) (hρ.gap _ F0) (hρ.critical _ F0) e0 hO (M.H N m) _ _ _ _ ht'.funded h3 hL (Q.pos j).le (cap_loop_ge (a:=a) (m+1)) hH hy
  exact (transplant (a.blocks m p).branches (larger hw hp m p) hO (hρ.critical p F0) (hρ.critical p F) P.funded ht'.funded (Q.price j)
    (hρ.gap p F0) (hρ.gap p F) e0 hb (fun u hu => Hu p F0 u hu e0)).1
end resumeSeed

section walk
variable {F : Horizon a} (T : World.Tour a M F) (hS : Coffers S A) {X : Passport a} (H₀ : Sensors M K U A H Q O X)
variable (h₁ : ∀ i,Design.Suitable G (a.params i))
include T H₀ hp hc hm hB hO h₁ hT hS hw hg
lemma descent {n i : ℕ} (h : i ≤ n) : ∃ (F : ℕ → PathData G) (b : ℕ → ℝ) (ρ : ∀ m, Branch a m),
    (F n=Design.top G (a.params n).clip ∧ Marking M K U A n n (F n) ∧ X n n (F n)) ∧
    ∀ m : ℕ, i ≤ m → m < n → Move M K U A Q O n m (F (m+1)) (F m) (ρ m) (b m) ∧ X n m (F m) := by
  classical
  induction h using Nat.decreasingInduction with
  | self =>
    exact ⟨fun _ => _, fun _ => 0,fun _ _ _ => 0,⟨rfl,summitt hp T hS h₁ n,H₀.start n⟩,fun m hm he => False.elim (hm.not_gt he)⟩
  | of_succ i hi IH =>
    obtain ⟨F,b,ρ,⟨h0,h₂,h₃⟩,hh⟩ := IH
    have ht : Marking M K U A n (i+1) (F (i+1)) ∧ X n (i+1) (F (i+1)) := by
      rcases (show i+1 ≤ n from hi).eq_or_lt with h|h
      · rw [h]; exact ⟨h₂,h₃⟩
      obtain ⟨hm,hw⟩ := hh _ le_rfl h
      exact ⟨⟨hm.ticket.rooted.attached,hm.ticket.funded,fun _=>hm.ticket.rooted,fun e => (lt_irrefl _ (e ▸ h)).elim,
        hm.ticket.cube,hm.ticket.quartic⟩,hw⟩
    obtain ⟨U',t,α,H,hU⟩ := customStep hc hw hp hm hg hO hB hT H₀ hi ht.1 ht.2
    refine ⟨update F i U', update b i α, update ρ i t, ?_,fun m he hl => ?_⟩
    · rw [update_of_ne hi.ne']; exact ⟨h0,h₂,h₃⟩
    rcases he.eq_or_lt with hv|hv
    · subst m; simpa only [update_self,update_of_ne (Nat.lt_succ_self i).ne'] using (And.intro H hU)
    simp only [update_of_ne hv.ne', update_of_ne (hv.trans (Nat.lt_succ_self m)).ne']; exact hh m hv hl

theorem expedition : ∃ Z : Kin M O, Z.Planned Q ∧ ∀ N m, m ≤ N → Marking M K U A N m (Z.path N m) ∧ X N m (Z.path N m) := by
  choose F b ρ hb ht using fun n => descent hc hw hp hm hg hO hB hT T hS H₀ h₁ (Nat.zero_le n)
  have hx (n m : ℕ) (hm : m ≤ n) : Marking M K U A n m (F n m) ∧ X n m (F n m) := by
    rcases hm.eq_or_lt with h|h
    · subst m; exact (hb n).2
    obtain ⟨P,he⟩ := ht n _ (Nat.zero_le _) h
    exact ⟨⟨P.ticket.rooted.attached,P.ticket.funded,fun _ => P.ticket.rooted,fun e => (lt_irrefl _ (e ▸ h)).elim,P.ticket.cube,P.ticket.quartic⟩,he⟩
  have hl (n m) (hm : m<n) := ht n m (Nat.zero_le _) hm |>.1
  refine ⟨⟨b,F,ρ⟩,
    { stage := hp.stage.symm
      lengths := hp.lengths.symm
      links := fun N m h => (hx N m h).1.stamp
      cap := fun N m h => (hx N m h).1.funded
      peak := fun N => ?_
      initial := fun N => ?_
      gap := fun n m p hm => (hl n m hm).shell.gap p
      critical := fun n m p hm F => ⟨(hl n m hm).shell.critical p F,(hl n m hm).shell.guessed p F⟩
      classicalPart := fun n m p hm => (hl n m hm).classicalPart p
      kinetic := fun n m hm => (hl n m hm).kinetic
      retains := fun n m p hm => (hl n m hm).thermal p }, hx⟩
  · dsimp only; rw [(hb N).1]; intro; apply Design.peak _ (h₁ N).direct
  dsimp only; rw [(hb N).1]; intro; rfl
end walk
end YM.Further.PhysicalPeriodLimitF933.Issuer
