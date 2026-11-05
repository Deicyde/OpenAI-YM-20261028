import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Inlet
import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Parade
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Leases
import YM.Extra.WILSON_STARTUP.Builder
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Letters
import YM.Push.RELAY_DIFFERENCE.Birth
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques
import YM.UVNext.FREE_STRESS_CERTIFICATE.Pressure



/-!
# Book against an actual selected-word and exposure inventory

Number ordered block terms (see `Value.expands`) in the reserved nat-address
space; the numbering can be step/forest/tag specific but carries NO extra
multiplicity. `Seats` asks of the missing factor dictionary simply to make
the two *Z* endpoints of each such selection available in the declared
one viewport. Doesn't supply or replace ANY of its read identities elsewhere.
In applications all such ratios are pure optional exponents, all genuine
loaded Nat slots in this convention numbered (others are blanks). α and β and
other γ suppliers aren't allowed unbounded positive exponential growth (except
the combined core residual with its own checks). Their REAL bound inputs,
e.g., via compulsory row-energy costs and profiled replacements, are separate
from this theorem. No support cost for the letters inferred from `sits`: it is
only a Gaussian-growth currency. Keep every dependence (including failed tests,
all tag/path reads etc.) of the genuine factors.

No exclusion between selections at equal endpoints. Exclusion of identical
optional ADDRESS is by the original `Run.one_copy` on first-subset expansion
(even for its exclusive variants), not by a hypothesis that independent
lists give an occupancy cap nor by deduplicating a paid list. Does NOT buy
repeating this Run arbitrarily many times in the *same integrand* (shouldn't
do ReLog under this Gaussian!!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad
open Function Filter Lattice Wilson RG Precision Pressure Pressure.Stores Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian
open Further.GaussianScalar AnalyticBridge.AnnulusRatioInsertions.Prism AnalyticBridge.AnnulusRatioInsertions.Parade
open Push.SectorMeasure Wisps Schur Spot Spot.Programme Notice
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {d : Desk G S} {u : Spot d}
  {X : Support c} {H R K α β γ : Type} {a : Viewport u X H R K} {D : u.Slices} {b : Finset ℕ}
  {q : Programme D b} {n : q.Run α β γ}

abbrev Serial (I : Type) := I → I → (Σ m, Tracks I m) ↪ ℕ

def address (u : Spot d) (e : Serial u.ActiveKey) (p : Full u.ActiveKey) : u.Log :=
  Sum.inr (.inr (.inr (.inl (.inr (p.map id (fun ⟨zeta,⟨i,j⟩,t⟩ => (i,j,e i j ⟨zeta,t⟩)))))))

lemma address_inj (u : Spot d) (e : Serial u.ActiveKey) : Injective (address u e) := by
  rintro (i|⟨zeta,⟨i,j⟩,t⟩) (k|⟨l,⟨k,r⟩,t'⟩) H <;> simp only [address,Sum.inr.injEq,Sum.inl.injEq,Sum.map_inl,id_eq,Sum.map_inr,reduceCtorEq] at H
  · rw [H]
  · obtain ⟨h,h',h''⟩ := (show i=k ∧ j=r ∧ (e i j) ⟨zeta,t⟩ = (e k r) ⟨l,t'⟩ by simpa only [Prod.mk.injEq] using H)
    subst k; subst r
    rcases Sigma.mk.inj ((e i j).injective h'') with ⟨rfl,hh⟩
    cases eq_of_heq hh; rfl

def project (a : Viewport u X H R K) (p : Position (H⊕R) u.ActiveKey) : Full u.ActiveKey :=
  p.map a.read (fun ⟨zeta,⟨i,j⟩,t⟩ => ⟨zeta,(a.read i,a.read j),t⟩)
lemma project_legs (p : Position (H⊕R) u.ActiveKey) : legs (project a p)=(a.read (legs p).1,a.read (legs p).2) := by
  rcases p with i|⟨zeta,⟨i,j⟩,t⟩ <;> rfl
lemma project_inj : Injective (project a) := by
  rintro (i|⟨zeta,⟨i,j⟩,t⟩) (k|⟨zeta',⟨k,r⟩,t'⟩) H <;> simp [project] at H
  · rw [H]
  rcases H with ⟨rfl,h⟩; simp at h
  rcases h with ⟨⟨rfl,rfl⟩,rfl⟩; rfl

abbrev located (n : q.Run α β γ) (a : Viewport u X H R K) (e : Serial u.ActiveKey) (j : γ) (p : Position (H⊕R) u.ActiveKey) : Prop :=
  n.marks j=address u e (project a p)

/-- PORT (and only structural data here). Every *actual* ratio address
uses the declared numbering (log identity/unused zeros & exact extended reads
required of the actual physical dictionary; see `Terms`). No selection bound
hypothesized in addition to the defining first-subset expansion. `paired`
is a required field of the actual read-support port: if that doesn't expose
these two endpoints with *all* colors in a single read it isn't this port.
-/
structure Seats (a : Viewport u X H R K) (n : q.Run α β γ) where
  number : Serial u.ActiveKey
  optional p : address u number p ∉ q.paying ∧ q.rawLog (address u number p)=none
  paired j p : n.marks j = address u number p → p∈Set.range (project a)

namespace Seats
variable (s : Seats a n)
def tag (j : γ) : Option (Position (H⊕R) u.ActiveKey) := if he : ∃ p, located n a s.number j p then some he.choose else none
lemma tagged {j p} : s.tag j=some p ↔ located n a s.number j p := by
  unfold tag; split
  next he =>
    rw [Option.some_inj]
    exact ⟨fun ht => ht ▸ he.choose_spec,fun h => project_inj (address_inj u s.number (he.choose_spec.symm.trans h))⟩
  next he => exact ⟨fun h => by contradiction,fun h => (he ⟨_,h⟩).elim⟩

lemma marker_inj : Injective n.marks := by
  intro i j h
  apply Sum.inr.inj (α:=β)
  apply Sum.inr.inj (α:=α)
  exact n.one_copy (show Sum.inr (α:=Gates u b) (n.marks i)=Sum.inr (n.marks j) from congr_arg _ h)

variable [Fintype γ]
def big := Finset.univ.filter fun j : γ => ∃ p,s.tag j=some p
def place (j : s.big) : Position (H⊕R) u.ActiveKey := Classical.choose (p:=fun p => s.tag j.val=some p) (Finset.mem_filter.mp j.property).2
lemma place_is (j : s.big) : s.tag j.val=some (s.place j) := Classical.choose_spec (p:=fun p=>s.tag j.val=some p) (Finset.mem_filter.mp j.property).2

def issued (j : s.big) := project a (s.place j)
lemma issued_inj : Injective s.issued := by
  intro i j h; apply Subtype.ext; apply marker_inj
  rw [s.tagged.mp (s.place_is i),s.tagged.mp (s.place_is j)]; exact congr_arg (address _ _) h

def charge (o : Site c) (P : ℕ) (z : s.big) : ℝ := (s.issued z).elim (fun i => grade P o (site i))
   (fun ⟨zeta,⟨i,_⟩,t⟩ => stretch o P (zeta+1) i t)
lemma charge_pos (o : Site c) (P : ℕ) (z : s.big) : 0<s.charge o P z := by
  unfold charge; rcases s.issued z with i|⟨zeta,⟨i,j⟩,t⟩
  · exact grade_pos ..
  exact stretch_pos ..
end Seats

/-- Rents not due to the Z-ratio letters. No send & wait taxes;
require concrete current operand bounds to cover EVERYTHING else. `expose`
= all *distinct physical* trigger carriers requesting credit in this
term; any subset, must show support of events in THAT same law before use.
`yen` can aggregate only `Residues`. External royalty meter/order intended
for any further positive-rank costs, support powers & scores; not claiming
those ancillary suppliers in this procurement. They cannot change watch/hit.
-/
structure Income (α β γ I : Type) where
  expose : Finset I
  gate : α → ℝ
  body : Finset β
  yen : ℝ
  spend : β → ℝ
  wages : γ → ℝ
  royalty : ℝ
  plan : ℕ
  gate_nn i : 0 ≤ gate i
  wages_nn i : 0 ≤ wages i

variable [Fintype H] [Fintype R] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq H] [DecidableEq R]
    [DecidableEq β] [DecidableEq γ] (s : Seats a n) (v : Charges) (M : Income α β γ (H⊕R))

def Seats.stipend (j : γ) := (s.tag j).elim (M.wages j) (fun p => v.pay d.betaHat u.A u.F G (project a p))
def Seats.sits (j : γ) : Finset ((H⊕R) × G.ColorIndex) := (s.tag j).elim ∅ (fun p => {(legs p).1,(legs p).2} ×ˢ Finset.univ)

def motionBill (v : Charges) (a : Viewport u X H R K) (o : Site c) (L : ℝ) (k : ℕ) (i : H×G.ColorIndex) : ℝ :=
  (max 1 ‖d.g⁻¹‖)*((1+‖Notice.term G i.2‖ * L)*rung (l:=a) o i.1 k) +
    (1+‖d.g⁻¹‖*(v.price * fiery G d.betaHat S.patch.L))*grade (d.out.power*k) o (site (a.read (Sum.inl i.1)))

def totalBill (o : Site c) (L : ℝ) (k : ℕ) := 1+|M.royalty|+(∑ j, M.wages j)+
  (∑ j:s.big, s.charge o (d.out.power*k) j) + ∑ j : H×G.ColorIndex, |motionBill v a o L k j|

omit [Fintype R] [Fintype α] [Fintype β] [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] in
lemma totalBill_pays (o : Site c) (L : ℝ) (k : ℕ) :
    let t := totalBill s v M o L k
    1 ≤ t ∧ (∀ j, M.wages j ≤ t) ∧ (∀ j, s.charge o (d.out.power*k) j ≤ t) ∧
      (∀ j : H×G.ColorIndex, motionBill v a o L k j ≤ t) ∧ |M.royalty| ≤ t := by
  intro t
  have hh : 0 ≤ ∑ j,M.wages j := Finset.sum_nonneg fun _ _ => M.wages_nn _
  have he : 0 ≤ ∑ j:s.big,s.charge o (d.out.power*k) j := Finset.sum_nonneg fun _ _ => (s.charge_pos ..).le
  have hx : 0 ≤ ∑ j : H×G.ColorIndex, |motionBill v a o L k j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hw := abs_nonneg M.royalty
  unfold t totalBill
  refine ⟨by linarith,fun j => ?_,fun j => ?_,fun j => ?_,by linarith⟩
  · linarith [Finset.single_le_sum (f:=M.wages) (fun i _=> M.wages_nn i) (Finset.mem_univ j)]
  · linarith [Finset.single_le_sum (f:=s.charge o (d.out.power*k)) (fun i _=> (s.charge_pos ..).le) (Finset.mem_univ j)]
  · linarith [le_abs_self (motionBill v a o L k j),Finset.single_le_sum (f:=fun i=>|motionBill v a o L k i|) (fun i _=> abs_nonneg _) (Finset.mem_univ j)]

-- capacity (=cap) chosen at same step as Charges, not subsequently adjusted.
def hire (o : Site c) (L : ℝ) (k : ℕ) (θ cap : ℝ) : Install (G:=G) α β γ (H⊕R) :=
  ⟨M.gate,M.spend,M.body,M.yen,s.big,s.stipend v M,s.sits,M.expose,anxious G S.patch.L d.betaHat θ d.input.beta,Arc.pinch cap,cap,
    3*totalBill s v M o L k, max 1 M.plan⟩

structure Limits (v : Charges) (P : Patch) (G : Gauge) (cap x : ℝ) : Prop where
  positive : 0 < cap
  paths : v.coin x*v.lifetime P G < 1
  bounded : v.top G P x ≤ 1
  small : 2*v.top G P x + Arc.pinch cap ≤ cap⁻¹/8

lemma offload (v : Charges) (P : Patch) (G : Gauge) {cap : ℝ} (hp : 0<cap) : ∀ᶠ x : ℝ in atTop, Limits v P G cap x := by
  have hh : 0 < min 1 (Arc.pinch cap) := lt_min zero_lt_one (Arc.pinch_pos hp)
  filter_upwards [v.sponsored G P hh] with x hx
  have he : (2:ℝ)*Arc.pinch cap+Arc.pinch cap=cap⁻¹/8 := by unfold Arc.pinch leisure; field_simp; norm_num
  exact ⟨hp,hx.1,hx.2.trans (min_le_left ..),by linarith [hx.2.trans (min_le_right ..)]⟩

namespace Seats
variable {o : Site c} {L θ cap : ℝ} {k : ℕ}

omit [Fintype H] [Fintype R] [Fintype α] [Fintype β] [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] [Fintype γ] in
lemma stipend_nn (j) : 0 ≤ s.stipend v M j := by
  unfold stipend; cases s.tag j
  · exact M.wages_nn _
  exact (v.pay_pos ..).le

omit [Fintype H] [Fintype R] [Fintype α] [Fintype β] [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] in
lemma stipend_big (j : s.big) : s.stipend v M j.val = v.pay d.betaHat u.A u.F G (s.issued j) := by
  unfold stipend issued; rw [s.place_is]; rfl

omit [Fintype H] [Fintype R] [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ] in
lemma sits_big (j : s.big) : s.sits j.val = {(legs (s.place j)).1,(legs (s.place j)).2} ×ˢ Finset.univ := by
  unfold sits; rw [s.place_is]; rfl

variable (h : Limits v S.patch G cap d.betaHat)
include h

omit [Fintype H] [Fintype R] [Fintype α] [Fintype β] [DecidableEq H] [DecidableEq R] [DecidableEq β] [DecidableEq γ] in
lemma stipend_le (j : s.big) : s.stipend v M j.val ≤ 1 := by
  rw [s.stipend_big v M j]; exact (v.pay_alone d.betaHat u.A u.F G rfl h.paths _).trans h.bounded

omit [Fintype R] [Fintype α] [Fintype β] [DecidableEq β] in
/-- All actual Gaussian diagonal debits together, including duplicate
projected locations from all ordered paths. -/
lemma jointly (i : (H⊕R)×G.ColorIndex) :
    let T := hire s v M o L k θ cap
    T.watch i + (∑ j : γ,T.hit j i) ≤ T.capacity⁻¹/8 := by
  intro T
  have he : T.watch i ≤ Arc.pinch cap := by unfold Install.watch; split; exact le_rfl; exact (Arc.pinch_pos h.positive).le
  let z := v.audited d.betaHat u.A u.F G (a.read i.1)
  have hh (j : s.big) : T.hit j.val i ≤ 2*z (s.issued j) := by
    obtain ⟨w,hw⟩ := j
    unfold Install.hit; split
    next ht =>
      have hp : i∈s.sits w := ht.2
      have hq := s.sits_big ⟨w,hw⟩
      rw [show s.sits w=_ from hq] at hp
      obtain hx|hx := Finset.mem_insert.mp (Finset.mem_product.mp hp).1
      all_goals
        try rw [Finset.mem_singleton] at hx
        have hz : v.pay d.betaHat u.A u.F G (s.issued ⟨w,hw⟩)=s.stipend v M w := (s.stipend_big v M ⟨w,hw⟩).symm
        unfold z Charges.audited
        rw [if_pos (show Arc.meets legs (s.issued ⟨w,hw⟩) _ from ?_),hz]; rotate_left
        · unfold Arc.meets issued; rw [project_legs]; rw [hx]; simp
        change s.stipend v M w + (s.stipend v M w)^2 ≤ _
        have h' := s.stipend_nn v M w
        have h₁ := s.stipend_le v M h ⟨w,hw⟩
        dsimp only at h₁; nlinarith
    exact mul_nonneg zero_le_two (v.audited_nn ..)
  have hx : ∑ j,T.hit j i = ∑ j:s.big,T.hit j.val i := by
    rw [Finset.sum_coe_sort s.big (fun j => T.hit j i)]
    exact (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => if_neg (fun h => hj h.1 : (j∈s.big ∧ _) → False)).symm
  apply le_trans _ h.small
  rw [hx]
  calc
    _ ≤ Arc.pinch cap + ∑ j:s.big,2*z (s.issued j) := add_le_add he (Finset.sum_le_sum fun j _=> hh j)
    _ ≤ _ := by
      rw [← Finset.mul_sum,← Finset.sum_image s.issued_inj.injOn, add_comm]; gcongr
      exact v.pay_finite _ _ _ _ rfl h.paths _ _

lemma lease : (hire s v M o L k θ cap).rents.Lease := by
  obtain ⟨hT,hW,-⟩ := totalBill_pays s v M o L k
  refine (hire s v M o L k θ cap).lease M.gate_nn (s.stipend_nn v M) h.positive (by change 1≤3*totalBill ..; linarith) (s.jointly v M h) ?_ (le_max_left ..)
  intro i
  change (if i ∈ s.big then s.stipend v M i ^ 2 else s.stipend v M i) ≤ 3*totalBill s v M o L k
  split
  next hi =>
    have he := s.stipend_nn v M i
    have ht := s.stipend_le v M h ⟨i,hi⟩
    dsimp only at ht; nlinarith
  next hi =>
    rw [big,Finset.mem_filter] at hi
    have : s.tag i=none := by cases he : s.tag i <;> [rfl; exact (hi ⟨Finset.mem_univ _, _,he⟩).elim]
    rw [stipend,this]; change M.wages i ≤ _; linarith [hW i]

omit [Fintype α] [Fintype β] [DecidableEq β] in
lemma enters (hp : 0<d.input.beta) (he : 0<θ) (z : Prices G (H⊕R)) : let T := hire s v M o L k θ cap
    0 < T.threshold ∧ (z∈triggered M.expose T.threshold → T.rents.Event z) ∧
      (M.expose.Nonempty → 0<T.rooted) := by
  intro T
  have hT : 0 < T.threshold := mul_pos he (div_pos d.paidScale (coupling_pos hp))
  have hh : 0 < T.eps := Arc.pinch_pos h.positive
  refine ⟨hT,fun hz=> T.mark_money (fun i hi=>pow_le_pow_left₀ hT.le (hz i hi) _) hh.le, fun hx => ?_⟩
  unfold Install.rooted
  have ht : (0:ℝ) < T.expose.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hx)
  positivity
end Seats
end YM.PhysicalNext.JointLoad
