import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Attic
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.Progress.JOINT_CALENDAR.Issue


/-!
# Earning the energy threshold after subtracting *selected affine squares*

`Peaking`: J.selects Q in annulus of O. H & F shared across
all readings. `stakeBook` uses TF=fine rank τ in Frontal.
Chart at retime. Can capture triggers here in the sector with
the true gaps to meet Fight arithmetic. Needs `annulus_pay` and
actual plot/horizon checks for the windows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Wax
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Paint Filter Finset Precision Tree Next.SectorChange
open Pressure.Tube Pressure.Teller Pressure.Stores YM.Bid Work Push.SectorMeasure
    YM.SectorNext.Remainder MeasureTheory
open _root_.YM.SectorNext.Remainder.Affine
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {w x t C u d : ℝ} {A B : Stores S} {U : Config G f} {Q V : Config G c} {k : S.Choices} {D : ℕ}
-- Change only F rows annotation; all compared rows on the
-- ACTUAL selected generation including curvature masks H before log.
def reread (T : Tube G S) (A : Window S) (u t : ℝ) (U : Config G f) (V : Config G c) (k : S.Choices) :=
    (∑ i∈ A.face,T.workF (till u) U V t (temp u) i) + (∑ i∈ A.noise,T.workI (till u) (S.prediction U k) V (temp u) i) +
      (∑ i∈ A.coarse,(T.workC (till u) V (temp u) i + (T.workL (till u) U (S.prediction U k) V (temp u) i+ T.workD (till u) V (temp u) i))) + ∑ i∈ A.rows, T.workN (till u) V (temp u) i
local notation "q"=>temp u
local notation "ν"=>fiery G u S.patch.L
private lemma rim (h : P.Funds S T) (ho : Wide A B D u w U k V) (H : Window S)
    (hp : H.annulus A B D (radiusB u)) (ht : ν/2 ≤ t) (hu : 0≤ ν)
    (hσ : till u + 1 ≤ radiusB u/50 ∧ ∀ k:ℕ, ν/2*Real.exp (k/P.top.clip.relaxation)<2 → k+1 ≤ radiusB u/50) :
    reread T H u t U V k= H.work T u U k V := by
  have hj (i) (hi:i∈ H.face) : T.workF (till u) U V t q i=T.workF (till u) U V ν q i := by
    have hx (j:Cell f)(ht : separation (S.ratio.parent i.1) (S.ratio.parent j.1) ≤ radiusB u) := (CleanFaces A B D u w U k V ho _ (hp.1 i hi)).1 j ht
    have he:toll U i≤ ν/2 := hx i (by simp)
    have hh:ν/2 ≤ ν:=by linarith only [hu]
    have heΔ (a) (ha : ν/2≤a): PathData.kept T.high a i.1 U := by
      intro j; by_contra! he
      have hi : a*Real.exp (separation i.1 j.1/T.high.relaxation) < toll U j:= he
      obtain ⟨c,d,hf,_⟩:=h.feeds
      have hA:0≤a:=by linarith only [hu,ha]
      have hB:LaneCounts T.up u a T.high (Work.E04.capacity P.top) 1 S.ratio.parent:= by rw [h.high]; exact Work.E04.lanes hf le_rfl hA one_pos (Work.E04.parent_separation _) ⟨hσ.1,fun j hj=> hσ.2 _ (lt_of_le_of_lt (mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le) hj)⟩
      have ht:= (hx j ((hB.dropped U _ _ hi).trans (Nat.div_le_self ..))).trans ha
      exact hi.not_ge (ht.trans (le_mul_of_one_le_right hA (Real.one_le_exp (div_nonneg (by positivity) T.high.radius_pos.le))))
    unfold Tube.workF crown trunk PathData.clipped
    change G.chord (faceValue U i)≤ _ at he
    rw [if_pos (heΔ _ ht),if_pos (heΔ _ hh),if_pos (he.trans ht),if_pos (he.trans hh)]
  unfold reread; unfold Window.work onWindow; rw [Finset.sum_congr (rfl : H.face=H.face) hj]
-- one-component use with any selected windows/directions acknowledged on the same incidence
def depth (T : Tube G S) (O : Stores S) (Q H : Window S) (u t : ℝ) (a : Directions G f) (U : Config G f) (V : Config G c) (k : S.Choices) :=
    stakeBook T O u t U (S.prediction U k) V+(reread T Q u t U V k- H.extract T u k V a)
local notation "R"=> retime x
local notation "Y"=> betaF G x S.patch.L

def Peaking (P : Teller G) (x W m K : ℝ) (L : Side) (n : ℕ) : Prop :=
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S),S.patch.L=L → 100*(1+radiusB (retime x)) ≤ c.val → P.Funds S T →
      ∀ (O A : Stores S) (F : Forest S.ratio) (U : Config G f) (k : S.Choices) (V : Config G c), Owns O A (retime x) → Wide O A n (retime x) W U k V → SliceSet S F U →
       ∀ (Q H : Window S), H.selects Q → Q.annulus O A n (radiusB (retime x)) → ∀ a : Directions G f,
         H.charts U V a K (retime x) → H.written T (retime x) k V a ∧ m*phase (betaF G x L)^2*O.shares ≤ depth T O Q H (retime x) (phase (betaF G x L)) a U V k
lemma spun {b D : ℝ} {L} (h : 0<b) (hs : 0<w) (hp : ∀ᶠ x in atTop, RankMeter P x w b L) (p : ℕ):
    ∀ᶠ x in atTop, Peaking P x w (b/8) D L p:=by
  obtain ⟨W,hW,e,he,hE,hT⟩:=annulus_pay P L w D hs p
  have hv : ∀ᶠ x:ℝ in atTop, e x ≤ b/2 * (fiery G x L)^2:= by
    have h₀:=hE 0; simp only [pow_zero,one_mul] at h₀
    filter_upwards [(Work.E01.betaF_tendsto G L).eventually (eventually_gt_atTop 0),h₀.eventually (ge_mem_nhds (show 0<b/2 by linarith))] with x hx hv
    let r:=betaF G x L; let z:=r; change r*e x ≤ b/2 at hv
    have hh : 0 < r:=hx; have hp : 0 < Real.sqrt r:= Real.sqrt_pos.mpr hx
    let f:= P; have h : (Real.sqrt r)⁻¹ ≤ fiery G x L:= le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
    apply le_of_mul_le_mul_left _ (show 0<r from hx)
    apply hv.trans; have hm:(Real.sqrt r)⁻¹^2 ≤ (fiery G x L)^2 := pow_le_pow_left₀ (inv_nonneg.mpr hp.le) h _; rw [inv_pow, Real.sq_sqrt hh.le] at hm
    calc
      _ = r * (b/2 * r⁻¹) := by field_simp
      _ ≤ r * (b/2*(fiery G x L)^2):= by gcongr
  filter_upwards [tall_limit.eventually hT,hp,crossfade G L,tall_limit.eventually (reserve_lane G L P.top.clip.relaxation P.top.clip.radius_pos),tall_limit.eventually hv] with x ht hP hx hs hf
  intro c f S T hh hu H O A F U k V hO hw hS Q J hj hQ a ha; obtain ⟨x',hZ,hY⟩:= ht S T hh hu H O A F U k V hS hw
  obtain ⟨htZ,hR⟩:= (hY Q J hj hQ).2.2.2 a ha
  have h':=localOwner hO hw
  have hpZ := hP c f S hh hu T H F O U k V hS h'
  unfold depth
  subst L; obtain ⟨hX,hU,h0,hD⟩:=hx; rw [rim H hw Q hQ h0 hU.le hs]
  have ht':b/8*phase (betaF G x S.patch.L)^2*(O.shares:ℝ) ≤ b/8*(4*(fiery G (retime x) S.patch.L)^2)*O.shares:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hX.le hD 2).trans_eq (by ring)) (by linarith)) (by positivity) -- Λ late
  refine ⟨htZ,le_trans ht' ?_⟩; linarith only [mul_le_mul_of_nonneg_right hf (show 0 ≤ (O.shares:ℝ) by positivity),hpZ,hR]

theorem preheat (P : Teller G) : ∃ n : ℕ,∀ L : Side,n ≤ L.val →∀ᶠ W in atTop,∃ m : ℝ, 0<m∧∀ K : ℝ,∀ D : ℕ,∀ᶠ x in atTop, Peaking P x W m K L D:= by
  obtain ⟨n,h⟩:=chamber P; refine ⟨n,fun L hl=>?_⟩; filter_upwards [h L hl,eventually_gt_atTop 0] with W hw he; obtain ⟨m,hm,h⟩:=hw; exact ⟨m/8,by positivity,fun K D=> spun (D:=K) hm he h D⟩
end YM.PhysicalNext.InteractingRank.Wax
