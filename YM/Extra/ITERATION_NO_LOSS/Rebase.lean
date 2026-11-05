import YM.Bid.Craft
import YM.Next.EXTRACTION.Tails
import YM.Work.B06

/-!
# Avoiding a circular strip choice between pinning and the path widths

Roll back **only for applying** `Bid.pinning`. This is possible for these
Horizon/Rack types because the only Clip parameter in their flat statements
is `.direct`. K chosen on a possibly cheaper provisional sheet. No such
claim about any beta-recursion predicates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG RG.Supply Precision Tree Bloch Bid Craft
open scoped Topology BigOperators
variable {G : Gauge}

structure Upgrade (P Q : Sheet G) : Prop where
  kernel : Q.kernel = P.kernel
  direct j : (Q.profile j).clip.direct = (P.profile j).clip.direct
  widths j : (Q.profile j).width ≤ (P.profile j).width
  paths j : (P.profile j).paths ≤ (Q.profile j).paths
  columns j : (P.profile j).columns ≤ (Q.profile j).columns
  drift j : (P.profile j).drift ≤ (Q.profile j).drift
  radius j : (P.profile j).clip.relaxation ≤ (Q.profile j).clip.relaxation
  exponent j : (P.profile j).supportExponent ≤ (Q.profile j).supportExponent

lemma floor_clip {B : Bed} {p q : Clip} {n : Side} {u v : ℝ} (h : Floor B p n u v) (he : q.direct = p.direct) : Floor B q n u v := by
  refine { h with roots := ?_ }; simpa [Bed.full,he] using h.roots

lemma roll_clip {c f : Side} {S : StepData c f} {H H' : Bed} {T : Towers S.patch.L} {p q v w : Clip}
    (hr : Towers.Roll S H H' T p q) (hv : v.direct=p.direct) (hw : w.direct=q.direct) : Towers.Roll S H H' T v w where
  m := hr.m
  n := by simpa only [Bed.full,hw] using hr.n
  fPart := by simpa only [Bed.full,hw,hv] using hr.fPart
  nPart := by simpa only [Bed.full,hw] using hr.nPart
  oPart := by simpa only [Bed.full,hw] using hr.oPart
  orthogonal := by simpa only [Bed.full,hv] using hr.orthogonal

namespace Upgrade
variable {P Q : Sheet G} (h : Upgrade P Q) {a : Levels G} (hk : a.clock.stage=Q.profile)

def reset (a : Levels G) (P : Sheet G) : Calendar G := { a.clock with stage := P.profile }

def cheap : Levels G := { a with
  clock := reset a P
  fits := { a.fits with
    deepOrder := P.orders.comp a.fits.mono
    deepPower := P.powers.comp a.fits.mono
    deepExp := P.prices.comp a.fits.mono
    driftSmall m := by
      have h0 : 0 ≤ Real.log (a.S.block m).val := Real.log_nonneg (by exact_mod_cast (show 1 ≤ (a.S.block m).val from (a.S.block m).pos))
      refine le_trans ?_ (a.fits.driftSmall m)
      exact div_le_div_of_nonneg_right (by unfold Calendar.params reset; rw [hk]; exact h.drift _) h0
    logCost m := by
      have h0 : 0 ≤ Real.log (a.S.block m).val := Real.log_nonneg (by exact_mod_cast (show 1 ≤ (a.S.block m).val from (a.S.block m).pos))
      refine le_trans ?_ (a.fits.logCost m)
      let j := a.clock.J (m+1); let p := P.profile j
      change Real.log (1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent)/_ ≤ Real.log _/_
      apply div_le_div_of_nonneg_right _ h0
      unfold Calendar.params; rw [hk]
      have hp := p.paths_pos; have hσ := p.width_pos; have hc := p.columns_ge; have hr := p.clip.radius_pos; have he := p.price_pos
      apply Real.log_le_log (by positivity)
      have hi := inv_anti₀ (Q.profile j).width_pos (h.widths j)
      change 1+(P.profile j).paths+_+_+_+_ ≤ 1+(Q.profile j).paths+_+_+_+_
      dsimp only [p]; linarith only [hi,h.paths j,h.columns j,h.radius j,h.exponent j] }
  blocks m p := { a.blocks m p with branches := (a.blocks m p).branches } }

def back (C : Horizon a) : Horizon (h.cheap hk) := ⟨C.H,C.towers⟩
def forth (C : Horizon (h.cheap hk)) : Horizon a := ⟨C.H,C.towers⟩
lemma back_rack {C : Horizon a} {X : MapPrices} (r : Rack a X C) : Rack (h.cheap hk) X (h.back hk C) where
  covers := r.covers
  oath := r.oath
  top := r.top
  legs := r.legs
  crosses := r.crosses
  creak := r.creak
  traces N i hi n := floor_clip (r.traces N i hi n) (by
    change (P.profile _).clip.direct=(a.params i).clip.direct; unfold Levels.params Calendar.params; rw [hk]; exact (h.direct _).symm)

lemma forth_plan {C : Horizon (h.cheap hk)} {K : MapPrices} (r : C.Suffices K) : (h.forth hk C).Suffices K where
  rows := r.rows
  all N i hi n := floor_clip (r.all N i hi n) (by
    change (a.params i).clip.direct = (P.profile _).clip.direct; unfold Levels.params Calendar.params; rw [hk]; exact h.direct _)
  costs := r.costs
  crossings := r.crossings
  stack N m p hm := roll_clip (S:=a.clock.op m p) (r.stack N m p hm) (by
    change (a.params _).clip.direct = (P.profile _).clip.direct; unfold Levels.params Calendar.params; rw [hk]; exact h.direct _) (by
    change (a.params _).clip.direct = (P.profile _).clip.direct; unfold Levels.params Calendar.params; rw [hk]; exact h.direct _)
  top := r.top
include h in
lemma floor_change (n : ℕ → ℕ) : Upgrade P {Q with floorL := n} := { h with kernel := h.kernel }
end Upgrade


end YM.Extra.Iteration
