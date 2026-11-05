import YM.WilsonBulk.Cash.Atomic
import YM.WilsonBulk.Recast.Legacy

/-!
# Price of carrying Qi rank after projection. Consequence: no hidden
   multiply by stage-ages on unchanged μ-flow. All moment assumptions discrete via Θ.

Projection for rank2 ONLY at every coupling reexpression; uses `subdue` FULL
revenue coefficients computed from unmasked pressure before normalization. Reset
lift exactly on Beard.Q summit with tested ∆ in κ moment plaque. No claim that the
remaining multipliers define renormalizable series in analytic norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Parapet
open Function Filter Equiv Finset Lattice Pert.Bulk Laurent Bloch Matrix Work.F08
open Exterior Precision Stationary Audience Wilson RG Sheet Atelier FreeResolvent Recall PowerSeries
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {P : Patch} {K : KernelChoices} {n k e E d i : ℕ} {σ θ μ η ζ x A M q y c p T δ : ℝ}
variable {J : ChartRatio G} {F : Model P K} {l : G.ColorIndex} {B Q B' Q' : Bed} {I I' : Library G}

-- unadjusted pressure-temperature after reexpression. extract e term explicit
abbrev tax (i : G.ColorIndex) (V : Library G) := pencil (missed i V) (recover (missed i V))
def cutReset (i : G.ColorIndex) (V : Library G) (e n : ℕ) := ∑ j∈(range e).erase 0,tax i V e n j • V j n
def patchReset (i : G.ColorIndex) (V : Library G) (e n : ℕ) := V e n + cutReset i V e n
lemma running_pole (h : constantCoeff (revenue l I)=1) (he : 0 < e) (n : ℕ) : resetI l I e n=patchReset l I e n + tax l I e n 0 • I 0 n:= by unfold resetI reorder patchReset cutReset; rw [sum_range_succ,pencil_hero e _ (poll_rule h).1 (crown (poll_rule h).1),one_smul, add_comm _ (I e n), add_assoc]; unfold tax; rw [Finset.sum_erase_add (range e) _ (mem_range.mpr he)]
lemma smooth_patch (hI : Pamphlet I) (l : G.ColorIndex) (e n) : Public (patchReset l I e n) := (hI _ _).plus (Public.gather _ fun i _=> (hI i _).scale _)
lemma rate_reset (ht : Crest I Q) (hg : subdue l (summit G Q 0 2)=1) (he : 0 < e) (hr : n≠2) : resetI l I e n=patchReset l I e n := by rw [running_pole (revenue_anchor l ht hg) he n,ht,summit, usher_else _ _ _ _ _ (Or.inl hr.symm), smul_zero,add_zero]
lemma rate_quad (hI : Whisper I) (ht : Crest I Q) (hg : subdue l (summit G Q 0 2)=1) (he : 0 < e) : resetI l I e 2= patchReset l I e 2 - subdue l (patchReset l I e 2) • onTop G Q := by
  let r:=tax l I e 2 0; let v:=patchReset l I e 2; have hp:= revenue_anchor l ht hg; have h := running_pole hp he 2
  have hs : subdue l (resetI l I e 2)=0:= by rw [← earnings l, (Healthy.after l hI ht hg).shared, coeff_one,if_neg (by omega)]
  have hv : subdue l v+r=0 := by
    rw [h,subdue_plus ((hI.palm 0 2).scale _) (smooth_patch hI.palm l e 2),subdue_pay, ht, hg,mul_one] at hs; exact hs
  rw [h,ht, show summit G Q 0 2=_ from usher_at 2 0 _, show tax l I e 2 0= -subdue l v from by unfold r at *; linarith, neg_smul, ← sub_eq_add_neg]
-- charge hot terms
lemma quote_smul {c' : Type} {D : Rule c'} {T S : Page c' n} (h : Reel δ p x y) (he : Options D σ δ A T S) : Options D σ δ (2*(p*A)) (x • T) (y • S) := by -- c' p
  have hp (b c : ℝ) (g : 0≤c) (hc : b≤c) : b ≤ 2*c := hc.trans (le_mul_of_one_le_left g one_le_two)
  have hb:= he.baseline
  refine ⟨h.radiusM,(he.plus.scale _).mono le_rfl (hp _ _ (mul_nonneg h.nonneg hb) ?h1),(he.minus.scale _).mono le_rfl (hp _ _ (mul_nonneg h.nonneg hb) ?h2),?_⟩
  rotate_right 1
  · rw [show x • T-y • S=(x-y) • S+x • (T-S) from by rw [smul_sub,sub_smul]; abel]
    refine ((he.minus.scale _).add (he.variation.scale _)).mono le_rfl ?_; rw [show δ*(2*(p*A))=(δ*p)*A+p*(δ*A) from by ring]; exact add_le_add (mul_le_mul_of_nonneg_right h.movement hb) (mul_le_mul_of_nonneg_right h.cost (mul_nonneg he.nonneg hb))
  · exact mul_le_mul_of_nonneg_right h.cost hb
  exact mul_le_mul_of_nonneg_right h.due hb

-- needs earlier Ω orders < e

def newMoney (e n : ℕ) (A : ℝ) (i : ℕ) := Album.purse e (Album.port e (pollCost e (A*A)) i) (Album.port e (inverseCost e (pollCost e (A*A))) n)
def newOrder (e n : ℕ) (A : ℝ) := ∑ i∈(range e).erase 0, 2*(newMoney e n A i*A)
lemma price_order (e n : ℕ) : Tariff (newOrder e n) := by
  let p x:=pollCost e (x*x); have hp : Tariff p := tariff_poller e (Tariff.one.prod Tariff.one)
  have h i : Tariff (fun x=>newMoney e n x i) := large_pow (orbit_tariff e i hp) (orbit_tariff e n (tariff_inv e hp)) _
  exact Tariff.gather _ (fun i _=>(Tariff.const (2:ℝ) (by norm_num)).prod ((h i).prod Tariff.one))
lemma currency (ha : constantCoeff (revenue l I)=1) (hb : constantCoeff (revenue l I')=1)
    (hA : Album e δ (A*A) (revenue l I) (revenue l I')) (h : ∀ i:ℕ,0 < i→ i < e → Options (lawn _) σ δ A (I i n) (I' i n)) :
    Options (lawn _) σ δ (newOrder e n A) (cutReset l I e n) (cutReset l I' e n) := by
  let g:=missed l I; have hp:=pollAlbum _ hA ha hb; have hq:= albumInverse hp (poll_rule ha).1 (poll_rule hb).1
  refine Options.gather _ (fun i hi=> ?_) hA.radiusM; obtain ⟨hu,hv⟩:= mem_erase.mp hi; rw [mem_range] at hv; exact quote_smul (Quote_pencil _ _ _ _ (by omega : e-i<e) hp hq) (h _ (by omega) hv)

-- projector stability

def reflector (σ p : ℝ) := 1+momentWeight σ 2*p
lemma reflector_large (hs : 0≤σ) (hp : 0≤p) : 1 ≤ reflector σ p:= le_add_of_nonneg_right (mul_nonneg (momentWeight_nonneg hs 2) hp)
lemma mirror_cost {V U : Text (Cloth G) 2} (hv : Within (lawn _) σ x V) (hu : Within (lawn _) σ y U) (hs : 0<σ) (k : G.ColorIndex) : Within (lawn _) σ (reflector σ y*x) (V-subdue k V • U) := by
  apply (hv.sub (hu.scale _)).mono le_rfl; rw [reflector,show (1+_)*x=x+((momentWeight σ 2)*x)*y by ring]; gcongr; exact hu.1; exact subdue_price _ hv hs -- gcongr
lemma mirror_difference {V U Y Z : Text (Cloth G) 2} (hu : Within (lawn _) σ y U) (he : Within (lawn _) σ x (V-U)) (hv : Within (lawn _) σ p Y) (h : Within (lawn _) σ q (Y-Z)) (hU : Public U) (hV : Public V) (hs : 0<σ) (k : G.ColorIndex) :
    Within (lawn _) σ (reflector σ p*x + momentWeight σ 2*y*q) ((V-subdue k V • Y)-(U-subdue k U • Z)) := by
  rw [show V-_-(U-_)= ((V-U)-subdue k (V-U) • Y)-(subdue k U • (Y-Z)) from by rw [subdue_minus hU hV, sub_smul,smul_sub]; abel]
  refine ((mirror_cost he hv hs k).sub (h.scale _)).mono le_rfl (add_le_add_right ?_ _); gcongr; exact h.1; exact subdue_price _ hu hs
end Parapet
end YM.WilsonBulk
