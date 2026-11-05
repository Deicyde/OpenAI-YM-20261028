import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Hour
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Necklace
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Pairing
/-!
# Equality of the configurations for guard expenditure

Not an equivalence of Gaussians. Use the Cab analytics when building
from off the charge calculator's center. Prove shelter (including all
trunks and frozen links), awaken the window from local price bounds, and
produce the broad guards (`torch`) on the real arbitrary configuration built
in the other chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Milk
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Spindle WeightedGaussianMarginal45C.Venue PhysicalGuard7f546.Curved
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open AnalyticNext.ConnectedActivity
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {T : Tube G S} {i : Site c} {x C β B W : ℝ} {d : ℝ} {X : Config G f}

section germs
lemma sweepB (i : Bond f) (h : i∈Aff.activeB A F (radiusB x)) : i∉F.trunks:=(mem_filter.mp h).2.1
def fundedB (i : Bond f) (h : i∈Aff.activeB A F (radiusB x)) : Active A x F:= ⟨⟨i,sweepB i h⟩,(stillActive ..).1 h⟩
-- choose on Y after prediction; freeze sizes regular enough for the estimates
variable (T : Tube G S) (V : Config G c) (k : S.Choices) (q : Chi)

def cabin (Y : LinkArray G (Frozen A x F)) : Aff.Mint T F A x:= ⟨V,(fun i=> if h:chill A x F i then Y ⟨i,h⟩ else 1),q,k,firstRadius G,Aff.holdSize G S.patch x⟩

def switchCab (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) : Aff.ArrayR G f :=
  let C := (cabin T V k q Y).μ
  fun i => if h : i.1 ∈ Aff.activeB A F (radiusB x) then a (fundedB i.1 h,i.2) - C i else 0

lemma shelter (Y : LinkArray G (Frozen A x F)) (a : Prices G (Active A x F)) :
    let K:=cabin T V k q Y
    K.build (K.μ+switchCab T V k q Y a)=Next.SectorChange.physical A F V Y (tape a):=by
  intro K; funext i
  by_cases hi:i∈F.trunks
  · rw [show Aff.Mint.build _ _ _=1 from F.on_tree _ ⟨i,hi⟩, show Next.SectorChange.physical A F V Y (tape a) i= (1:G.El) from F.on_tree _ ⟨i,hi⟩]
  let p : F.Free:=⟨i,hi⟩; let b:= K.μ+switchCab T V k q Y a
  have hx : Next.SectorChange.physical A F V Y (tape a) i=Next.SectorChange.returned A F V Y (tape a) p:= F.off_tree _ p
  rw [hx]; unfold Aff.Mint.build Aff.install; change F.drape _ p.val=_; rw [F.off_tree]
  split_ifs with he
  · let j:=fundedB p.val he
    have hZ : Aff.lie b i=tape a j := by
      ext u; change K.μ _ + switchCab T V k q Y a (i,u)=_
      unfold switchCab; rw [dif_pos (show i ∈ _ from he)]; change _ = a (j,u); unfold j K; dsimp only; abel
    rw [show Next.SectorChange.returned A F V Y (tape a) p=_ from freeze_regular (j:=j) ..]
    rw [hZ]; rfl
  let j : Frozen A x F:=⟨p, Classical.not_not.mp (mt (stillActive ..).2 he)⟩
  rw [show Next.SectorChange.returned A F V Y (tape a) p = Y j from freeze_held (j:=j) ..]; exact dif_pos j.property
end germs
section region
-- coordinate-aware, i here coarse
def Toned (D : ℕ) (i : Site c) (z : Prices G (Active A x F)) (t : ℝ) :=
  ∀ j : In x A F (G:=G), separation i (front A F j) ≤ D → |z j| ≤ t
namespace Toned
lemma shift {p : Prices G (Active A x F)} {s d : ℕ} {i' : Site c} (h : Toned d i p C) (hh : separation i i'+s≤d) : Toned s i' p C :=
  fun _ hp => h _ ((separation_triangle _ i' _).trans ((Nat.add_le_add_left hp _).trans hh))
end Toned

private lemma vanish (G : Gauge) (D : Patch) (ε : ℝ) (he : 0<ε) :
    ∀ᶠ x in atTop,x^(-(3/4):ℝ) ≤ ε*fiery G x D.L:= by
  filter_upwards [threshold_large G D.L ε⁻¹ (by positivity),eventually_gt_atTop (0:ℝ)] with x hx hh
  rw [linkRoom_sq hh] at hx; exact (mul_le_mul_of_nonneg_left hx he.le).trans' (by rw [← mul_assoc,mul_inv_cancel₀ he.ne',one_mul])

-- Awake at the price budget.
structure Prognosis (P : Teller G) (D : Patch) (x ε : ℝ) (Q : Win.Promise.Turns) : Prop where
  prices (c f : Side) (S : StepData c f) (T : Tube G S) : P.Funds S T → S.patch=D → Larger (G:=G) S →
    ∀ H K, Aff.Alongside H K T → Booth P S T → ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c) (k : S.Choices),
    Aff.cert S x A V → ∀ (χ : Chi) (d β : ℝ) (p : RoomView A x F G), 0<β →
      let C:= cabin T V k χ p.1
      let w := portrait T A F k x V .endpoint χ d p.1 + coupling β • p.2
      let B := radiusB x; let t:=fiery G x S.patch.L; let z':=switchCab T V k χ p.1 w
      Q.Takes (Aff.eyes S G (radiusB x)) C.sheet (Aff.dcol S) (Aff.paceR x) →
       ∀ i : Site c,i∉ A.dome (40*B) → Toned B i p.2 (ε/2*t/coupling β) → Jewels.Awake S B i z' (ε*t)
lemma prognosis (hC : Aff.Reserve P C) (D : Patch) (h : D.Branches P.bind G) (Q : Win.Promise.Turns) {ε} (he : 0<ε) :
    ∀ᶠ x in atTop, Prognosis P D x ε Q:= by
  filter_upwards [peers hC D h Q, vanish G D (ε/2) (half_pos he)] with x hp ht
  constructor
  intro c f S T hT hS h₀ H K hk hF F A V k hv χ d β p hβ L w B t z hQ i hI h j hj
  let a := Aff.home S j.1; let D' := portrait T A F k x V .endpoint χ d p.1; let g:=coupling β
  have hg:0<g:=coupling_pos hβ
  have hD: separation i a ≤ B:= (mem_filter.mp hj).2
  have he₁: a ∉ A.dome (30*B):= Aff.exclude A _ _ _ _ hI (by omega)
  have hn:0 ≤ t:= temp_nonneg _
  by_cases hz : j.1 ∈ Aff.activeB A F (radiusB x)
  · let j0:=fundedB j.1 hz
    let i':=(j0,j.2)
    have hζ : |g*p.2 i'| ≤ ε/2*t := by
      rw [abs_mul,abs_of_nonneg hg.le,mul_comm]; exact (le_div_iff₀ hg).mp (h i' hD)
    have hc : |D' i'-L.μ j| ≤ ε/2*t:= by
      have hh:= (PiLp.norm_apply_le (tape D' j0-Aff.lie L.μ j.1) j.2).trans (hp _ _ S T hT hS h₀ H K hk hF F A L hv hQ j0 he₁ χ d p.1)
      exact hh.trans (by unfold t; rw [hS]; exact ht)
    have hx : z j = g*p.2 i'+(D' i'-L.μ j):= by
      unfold z switchCab; rw [dif_pos hz]; change D' i'+ g*p.2 i' - L.μ j= _; ring
    rw [hx]; exact (abs_add_le ..).trans ((add_le_add hζ hc).trans_eq (by ring))
  rw [show z j=0 from dif_neg hz,abs_zero]; positivity

-- Main local triggers primitive
structure Beacons (P : Teller G) (D : Patch) (W ε x : ℝ) : Prop where
  fires (c f : Side) (S : StepData c f) (T : Tube G S) : P.Funds S T → S.patch=D → Larger (G:=G) S →
    ∀ H K, Aff.Alongside H K T → Booth P S T → ∀ (F : Forest S.ratio) (A : Stores S) (V : Config G c) (k : S.Choices), Aff.cert S x A V →
    ∀ (χ : Chi) d (Y : RoomView A x F G) (β : ℝ), 0<β →
      let U:=gazed T k χ V x β d Y; let a:= portrait T A F k x V .endpoint χ d Y.1+coupling β • Y.2
      let B:=radiusB x; let t:=fiery G x S.patch.L; let q:=ε*t/(coupling β)
      ∀ i : Site c,i∉A.dome (40*B) → Toned B i Y.2 q → (∀ j : Active A x F,Aff.home S j.val.val=i→‖tape a j‖<firstRadius G) ∧
        (∀ j : Cell f,S.ratio.parent j.1=i → toll U j < t/4) ∧
        ∀ j : Bond c,j.1=i→ wire (S.prediction U k) V j < W*t ∧ Aff.αSite U j.1 k=1 ∧ Aff.αBond U j k=1
lemma torch (hC : Aff.Reserve P C) (D : Patch) (hp : D.Branches P.bind G) (h : Jewels.wedge P C D.L) (W : ℝ) (hw : 0<W) (hW : Jewels.Wedge P C W) :
    ∃ e : ℝ,0 <e ∧ ∀ᶠ x in atTop, Beacons P D W e x:=by
  obtain ⟨M,g,hg,hM⟩:= Aff.install_promises P D hp
  obtain ⟨ε,he,H⟩:= Jewels.night P C hC D hp h W hw hW g
  refine ⟨ε/2,by positivity,?_⟩
  filter_upwards [prognosis hC D hp g he, hM, H, (Rates.vanishes G D 17).eventually (gt_mem_nhds (first_pos G)), Jewels.guard_broad P C hC D hp ε he.le g] with x hx hp h hη hζ
  constructor
  intro c f S T hT hS h₀ J K hk hF F A V k hV χ d p β hβ U a B t v i hi hh
  let L:=cabin T V k χ p.1; let p':= switchCab T V k χ p.1 a
  have hL:g.Takes (Aff.eyes S G B) L.sheet (Aff.dcol S) (Aff.paceR x):=(hp.2 c f S T V A F hT hS hV).2
  have hU : L.build (L.μ+p')=U:= shelter ..
  have he' := hx.prices c f S T hT hS h₀ J K hk hF F A V k hV χ d β p hβ hL i hi hh
  have hI : i∉A.dome (20*B):= fun h=>hi (Aff.placed A _ _ (by omega) h)
  have ht:= h.earns c f S T hS hT A F L hV J K hk hL (by unfold L cabin; dsimp only; rw [hS]) p'
  refine ⟨fun j h=> ?_,fun j hh=> hU ▸ ((ht.1 j) (hh.symm ▸ hI) (hh.symm ▸ he')),fun j hh=> hU ▸ ht.2 j (hh.symm ▸ hI) (hh.symm ▸ he')⟩
  let W := L.μ+p'
  have hz := hζ c f S T hT hS A F L hV hL (by unfold L cabin; dsimp only; rw [hS]) p' j.val.val (fun p=> ?_)
  swap; rw [← hS]; apply he' (j.val.val,p); apply mem_filter.mpr; rw [h,separation_self]; exact ⟨mem_univ _,by omega⟩
  have hf : Aff.lie W j.val.val=tape a j := by
    ext p; change L.μ _ + p' _=_
    unfold p' switchCab; rw [dif_pos ((stillActive ..).2 j.property)]
    change _= a (j,p); unfold L; abel
  exact lt_of_le_of_lt (hf ▸ hz) hη
end region
end YM.PhysicalNext.InteractingRank.Milk
