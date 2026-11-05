import YM.Next.FREE_KERNELS.Account
import YM.Next.FREE_KERNELS.Train

/-!
# The propagated covariance and its pole splits

Auxiliary diagonal symbols D *off the poles*. To simplify the bookkeeping,
use field division including Lean's zero convention (meromorphic formulas are
compared on their regular sets). These D's won't be used as continuous harmonic
extensions. `levelD` expands along ALL aliases with physical counting, including
each earlier noise. This is for arbitrary linear histories descending from the
Wilson Hessian. Money parameters incl penalty are still free parameters here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric
open scoped Topology BigOperators

variable {j : ℕ}

def massFilter (P : RG.Patch) (p : Momentum) := area P.L p ^ P.J

def pullLine (P : RG.Patch) (a : Axis) (p : Momentum) := massFilter P p*rail P.L (p a)

def yen (f : Momentum → ℂ) (p : Momentum) := f p*f (-p)

lemma yen_symm (f : Momentum → ℂ) (p : Momentum) : yen f (-p)=yen f p := by simp only [yen,neg_neg,mul_comm]
lemma yen_stable {f : Momentum → ℂ} (h : Stable f) : Stable (yen f) := by
  intro p x
  rw [yen, yen, h, show -(p+reciprocal x)=(-p)+reciprocal (-x) by rw [reciprocal_negate]; abel, h]

lemma pullLine_stable (P : RG.Patch) (a : Axis) : Stable (pullLine P a) := fun p x => by
  simp only [pullLine,massFilter,Train.area_period,Pi.add_apply,reciprocal,rail_repeat]


namespace Train

def drive (v : Train j) (a : Axis) (p : Momentum) := v.smooth p*rail v.mass (p a)

lemma drive_period (v : Train j) (a) : Stable (v.drive a) := fun p x => by
  simp only [drive,smooth_period,Pi.add_apply,reciprocal,rail_repeat]
lemma drive_flip (v : Train j) (a) (p : Momentum) : star (v.drive a p)=v.drive a (-star p) := by
  rw [drive,drive,star_mul,smooth_conj,rail_bar, mul_comm]; rfl
lemma drive_signed (v : Train j) (a) (p : Momentum) (s : Signed) :
    yen (v.drive (s.perm a)) (s.act p)=yen (v.drive a) p := by
  simp only [yen,drive,← Signed.act_neg,smooth_signed, Signed.act_at, Pi.neg_apply]; split <;> simp only [neg_neg]; ring
lemma drive_price (v : Train j) (a) (p : Momentum) (hp : physical p) : Silver (yen (v.drive a) p) := by
  have he := drive_flip v a p; rw [show star p=p from hp] at he
  rw [yen,← he]; exact Silver.gram _
lemma drive_links (P : RG.Patch) {h : j≤P.J} {h' : P.J≤j+1} (v : Train P.J) (a : Axis) (p : Momentum) :
    (hop P h h' v).drive a p=pullLine P a (v.mass.val • p)*v.drive a p := by
  simp only [drive,pullLine,massFilter,mass,bind]; rw [← rail_bind];
  rw [Pi.smul_apply,nsmul_eq_mul]; ring_nf

end Train

def shuttle (L : Side) (g f : Momentum → ℂ) (p : Momentum) :=
    ((L.val:ℂ)^2)⁻¹ * ∑ i : Site L, yen g (aliasAt p i) * f (aliasAt p i)

def feed (v : Train j) (a : Axis) := shuttle v.mass (v.drive a)

def slide (P : RG.Patch) (a : Axis) := shuttle P.L (pullLine P a)

lemma bind_feeds (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J)
    (a : Axis) (f : Momentum → ℂ) (p : Momentum) :
    feed (.hop P h h' v) a f p = slide P a (feed v a f) p := by
  let L := P.L
  let w := Train.hop P h h' v
  let e := radices P.odd_side v.mass_odd
  have he (l : Site L) (r : Site v.mass) (q : Momentum) :
      w.drive a (aliasAt q r)=pullLine P a q * v.drive a (aliasAt q r) := by
    rw [Train.drive_links,alias_scale,pullLine_stable]
  have hb (l : Site L) (r : Site v.mass) (q : Momentum) :
      w.drive a (-aliasAt q r)=pullLine P a (-q)*v.drive a (-aliasAt q r) := by
    rw [← alias_reverse q v.mass_odd,he l]
  let W := fun b : Site (L*v.mass) => yen (w.drive a) (aliasAt p b) * f (aliasAt p b)
  let A := fun l : Site L => yen (pullLine P a) (aliasAt p l)
  let B := fun (l : Site L) (r : Site v.mass) => yen (v.drive a) (aliasAt (aliasAt p l) r) * f (aliasAt (aliasAt p l) r)
  have hu (l r) : W (e (l,r))=A l * B l r := by
    unfold W A B; rw [show aliasAt p (e (l,r))=_ from (alias_refine P.odd_side v.mass_odd p l r).symm]
    unfold yen; rw [he l,hb l]; ring
  have hw : ∑ i, W i = ∑ l, A l * ∑ r, B l r := by
    rw [← e.sum_comp W, Fintype.sum_prod_type]; simp_rw [hu,Finset.mul_sum]; rfl
  change (((L*v.mass).val:ℂ)^2)⁻¹ * (∑ i, W i) = ((L.val:ℂ)^2)⁻¹ * ∑ l, A l * ((((v.mass.val:ℂ)^2)⁻¹) * ∑ r, B l r)
  rw [hw,mul_side_complex,mul_pow, mul_inv_rev]
  simp_rw [Finset.mul_sum]
  ring_nf

lemma feed_stable (v : Train j) (a : Axis) {f : Momentum → ℂ} (h : Stable f) : Stable (feed v a f) := by
  intro p x
  let g := fun p => yen (v.drive a) p*f p
  have he : Stable g := fun p x => by unfold g; rw [yen_stable (v.drive_period a),h]
  unfold feed shuttle
  rw [show (∑ i : Site v.mass, _)=_ from shuttle_stable v.mass g he p x]
lemma feed_cost (v : Train j) (a : Axis) {f : Momentum → ℂ}
    (h : ∀ p : Momentum, physical p → Silver (f p)) : ∀ p : Momentum, physical p → Silver (feed v a f p) := fun _ hp =>
  ((Silver.side _).pow _).inv.mul (Silver.sum _ _ (fun _ _ =>
    (v.drive_price _ _ (alias_real hp _)).mul (h _ (alias_real hp _))))

lemma feed_signed (v : Train j) (a : Axis) {f : Momentum → ℂ}
    (h : ∀ p : Momentum, ∀ s : Signed, f (s.act p)=f p) (p : Momentum) (s : Signed) :
    feed v (s.perm a) f (s.act p)=feed v a f p := by
  unfold feed shuttle
  congr 1
  let A := fun i : Site v.mass => yen (v.drive (s.perm a)) (aliasAt (s.act p) i)*f (aliasAt (s.act p) i)
  rw [← Equiv.sum_comp (s.actEquiv.toEquiv) A]; refine Finset.sum_congr rfl fun i _ => ?_
  change A (s.act i)=_; unfold A; rw [alias_signed v.mass_odd,v.drive_signed,h]

lemma feed_top (a : Axis) (j) (f : Momentum → ℂ) (p : Momentum) : feed (.top j) a f p = f p := by
  unfold feed
  have hm : (Train.top j).drive a = fun _ => 1 := by funext i; rw [Train.drive]; simp [Train.mass]
  rw [hm]; change shuttle 1 _ _ _ = _
  unfold shuttle
  simp only [yen,one_mul]
  letI : Subsingleton (Site 1) := inferInstanceAs (Subsingleton (Axis → ZMod 1))
  have he : (∑ i : Site 1, f (aliasAt p i))=f (aliasAt p (0 : Site 1)) := Finset.sum_eq_single _ (fun i _ h => False.elim (h (Subsingleton.elim ..))) (fun h => False.elim (h (Finset.mem_univ _)))
  rw [he]; simp [aliasAt]

namespace Train

/-- Prefixes receiving independent noise; empty at the cutoff. -/
def nozzle {j} : Train j → List (Train j)
| top _ => []
| hop P h h' v => (top _) :: (v.nozzle.map (hop P h h'))

def stream (l : List (Train j)) (a : Axis) (p : Momentum) :=
  (l.map fun v => feed v a (fun _ => 1) p).sum

def levelNoise (v : Train j) (a : Axis) := stream v.nozzle a

def levelD (k : ℝ) (v : Train j) (a : Axis) (p : Momentum) :=
    feed v a (fun i => (divisor 1 i)⁻¹) p + (k:ℂ)⁻¹ * v.levelNoise a p

lemma bound_shuttle (P : RG.Patch) (a : Axis) (f g : Momentum → ℂ) (r : ℂ) (p : Momentum) :
    slide P a (fun p => f p+r*g p) p=slide P a f p+r*slide P a g p := by
  unfold slide shuttle
  simp_rw [mul_add,Finset.sum_add_distrib,mul_add]
  simp_rw [Finset.mul_sum]; congr 1; refine Finset.sum_congr rfl fun x _ => ?_; ring

lemma nozzle_flow {j : ℕ} (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J)
    (a : Axis) (p : Momentum) : (hop P h h' v).levelNoise a p=1+slide P a (v.levelNoise a) p := by
  have hh (l : List (Train P.J)) : stream (l.map (hop P h h')) a p=slide P a (stream l a) p := by
    induction l with
    | nil => simp [stream,slide,shuttle]
    | cons b l ih =>
      have he : stream (b :: l) a=fun q => feed b a (fun _ => 1) q + 1*stream l a q := by funext q; simp [stream]
      rw [he,bound_shuttle,← ih,one_mul]
      simp only [stream,List.map_cons,List.sum_cons,bind_feeds]
  simp only [levelNoise,nozzle]; simp only [stream, List.map_cons,List.sum_cons, feed_top]
  exact congr_arg (1+·) (hh v.nozzle)

lemma D_feedback (k : ℝ) (P : RG.Patch) (h : j≤P.J) (h' : P.J≤j+1) (v : Train P.J)
    (a : Axis) (p : Momentum) : levelD k (hop P h h' v) a p=slide P a (levelD k v a) p+(k:ℂ)⁻¹ := by
  unfold levelD; rw [bind_feeds,nozzle_flow,bound_shuttle]; ring

lemma D_cost (k : ℝ) (hk : 0<k) (v : Train j) (a) {p : Momentum} (hp : physical p) : Silver (levelD k v a p) := by
  have hh (l : List (Train j)) : Silver (stream l a p) := by
    induction l with
    | nil => exact Silver.zero
    | cons b l ih => exact (feed_cost b a (fun _ _ => Silver.one) p hp).add ih
  exact (feed_cost v a (fun p h => (Silver.chipSq 1 h).inv) p hp).add ((Silver.real hk.le).inv.mul (hh _))
lemma D_stable (k : ℝ) (v : Train j) (a) : Stable (levelD k v a) := by
  have hh (l : List (Train j)) : Stable (stream l a) := by
    induction l with
    | nil => intro p x; simp only [stream,List.map_nil,List.sum_nil]
    | cons b l ih =>
      intro p x
      exact congr_arg₂ (·+·) (feed_stable b a (f:=fun _ => 1) (fun _ _ => rfl) p x) (ih p x)
  intro p x
  unfold levelD levelNoise
  rw [feed_stable v a (show Stable (fun p => (divisor 1 p)⁻¹) from fun p x => congr_arg Inv.inv (chipSq_stable p x)),hh]
lemma D_signed (k : ℝ) (v : Train j) (a) (s : Signed) (p : Momentum) : levelD k v (s.perm a) (s.act p)=levelD k v a p := by
  have hh (l : List (Train j)) : stream l (s.perm a) (s.act p)=stream l a p := by
    induction l with
    | nil => simp only [stream,List.map_nil,List.sum_nil]
    | cons b l ih => exact congr_arg₂ (·+·) (feed_signed b a (f:=fun _ => 1) (fun _ _ => rfl) p s) ih
  unfold levelD levelNoise; rw [feed_signed v a (fun p s => congr_arg Inv.inv (chipSq_signed 1 p s)),hh]
lemma D_even (k : ℝ) (v : Train j) (a) (p : Momentum) : levelD k v a (-p)=levelD k v a p :=
  D_signed k v a ⟨1,fun _ => true⟩ p

/-- Explicit pole split, formulas still allow real poles `p=0` by totalized
reciprocals. We'll only *match* singular expressions off pole. -/
def lid (v : Train j) (a : Axis) (p : Momentum) := yen (v.drive a) (narrow v.mass p)

def high (v : Train j) (a : Axis) (p : Momentum) := ∑ i∈Finset.univ.erase (0 : Site v.mass),
    yen (v.drive a) (aliasAt p i) * (blow 1 p i)⁻¹

def drain (k : ℝ) (v : Train j) (a : Axis) (p : Momentum) := v.high a p + (k:ℂ)⁻¹ * v.levelNoise a p

lemma pole_split (k : ℝ) (v : Train j) (a : Axis) (p : Momentum) :
    levelD k v a p = v.lid a p * (divisor v.mass p)⁻¹ + drain k v a p := by
  unfold levelD feed shuttle drain lid high; rw [← add_assoc, Finset.mul_sum]
  congr 1
  let M := v.mass
  let f := fun i : Site M => yen (v.drive a) (aliasAt p i) * (blow 1 p i)⁻¹
  calc
    _ = ∑ i, f i := Finset.sum_congr rfl fun i _ => by unfold f blow; rw [mul_inv_rev]; ring
    _ = f 0 + ∑ i∈Finset.univ.erase 0, f i := (Finset.add_sum_erase _ f (Finset.mem_univ _)).symm
    _ = _ := by unfold f; rw [blow_zero,mul_one,alias_zero_eq]

lemma drain_cost (k : ℝ) (hk : 0<k) (v : Train j) (a : Axis) {p : Momentum} (hp : physical p) : Silver (drain k v a p) := by
  have hh (l : List (Train j)) : Silver (stream l a p) := by
    induction l with
    | nil => exact Silver.zero
    | cons b l ih => exact (feed_cost b a (fun _ _ => Silver.one) p hp).add ih
  refine Silver.add (Silver.sum _ _ (fun i _ => ?_)) ((Silver.real hk.le).inv.mul (hh _))
  exact (drive_price _ _ _ (alias_real hp _)).mul (((Silver.side _).pow _).mul (Silver.chipSq 1 (alias_real hp _))).inv
end Train
end YM.Next.Free
