import YM.RG08.Fields.Banjo

/-!
# Closing the analytic covariance projection

Use all integer cells on genuine single wraps, even included.

Full
Train.D except at zero external momentum.

This one value doesn't enter
the Fourier integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Drift
open Function Filter Set Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08
open scoped Topology BigOperators

variable {c f : Side} {j n : ℕ} {k : ℝ} {ι β : Type} [DecidableEq ι] [Fintype ι] [DecidableEq β] [Fintype β]
lemma mon_here {p : Site c} : mon p=0 ↔ p=0 := by
  refine ⟨fun h => ?_,fun h=>h ▸ mon_zero⟩
  by_contra hx; obtain ⟨i,hi⟩:=step_picks p hx; rw [cell_step,h] at hi; simp at hi
lemma mon_opposite (p : Site c) : ∃ x : Cover, mon (-p)= -mon p + reciprocal x := by
  have hx : wrap c (-lift p) = wrap c (lift (-p)) := by simp
  obtain ⟨x,hx⟩:= cover_of_eq _ _ hx; use x
  rw [mon,hx]; unfold mon; ext i
  have hc := side_ne c; simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,Pi.neg_apply,reciprocal,nsmul_eq_mul,Pi.mul_apply,Pi.natCast_apply,Int.cast_add,Int.cast_neg, Int.cast_mul,Int.cast_natCast]; field_simp

section scroll
variable (A : Site c → Matrix ι β ℂ)
def orchard := (stageVolume c)⁻¹ • (rotations c ι*fiber A*(rotations c β)ᴴ)
lemma orchard_rotate : orchard A * rotations c β=rotations c ι * fiber A := by
  obtain ⟨hq,hx,ht⟩:=rotations_crew c β
  rw [orchard,Matrix.smul_mul,Matrix.mul_assoc (rotations c ι*fiber A),ht,Matrix.mul_smul,Matrix.mul_one,smul_smul,inv_mul_cancel₀ hq,one_smul]
lemma orchard_show (s t : Site c) (a : ι) (b : β) : orchard A (s,a) (t,b)=(stageVolume c)⁻¹ * ∑ p : Site c, cell p s * A p a b*star (cell p t) := by
  unfold orchard; rw [Matrix.smul_apply,Matrix.mul_apply,Fintype.sum_prod_type]; simp_rw [rot_fiber]; simp [rotations,apply_ite (starRingEnd ℂ),mul_ite]

def daylight := (orchard A).map Complex.re
lemma cell_back (x p : Site c) : cell (-p) x=star (cell p x) := by rw [cell_duality,cell_inverse,cell_duality x p]; simp
lemma orchard_real (H : ∀ (p : Site c) i j,A (-p) i j=star (A p i j)) : approached (daylight A)=orchard A := by
  ext ⟨x,i⟩ ⟨y,j⟩; unfold daylight; simp only [approached,Matrix.map_apply,orchard_show]
  let f (p : Site c):=cell p x*A p i j*star (cell p y); let d:=(stageVolume c)⁻¹; let n:=∑ p,f p
  have he (p : Site c): f (-p)=star (f p) := by unfold f; rw [cell_back,cell_back,H]; simp only [star_mul]; ring
  have hh : star (d*n)=d*n := by
    have hp : star n=n:=by unfold n; simp only [star_sum,← he]; exact Equiv.sum_comp (Equiv.neg (Site c)) f
    have hz : star d=d := by simp [d,stageVolume]
    rw [star_mul,hp,hz,mul_comm]
  change ((d*n).re:ℂ)=d*n; obtain ⟨r,hr⟩ := Complex.conj_eq_iff_real.mp hh; rw [hr]; rfl
lemma tokenized (H : ∀ (p : Site c) i j,A (-p) i j=star (A p i j)) : Runs (rotations c ι) (rotations c β) (daylight A) (fiber A) := by unfold Runs; rw [orchard_real A H,orchard_rotate]
end scroll

-- no real transverse test charges the absent finite-volume cell
noncomputable def curfew (k : ℝ) (v : Train j) (p : Momentum) : Matrix (TypeFace 1) (TypeFace 1) ℂ := by
  classical
  exact if p=0 then 0 else fieldD 1 k v p
open scoped Classical
lemma quaint (hk : 0<k) (v : Train j) (p : Site c) (i b) :
    curfew k v (mon (-p)) i b=star (curfew k v (mon p) i b) := by
  by_cases h:p=0
  · simp [curfew,h]
  unfold curfew; rw [if_neg (mt mon_here.mp (neg_ne_zero.mpr h)), if_neg (mt mon_here.mp h)]
  simp only [fieldD,mask_value,scaleD_one]; split
  · obtain ⟨x,H⟩:=mon_opposite p; rw [H,Train.D_stable,Train.D_even]; exact (Train.D_cost k hk v _ (real_frequency _)).fixed.symm
  simp

def bedtime (k : ℝ) (v : Train j) (c : Side) := daylight (fun p : Site c=> curfew k v (mon p))
lemma bud_runs (hk : 0<k) (v : Train j) : Runs (rotations c (TypeFace 1)) (rotations c (TypeFace 1)) (bedtime k v c) (solo c (curfew k v)):=
    tokenized _ (fun p=> quaint hk v p)
lemma trace_nimb (v : Train j) (c : Side) (x y : Site c) (i t : TypeFace 1) : bedtime k v c (x,i) (y,t)=bedtime k v c (0,i) (y-x,t) := by
    simp only [bedtime,daylight,Matrix.map_apply, orchard_show,cell_origin,one_mul]
    refine congr_arg Complex.re (congr_arg ((stageVolume c)⁻¹ * ·) (Finset.sum_congr rfl ?_)); intro p hp
    rw [sub_eq_add_neg,cell_add,cell_inverse,star_mul, star_inv₀, show star (cell p x)=_ from cell_bar p x, inv_inv]
    ring!
lemma punctual_curfew {v : Train j} (b : TypeFace 1) (p : Momentum) :
    curfew k v p b b=if p=0 then 0 else v.levelD k (axisEquiv.symm b) p := by
  unfold curfew; split <;> simp [fieldD,mask_value,scaleD_one, *]
lemma herm_curfew (hk : 0 < k) {p : Momentum} (hp : physical p) (v : Train j) :
    (curfew k v p)ᴴ=curfew k v p := by
  unfold curfew; split
  · simp
  ext i j; rw [conjTranspose_apply]; unfold fieldD; simp_rw [mask_value,scaleD_one, show i=j ↔ j=i from eq_comm]
  split
  · next h=> subst i; exact (Train.D_cost k hk v _ hp).fixed
  simp
lemma bed_even (hk : 0<k) (v : Train j) : (bedtime k v c)ᵀ=bedtime k v c := by
  have ht := rotations_crew c (TypeFace 1)
  have he := bud_runs (c:=c) hk v
  have hh := he.back ht ht
  rw [div_self (stage_ne c), one_smul] at hh; unfold solo at hh; rw [fiber_H] at hh
  simp_rw [herm_curfew hk (real_frequency _) v] at hh; exact hh.lands he ht
lemma rotor_zero (v : Train j): rotor 1 k v 0=0 := by
  have h : signal 1 1 0=0 := by simp [signal,tripQ,wedge]
  unfold rotor; simp [h]
lemma snaps (hk : 0<k) (hj : 4≤j) (v : Train j) (c : Side) :
    let K:= Precision.K ((pink k v).acts c)
    K*bedtime k v c*K=K := by
  intro T
  have he := runs_rotor k hk hj v c; have hh:= bud_runs (c:=c) hk v
  have hP := (he.product hh).product he
  unfold solo at hP; rw [fiber_mult,fiber_mult] at hP
  have hm (p : Site c) : rotor 1 k v (mon p) * curfew k v (mon p)* rotor 1 k v (mon p)=rotor 1 k v (mon p) := by
    unfold curfew; split
    · rename_i hx; simp [hx]
    next hx=> rw [Matrix.mul_assoc,rotor_before 1 k hk v (base_subset_realCube zone_pos (mon_mem ..)) hx,
         Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, (rotor_immunity 1 k v _).1,Matrix.zero_mul, sub_zero]
  simp_rw [hm] at hP; exact hP.lands he (rotations_crew c _)

/-- Gradient+harmonic complement on the torus. -/
def haloMat (c : Side) := daylight fun p : Site c => if p=0 then 1 else (0:Matrix (TypeFace 1) (TypeFace 1) ℂ)
lemma halo_show (c : Side) (x y : Site c) (a b : TypeFace 1) : haloMat c (x,a) (y,b)=(c.val:ℝ)⁻¹^4 * (1:Matrix (TypeFace 1) (TypeFace 1) ℝ) a b := by
  unfold haloMat daylight; rw [Matrix.map_apply,orchard_show,Finset.sum_eq_single 0]; swap
  · intro i _ hi; simp [hi]
  · by_cases h:a=b
    · subst b; rw [cell_duality (0:Site c),cell_duality (0:Site c)]; simp [stageVolume,← inv_pow]; rw [show ((c.val:ℂ)⁻¹)^4=((((c.val:ℝ)⁻¹)^4:ℝ):ℂ) by simp]; rfl
    rw [cell_duality (0:Site c),cell_duality (0:Site c)]; simp [h]
  simp
lemma shipped (hk : 0<k) (hj : 4 ≤ j) (v : Train j) (c : Side) :
    ∃ J, 1-bedtime k v c*Precision.K ((pink k v).acts c) = d 0 c * J + haloMat c := by
  let P:= rotations c (TypeFace 1); let Q:= rotations c (TypeFace 0)
  let o (p:Site c):= if p=0 then (1:Matrix (TypeFace 1) (TypeFace 1) ℂ) else 0
  have h1 (p : Site c) (i j) : o (-p) i j=star (o p i j) := by
    by_cases h:p=0 <;> simp [h,Matrix.one_apply,o]
  have hv:= (Runs.nil P).minus ((bud_runs hk v).product (runs_rotor k hk hj v c))
  have hw : Runs P P _ _:= tokenized o h1
  let A:=fun p : Site c=> if p=0 then 0 else pipe 1 k v (mon p)
  let F:= 1-bedtime k v c*Precision.K ((pink k v).acts c) - haloMat c
  have h := hv.minus hw; unfold solo at h; rw [fiber_mult,← fiber_one,fiber_less,fiber_less] at h
  let S:=fun p : Site c=> signal 1 0 (mon p)
  have hy p : 1-curfew k v (mon p)*rotor 1 k v (mon p)-o p=S p*A p := by
    by_cases he:p=0
    · simp [he,o,A,S,curfew]
    have hx:=mt mon_here.mp he
    simp only [curfew,A,he,hx,if_false,o,sub_zero]; rw [rotor_before 1 k hk v (base_subset_realCube zone_pos (mon_mem c p)) hx,sub_sub_cancel]
  simp_rw [hy] at h; rw [← fiber_mult] at h
  have heq : approached F = approached (d 0 c)*orchard A := by
    apply cancel_rotation
    change _=approached (d 0 c)*orchard A*P; change approached F * P=_ at h; rw [h,Matrix.mul_assoc (approached _), show orchard A*P=_ from orchard_rotate A]
    rw [show rotations c (TypeFace 0) =Q from rfl, ← Matrix.mul_assoc,← Matrix.mul_assoc, show approached (d 0 c) * Q=_ from (cobound_true 0).coarse c]; rfl
  refine ⟨daylight A,?_⟩; rw [← sub_eq_iff_eq_add]
  change F= _; ext i j; change (approached F i j).re=_; rw [heq,Matrix.mul_apply,Complex.re_sum, Matrix.mul_apply]; exact Finset.sum_congr rfl fun i _ => by simp [approached,daylight]
end YM.RG08.Drift
