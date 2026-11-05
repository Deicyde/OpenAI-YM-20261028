import YM.EveryPhase.Slots

/-!
# Continue conservation of the weighted stress

Partial strips entirely in absolute arguments. Use the same stage for each
label. Here we work in the OPEN strips. Real-space arguments may be real but
`emit` also knows their holomorphic jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase.Stress
open Function Set Filter MeasureTheory Boundary Next.BOUNDARY Mink Complex Descent
open Work.C20
open scoped Topology BigOperators
variable {G : Gauge} {L : Register G} {S U : Table L} {R : Table.Rotation S} {W : Surface S}
  {D : ∀ n, Blanket n} {Z : W.Aurora D} {n : ℕ}

/-- All translations plus infinitesimal Lorentz transformations. -/
structure Killing where
  translation : E4
  V : M4
  ok : tangent V

namespace Killing
variable (K : Killing)
def realV (x : E4) := K.translation + M4.move K.V x
def w (b : Axis) (x : Axis → ℂ) := zeta b * ((K.translation b:ℂ)+∑ i : Axis, (K.V b i:ℂ)*x i)
-- Euclidean column at points for shell
def we (b : Axis) (y : E4) := K.w b (fun a => wick a * (y a:ℂ))
lemma w_real (b : Axis) (r : Space3) (t : ℝ) : K.w b (lay r t) = zeta b * (K.realV (position r t) b:ℂ) := by
  simp only [w,lay_real, realV,PiLp.add_apply, M4.at_coord, ofReal_add, ofReal_sum,ofReal_mul]
lemma w_wick (b : Axis) (j : Fin n) (x : Points n) : K.w b (fun a => wickSlice n x (j,a))=K.we b (x j) := by
  simp_rw [wick_apply,we,wick]; congr 1; funext a; ring

def tilted (X : M4) (i j : Axis) := zeta i * wick j * (X i j:ℂ)
lemma tilted_space {X : M4} (h : spaceLikeGen X) (a b) : tilted X a b=(X a b:ℂ) := by
  unfold tilted
  calc _ = zeta a * (X a b:ℂ) * wick b := by ring
       _ = _ := by rw [← space_scale b a h.2, mul_right_comm,zeta_wick,one_mul]
lemma tilted_boost {X : M4} (h : boostLike X) (a b) : tilted X a b=(-I)*((X*theta) a b:ℂ) := by
  unfold tilted
  calc _ = zeta a * (X a b:ℂ) * wick b := by ring
       _ = _ := by rw [← boost_scale b a h]
                   calc _ = (zeta b * wick b) * (-I) * ((X*theta) a b:ℂ) := by ring
                        _ = _ := by rw [zeta_wick,one_mul]
lemma tilted_add (X Y : M4) (a b) : tilted (X+Y) a b=tilted X a b+tilted Y a b := by simp [tilted,mul_add]
lemma tilted_skew {X : M4} (ht : tangent X) (a b) : tilted X a b= -tilted X b a := by
  have h (V : M4) (h : star V= -V) : (V a b:ℝ)= -V b a := by
    rw [← Matrix.neg_apply,← h]; simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,star_trivial]
  obtain ⟨A,U,rfl,hA,hU⟩ := tangent_parts ht
  simp only [tilted_add,tilted_space hA,tilted_boost hU]
  rw [h A hA.1,h (U*theta) (off_skew hU)]
  push_cast; ring

lemma momentum (b : Axis) (i : Fin n) (x : Full n) :
    AnalyticAt ℂ (fun x : Full n => K.w b (fun a => x (i,a))) x := by
  let A : Full n →L[ℂ] ℂ := zeta b • (∑ j : Axis, (K.V b j:ℂ) • (PiLp.proj _ _ (i,j)))
  have hf : (fun x : Full n => K.w b (fun a => x (i,a))) = fun x => A x+ zeta b*(K.translation b:ℂ) := by
    funext u; simp [A,w,mul_add]; ring
  rw [hf]; exact (A.analyticAt x).add analyticAt_const
lemma slope (b : Axis) (i : Fin n) (a : Axis) (x : Full n) :
    fderiv ℂ (fun x : Full n => K.w b (fun a => x (i,a))) x (wickSlice n (Points.direction i a))=tilted K.V b a := by
  let A : Full n →L[ℂ] ℂ := zeta b • (∑ j : Axis, (K.V b j:ℂ) • (PiLp.proj _ _ (i,j)))
  have hf : (fun x : Full n => K.w b (fun a => x (i,a))) = fun x => A x+ zeta b*(K.translation b:ℂ) := by
    funext u; simp [A,w,mul_add]; ring
  rw [hf,(A.hasFDerivAt.add_const _).fderiv]; simp only [A, _root_.smul_apply, _root_.sum_apply]
  rw [Finset.sum_eq_single a]; swap
  · intro b hb ha; simp [wick_apply,Points.direction,ha]
  · simp [wick_apply, Points.direction,tilted,wick]; split_ifs <;> simp [*]; ring
  simp
end Killing

-- open-strip stress in a free slot
variable {P : DiffPlan S} {H : S.RealSpin} {F : Waves S} {T : S.Stress}

def tide (Z : W.Aurora D) (K : Killing) (j : Fin (n+1)) (v : Fin n → S.Union) (T : S.Stress)
    (a : Axis) (x : Full (n+1)) := ∑ b : Axis, K.w b (fun i => x (j,i))*Z.emit (hole j v (S.pin 4 (T a b))) x
lemma tide_analytic (K : Killing) (j : Fin (n+1)) (v : Fin n → S.Union) (T : S.Stress)
    (a : Axis) (hZ : Z.FullBody F) : AnalyticOnNhd ℂ (tide Z K j v T a) (tube (n+1)) := fun x hx => by
  unfold tide; exact Finset.analyticAt_fun_sum _ (fun b _ => (K.momentum b j x).mul (hZ.hol _ _ _ hx))

lemma hole_replace {A : Type*} (j : Fin (n+1)) (v : Fin n → A) (x y : A) :
    hole j v x=update (hole j v y) j x := by
  funext k; refine Fin.succAboveCases j ?_ ?_ k
  · simp
  intro l; rw [update_of_ne (Fin.succAbove_ne _ _)]; simp

lemma emitsL (j : Fin (n+1)) (v : Fin n → S.Union) (Z : W.Aurora D) (x : Full (n+1)) :
    ∃ A : S.Union →ₗ[ℂ] ℂ, ∀ a, Z.emit (hole j v a) x=A a := by
  let B := (W.W (n+1)).toLinearMap (hole j v 0) j
  let c := ((Probe.pref (Points (n+1)))⁻¹ : ℂ)
  let A : S.Union →ₗ[ℂ] ℂ :=
    { toFun a := c * B a (Probe.hat (Z.lens _ x))
      map_add' a b := by rw [map_add]; simp [mul_add]
      map_smul' a b := by rw [map_smul]; simp [mul_left_comm] }
  exact ⟨A, fun a => by rw [hole_replace j v a 0]; rfl⟩

lemma tide_div (K : Killing) (j : Fin (n+1)) (v : Fin n → S.Union) (T : S.Stress)
    (hT : Table.Conserved P H T) (hu : U.Hierarchy) (hs : S.Symmetric) (hi : P.Inclusions S)
    (hd : P.Derivatives U) (hF : F.Region U) (hZ : Z.FullBody F) (x : Full (n+1)) (hx : x∈tube (n+1)) :
    (∑ a : Axis, fderiv ℂ (tide Z K j v T a) x (wickSlice (n+1) (Points.direction j a)))=0 := by
  let t := fun a => wickSlice (n+1) (Points.direction j a)
  obtain ⟨N,hN⟩ := emitsL j v Z x
  let q := fun a b => Killing.tilted K.V b a * N (S.pin 4 (T a b))
  let r := fun a b => K.w b (fun i => x (j,i))* N (S.pin 5 (P.deriv 4 a (T a b)))
  have hh a : fderiv ℂ (tide Z K j v T a) x (t a)=(∑ b : Axis, q a b)+(∑ b : Axis, r a b) := by
    unfold tide; rw [fderiv_fun_sum,_root_.sum_apply,← Finset.sum_add_distrib]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      let W := fun x : Full (n+1) => K.w b (fun i => x (j,i))
      let L := Z.emit (hole j v (S.pin 4 (T a b)))
      have hw : DifferentiableAt ℂ W x := (K.momentum b j x).differentiableAt
      have hl : DifferentiableAt ℂ L x := (hZ.hol _ _ _ hx).differentiableAt
      change fderiv ℂ (fun x => W x*L x) x (t a)=_
      rw [fderiv_fun_mul hw hl]
      have ht : fderiv ℂ L x (t a)=N (S.pin 5 (P.deriv 4 a (T a b))) := by
        unfold L; rw [← hN,hole_replace j v (S.pin 4 (T a b)) 0,hole_replace j v (S.pin 5 (P.deriv 4 a (T a b))) 0]
        exact (field_jet P hu hs hi hd hF hZ _ _ _ _ _ hx).symm
      change W x*fderiv ℂ L x (t a)+L x*fderiv ℂ W x (t a)=_
      rw [ht, show fderiv ℂ W x (t a)=_ from K.slope b j a x, show L x=_ from hN (S.pin 4 (T a b))]; unfold q r W; ring
    intro b _; exact ((K.momentum b j x).differentiableAt.mul (hZ.hol _ _ _ hx).differentiableAt)
  have hq : (∑ a, ∑ b, q a b)=0 := by
    have he (a b) : q a b= -q b a := by unfold q; rw [Killing.tilted_skew K.ok b a,hT.symmetric a b,neg_mul]
    have hh : (∑ a, ∑ b, q a b)= -(∑ a, ∑ b, q a b) := calc
      _ = (∑ a : Axis, ∑ b : Axis, -q b a) := Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl fun j _ => he i j)
      _ = _ := by rw [Finset.sum_comm]; simp
    have hp := congr_arg Complex.re hh; have hz := congr_arg Complex.im hh
    simp only [neg_re,neg_im] at hp hz; apply Complex.ext <;> simp only [zero_re,zero_im] <;> linarith
  have hr : (∑ a, ∑ b, r a b)=0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero; intro b _; unfold r
    rw [← Finset.mul_sum, ← map_sum, ← map_sum,hT.divergence]; simp
  change (∑ a : Axis, fderiv ℂ _ x (t a))=0
  simp_rw [hh]; rw [Finset.sum_add_distrib,hr,hq]; ring

lemma lodge_cont (j : Fin (n+1)) : Continuous
    (fun p : (SpacePoints n × Times n) × (Space3 × ℂ) => lodge j p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold lodge laid dawn place points glow
  simp_rw [show position = _ from funext fun x => funext fun t => (Mink.combine_at x t).symm]
  unfold hole
  fun_prop

-- Easier increments on straight lines.
lemma lay_time (r : Space3) (z u : ℂ) (b : Axis) : lay r (z+u) b=lay r z b+if b=timeAxis then u else 0 := by unfold lay; split <;> simp

def needle (i : SpaceAxis) : Space3 := (Ray.fromAxis i).val
lemma lay_space (r : Space3) (z : ℂ) (t : ℝ) (i : SpaceAxis) (b : Axis) :
    lay (r+t • needle i) z b=lay r z b+if b=i.castSucc then t else 0 := by
  rcases Fin.eq_castSucc_or_eq_last b with ⟨l,rfl⟩ | rfl
  · rw [lay,if_neg (Fin.castSucc_ne_last l),lay,if_neg (Fin.castSucc_ne_last l)]
    change (spatial (position (r+_) 0) l:ℂ)=(spatial (position r 0) l:ℂ)+_
    rw [spatial_position,spatial_position]; by_cases e : l=i <;> simp [needle,Ray.fromAxis,e]
  rw [lay,lay,if_pos rfl,if_pos rfl,if_neg (Fin.castSucc_ne_last _).symm,ofReal_zero,add_zero]

lemma lodge_z (j : Fin (n+1)) (x : SpacePoints n) (u : Times n) (r : Space3) (z : ℂ) :
    HasDerivAt (lodge j x u r) (realPartL _ (Points.direction j timeAxis)) z := by
  let q := realPartL _ (Points.direction j timeAxis)
  have ht : lodge j x u r = fun t => lodge j x u r 0 + t • q := by
    funext t
    ext1 i
    obtain ⟨i,b⟩ := i
    change laid _ _ (i,b)=lodge j x u r 0 (i,b) + t*glow (Points.direction j timeAxis) 0 (i,b)
    refine Fin.succAboveCases j ?_ ?_ i
    · simp only [lodge,laid_at,hole_self]; by_cases h : b=timeAxis <;> simp [lay,glow,Points.direction,h]
    intro p
    simp only [lodge,laid_at,hole_next]; simp [glow,Points.direction,Fin.succAbove_ne]
  nth_rw 1 [ht]; simpa only [one_smul] using ((hasDerivAt_id' z).smul_const q).const_add _

lemma lodge_r (j : Fin (n+1)) (x : SpacePoints n) (u : Times n) (r : Space3) (z : ℂ) (i : SpaceAxis) :
    HasDerivAt (fun t : ℝ => lodge j x u (r+t • needle i) z) (wickSlice _ (Points.direction j i.castSucc)) 0 := by
  let q := wickSlice _ (Points.direction j i.castSucc)
  have he : (fun t : ℝ => lodge j x u (r+t • needle i) z)=fun t : ℝ => lodge j x u r z + t • q := by
    funext t
    ext1 l
    obtain ⟨l,b⟩ := l
    change laid _ _ (l,b) = lodge j x u r z (l,b) + t • wickSlice _ (Points.direction j i.castSucc) (l,b)
    refine Fin.succAboveCases j ?_ ?_ l
    · simp only [lodge,laid_at,hole_self,lay_space]; by_cases h : b=i.castSucc <;>
        simp [wick_apply,Points.direction,h, show i.castSucc≠timeAxis from Fin.castSucc_ne_last i, real_smul]
    intro p; simp only [lodge,laid_at,hole_next]; simp [wick_apply, Points.direction, Fin.succAbove_ne]
  rw [he]; simpa only [one_smul] using ((hasDerivAt_id' (0:ℝ)).smul_const q).const_add (lodge j x u r z)

lemma lodge_smooth (j : Fin (n+1)) (x : SpacePoints n) (u : Times n) (z : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r : Space3 => lodge j x u r z) := by
  -- use additive increment all r
  let M := LinearMap.toContinuousLinearMap ({
    toFun := fun r => realPartL _ (seat j 0 (position r 0))
    map_smul' := fun (c : ℝ) r => by
      rw [← map_smul]; congr 1; ext1 i; refine Fin.succAboveCases j ?_ ?_ i
      · simp only [seat_seat,PiLp.smul_apply]; apply ext_by <;> simp
      intro k; simp
    map_add' := fun r s => by
      rw [← map_add]; congr 1; ext1 i; refine Fin.succAboveCases j ?_ ?_ i
      · simp only [seat_seat,PiLp.add_apply]; apply ext_by <;> simp
      intro k; simp } : Space3 →ₗ[ℝ] Full (n+1))
  rw [show (fun r : Space3 => lodge j x u r z)= fun r => M r + lodge j x u 0 z by
    funext r; ext1 i; obtain ⟨i,b⟩ := i; change laid _ _ _=glow _ _ _+lodge _ _ _ _ _ (i,b)
    refine Fin.succAboveCases j ?_ ?_ i
    · simp only [lodge,laid_at,hole_self]; unfold lay; split
      · next h => subst b; simp [glow,show position r 0 timeAxis=0 from time_position _ _]
      simp [glow,show position 0 0=0 by apply Mink.ext_by <;> simp]
    intro p; simp [lodge,laid_at,glow] ]
  exact M.contDiff.add contDiff_const

lemma laid_hol (x : SpacePoints n) : Differentiable ℂ (laid x) := by
  let N := LinearMap.toContinuousLinearMap ({
    toFun := fun u => WithLp.toLp 2 (fun p => if p.2=timeAxis then (u p.1:ℂ) else 0)
    map_add' := fun f g => by ext1 p; change (ite _ _ _ : ℂ)=ite _ _ _ + ite _ _ _; split <;> simp [*]
    map_smul' := fun c f => by ext1 p; change (ite _ _ _:ℂ)= (c:ℂ)* (ite _ _ _); split <;> simp [*] } : Times n→ₗ[ℂ] Full n)
  rw [show laid x = fun u => N u + laid x 0 by
    funext u; ext1 i; obtain ⟨i,b⟩ := i; change _=(ite (b=timeAxis) (u i) 0:ℂ)+ laid x 0 (i,b); simp only [laid_at,lay]; split <;> simp ]
  exact N.differentiable.add (differentiable_const _)

lemma hole_hol (j : Fin (n+1)) : Differentiable ℂ (fun p : Times n × ℂ => hole j p.1 p.2) := by
  apply differentiable_pi.mpr; intro i; refine Fin.succAboveCases j ?_ ?_ i
  · simp
  intro k; simp; fun_prop

lemma lodge_hol (j : Fin (n+1)) (x : SpacePoints n) (r) :
    Differentiable ℂ (fun p : Times n × ℂ => lodge j x p.1 r p.2) :=
  (laid_hol _).comp (hole_hol j)

end YM.EveryPhase.Stress
