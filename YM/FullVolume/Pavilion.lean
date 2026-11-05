import YM.Extraction.Equicontinuity
import YM.Next.RANK.Bought
import YM.FullVolume.Skein

/-!
# All-p uniform price at generic detector neighborhoods
Swap the Wcmain estimates in E's `comparable` use for the unextracted
ones. Probes from a `Purchases` ticket are COMPLETELY inside the
smallest admitted box as well, so we can buy epsilon-continuity at
these physical neighborhoods before the period. Used only for the
probe lower bounds; no assertion YET about all-position convergence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume
open Function Set Filter MeasureTheory Metric Lattice RG Wilson Extraction Extraction.Lease Difference Gaps Cells Next.Rank.Market Push.RelayDifference
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G:Gauge}{C : Family G} {d k N p n : ℕ} {S : Table C.book} {X:Columns C S d} (T:X.Trials)
structure Booths : Prop where
    bounded k : ∃ A : ℝ, ∀ N p i, ‖T.lift k N p i‖ ≤ A
    fit : ∃ η : ℝ, 0 < η ∧ ∀ k i j a,
        |T.realPlace k i j a| ≤ C.S.a (T.width k)*((2:ℝ)⁻¹-η)
    axis (k i) : T.realPlace k i∈YM.generic _
lemma invested (h:Purchases T):Booths T:=⟨h.bounded,h.fit,h.axis⟩
variable (h:Booths T)

/-- positions on the common covering lattice used in the probe, if present. -/
def loc (k : ℕ) (r:Fin X.amount)(i:Cutoffs) : Positions ((X.row r).extra+1):= if h:T.depth k ≤ i.1 then (fun j => (C.S.toDepth h i.2).count.val • T.mark k r j) else 0
lemma loc_wrap (k : ℕ) (r : Fin X.amount) (i:Cutoffs) (hk:T.depth k ≤ i.1) (j) : wrap (C.side i.1 i.2) (loc T k r i j) = location C.S (T.depth k) i.1 i.2 (T.mark k r j):=by
  rw [loc,location,dif_pos hk, dif_pos hk, Ratio.embed_wrap]
lemma loc_tag (k : ℕ) (r : Fin X.amount) (i:Cutoffs) (hk:T.depth k ≤ i.1) : tag (C.S.a i.1) (loc T k r i) = T.realPlace k r:=by
  ext j a
  let B:=C.S.toDepth hk i.2
  change C.S.a i.1 * (loc T k r i j a : ℤ)=_ --
  rw [loc,dif_pos hk]; change C.S.a i.1 * (((B.count.val • T.mark k r j a:ℤ):ℝ))= C.S.a (T.depth k) * (T.mark k r j a:ℝ)
  rw [nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,←mul_assoc, C.S.embeds_scale B]

-- generic reductions from expand_equivalent, all periods used
private lemma ltd (S : Schedule) (p:ℕ) : 4 ≤ length S p := by
  exact_mod_cast Nat.le_of_dvd (S.period p).property (S.period_four p)
private lemma pod {δ:ℝ}(hv:|δ|<2) (S : Schedule) (p : ℕ) : off S p δ |δ|:= by
  intro u; rw [Real.dist_eq]; rcases lt_trichotomy u 0 with e|e|e
  · have he : (u:ℝ) ≤ -1:= by exact_mod_cast (show u ≤ -1 by omega)
    have hk : (u:ℝ)* length S p ≤ -length S p := by nlinarith [ltd S p]
    grind [ltd]
  · subst u; simp
  have he : (1:ℝ) ≤ u:= by exact_mod_cast (show 1 ≤ u by omega)
  have hk : length S p ≤ (u:ℝ)*length S p:= by nlinarith [ltd S p]
  -- linarith with abs
  grind [ltd]

include h in
lemma arena (k:ℕ) (j : Fin X.amount) : ∃ t r : ℝ, 0<t ∧ 0<r ∧ ∀ x∈closedBall (T.realPlace k j) t,∀ p:ℕ, Gaps.allFine C.S p (4*r) x:= by
  let m := (X.row j).extra+1
  let y:=T.realPlace k j
  obtain ⟨b,hb,hK⟩:=h.fit
  have he i a: |y i a|<1 := by
    have hB:= (hK k j i a)
    have hu := C.S.strictAnti.antitone (Nat.zero_le (T.width k))
    rw [Schedule.a_zero] at hu; change |y i a| ≤_ at hB; nlinarith [C.S.a_pos (T.width k)]
  let v : Set (Points m) := {x|∀ i a, |x i a|<1}
  have hp: v∈𝓝 y:=eventually_all.mpr (fun i=>eventually_all.mpr (fun a=>
    (show Continuous (fun x:Points m=> |x i a|) by fun_prop).continuousAt (x:=y)|>.eventually (gt_mem_nhds (he i a))))
  have hz : generic m ∈ 𝓝 y := (genericOpen _).mem_nhds (h.axis k j)
  obtain ⟨t,ht,hV⟩:= Metric.mem_nhds_iff.mp (inter_mem hp hz)
  let B:= closedBall y (t/2)
  have hU : B ⊆ v ∩ generic m:= (closedBall_subset_ball (half_lt_self ht)).trans hV
  have hB : B ⊆ Cyclic C.S 0 m :=by
    intro x hx; refine (no_wrap_tie C.S ?_).2 ((hU hx).2)
    intro i a; obtain ⟨hf,hd⟩:=abs_lt.mp ((hU hx).1 i a)
    have hh: 1 ≤ C.S.radius 0:= by have hf:=ltd C.S 0; change 4 ≤ ((C.S.period 0).val:ℝ) at hf; unfold Schedule.radius; linarith
    constructor <;> linarith
  obtain ⟨r,hr,H⟩ := Gaps.all C.S 0 (isCompact_closedBall ..) hB
  refine ⟨t/2,r/4,half_pos ht,by positivity,fun x hx p i j h a z=>?_⟩
  have he:= H x hx i j h a 0
  simp at he
  have hp : |distances x i j a|<2:= lt_of_le_of_lt (abs_sub ..) (by linarith only [(hU hx).1 j a,(hU hx).1 i a])
  refine le_trans (le_trans (b:=r) (by linarith) ?_) (pod hp C.S p z); simpa [Real.norm_eq_abs] using he

-- relay step adjacency bounds uniform for every fixed row set bounded
abbrev bookshelf (C:Family G) (m:ℕ):= Fin m→ C.label d

lemma spin_bound (C:Family G) (a:Axis) (b:ℝ) : ∃ D:ℝ,∀ x:C.label d, ‖x‖ ≤ b →
    ‖(C.book.reflectedToken a ⟨d,x⟩).2‖ ≤ D := by
  -- continuous across coefficient norm, use compact image
  let f (x:C.label d): C.label d:= (C.book.reflectedToken a ⟨d,x⟩).2
  have hf:Continuous f:=by
    exact (C.book.mirrorGroup d (Signed.mirror a)).continuous_of_finiteDimensional.comp continuous_star
  obtain ⟨D,hD⟩:= ((isCompact_closedBall (0:C.label d) b).image hf.norm).bddAbove
  exact ⟨D,fun x hx=> hD ⟨x,Metric.mem_closedBall.mpr (by rwa [dist_zero_right]),rfl⟩⟩
lemma provisions (_M: C.Makes)(H: Wcmain C) (m : ℕ) (r : ℝ): ∀ᶠ k in atTop, ∃ A : ℝ, 0≤ A ∧ ∀ᶠ i in mesh,∀ x:Fin m → C.label d,(∀ j,‖x j‖ ≤ r) → Permit (fun j=> (⟨d,x j⟩: C.book.Token)) A k i.1 i.2:=by
  choose D hD using spin_bound (d:=d) C (b:=r)
  obtain ⟨b,hb,hb',hb''⟩:= ((eventually_gt_atTop (0:ℝ)).and ((eventually_ge_atTop r).and (eventually_all.mpr fun a:Axis=>eventually_ge_atTop (D a)))).exists
  obtain ⟨a,ha,hF⟩:= H d b 1 hb zero_lt_one
  filter_upwards [eventually_ge_atTop (C.ref d)] with k hk
  refine ⟨a*C.S.a k^(-(d:ℝ)-1),mul_nonneg ha (Real.rpow_nonneg (C.S.a_pos _).le _),?_⟩
  filter_upwards [deepen.eventually (hF k hk)] with i hi x h
  rintro j w (rfl|⟨s,rfl⟩)
  · exact hi _ (x j) ((h _).trans hb')
  let w:= C.book.reflectedToken s ⟨d,x j⟩; exact hi i.2 (w.2) ((hD s (x j) (h _)).trans (hb'' s))

private theorem norm_tag {m : ℕ} (x y : positions m) (t : ℝ) :
    dist (tag t x) (tag t y) ^ 2 = ∑ i : Fin m × Axis, (t * (x i.1 i.2 - y i.1 i.2 : ℤ))^2 := by
  rw [dist_eq_norm,← Points.flatten.norm_map,EuclideanSpace.real_norm_sq_eq]; simp only [map_sub,PiLp.sub_apply]
  refine Finset.sum_congr rfl fun i _ => ?_; change (_ * _ - _ * _) ^ 2 = _
  simp only [Int.cast_sub,mul_sub]

section
variable {n : ℕ} (x y : positions n)
private def via (s : Finset (Fin n × Axis)) (i : Fin n) (a : Axis) := if (i,a)∈s then x i a else y i a

private lemma replaces (t : ℝ) (s u : Finset (Fin n × Axis)) :
    dist (tag t (via x y s)) (tag t (via x y u)) ≤ dist (tag t x) (tag t y) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).1
  simp_rw [norm_tag]; apply Finset.sum_le_sum; intro p _
  unfold via; split_ifs <;> simp <;> first | rfl | positivity | ring_nf; rfl

private theorem pricing (h : C.Makes) {n : ℕ} (v : Fin (n+1) → C.book.Token)
    {A r t : ℝ} (ha : 0 ≤ A) (hr : 0<r) (K L : Set (Points (n+1))) (p N D : ℕ) (hd : D≤N) (H : Permit v A D N p)
    (he : ∀ y∈L, allFine C.S p (4*r) y) (hv : C.S.a D < r) (Ks : cthickening t K ⊆ L)
    (x y : positions (n+1)) (hy : tag (C.S.a N) y ∈ K)
    (hx : dist (tag (C.S.a N) x) (tag (C.S.a N) y) ≤ min r t) :
    dist (lifted C N p v x) (lifted C N p v y) ≤
      ((n+1:ℕ)* (4:ℝ)) *((A^(n+1)/r)*dist (tag (C.S.a N) x) (tag (C.S.a N) y)) := by
  let a := C.S.a N
  let E := A^(n+1)/r
  let R := dist (tag a x) (tag a y)
  let D' := lifted C N p v
  let W := via x y
  have hb (s u) : dist (tag a (W s)) (tag a (W u)) ≤ R := replaces x y a s u
  have hy' : W ∅=y := by ext; simp [W,via]
  have hR (s) : tag a (W s)∈L := Ks (mem_cthickening_of_dist_le _ _ _ K hy
    ((hy' ▸ hb s ∅ : dist (tag a (W s)) (tag a y) ≤ R).trans (hx.trans (min_le_right ..))))
  have he' : 0≤E := div_nonneg (pow_nonneg ha _) hr.le
  have ht {u v' : Finset (Fin (n+1) × Axis)} (i j l) (hk : W u = advance (W v') i j l) :
      dist (D' (W u)) (D' (W v')) ≤ E*R := by
    apply le_trans (show dist (D' (W u)) (D' (W v')) ≤ E * dist (tag a (W u)) (tag a (W v')) from by
      rw [hk]; refine stepTotal h v ha hr L p N D hd H he hv i j l (W v') (hR v') ?_
      exact hk ▸ (hb u v').trans (hx.trans (min_le_left ..))) (mul_le_mul_of_nonneg_left (hb u v') he')
  have hs (s) : dist (D' (W s)) (D' y) ≤ (s.card:ℝ)*(E*R) := by
    induction s using Finset.induction_on with
    | empty => simp [hy']
    | @insert b s hB ih =>
      obtain ⟨i,j⟩ := b
      rw [Finset.card_insert_of_notMem hB,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm ((s.card:ℝ)*_)]
      refine (dist_triangle _ (D' (W s)) _).trans (add_le_add ?_ ih)
      rcases le_total (x i j) (y i j) with h|h
      · rw [dist_comm]; apply ht i j (y i j-x i j).natAbs
        funext u w
        by_cases hu : u=i
        swap; simp [advance,W,via,hu]
        subst u
        by_cases hw : w=j
        · subst w
          simp only [advance,W,via, Function.update_self, hB,Finset.mem_insert_self, Pi.add_apply,Pi.smul_apply,
            ↓reduceIte, step_apply]; simp [abs_of_nonneg (sub_nonneg.mpr h)]
        · simp [advance,W,via,hw]
      apply ht i j (x i j-y i j).natAbs
      funext u w; by_cases hu : u=i
      · subst u; by_cases hw : w=j
        · subst w; simp [W,via,advance,hB,abs_of_nonneg (sub_nonneg.mpr h)]
        simp [W,via,advance,hw]
      simp [W,via,advance,hu]
  convert hs Finset.univ using 1
  · rw [show W Finset.univ=x by ext; simp [W,via]]
  simp only [Finset.card_univ,Fintype.card_prod,Axis,Fintype.card_fin, Nat.cast_mul,Nat.cast_ofNat];rfl
end

private lemma tax {n : ℕ} (A r T ε : ℝ) (he : ε>0) (hr : 0<r) (hA : 0≤A) (hT : 0<T) :
    ∃ t : ℝ, 0<t ∧ t ≤ min r T ∧ ((↑(n+1:ℕ):ℝ)* (4:ℝ)) * ((A^(n+1)/r)*t) < ε := by
  let L := ((↑(n+1:ℕ):ℝ)* (4:ℝ)) * (A^(n+1)/r)
  have hL : 0≤L := by unfold L; positivity
  let t := min (min r T) (ε/(1+L))
  have ht : 0<t := by unfold t; exact lt_min (lt_min hr hT) (by positivity)
  refine ⟨t,ht,min_le_left ..,?_⟩
  rw [← mul_assoc]
  change L*t<ε
  calc
    _ < (1+L)*t := by linarith
    _ ≤ _ := (le_div_iff₀' (by linarith : 0<1+L)).mp (min_le_right ..)

include h
/-- Uniform local approximation of primary probe evaluations.
Centers near exactly the same grid point even at period 0. -/
lemma lobby (M:C.Makes) (hc : Wcmain C) (k:ℕ) (j : Fin X.amount) (b ε:ℝ)(hε:0<ε):
    let m:=(X.row j).extra+1
    ∃ r : ℝ, 0<r ∧ ∀ᶠ i in FullVolume.mesh, ∀ v:Fin m→ C.label d,(∀ u:Fin m, ‖v u‖ ≤ b) →
      ∀ x, dist (tag (C.S.a i.1) x) (T.realPlace k j) ≤ r → let f (x:Positions m):= Extraction.lifted C i.1 i.2 (fun u=> (⟨d,v u⟩: C.book.Token)) x
      dist (f x) (f (loc T k j i)) < ε:=by
  intro m
  obtain ⟨t,r,ht,hr,hK⟩:= arena T h k j
  obtain ⟨l,⟨A,hA,hc'⟩,hl⟩:= ((provisions (d:=d) M hc m b).and (C.S.shrinks.eventually (gt_mem_nhds hr))).exists
  obtain ⟨u,hu,hU,hv⟩:=tax (n:=(X.row j).extra) A r t ε hε hr hA ht
  refine ⟨u,hu,?_⟩
  let y:=T.realPlace k j
  filter_upwards [hc',deepen.eventually_ge_atTop l,deepen.eventually_ge_atTop (T.depth k)] with i hi H hD v hV x hp
  intro f
  have hx:= loc_tag T k j i hD
  obtain ⟨hr',ht'⟩:=le_min_iff.mp hU
  have he:= pricing (C:=C) M _ hA hr {y} (closedBall y t) _ i.1 l H (hi v hV) (fun x hx => hK x hx i.2) hl (show Metric.cthickening t {y}⊆ Metric.closedBall y t from ?_) x (loc T k j i) (by rw [hx]; exact mem_singleton _) (by rw [hx]; exact hp.trans hU)
  · rw [hx] at he; exact lt_of_le_of_lt he (lt_of_le_of_lt (by gcongr) hv)
  simp [cthickening_singleton y ht.le]
end YM.FullVolume
