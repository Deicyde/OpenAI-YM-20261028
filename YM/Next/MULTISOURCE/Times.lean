import YM.Next.MULTISOURCE.Tariff

/-!
# Reference sizes for mixed and birth ports
-/
set_option autoImplicit false
noncomputable section

namespace YM.Multi.Single

open RG Wilson Lattice Function Filter Finset Source Labels AxisShift Couples MeasureTheory Maquette Work
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {d N p j : ℕ} (H : C.Makes)
include H

lemma source_home (d : ℕ) (o : Site (C.side j p)) : o∈ (C.localSection d).footprint o :=
  mem_image.mpr ⟨0,(H.sections d).anchored,by simp⟩

lemma cache_full (o : Site (C.side N p)) (hx : C.ref d ≤ N) (v : C.label d) (U : Config G (C.side N p)) :
    (cache C v o).full U=(C.S.a N:ℂ)^d*C.O N p v o U := by
  let X := C.localSection d
  let F := C.labels.level d
  let f := C.factory d N p
  let P := C.path.levels.budget N
  let c := (coeff C N p N v).x
  have he : f.terminal.symm v=c := ((H.calibrated d N p hx).bare_coord _).symm
  change c 0 + X.places (F.scaled P.threshold⁻¹ (F.core c)) o U=
    (C.S.a N:ℂ)^d*( ((C.S.a N:ℂ)^d)⁻¹ • (X.places (F.scaled P.threshold⁻¹ (f.terminal.symm v)) o U))
  let g := F.scaled P.threshold⁻¹
  have h1 : c=c 0 • F.e0 + F.core c := by
    funext i; change c i=c 0 * _ + Function.update c 0 0 i
    by_cases h : i=0 <;> simp [h,Frame.e0]
  have hf : X.places (g c) o U=c 0+X.places (g (F.core c)) o U := by
    nth_rw 1 [h1]; rw [map_add, map_smul, F.scaled_unit,SectionData.places,X.eval_linear.map_add]
    simp_rw [X.eval_linear.map_smul]
    change c 0 * X.evaluate _ _ + _= _
    rw [(H.sections d).unit]; change c 0*1+_= _; rw [mul_one]; rfl
  change c 0+X.places (g (F.core c)) o U=(C.S.a N:ℂ)^d*(((C.S.a N:ℂ)^d)⁻¹*_)
  rw [he,← hf,mul_inv_cancel_left₀]
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')

lemma cache_weight (o : Site (C.side N p)) (v : C.label d) :
    Weight (C.path.rep N p N).p (cache C v o).siteSet ((cache C v o).tail (C.path.rep N p N)) :=
  (cache C v o).tail_weight _ ((C.localSection d).placed_local o _) ((C.localSection d).continuous_places _ o).measurable
    ((C.localSection d).placed_invariant (H.sections d) o _)

lemma verify_cache (v : C.label d) (o : Site (C.side N p)) (hx : C.ref d ≤ N)
    (he : room (C.localSection d) ≤ C.path.levels.clock.coverSize N) :
    (cache C v o).Check (C.path.rep N p N) o (C.localSection d).stencil.card (ankle C N p N v) (tariff C N p N v) := by
  let P := C.path.rep N p N; let c := C.path.levels; let S := C.localSection d
  let F := C.labels.level d; let p' := c.budget N
  let x := (coeff C N p N v).x
  obtain ⟨hA,hs,ht⟩ := flows C v N o he
  have hy : P.p=p' := (H.wilson.represents _ _ _ le_rfl).vac
  let r := F.coeffSize x; let g := F.coeffSize (F.core x)
  have hr : 0≤r := G08.size_nonneg ..
  have hg : 0≤g := G08.size_nonneg ..
  have hr' : g ≤ r := G08.size_core ..
  let u := (c.params N).columns
  have hu : 1 ≤ u := (c.params N).columns_ge
  have hb : 1 ≤ stipend C N := stipend_hi C N
  change burn p' _ _ ≤ _ at hs
  change 2*(stipend C N*r*u)≤ _ at hA
  let V := cache C v o
  have hu' := zero_le_one.trans hu
  have he : 0≤stipend C N*r*u := by positivity
  have hl : stipend C N*r*u ≤ tariff C N p N v := (by linarith)
  have hK := G08.size_core F x
  have hh : 0 ≤ upper S := zero_le_one.trans (purposes S 0).1
  have hi : 0 ≤ excess C d N := zero_le_one.trans (excess_one C d N)
  have hj : 0 ≤ ankle C N p N v := by change 0≤upper S * excess C d N*r; positivity
  refine ⟨source_home H d o, Finset.card_image_le,?_, ?_,⟨hj,?_⟩, cache_weight H o v,?_⟩
  · apply le_trans (show ‖x 0‖≤ r from Finset.single_le_sum (f:=fun i => ‖x i‖)
      (fun i _ => norm_nonneg _) (mem_univ 0))
    exact le_trans (le_trans (le_mul_of_one_le_left hr hb)
      (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hb) hr) hu)) hl
  · change Banked P.p _ _ (masked P.p.threshold (S.footprint o) V.seen) _
    rw [hy]
    have hp (i : F.Index) := H.priced d N p hx o i
    refine (saves S o p' u 2 (F.core x) (source_home H d o) (by positivity) hp).enlarge ?_
    change _*u*g ≤ _
    rw [mul_right_comm _ u g]
    apply le_trans _ hl
    gcongr
  · intro i
    have hI : ‖V.seen i‖ ≤ ankle C N p N v :=
      (maximum S _ (potential_hat c N).1 p' (potential_hat c N).2 o (F.core x) i).trans
        (mul_le_mul_of_nonneg_left hr' (mul_nonneg hh hi))
    change ‖V.full i - V.cheek P i‖ ≤ _
    by_cases h : Healthy P.p.threshold V.siteSet i
    · simp only [Vessel.cheek,Vessel.full, masked_eq _ _ _ _ h,sub_self,norm_zero]; exact hj
    simpa only [Vessel.cheek,Vessel.full, masked_ne _ _ _ _ h,add_zero,add_sub_cancel_left] using hI
  change liftFee _ * (burn P.p _ _ * _) ≤ _
  rw [hy]; apply le_trans _ ht
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs hj)
    (lift_pos _).le

lemma origin_price (v : C.label d) (hx : C.ref d ≤ j) (hk : j≤N)
    (he : room (C.localSection d) ≤ C.path.levels.clock.coverSize j) (p : ℕ) :
    Credit (C.path.rep N p j).p 0 (money C.path.levels j) {0} (BranchOne.center
      (coeff C N p j v) (C.localSection d) 0 (C.path.rep N p j)) (tariff C N p j v) := by
  let F := C.labels.level d; let f := C.localSection d; let P := C.path.rep N p j; let c := coeff C N p j v; let r := C.path.levels
  obtain ⟨hg,hs,-⟩ := flows C v N (0 : Site (C.side j p)) he
  have hp : P.p=r.budget j := (H.wilson.represents _ _ _ hk).vac
  let a := F.coeffSize c.x; let b := F.coeffSize (F.core c.x)
  let u := (r.params j).columns
  have ha : 0≤a := G08.size_nonneg ..
  have hb : 0≤b := G08.size_nonneg ..
  have hh : b ≤ a := G08.size_core ..
  let w := stipend C j
  have hf : 1≤w := stipend_hi ..
  change 2*(w*a*u) ≤ tariff .. at hg
  have hu : 1≤u := (r.params j).columns_ge
  have hu' := zero_le_one.trans hu
  have he : 0≤w*a*u := by positivity
  have hl := H.calibrated d N p (hx.trans hk)
  have hw : u*b ≤ w*a*u := calc
    _ ≤ u*a := by gcongr
    _ ≤ w*a*u := by rw [mul_comm u]; gcongr; exact le_mul_of_one_le_left ha hf
  refine BranchOne.costs _ _ _ C.params (hl.format _ hx hk _) (hh:=hl.cap _ hx hk _) _ (w*a*u) ?_ ?_ ?_ ?_
  · apply le_trans (show ‖c.x 0‖ ≤ a from Finset.single_le_sum (f:=fun i => ‖c.x i‖)
      (fun i _ => norm_nonneg _) (mem_univ 0))
    exact (le_trans (le_mul_of_one_le_left ha hf) (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hf) ha) hu)).trans (by linarith)
  · change Banked P.p _ _ (masked P.p.threshold _ (f.places (F.scaled P.p.threshold⁻¹ (F.core c.x)) 0)) _
    rw [hp]
    obtain hz := saves f 0 (r.budget j) u 0 (F.core c.x) (source_home H d (p:=p) (j:=j) 0) le_rfl (H.priced d j p hx 0)
    apply hz.enlarge
    change burn _ 0 _ *u*b ≤ _
    rw [mul_right_comm _ u b]
    apply mul_le_mul_of_nonneg_right _ hu'; apply mul_le_mul _ hh hb (by linarith : 0≤w)
    apply le_trans _ hs; apply Real.exp_monotone
    gcongr; try norm_num
  · change u*b+_ ≤ _
    linarith
  change u*b ≤ _
  linarith
end YM.Multi.Single
