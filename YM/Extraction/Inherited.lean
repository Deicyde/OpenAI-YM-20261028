import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Cells.Transforms
import YM.Euclid.Differential
import YM.TimeKernel.Trace




/-!
# Symmetries, including all points from generic port

Use actual k-grid tests on the common hierarchy. Raw proof needs generic
witness with S smooth on conf. RP treated separately because point words +
reflection have intrinsic ties.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Filter Set Cells Lattice Wilson MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge}
namespace Order
variable {C : Family G} {f : Order} {n : ℕ}

/-- Useful consequence (not definition of two limits!) -/
def fuse (f : Order) : Filter (ℕ × ℕ) := Filter.map (fun i : ℕ × ℕ => (f.mesh i.2, f.per i.1)) (atTop.curry atTop)
@[simp] lemma fused (f : Order) (h : ℕ×ℕ → Prop) : (∀ᶠ x in f.fuse, h x) ↔ f.late (fun i j => h (i,j)) := Iff.rfl
instance (f : Order) : NeBot f.fuse := by
  constructor; intro h
  have he : ∀ᶠ (_ : ℕ×ℕ) in f.fuse, False := h.symm ▸ (by simp); rw [fused,late] at he
  obtain ⟨_,ht⟩ := he.exists; obtain ⟨_,H⟩ := ht.exists; exact H

lemma along {Y : Type*} [TopologicalSpace Y] {p L} {y : Y} (h : f.limits p L y) : Tendsto (fun c : ℕ × ℕ => L c.1 c.2)
    f.fuse (𝓝 y) := by
  rw [tendsto_def]
  intro s hs; exact neighborhood h hs

lemma inPatch {S : Table C.book} (h : f.PointLimits C S) (k : ℕ) (x : Fin n → Cover) (hp : tag (C.S.a k) x ∈ generic n)
    (v : Fin n → C.book.Token) : Tendsto (fun j : ℕ × ℕ => C.numeric j.1 j.2 v (fun i => location C.S k j.1 j.2 (x i))) f.fuse
      (𝓝 (S.read (tag (C.S.a k) x) v)) := by
  change Tendsto _ f.fuse (𝓝 (S.read (Order.grid C k x) v))
  refine along (L := fun N p => C.numeric N p v (fun i => location C.S k N p (x i))) (p := fun p => Order.grid C k x∈Cyclic C.S p n) ?_
  exact Cells.eventual_grid C f S (k := k) h x (show grid C k x∈generic n from hp) v
lemma witnesses (v : Fin n → C.book.Token) (f : Order) : ∀ᶠ i in f.fuse, C.sufficient i.1 v := by
  rw [fused,late]; exact Eventually.of_forall fun _ => eventually_all.mpr (fun i => f.mesh.cofinal.eventually (eventually_ge_atTop (C.ref (v i).1)))

lemma equal {n : ℕ} {K P : Points n → ℂ} (hk : ContinuousOn K (conf n)) (hp : ContinuousOn P (conf n))
    (H : EqOn K P (generic n)) : EqOn K P (conf n) := by
  have he : K =ᵐ[volume.restrict (conf n)] P := ae_restrict_of_ae ((almostGeneric n).mono fun x hx => H hx)
  exact MeasureTheory.Measure.eqOn_of_ae_eq he hk hp (by rw [(conf_open _).interior_eq]; exact subset_closure)

private lemma denseGrid (S : Schedule) {n} {K P : Points n → ℂ} (hk : ContinuousOn K (generic n))
    (hp : ContinuousOn P (generic n))
    (H : ∀ (k : ℕ) (x : Fin n → Cover), tag (S.a k) x ∈ generic n → K (tag (S.a k) x) = P (tag (S.a k) x)) : EqOn K P (generic n) := by
  intro x hx; have ht := chosen (S := S) x; have he := ht.eventually ((genericOpen n).mem_nhds hx)
  have hK := (hk x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht,he⟩)
  have hP := (hp x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht,he⟩)
  exact tendsto_nhds_unique (hK.congr' (he.mono fun i hi => H i _ hi)) hP

lemma nearGeneric {n} (a : E4) {x : Points n} (h : x∈generic n) : Points.across a x∈generic n := by
  intro b i j hi; exact h b (add_right_cancel (show _ + a b = _ + a b from hi))

lemma upward {n : ℕ} (u : E4) : Continuous (Points.across u (n := n)) := by
  let z := points fun _ : Fin n => u
  exact show Continuous (fun x : Points n => x + z) from continuous_id.add continuous_const


private lemma trans_grid (t : E4) (S : Schedule) : ∃ b : ℕ → Cover,
    Tendsto (fun i => S.gridPoint i (b i)) atTop (𝓝 t) := by
  let x : Points 1 := points fun _ => t
  let b := fun i => address (S.a i) x
  have ht := chosen (S := S) x
  exact ⟨fun i => b i 0,(show Continuous (fun x : Points 1 => x 0) from by fun_prop).continuousAt.tendsto.comp ht⟩

lemma location_add (S : Schedule) (p k) {N : ℕ} (x y : Cover) :
    location S k N p (x+y)=location S k N p x + location S k N p y := by
  unfold location
  split
  · rw [map_add]; exact (Ratio.root _).map_add ..
  simp

lemma homogeneous {S : Table C.book} (H : C.Makes) (h : S.Smooth) (he : f.PointLimits C S) : S.Homogeneous := by
  intro n x hx s v
  let F (x : Points n) := S.read x v
  have ht : ContinuousOn F (conf n) := (S.smooth_read h v).continuousOn
  have hb : ContinuousOn (F ∘ Points.across s) (conf n) := ht.comp (upward s).continuousOn (fun _ hg => Points.across_in _ hg)
  apply equal hb ht _ hx
  obtain ⟨o,ho⟩ := trans_grid s C.S
  intro t hq; let c (k) := address (C.S.a k) t; let y (k) := tag (C.S.a k) (c k)
  let u (k) := Points.across (C.S.gridPoint k (o k)) (y k)
  have hY : Tendsto y atTop (𝓝 t) := chosen ..
  have hX : Tendsto u atTop (𝓝 (Points.across s t)) := by
    have hv := ho
    let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
    exact L.symm.continuous.continuousAt.tendsto.comp (show Tendsto (fun k => L (u k)) atTop (𝓝 (L (Points.across s t)))
      from tendsto_pi_nhds.mpr fun k => (show Tendsto (fun i => y i k) atTop (𝓝 (t k)) from
        (show Continuous (fun s : Points n => s k) by fun_prop).continuousAt.tendsto.comp hY).add hv)
  have hy := hY.eventually ((genericOpen n).mem_nhds hq)
  have hc := ht (Points.across s t) (generic_conf _ (nearGeneric s hq)) |>.tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hX,(hX.eventually ((conf_open _).mem_nhds (generic_conf _ (nearGeneric s hq))))⟩)
  have hh := ht t (generic_conf _ hq) |>.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hY,hy.mono fun _ p => generic_conf _ p⟩)
  apply tendsto_nhds_unique (hc.congr' _) hh
  filter_upwards [hy] with i hi
  change S.read (u i) v = S.read (y i) v
  let w := fun j => c i j + o i
  have hv : u i=tag (C.S.a i) w := by
    ext1 j; ext a
    simp [u,y,w,Points.across,c,tag,Schedule.gridPoint, mul_add]
  rw [hv]; apply tendsto_nhds_unique ((inPatch he i w (hv ▸ nearGeneric _ hi) v).congr' _) (inPatch he i (c i) hi v)
  exact (witnesses v f).mono fun (k,r) ht => show _ from by
    simp only [w, location_add]; exact C.anchored H v ht (location C.S i k r (o i)) _

lemma location_s (S : Schedule) (p k N) (u : Cover) (s : Signed) : location S k N p (s.act u) = s.act (location S k N p u) := by
  unfold location; split
  · rw [← wrap_signed,Ratio.signed]
  simp
lemma mirrorG (s : Signed) {n : ℕ} {x} (h : x∈ generic n) : Points.move s.ortho x∈ generic n := by
  intro a i j hs; obtain ⟨b,rfl⟩ := s.perm.surjective a
  simp [Signed.ortho_move] at hs; split at hs
  · exact h b (neg_injective hs)
  exact h b hs

lemma spin {S : Table C.book} (H : C.Makes) (h : S.Smooth) (he : f.PointLimits C S) : S.RealSpin := by
  constructor
  · intro n t x hx v
    let K (y : Points n) := S.read y v; let P (y : Points n) := S.read (Points.move t.ortho y) (C.book.move t ∘ v)
    have hv : ContinuousOn K (conf n) := (S.smooth_read h v).continuousOn
    have hh : ContinuousOn P (conf n) := ((S.smooth_read h _).continuousOn).comp (show Continuous
      (Points.move (n := n) t.ortho) by
        let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)
        exact L.symm.continuous.comp (show Continuous (fun y : Points n => fun i => t.ortho.motion (y i)) from
          continuous_pi fun i => (t.ortho.motion.continuous.comp (show Continuous (fun y : Points n => y i) from by fun_prop)))).continuousOn (fun _ hb => Points.move_in _ hb)
    apply equal hh hv _ hx; apply denseGrid C.S (hh.mono (generic_conf n)) (hv.mono (generic_conf _)); intro k p hg
    have hs : Points.move t.ortho (tag (C.S.a k) p)=tag (C.S.a k) (t.act ∘ p) := by
      ext1 i; ext a; obtain ⟨b,rfl⟩ := t.perm.surjective a; simp [tag,Signed.ortho_move]
    unfold P; rw [hs]; apply tendsto_nhds_unique ((inPatch he k (t.act ∘ p) (hs ▸ mirrorG t hg) _).congr' _) (inPatch he k p hg v)
    refine (witnesses v f).mono fun (N,r) hW => ?_
    dsimp only [Function.comp_apply] -- maybe change
    have hx := C.oriented H v hW t 0 (fun j => location C.S k N r (p j))
    simpa only [location_s,Function.comp_def, affine, add_zero] using hx
  intro n x hx v
  let P (y : Points n) := S.read y (C.book.conjugate ∘ v); let F (x : Points n) := S.read x v
  have hc : ContinuousOn P (conf n) := (S.smooth_read h _).continuousOn
  have hf : ContinuousOn (fun x => star (F x)) (conf n) := (S.smooth_read h v).continuousOn.star
  apply equal hc hf _ hx
  apply denseGrid C.S (hc.mono (generic_conf _)) (hf.mono (generic_conf _)); intro k p hg
  apply tendsto_nhds_unique ((inPatch he k p hg (C.book.conjugate ∘ v)).congr' _) (inPatch he k p hg v).star
  exact (witnesses v f).mono fun (N,r) ht => C.real_eval H v ht _

lemma limits_basic {S : Table C.book} (H : C.Makes) (h : S.Smooth) (he : f.PointLimits C S) : S.Basic := by
  have hp : S.Symmetric := ⟨fun {n} r x hx v => by
    let K (x : Points n) := S.read x v; let P (x : Points n) := S.read (Points.rearrange r x) (v ∘ r)
    have hc : ContinuousOn K (conf n) := (S.smooth_read h _).continuousOn
    have hy : ContinuousOn P (conf n) := (S.smooth_read h _).continuousOn.comp (Points.arrangeL r).continuous.continuousOn
      (fun _ h => Points.rearrange_in _ h)
    apply equal hy hc _ hx; apply denseGrid C.S (hy.mono (generic_conf _)) (hc.mono (generic_conf _)); intro k b hu
    have hv : tag (C.S.a k) (b ∘ r) ∈ generic _ := fun a => (show Injective _ from hu a).comp r.injective
    apply tendsto_nhds_unique ((inPatch he k (b ∘ r) hv (v ∘ r)).congr' _) (inPatch he k b hu v)
    refine Eventually.of_forall fun (N,p) => ?_
    dsimp only
    rw [C.num,C.num]
    exact integral_congr_ae (Eventually.of_forall fun x => Equiv.prod_comp r (fun i => C.seen (v i) (location C.S k N p (b i)) x))⟩
  constructor
  · exact hp
  · intro v x
    let u : Fin 0→Cover := Fin.elim0
    have ht : x=tag (C.S.a 0) u := Subsingleton.elim _ _
    rw [ht]
    have H := inPatch he 0 u (fun _ _ _ _ => Subsingleton.elim _ _ ) v
    apply tendsto_nhds_unique H
    have he (N p) : C.numeric N p v (fun i => location C.S 0 N p (u i)) = 1 := by rw [C.num]; simp
    simp_rw [he]; exact tendsto_const_nhds
  intro n x hx d v
  let u := Fin.cons (C.book.one d) v (α := fun _ => C.book.Token)
  have ht : ContinuousOn (fun (x : Points (n+1)) => S.read (Points.tail x) v) (conf (n+1)) := (S.smooth_read h v).continuousOn.comp
    (show Continuous (Points.tail (n := n)) from by
      let F : Points (n+1)→L[ℝ] Points n := LinearMap.toContinuousLinearMap
        { toFun := Points.tail, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      exact F.continuous).continuousOn (fun _ hx => Points.tail_in hx)
  apply equal (S.smooth_read h u).continuousOn ht _ hx; apply denseGrid C.S ((S.smooth_read h u).continuousOn.mono (generic_conf _)) (ht.mono (generic_conf _)); intro k z hg
  have hv : tag (C.S.a k) (Fin.tail z) ∈ generic n := fun a => (show Injective _ from hg a).comp (Fin.succ_injective n)
  apply tendsto_nhds_unique ((inPatch he k z hg u).congr' _) (inPatch he k (Fin.tail z) hv v)
  refine (witnesses u f).mono fun (N,p) hh => ?_
  have hw : C.ref d ≤ N := hh 0
  -- unit deletion at literal cylinder
  dsimp only
  rw [C.num,C.num]
  apply integral_congr_ae
  filter_upwards with i
  rw [Fin.prod_univ_succ]
  rw [show C.seen (u 0) (location _ _ N p (z 0)) = _ from C.constant H (p := p) d hw _]
  simp only [Pi.one_apply,one_mul];rfl
end Order
end YM.Extraction
