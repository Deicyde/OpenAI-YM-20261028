import YM.Next.FOUNDATIONS.Regular
import YM.Push.RELAY_MARK.Dollar

/-!
# Dollar budget on actual primaries (thus also the chosen equation fields)

Cf. : no separate remainder
purchases for subtraction of *our* equation cylinder. It is this
primary. Nevertheless show from `dollar` top-coordinate cost that,
undoing the physical units, one gets proper weighted upper bounds at ANY
origin and full-group sup price there. Include the real production
format/remainder and scale explicitly (same chosen calibration at 0), in
case of transfer etc. uses en route to RPrep.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function Set MeasureTheory Filter Labels Wilson Source Lattice RG Bid Next.Foundations
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {d N p : ℕ}

lemma normal (x : Rowe C d) (N p : ℕ) (o) :
    ((C.S.a N:ℂ)^d) • upper C x N p o=(C.localSection d).places (writing C d x (N,p)) o := by
  have hh : ((C.S.a N:ℂ)^d)≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
  rw [upper, Family.O, TransferData.cylinder, initial, smul_smul, mul_inv_cancel₀ hh,one_smul]; rfl

lemma primary_priced (h : C.Makes) (i : ℕ) (N p : ℕ) (hh : C.ref i≤N) (x : (C.labels.level i).Coeff)
    (o : Site (C.side N p)) :
    let T := C.localSection i
    let B := C.labels.level i
    let P := C.path.levels.budget N
    P.Regular (T.footprint o) (T.places x o) ∧ P.supBounds o (T.footprint o) (T.places x o)
      ((C.path.levels.params N).columns * B.coeffSize (tied C i N x)) := by
  -- similar to combination_bound in Foundations, but just uses Makes
  classical
  intro T B P
  let L : B.Coeff →ₗ[ℂ] Config G (C.side N p) → ℂ := {
    toFun v := T.places v o
    map_add' a b := funext fun U=> congr_fun (T.eval_linear.map_add a b) _
    map_smul' a b := funext fun U=> congr_fun (T.eval_linear.map_smul a b) _ }
  let u := (C.path.levels.params N).columns
  have he : T.places x o=∑ j:B.Index,x j • L (Pi.single j 1) := by
    change L x=_
    simp_rw [← map_smul,← map_sum]; apply congr_arg L; funext b; simp [Pi.single_apply]
  have hu (j : B.Index) : u * ‖(tied C i N x) j‖ = ‖x j‖ * (u*P.threshold^(B.grades j).2) := by
    change u*‖B.scaled P.threshold x j‖=_
    rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg P.threshold_pos.le _)]
    ring
  rw [he]; unfold Frame.coeffSize
  rw [Finset.mul_sum]; unfold u at hu; simp_rw [hu]
  exact regular_bound_sum _ _ _ fun j _ =>
    ⟨regular_smul _ (h.priced i N p hh o j).1,bound_smul _ (h.priced i N p hh o j).2⟩

lemma size_le (B : Frame G d) (x : B.Coeff) : B.coeffSize x ≤ (Fintype.card B.Index:ℝ)*‖x‖ := by
  simpa only [Frame.coeffSize,nsmul_eq_mul] using Pi.sum_norm_apply_le_norm (G:=fun _ : B.Index=>ℂ) x
lemma non_scalar (B : Frame G d) (x : B.Coeff) : B.coeffSize (B.core x) ≤ B.coeffSize x := by
  unfold Frame.coeffSize
  refine Finset.sum_le_sum fun i hi=>?_
  by_cases h : i=0 <;> simp [h,Frame.core]
lemma counted_cost (h : C.Makes) (x : Rowe C d) (hn : C.ref d ≤ N) :
    let v := (C.factory d N p).terminal.symm (x (N,p))
    ∀ o : Site (C.side N p),let f := ((C.S.a N:ℂ)^d) • upper C x N p o
                         let Y := (C.localSection d).footprint o
                         let P := C.path.levels.budget N
                         P.Regular Y f ∧ P.supBounds o Y f ((C.path.levels.params N).columns * (C.labels.level d).coeffSize v) := by
  dsimp only; intro o; rw [normal]
  have he := primary_priced h d N p hn (writing C d x (N,p)) o
  dsimp only at he
  rw [writing,LinearEquiv.apply_symm_apply] at he; exact he

lemma cover_cost (C : Family G) (d : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x : Rowe C d, ∀ (N p : ℕ) (o : Site (C.side N p)) U,
    ‖(((C.S.a N:ℂ)^d) • upper C x N p o) U‖ ≤ D*‖writing C d x (N,p)‖ := by
  classical
  let B := C.labels.level d
  let L := ((C.localSection d).eval_linear).mk' _
  choose K hK using fun i:B.Index=> ((C.localSection d).continuous_evaluate (Pi.single i 1)).bounded_above_of_compact_support
    (HasCompactSupport.of_compactSpace _)
  have ht i : 0≤K i := (norm_nonneg _).trans (hK i 1)
  refine ⟨∑ i,K i, Finset.sum_nonneg fun i _=> ht i,fun x N p o U=>?_⟩
  rw [normal];
  let v := writing C d x (N,p)
  change ‖L v (expandAt o U)‖ ≤ _
  rw [show L v=∑ j:B.Index,v j • L (Pi.single j 1) by
    simp_rw [← map_smul, ← map_sum]; apply congr_arg L; funext i; simp [Pi.single_apply],Finset.sum_apply,Finset.sum_mul]
  apply le_trans (norm_sum_le ..)
  refine Finset.sum_le_sum fun i hi=> ?_
  rw [Pi.smul_apply,norm_smul, mul_comm]
  exact mul_le_mul (hK ..) (norm_le_pi_norm v i) (norm_nonneg _) (ht _)

/-- Budget includes actual Based format at origin and credit on inserted
expression at each offset. `Sized` also checks it is the origin entry
before any taking of transfer. -/
structure Sized (C : Family G) (d : ℕ) (x : Rowe C d) (D : ℕ → ℕ → ℝ) (F : Extraction.Order) : Prop where
  fee : Score C.S F (Function.uncurry D)
  top : F.late fun N p=>
    let T := C.factory d N p
    let P := C.path.rep N p N
    let v := T.terminal.symm (x (N,p))
    let A := T.entries N v
    (C.labels.level d).coeffSize A.x ≤ D N p ∧
     A.Format 0 C.params P ∧ A.remBound 0 P (Real.sqrt (C.path.levels.clock.forcedAllowance N)) (D N p) ∧
     (A.density 0 (C.localSection d) P = fun U=> ((C.S.a N:ℂ)^d) * (((bare (C.beta N p) U):ℝ):ℂ) * upper C x N p 0 U) ∧
     ∀ o, let B := C.path.levels.budget N
          let f := ((C.S.a N:ℂ)^d) • upper C x N p o
          let Y := (C.localSection d).footprint o
          Reads C.params o Y ((C.labels.level d).coords.symm (writing C d x (N,p))) f ∧
          B.Regular Y f ∧ B.supBounds o Y f (D N p) ∧ ∀ U, ‖f U‖ ≤ D N p

lemma grow_rem {R : Frame G d} {V : Coefficient R (C.side N p)} {o a x y} {P : Rep G (C.side N p)} (h : V.remBound o P a x)
    (he : x ≤ y) : V.remBound o P a y := by
  obtain ⟨b,c,hb,hc,ha,hv,hf⟩ := h; exact ⟨b,c,hb,hc,ha.trans he,hv,hf⟩

lemma grow_pre {n : Side} {o : Site n} {P : BudgetPoint} {s : Support n} {f : Config G n→ℂ} {x y}
    (h : P.supBounds o s f x) (he : x≤y) : P.supBounds o s f y :=
    ⟨h.1.trans he, fun u hu l hl hD=> (h.2 u hu l hl hD).trans he⟩

theorem sizable (h : C.Makes) (x : Rowe C d) (he : dollar C F x) : ∃ D, Sized C d x D F := by
  classical
  obtain ⟨K,hK,hY⟩ := cover_cost C d
  let B := C.labels.level d
  let W (j : ℕ×ℕ) := (C.factory d j.1 j.2).terminal.symm (x j)
  let Z (j : ℕ ×ℕ) := (C.path.levels.params j.1).columns * B.coeffSize (W j)
  let S (j : ℕ ×ℕ) := K*‖writing C d x j‖
  have hS : Score C.S F S := (Score.const C.S F K).mul ((dollar_iff x).1 he) (Eventually.of_forall fun _=> norm_nonneg _)
  have hz (j) : 0≤ B.coeffSize (W j) := Finset.sum_nonneg fun i _=> norm_nonneg _
  have hh (j : ℕ × ℕ) : B.coeffSize (W j) ≤ Z j := le_mul_of_one_le_left (hz _) (C.path.levels.params _).columns_ge
  have hZ : Score C.S F Z := by
    have hm := ((Score.const C.S F (Fintype.card B.Index : ℝ)).mul ((accounting x).mp he) (Eventually.of_forall fun _=> norm_nonneg _))
    exact (columns_paid C F).mul (hm.easier (Eventually.of_forall fun j=> size_le B (W j))) (Eventually.of_forall hz)
  refine ⟨fun N p=> Z (N,p)+S (N,p),hZ.add hS,?_⟩
  apply Eventually.of_forall; intro p
  filter_upwards [F.mesh.cofinal.eventually_ge_atTop (C.ref d)] with j hj
  let N := F.mesh j
  let p' := F.per p
  let P := C.path.rep N p' N
  let v := W (N,p')
  let T := C.factory d N p'
  let Q := T.entries N v
  have ht := h.calibrated d N p' hj
  let D := Z (N,p')+S (N,p')
  have hk : Z (N,p') ≤ D := le_add_of_nonneg_right (mul_nonneg hK (norm_nonneg _))
  have hC := ht.cap N hj le_rfl v
  rw [ht.bare_coord] at hC
  refine ⟨?_,ht.format _ hj le_rfl _,grow_rem (C:=C) (N:=N) (p:=p') hC (?_ : _ ≤ D), ?_,fun o=>?_⟩
  · rw [ht.bare_coord]; exact (hh (N,p')).trans hk
  · apply le_trans ?_ hk
    exact mul_le_mul_of_nonneg_left (non_scalar B v) (le_trans zero_le_one (C.path.levels.params _).columns_ge)
  · funext U; rw [ht.encode,(h.wilson.starts N p').2]; rfl
  dsimp only
  have hp := counted_cost h x (p:=p') hj o
  refine ⟨?_,hp.1,grow_pre hp.2 hk,fun U=> (hY x N p' o U).trans (le_add_of_nonneg_left ((hz (N,p')).trans (hh (N,p'))))⟩
  rw [normal]
  exact placed_reads _ o (h.places d N p' hj) (h.sections d) _
end YM.Push.Mark
