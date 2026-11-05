import YM.Push.LOCAL_SPLITTING.Merge

/-!
# Covariance of source decomposition data on an actual activity Moves

Transport the given `Coefficient` and every support/mask through affine
signed lattice automorphisms. Retain ordered-derivative/cover prices, no
independent readout. The push covariance compares *whole* matched
transformations on adjacent levels, not arbitrary reblocking at a new origin.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local
open Function Filter Lattice Wilson RG Source Labels MeasureTheory Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

section Principal
variable (W : PathData G) (b : Site n) (c : Clip) (B : BudgetPoint)

theorem expand_translate (x b : Site n) (U : Config G n) : expandAt x (translate b U) = expandAt (x+b) U := by
  funext i; simp only [expandAt,translate,add_assoc]

private def shift (b : Site n) : Equiv.Perm (Face (Per n)) := (Equiv.addRight b).prodCongr (Equiv.refl _)

private theorem face_translate (U : Config G n) (p : Face (Per n)) (b : Site n) : faceValue (translate b U) p = faceValue U (shift b p) := by
  rw [← pull_one,faceValue, travel_pull,faceValue]; simp [shift,affine]

private theorem base_translate (U : Config G n) (p : Face (Per n)) : W.baseTerm c B (translate b U) p = W.baseTerm c B U (shift b p) := by
  have he : W.ell (translate b U) p = W.ell U (shift b p) := by unfold PathData.ell PathData.ellTerms Slot.atSite; simp [expand_translate,shift]
  have hk : PathData.kept c B.threshold (p.1+b) U ↔ PathData.kept c B.threshold p.1 (translate b U) := by
    unfold PathData.kept; rw [← (shift b).forall_congr_right]; simp_rw [face_translate,show ∀ q, (shift b q).1 = q.1+b from fun _ => rfl,separation_translate]
  unfold PathData.baseTerm; rw [face_translate,he,hk.symm]; rfl

theorem masked_pull {Z : Type*} [Zero Z] (s : Signed) (b : Site n) (U : Config G n) (f : Config G n → Z) (X : Support n) (t : ℝ) :
    masked t X f (pull s b U) = masked t (X.image (turnSites s b)) (f ∘ pull s b) U := by
  by_cases h : Healthy t X (pull s b U)
  · rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ ((healthy_pull ..).2 h)]; rfl
  rw [masked_ne _ _ _ _ h, masked_ne _ _ _ _ (mt (healthy_pull ..).1 h)]

private theorem atom_translate {k : ℕ} (a : Atom G k) (U : Config G n) (x : Site n) : a.placed B (translate b U) x = a.placed B U (x+b) := by
  rw [Atom.placed, ← pull_one, masked_pull]
  rw [show (a.footprint x).image (turnSites (1 : Signed) b) = a.footprint (x+b) by unfold Atom.footprint; simp [Finset.image_image,comp_def,show ⇑(turnSites (1:Signed) b) = affine 1 b from rfl,affine,add_assoc], show ((fun V => a.unmasked V x) ∘ pull 1 b : Config G n → ℝ) = fun V => a.unmasked V (x+b) from funext fun V => by simp [comp_apply,pull_one,Atom.unmasked,Slot.atSite,expand_translate]]; rfl

private theorem series_translate {k : ℕ} (a : ℕ → Atom G k) (U : Config G n) (x : Site n) : PathData.atomSeries a B (translate b U) x = PathData.atomSeries a B U (x+b) :=
  tsum_congr fun _ => atom_translate b B _ _ _

private theorem principal_translate (U : Config G n) (β : ℝ) : W.principal c B β (translate b U) = W.principal c B β U := by
  unfold PathData.principal; simp only [base_translate,series_translate, Equiv.sum_comp (shift b)]
  rw [← Equiv.sum_comp (Equiv.addRight b) (fun x : Site n => PathData.atomSeries W.cubic B U x + PathData.atomSeries W.quartic B U x), ← Equiv.sum_comp (Equiv.addRight b) (fun x : Site n => PathData.atomSeries W.loop B U x)]
  rfl

theorem channels_pull (s : Signed) (U : Config G n) (β : ℝ) : W.inChannels c B β (pull s b U) = W.inChannels c B β U := by
  have he (q : Signed) : W.principal c B β (pull q 0 (pull s b U)) = W.principal c B β (pull (s*q) 0 U) := by
    rw [pull_pull]
    have hb := (s*q).act_inv b
    rw [show pull (s*q) (affine s b 0) U = translate ((s*q)⁻¹.act b) (pull (s*q) 0 U) from Eq.symm (by rw [← pull_one,pull_pull,mul_one]; simp only [affine,hb,Signed.act_zero,zero_add,add_zero])]
    rw [principal_translate]
  unfold PathData.inChannels; simp_rw [he]; exact congr_arg _ (Equiv.sum_comp (Equiv.mulLeft s) (fun q => W.principal c B β (pull q 0 U)))
end Principal

section Moves
variable {R : Rep G n} {o : Site n} {s : Signed} {b : Site n} (m : R.activities.Moves s b)

theorem admissible_map (q : Finset ℕ) (U : Config G n) :
    R.activities.admissible R.p U (q.map m.kp.toEmbedding) ↔ R.activities.admissible R.p (pull s b U) q := by
  let r := turnSites s b
  have hf (i j) : Disjoint (patch R.activities (m.kp i)) (patch R.activities (m.kp j)) ↔ Disjoint (patch R.activities i) (patch R.activities j) := by rw [patch,patch,m.forced_support,m.forced_support]; exact Finset.disjoint_image r.injective
  have hi : (q.map m.kp.toEmbedding).biUnion (flagsFor R.activities) = (q.biUnion (flagsFor R.activities)).image r := by
    ext x; simp only [Finset.mem_biUnion, Finset.mem_image,Finset.mem_map, Equiv.coe_toEmbedding]; constructor
    · rintro ⟨_,⟨j,hj,rfl⟩,hx⟩; rw [flagsFor,m.forced_inventory] at hx; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx; exact ⟨y,⟨j,hj,hy⟩,rfl⟩
    rintro ⟨y,⟨j,hj,hy⟩,rfl⟩; exact ⟨m.kp j,⟨j,hj,rfl⟩,by rw [flagsFor,m.forced_inventory]; exact Finset.mem_image_of_mem _ hy⟩
  unfold Activities.admissible; refine and_congr ⟨fun h i hi j hj hN => ?_,fun h i hi j hj hN => ?_⟩ ?_
  · exact (hf i j).1 (h (Finset.mem_map_of_mem _ hi) (Finset.mem_map_of_mem _ hj) (m.kp.injective.ne hN))
  · obtain ⟨i,hi',rfl⟩ := Finset.mem_map.mp hi; obtain ⟨j,hj',rfl⟩ := Finset.mem_map.mp hj
    exact (hf ..).2 (h hi' hj' (fun he => hN (he ▸ rfl)))
  rw [hi,← Work.H03.flags_send s b]; exact (Finset.image_injective r.injective).eq_iff

include m in
theorem exponent_pull (U : Config G n) : R.exponent (pull s b U) = R.exponent U := by
  unfold Rep.exponent Activities.additive; rw [channels_pull]; conv_rhs => rw [← m.ep.tsum_eq (fun i => R.activities.regularOccurrence R.p i U)]
  congr 1; exact tsum_congr fun i => by
    simp only [Activities.regularOccurrence,m.reg_support,masked_pull s b U]; rw [show R.activities.E (m.ep i) = R.activities.E i ∘ pull s b from funext fun U => m.valuesE i U]; rfl

include m in
theorem eval_pull (U : Config G n) : R.eval (pull s b U) = R.eval U := by
  unfold Rep.eval Activities.gas; rw [exponent_pull m]; conv_rhs => rw [← m.kp.finsetCongr.tsum_eq (fun i => R.activities.gasOccurrence R.p i U)]
  congr 1; refine tsum_congr fun i => ?_
  rw [show m.kp.finsetCongr i = i.map m.kp.toEmbedding from rfl]; unfold Activities.gasOccurrence; rw [admissible_map m]; split <;> simp only [Finset.prod_map,Equiv.coe_toEmbedding,m.valuesK]

theorem footprint_turn {A : Hol G} {T : SectionData F} (ht : T.Sound A) (s : Signed) (o b : Site n) :
    T.footprint (affine s b o) = (T.footprint o).image (affine s b) := by
  unfold SectionData.footprint
  conv_lhs => rw [← ht.stable s, Finset.image_image]
  simp [Finset.image_image,comp_def,affine, Signed.act_add, add_assoc, wrap_signed]

/-- Actual matched change of placement in the same vacuum. Do not adjust budgets
or coordinates based on measured configurations. The regular supports transform
as wholes even for zero values. -/
def reorient (P : Coefficient F n) : Coefficient F n where
  x := F.act s.ortho P.x
  support i := (P.support i).image (turnSites s b)
  regular i := P.regular i ∘ pull s b
  forced i := P.forced (m.kp.symm i) ∘ pull s b

@[simp] theorem forced_reorient (P : Coefficient F n) (i) : (reorient m P).forced (m.kp i) = P.forced i ∘ pull s b := by simp [reorient]

theorem format_reorient {A : Hol G} {P : Coefficient F n} (h : P.Format o A R) (hn : 2 ≤ n.val) :
    (reorient m P).Format (affine s b o) A R := by
  have hj (i) := reads_pull (b:=b) ((reads_null_iff A d ..).2 ⟨h.identity_null i, h.projects i⟩) (h.smooth i).sites hn s
  simp only [map_zero] at hj
  refine ⟨fun i => regular_pull (h.smooth i) s b,fun i => Finset.mem_image_of_mem (affine s b) (h.origin i),
    fun i => ((reads_null_iff ..).mp (hj i)).1, fun i => ((reads_null_iff ..).mp (hj i)).2, fun i U hu => ?_,fun i hi => ?_, fun i => invariant_pull (h.invariant _) s b, fun i => ?_, fun i => (h.borel _).comp (continuous_pull ..).measurable⟩
  · obtain ⟨i,rfl⟩ := m.kp.surjective i; rw [forced_reorient] at hu; exact (Work.H03.eligible_send s b _ _ _ _ (m.forced_support _) (m.forced_inventory _) (m.forced_tests ..)).2 (h.forcing _ _ hu)
  · obtain ⟨i,rfl⟩ := m.kp.surjective i; rw [forced_reorient] at hi; rw [m.forced_support]; exact Finset.mem_image_of_mem _ (h.carried i (fun h => hi (by rw [h]; rfl)))
  obtain ⟨i,rfl⟩ := m.kp.surjective i; rw [forced_reorient,m.forced_support]; exact uses_pull (h.supported _) s b



theorem density_reorient {A : Hol G} {T : SectionData F} (ht : T.Sound A) (P : Coefficient F n) :
    (reorient m P).density (affine s b o) T R = P.density o T R ∘ pull s b := by
  funext U
  let V := pull s b U
  have he := footprint_turn ht s o b
  have hK (q : Finset ℕ) : (reorient m P).marked R (m.kp.finsetCongr q) U = P.marked R q V := by
    simp only [Coefficient.marked,show m.kp.finsetCongr q = q.map m.kp.toEmbedding from rfl, admissible_map m]; split
    · simp only [Finset.sum_map, ← Finset.map_erase, Finset.prod_map]; simp only [Equiv.coe_toEmbedding,forced_reorient,comp_apply,m.valuesK,V]
    rfl
  simp only [Coefficient.density, comp_apply]; rw [← m.kp.finsetCongr.tsum_eq,eval_pull m, exponent_pull m]; simp_rw [hK]; congr 2
  have hP v : T.places v o ∘ pull s b = T.places (F.act s.ortho v) (affine s b o) := funext fun V => T.placed_signed ht s o b v V
  unfold Coefficient.exponentialEntry Coefficient.maskedTerm reorient; dsimp only; rw [act_at_zero, ← core_act, F.scaling, he, masked_pull, hP]
  simp only [masked_pull]
  rfl
end Moves

section Step
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem parent_affine {c f : Side} (r : Ratio c f) (hr : Odd r.count.val) (s : Signed) (b : Site c) (o : Site f) :
    r.parent (affine s (r.embed b) o) = affine s b (r.parent o) := by
  have he (z : Site f) : r.parent (z + r.embed b) = r.parent z + b := by
    obtain ⟨⟨x,y⟩,rfl⟩ := r.assemble_bijective.2 z
    rw [show r.assemble (x,y)+r.embed b = r.assemble (x+b,y) by unfold Ratio.assemble; dsimp only; rw [show r.embed (x+b)=r.embed x+r.embed b from map_add r.root x b]; abel, r.assemble_parent,r.assemble_parent]
  rw [affine,he,r.parent_signed hr, affine]




end Step
end YM.Push.Local
