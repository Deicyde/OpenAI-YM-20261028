import YM.Push.LOOP_COEFFICIENT.Paths.Bill

/-!
# Local action: joint derivative production in the fine translation chart
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Matrix Function Filter Set Metric Lattice Laurent Bloch RG Precision Wilson Work.F02 Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {k : ℕ} {ι κ : Type} {σ C Λ : ℝ} {W : PathData G} {p : Clip}

abbrev Catalog := PlaqAxes ⊕ (PlaqAxes × ℕ × ℕ) ⊕ ℕ ⊕ ℕ

def shots (W : PathData G) (p : Clip) (s : Signed) : Catalog → Film (Angles G) := Sum.elim (directFilm G p s) <| Sum.elim
  (fun ⟨b,i,j⟩ => rowFilm G s (W.row b i) (W.row b j)) (Sum.elim (fun i => atomFilm s (W.cubic i)) fun i => atomFilm s (W.quartic i))

def production (W : PathData G) (p : Clip) (i : Signed × Catalog) := (amplify ((Fintype.card Signed : ℂ)⁻¹) (uncurry (shots W p) i)).reader

lemma damped_elim {a α β : Type} [Fintype a] {A : α → Film a} {B : β → Film a} {η ρ D : ℝ} (ha : Damped (Film.reader ∘ A) η ρ C) (hb : Damped (Film.reader ∘ B) η ρ D) : Damped (Film.reader ∘ Sum.elim A B) η ρ (C+D) := by
  convert ha.coprod hb using 1; ext1 i; cases i <;> rfl

lemma production_damped (G : Gauge) (p : Clip) (hσ : 0<σ) (C : ℝ) : ∃ ρ B : ℝ,0<ρ ∧ ∀ {W : PathData G} {Λ : ℝ}, W.Bounds p σ C Λ → Damped (production W p) (σ/4) ρ B := by
  obtain ⟨ρ,hρ,H⟩ := letter_bounds G (half_pos hσ)
  choose D hD using fun s : Signed => Damped.finite (fun i => (directFilm G p s i).reader) (show 0<σ/4 by positivity) hρ (directFilm_diff p s)
  refine ⟨ρ, ‖(Fintype.card Signed : ℂ)⁻¹‖*(∑ s,(D s + ((∑ _i : PlaqAxes, (Fintype.card G.ColorIndex * slotConst G^2) * (C*C)) + (slotConst G^3*C + slotConst G^4*C)))), hρ,fun {W Λ} h => ?_⟩
  refine (Damped.group (C:=fun s => D s + ((∑ _i : PlaqAxes, (Fintype.card G.ColorIndex * slotConst G^2) * (C*C)) + (slotConst G^3*C + slotConst G^4*C))) (N:=fun i => (uncurry (shots W p) i).reader) (show 0<σ/4 by positivity) hρ (fun s => ?_)).amplify ((Fintype.card Signed:ℂ)⁻¹)
  exact damped_elim (hD s) (damped_elim (Damped.group (N:=fun z : PlaqAxes × ℕ × ℕ => (rowFilm G s (W.row z.1 z.2.1) (W.row z.1 z.2.2)).reader) (show 0<σ/4 by positivity) hρ (fun i => rowFilm_damped hσ hρ H (W.row i) (h.rows i) s))
    (damped_elim (atomFilm_damped hσ hρ H W.cubic h.three s) (atomFilm_damped hσ hρ H W.quartic h.four s)))

lemma cluster {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] {F : ι × κ → E} {g : ι → E} (h : ∀ i, HasSum (fun j => F (i,j)) (g i)) : HasSum F (∑ i,g i) := by
  haveI := FiniteDimensional.complete ℝ E
  have he := summable_norm_iff.mp ((summable_prod_of_nonneg (f:=fun i => ‖F i‖) (fun i => norm_nonneg _)).mpr ⟨fun i => summable_norm_iff.mpr (h i).summable,.of_finite⟩)
  convert! he.hasSum using 1; rw [he.tsum_prod,tsum_fintype]; exact Finset.sum_congr rfl fun i _ => (h i).tsum_eq.symm
lemma squares_sum' {g : ι → G.Color} (h : Summable g) : ‖∑' i,g i‖^2 = ∑' i, ∑' j,inner ℝ (g i) (g j) := by
  have he := (innerSL ℝ (∑' i,g i)).map_tsum h; rw [← real_inner_self_eq_norm_sq]; refine he.trans (tsum_congr fun i => ?_)
  change inner ℝ (∑' j,g j) (g i) = _
  rw [real_inner_comm]; exact (innerSL ℝ (g i)).map_tsum h

lemma squares_sum {g : ι → G.Color} (h : Summable g) : HasSum (fun i : ι × ι => (inner ℝ (g i.1) (g i.2))/2) (‖∑' i,g i‖^2/2) := by
  have hh := summable_norm_iff.mpr h
  have ht : Summable (fun i : ι × ι => inner ℝ (g i.1) (g i.2)) := Summable.of_norm_bounded (hh.mul_of_nonneg hh (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)) (fun i => norm_inner_le_norm ..)
  have he := ht.div_const 2
  convert! he.hasSum using 1; rw [he.tsum_prod,squares_sum' h]; simp_rw [tsum_div_const]

variable (z : Co n (Angles G) → ℝ) (h : W.Bounds p σ C Λ)
lemma direct_sum (s : Signed) (x : Site n) : HasSum (fun i => (directFilm G p s i).value (unwrap z (s.act x))) (∑ i : PlaqAxes,(p.direct*(G.price (faceValue (pull s 0 (merged z)) (x,i))):ℝ):ℝ) := by
  push_cast; simp_rw [directFilm_merged]; exact hasSum_fintype _
include h
lemma row_sum (s : Signed) (x : Site n) : HasSum (fun i : PlaqAxes × ℕ × ℕ => (rowFilm G s (W.row i.1 i.2.1) (W.row i.1 i.2.2)).value (unwrap z (s.act x))) ((∑ i, ‖W.ell (pull s 0 (merged z)) (x,i)‖^2/2 : ℝ):ℂ) := by
  push_cast only [ofReal_sum]; apply cluster; intro i
  simp_rw [rowFilm_merged]
  have he := ofRealCLM.hasSum (squares_sum ((W.ell_dominated h (x,i)).summable (pull s 0 (merged z))))
  convert! he using 1; funext j; simp [PathData.ellTerms,real_inner_smul_left,real_inner_smul_right]; ring
lemma unmasked_series {A : ℕ → Atom G k} (hb : SumBudget (fun i => (A i).budget σ) C) (u : Config G n) (x : Site n) : Summable (fun i => (A i).unmasked u x) := Summable.of_norm_bounded (hb.2.1.mul_right (2^k:ℝ)) (fun i => ((A i).unmasked_bound u x).trans (by gcongr; exact (A i).lower_budget σ h.width))
lemma shot_sum (s : Signed) : HasSum (fun i : Catalog => ((shots W p s i).reader.distributed (Equiv.refl _) (cvec z))) (((quadratic p W (pull s 0 (merged z)) + uncut W.cubic (pull s 0 (merged z))+uncut W.quartic (pull s 0 (merged z))):ℝ):ℂ) := by
  let U := pull s 0 (merged z)
  let H (x : Site n) := ((∑ i : PlaqAxes,p.direct*G.price (faceValue U (x,i))) + (∑ i : PlaqAxes,‖W.ell U (x,i)‖^2/2) + (∑' i,(W.cubic i).unmasked U x) + (∑' i,(W.quartic i).unmasked U x) :ℝ)
  have hA {k : ℕ} (x : Site n) (A : ℕ → Atom G k) (hb : SumBudget (fun i => (A i).budget σ) C) : HasSum (fun i => (atomFilm s (A i)).value (unwrap z (s.act x))) ((∑' i,(A i).unmasked U x :ℝ):ℂ) := by simp_rw [atomFilm_merged]; exact ofRealCLM.hasSum ((unmasked_series h hb U x).hasSum)
  have hb (x : Site n) : HasSum (fun i => (shots W p s i).value (unwrap z (s.act x))) (H x : ℂ) := by
    dsimp only [H]; push_cast only [ofReal_add]; rw [add_assoc,add_assoc]; refine HasSum.sum (direct_sum z s x) (HasSum.sum (row_sum z h s x) (HasSum.sum (hA x W.cubic h.three) (hA x W.quartic h.four)))
  convert! hasSum_sum (s:=Finset.univ) (fun i _ => hb i) using 1
  · funext i; rw [Reader.distributed, ← Equiv.sum_comp s.actEquiv.toEquiv]; exact Finset.sum_congr rfl fun j _ => Film.wrapped ..
  rw [quadratic,Fintype.sum_prod_type,uncut,uncut]; simp only [← ofReal_sum]; apply congr_arg; simp only [H,Finset.sum_add_distrib]; rfl
lemma production_real : total (production W p) (Equiv.refl _) (cvec z) = ((mainTerm p W (merged z)):ℂ) := by
  rw [total,mainTerm, Patch.average,ofReal_mul]; push_cast
  convert (cluster (F:=fun i : Signed × Catalog => ((Fintype.card Signed:ℂ)⁻¹)*(((uncurry (shots W p) i).reader.distributed (Equiv.refl _) (cvec z)))) (fun s => (shot_sum z h s).mul_left _)).tsum_eq using 1
  · apply tsum_congr; intro i; simp [Reader.distributed, Finset.mul_sum, production, amplify]; rfl
  rw [← Finset.mul_sum]; push_cast; rfl
end YM.Push.Loops.Paths
