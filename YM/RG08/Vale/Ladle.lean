import YM.RG08.Vale.Pastels
/-!
# Priced coordinate projections by arity on unscaled radial probes
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 120000
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Shade Quire Source Source.Drops Labels
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {d i j k e r n : ℕ} {F : Labels.Frame G d} {V W: Shale (Loc G 1) r}
def Plume (G:Gauge)(d j:ℕ) : Submodule ℝ (Tensor.T (Snap G d) ℝ j) where
  carrier := {x| Tensor.Sym x ∧ ∀ v:Fin j→Snap G d,∀ i:G.El,x ((Film.colorIn G d i)∘v)=x v}
  zero_mem' := ⟨fun _ _=>rfl,fun _ _=>rfl⟩
  add_mem' := by intro a b (⟨ha,h⟩) ⟨hb,g⟩; exact ⟨fun i j=> congr_arg₂ (·+·) (ha i j) (hb i j),fun i j=> congr_arg₂ (·+·) (h i j) (g i j)⟩
  smul_mem' := fun a _ ⟨h,hT⟩ => ⟨fun i j=> congr_arg (a•·) (h i j),fun i j=> congr_arg (a•·) (hT i j)⟩
def shadeC (p:Plume G d j): Tensor.T (Snap G d) ℂ j := (j.factorial:ℝ)⁻¹ • (Complex.ofRealCLM.compContinuousMultilinearMap p.val)
abbrev shady (p:Plume G d j) := Tensor.diagonal (shadeC p)
lemma shade_all (p:Plume G d j) (v: Fin j→Snap G d) : shadeC p v= Complex.ofReal ((j.factorial:ℝ)⁻¹ * p.val v) := (Complex.ofRealCLM.map_smul (j.factorial:ℝ)⁻¹ (p.val v)).symm
lemma shade_sym (p:Plume G d j) : Tensor.Sym (shadeC p) := fun i z=> congr_arg (fun x:ℝ=> (j.factorial:ℝ)⁻¹ • Complex.ofReal x) (p.property.1 i z)
lemma shade_safe (p:Plume G d j) : Parts.Safe (shady p) :=
    ⟨(Tensor.diag_smooth ..).contDiffAt,fun i=> Eventually.of_forall fun x=> congr_arg (fun x:ℝ=> (j.factorial:ℝ)⁻¹ • Complex.ofReal x) (p.property.2 (fun _=>x) i)⟩
def basin (p:Plume G d j) := Parts.archive (shade_safe p)
lemma basin_tile (p:Plume G d j)(hi:i≤d)(hk:k≤d): (gradePart (i,k) (basin p)).val=if h:k=j then WardBin.tile (shadeC p) i else 0 := by
  rw [basin,Parts.capture _ hi hk]
  split; next h=> subst j; rw [coeff_at_diagonal _ (shade_sym p)]
  next h=> rw [coeff_diagonal_else _ (shade_sym p) h]; simp [WardBin.tile]
lemma grade_digs {a b:Label G d}(h : ∀ i≤d,∀ k≤d,(gradePart (i,k) a).val=(gradePart (i,k) b).val): a=b := by
  refine Eq.trans (Labels.decompose a).symm ((Finset.sum_congr rfl ?_).trans (Labels.decompose b)); intro i hi
  exact sum_congr rfl fun k hk=> Subtype.ext (h i (Nat.le_of_lt_succ (mem_range.mp hi)) k (Nat.le_of_lt_succ (mem_range.mp hk)))
lemma basin_add (p q:Plume G d j) : basin (p+q)=basin p+basin q := by
  apply grade_digs; intro i hi k hk
  simp_rw [_root_.map_add, Submodule.coe_add,basin_tile _ hi hk]; split_ifs with h
  · unfold WardBin.tile; rw [← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=> ?_
    simp only [shade_all,Submodule.coe_add,_root_.add_apply,mul_add,Complex.ofReal_add,map_add,add_mul]
  exact (add_zero _).symm
lemma basin_sm (p:Plume G d j)(t:ℝ) : basin (t•p)= (t:ℂ) • basin p := by
  apply grade_digs; intro i hi k hk
  simp_rw [_root_.map_smul, Submodule.coe_smul_of_tower,basin_tile _ hi hk]; split_ifs with he
  · unfold WardBin.tile; rw [Finset.smul_sum]; refine sum_congr rfl fun v _=> ?_
    simp only [shade_all,SetLike.val_smul,_root_.smul_apply, smul_eq_mul,mul_left_comm _ t,Complex.ofReal_mul,map_mul]; rw [Algebra.smul_def,show algebraMap ℂ (Pol G)=MvPolynomial.C from rfl]; ring
  exact (smul_zero _).symm
lemma basin_real (p:Plume G d j) : realBar (basin p)=basin p := by
  apply Next.Foundations.jet_test_ext; intro J k hk
  let f (t:ℝ):= Labels.read (scaleJet J t) (basin p).val
  have h : iteratedDeriv k f 0= iteratedDeriv k (fun t=> shady p (WardBin.engineered t (trunk d J))) 0 := Parts.archive_read (shade_safe p) hk _
  change iteratedDeriv k (fun t:ℝ=> Labels.read (scaleJet J t) (conjPol (basin p).val)) 0=_; simp_rw [conj_value]
  let s (t:ℝ) := shady p (WardBin.engineered t (trunk d J)); let C:ℂ ≃L[ℝ] ℂ := (starL' ℝ)
  have he (f:ℝ→ℂ): C (iteratedDeriv k f 0)=iteratedDeriv k (C ∘ f) 0 := by rw [iteratedDeriv,iteratedDeriv,C.iteratedFDeriv_comp_left]; rfl
  have hv : C ∘ s=s:= funext fun x=>by unfold s; simp only [shady,Tensor.diagonal,shade_all]; exact Complex.conj_ofReal _
  change iteratedDeriv k (C ∘ f) 0=iteratedDeriv k f 0; rw [← he, h, he s,hv]
private lemma norm_v {E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →ₗ[ℝ] F): ∃ C:ℝ,0≤C ∧ ∀ x, ‖L x‖ ≤ C*‖x‖ := by
  let M := LinearMap.toContinuousLinearMap L
  exact ⟨‖M‖,norm_nonneg M,fun x=> M.le_opNorm x⟩
private lemma norm_w {E F:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : Submodule ℝ E) (L : S →ₗ[ℝ] F): ∃ C:ℝ,0≤C ∧ ∀ x, ‖L x‖ ≤ C*‖x.val‖ := norm_v L
lemma basin_earn (F: Labels.Frame G d) (j : ℕ) : ∃ A:ℝ,0≤A∧∀ p:Plume G d j,‖F.coords (basin p)‖ ≤ A*‖p.val‖ := by
  let L : Plume G d j →ₗ[ℝ] F.Coeff := {
    toFun p:= F.coords (basin p)
    map_add' p q:=by rw [basin_add,map_add]
    map_smul' c p:= by rw [basin_sm,map_smul]; ext1 i; exact Eq.symm Complex.real_smul }
  exact norm_w (E:=Tensor.T (Snap G d) ℝ j) (F:=F.Index→ℂ) (Plume G d j) L
lemma basin_genuine (p:Plume G d j)(F:Labels.Frame G d)(i:F.Index): Complex.ofReal ((F.coords (basin p) i).re)= F.coords (basin p) i := by
  have hp:= F.conj_basis (F.coords (basin p)) i; rw [LinearEquiv.symm_apply_apply,basin_real] at hp
  exact Complex.conj_eq_iff_re.mp hp.symm
-- For forming budgets before checking branch legality
variable (H:Hol G)
def cook (h: Dappled V) (hp:Polished V) (H:Hol G) (d j:ℕ) : Plume G d j := ⟨amount V d j,coinSym h.toTidy hp d j,fun v=> showed H h hp v⟩ -- implicit section params duplicated?
-- Called only on Dappled

def ladle (V:Shale (Loc G 1) r)(d j : ℕ) : Label G d := if h:Dappled V ∧ Polished V then basin (cook h.1 h.2 H d j) else 0
lemma ladle_add (h:Dappled V)(g:Dappled W)(hp:Polished V)(hq:Polished W)(d j:ℕ): ladle H (V+W) d j=ladle H V d j+ladle H W d j := by
  unfold ladle; rw [dif_pos ⟨dappled_more h g,polished_more hp hq⟩,dif_pos ⟨h,hp⟩,dif_pos ⟨g,hq⟩]; rw [← basin_add]; exact congr_arg _ (Subtype.ext (amount_add h.toTidy hp g.toTidy hq d j))
lemma ladle_scale (h:Dappled V)(hp:Polished V)(c:ℝ)(d j:ℕ): ladle H (c•V) d j=(c:ℂ) • ladle H V d j := by
  rw [ladle,dif_pos ⟨dappled_sm h c,polished_scale hp c⟩,ladle,dif_pos ⟨h,hp⟩,← basin_sm]; exact congr_arg _ (Subtype.ext (amount_scale h.toTidy hp c d j))
lemma ladle_real (i:F.Index) : ↑((F.coords (ladle H V d j) i).re)= F.coords (ladle H V d j) i := by unfold ladle; split; exact basin_genuine ..; simp
lemma basin_zero (p : Plume G d j) (h:p.val=0) : basin p=0 := by simpa only [zero_smul,Complex.ofReal_zero,smul_zero,← show p=(0: Plume G d j) from Subtype.ext h] using basin_sm p 0
lemma ladle_arity (h : j < r)(d:ℕ) : ladle H V d j=0 := by
  unfold ladle; split; next hV=> exact basin_zero _ (ContinuousMultilinearMap.ext (fun v=> (penny_amt hV.1.toTidy hV.2 v).trans (pennydime h v)))
  next hV=> rfl
@[simp] lemma ladle_zero (d j : ℕ) : ladle H (0:Shale (Loc G 1) r) d j=0 := by unfold ladle; split; exact basin_zero _ (zero_amt ..); rfl
lemma ladle_legs {p : F.Index} (he : (F.grades p).2≠ j): F.coords (ladle H V d j) p=0 := by
  rw [Film.costs_only]; unfold ladle; split
  next h=> rw [show gradePart _ _=0 from Subtype.ext ((basin_tile (i:=(F.grades p).1) (k:=(F.grades p).2) _ (F.bound p) (Film.second_fits F p)).trans (if_neg he)),map_zero]; rfl
  next h=> simp
lemma ladles (G:Gauge)(F:Labels.Frame G d)(j r:ℕ): ∃ A:ℝ, 0≤A ∧ ∀ (V:Shale (Loc G 1) r)(C:ℝ),Quire.Ink (mint (d*j)) V C → ∀ H:Hol G,‖F.coords (ladle H V d j)‖ ≤ A*C := by
  obtain ⟨A,hA,hh⟩:=weights G d j r; obtain ⟨B,hB,hv⟩:=basin_earn F j
  refine ⟨B*A,mul_nonneg hB hA,fun V C hc H=>?_⟩
  unfold ladle; split; next h=> exact (hv _).trans ((mul_le_mul_of_nonneg_left (hh _ _ hc) hB).trans_eq (mul_assoc ..).symm)
  next h=> simp only [map_zero,norm_zero]; exact mul_nonneg (mul_nonneg hB hA) hc.nonneg
end YM.RG08.Vale
