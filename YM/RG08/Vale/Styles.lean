import YM.RG08.Vale.Salt
/-!
# Engineering-scaled section, test and holonomy stencil both genuine
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Bloch Exterior Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Tall
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{p m c:Side}{R:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}
variable {F: Labels.Frame G d} (T : SectionData F)(b : Letter F) {V : BoardU D R G}
def pillar : Place.Dev T.stencil G→ ℝ := Complex.re ∘ Place.column T b.label
def crownP (j:ℕ) := stock T.stencil (Tensor.coeff (pillar T b) j 0)
def setSl (m:Side)(i:Site m) : Config G m→ℝ := Complex.re ∘ T.places (Place.copy F b.label) i
lemma back_sl (i:Site m) : setSl T b m i ∘ input G m = pillar T b ∘ salon T.stencil G i := funext fun v=>congr_arg Complex.re (slants ..)
lemma smooth_sl (i:Site m): ContDiff ℝ ω (setSl T b m i ∘ input G m) := by
  rw [back_sl]; exact (Complex.reCLM.contDiff.comp (column_smooth T b.label)).comp (salon T.stencil G i).contDiff
lemma pillar_real (H:Hol G)(h:T.Sound H)(x) : ((pillar T b x:ℝ):ℂ)= column T b.label x := by
  apply Complex.conj_eq_iff_re.mp
  have he: star (Place.copy F b.label)=Place.copy F b.label := by ext i; simp [Pi.single_apply,Place.copy]
  exact (h.ordinary_real _ _).symm.trans (congr_arg (fun U:F.Coeff=> T.evaluate U (pore x)) he)
lemma crown_pays (i:Site m): stitch (crownP T b j) m i= Tensor.coeff (setSl T b m i ∘ input G m) j 0 := by -- test param unused remove
  apply Tensor.ext_diag _ _ ((stock_tidied ..).sym i) (Tensor.coeff_symm (((smooth_sl ..).of_le le_top).contDiffAt)); funext x
  let S:=salon T.stencil G i; let F:=pillar T b; have he:ContDiffAt ℝ j F 0:= ((Complex.reCLM.contDiff.comp (column_smooth T b.label)).contDiffAt.of_le le_top)
  have hh := Next.Foundations.jets_linear S he
  rw [back_sl]; exact (stocks _ _ i x).trans (congr_arg ((j.factorial:ℝ)⁻¹ • · : ℝ→ℝ) (DFunLike.congr_fun hh (fun _=>x)).symm)
lemma crown_small (b' : Bid.pop T)(h : j < slot b) : crownP T b j=0 := by
  have hA := Place.radials_vanish T b' b.label j h
  let f:= Place.column T b.label
  have he : ContDiffAt ℝ j f 0:= ((column_smooth ..).contDiffAt.of_le le_top)
  have ht : Tensor.coeff (pillar T b) j 0=0 := by
    ext1 v; unfold Tensor.coeff; change ((j.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ j (Complex.reCLM ∘ f) 0 v=0
    rw [Complex.reCLM.iteratedFDeriv_comp_left he le_rfl]; unfold f; rw [hA]; exact smul_zero _
  rw [crownP,ht,stock_zero]
lemma crown_tidy (j : ℕ): Tidy (crownP T b j):= stock_tidied ..

variable (hz:d ≤ D) (hR:0≤R)

def timesL (r:ℕ) : EnvelopeU D R G r := fun i=>crownP T b r i • bareL b.test ((le_trans (Nat.le_add_left ..) b.bill).trans hz) hR
def startU (i r:ℕ) : EnvelopeU D R G r := if r=slot b+i then timesL T b hz hR r else 0
lemma start_cap : Fits (slot b) (startU T b hz hR) := fun i j h=> (eq_or_ne j _).elim (fun he=> he.le) (fun he=> (h (if_neg he)).elim)
def chant (φ:Exam D) : ℝ := bareL b.test ((le_trans (Nat.le_add_left ..) b.bill).trans hz) hR (sheet D R φ)
lemma times_tid (r:ℕ): Tidy (timesL T b hz hR r) := ((crown_tidy T b r).map (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (bareL b.test ((le_trans (Nat.le_add_left ..) b.bill).trans hz) hR)))
lemma start_tid (i j:ℕ): Tidy (startU T b hz hR i j) := by unfold startU; split; apply times_tid; exact Tidy.zero ..
lemma start_lit (w:ℝ) (hw: 0≤w)(i j:ℕ) : ∃ A,Quire.Lit (startU T b hz hR i j) w A := by
  unfold startU; split
  next h=>
    let V : Voice D R:=bareL b.test ((le_trans (Nat.le_add_left ..) b.bill).trans hz) hR
    obtain ⟨A,hA⟩:=stock_paid T.stencil (Tensor.coeff (pillar T b) j 0) w hw
    refine ⟨‖V‖*A,?_⟩; have he:= budget_scale (C:=A) (norm_nonneg V) hA; unfold Quire.Lit Quire.Ink
    convert he using 1; funext i; unfold timesL crownP; rw [norm_smul]; ring
  next h=> exact ⟨0,Ink.none ..⟩
lemma start_lank : Lank (startU T b hz hR) := fun i j=> scarlet (start_lit T b hz hR 1 zero_le_one i j).choose_spec one_pos
lemma echo_start (φ:Exam D): plug φ R∘ startU T b hz hR i r= if r=slot b+i then chant b hz hR φ • crownP T b r else 0 := by
  ext x; simp only [startU]; split_ifs; change plug _ _ (_•_)= _* _; rw [map_smul]; exact mul_comm ..
  exact map_zero _
variable (hp: Bid.pop T)
include hp
lemma lights_out (φ:Exam D) : Loom.strand (slot b) j (fun i r=>plug φ R∘startU T b hz hR i r) r=if j=0 then chant b hz hR φ • crownP T b r else 0 := by
  unfold Loom.strand; split_ifs with h hb ht
  · change plug φ R ∘ startU T b hz hR _ r=_; rw [echo_start,if_pos (by omega)]
  · change plug φ R ∘ startU T b hz hR _ r=_; rw [echo_start,if_neg (by omega)]
  · rw [crown_small T b hp (by omega),smul_zero]
  · rfl
lemma start_duty (H:Hol G)(h:T.Sound H) : Marvel (slot b) (startU T b hz hR):= by
  refine ⟨start_cap T b hz hR,start_tid T b hz hR,fun m φ i=> ?_⟩
  have he : Loom.Shell G m (setSl T b m i):={
      measure := Complex.continuous_re.measurable.comp (T.continuous_places (Place.copy F b.label) i).measurable
      hol:=(smooth_sl ..).contDiffAt
      coast:=fun _ _ _ _ _ _ hh=> hh.mono fun _ he=> by dsimp only [Function.comp_apply]; rw [he]; exact congr_arg Complex.re (T.placed_invariant h ..) }
  let X j := if j=0 then chant b hz hR φ • setSl T b m i else 0
  refine vocalized (fun k=> ⟨X,fun j=> ⟨?_, fun r hv=>?_⟩⟩); unfold X; split_ifs; exact Shell.scale he _; exact shell_zero
  unfold X; rw [lights_out _ _ _ _ hp]; split_ifs; swap
  · simp only [st_zero]; change Tensor.coeff (0: Link G m→ℝ) r 0=0; simp [Tensor.coeff]
  let B := setSl T b m i; let q:= chant b hz hR φ
  rw [st_scale _ (crown_tidy ..).pens.of_norm, crown_pays]; change Tensor.coeff (q • (B ∘ input G m)) r 0=_
  exact Tensor.coeff_smul q (he.hol.of_le le_top)
end YM.RG08.Vale
