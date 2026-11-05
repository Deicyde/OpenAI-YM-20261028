import YM.RG08.Germ.Layer

/-! # The full connected action, before removing kinetic correction

Independent flat-lattice prescription. Formal vacuum coefficients store
no free grade-zero leading Hessian or constants. At a finite step, `exhale`
DOES report the generated rank-zero COEFFICIENT in the log density (negative,
action units) AFTER factoring out fixed normalizations, NO other rank-zero
claim. See Ward and scalar adapters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Exterior Precision Bloch Next.Free Work.F08 Push.AbsoluteSums Finset Function Filter
open Stationary Analysis UVExt.Paths Matrix Tree
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius InnerProductSpace Classical
variable {c f m L : Side} {G : Gauge} {w : ℝ} {ν : G.ColorIndex} {n r e : ℕ}

abbrev Air (G : Gauge) := Canticle (Loc G 1)
def Gets {α : Type} [Fintype α] (F : Canticle α) := Decked F ∧ ∀ i j,Tunable (F i j) ∧ Glows (F i j)
def Halt (F : Air G) := ∀ e,F e 0=0

variable (P : Patch) (D : ChartRatio G) (k : KernelChoices) (X : Repeated P.L)

def awakening (i : G.ColorIndex) (P : Patch) (D : ChartRatio G) (κ : ℝ) (F : Air G) (e r : ℕ) : Shale (Park G P.L) r :=
    -gemL P.L (F e r)-(if r=e+2 ∧ 0<e then blot i P κ r else 0)+(if r=e ∧ 0<e then gemL P.L (brimJ i D r) else 0)

private lemma dormant {L : Side} : gemL L (0:Pot G r)=0 := by
  have he : Summable (0:Pot G r) := summable_zero
  simpa only [sub_self] using gem_less he he L
private lemma germ_glow {F : Pot G r} (h : Glows F) (L : Side) : Glows (gemL L F) := by
  obtain ⟨s,C,hs,H⟩:=h; let b := s/((r+1:ℕ):ℝ); have hb : 0<b := by unfold b; positivity
  refine ⟨_,_,hb,gem_price F H hb.le ?_⟩; unfold b; rw [mul_div_cancel₀ s (by positivity)]; exact le_mul_of_one_le_left hs.le (by exact_mod_cast L.property)
lemma Gets_awake (i : G.ColorIndex) {F : Air G} (h : Gets F) : Gets (awakening i P D k.penalty F) := by
  constructor
  · intro e r he; contrapose! he
    unfold awakening; rw [not_ne_iff.mp (mt (h.1 e r) he), dormant, neg_zero, if_neg, if_neg,sub_zero,add_zero]
    · intro hv; exact he ⟨hv.2,1,by rw [hv.1]⟩
    intro hv; exact he ⟨hv.2,0,by omega⟩
  intro e r
  let H := gemL P.L (brimJ i D r); let s := blot i P k.penalty r
  obtain ⟨hx,hF⟩:=h.2 e r
  obtain ⟨C,hC,v⟩:=brim_price i D (zero_le_one) r
  have he : Glows H := germ_glow ⟨_,_,one_pos,v⟩ P.L
  have ht : Tunable H := gem_tune _ _ (brim_tune i D r).1
  obtain ⟨Q,hQ,hv⟩:= blot_pays P i k.penalty zero_le_one (r:=r)
  have hS : Glows s := ⟨_,_,one_pos,hv⟩
  let V:=gemL P.L (F e r)
  have hm : Glows V := germ_glow hF _
  unfold awakening
  have hh : Glows (-V) := by simpa using hm.scale (-1)
  have hq : Tunable (if r=e ∧ 0<e then H else 0) := by split; exact ht; exact Tunable.zero ..
  have hs : Tunable (if r=e+2 ∧ 0<e then s else 0) := by split; exact blot_sym ..; exact Tunable.zero ..
  refine ⟨(((gem_tune _ _ hx.1).neg).sub hs).add hq,?_⟩
  apply Glows.plus
  · rw [sub_eq_add_neg]; apply hh.plus; split; next h => simpa using hS.scale (-1)
    rw [neg_zero]; exact Glows.zero
  split
  · exact he
  exact Glows.zero

-- independent primitive gives Γ and tree mean A (on inverse kernel)
-- Heat to log via inscription. A higher mark must use multi-source wrapper.
def exhale {L : Side} (A : Row (Fink G L) (Fink G L)) (Q : Row (Fink G L) (Loc G 1))
    (E : Canticle (Park G L)) (p : Option Side) (e r : ℕ) : Pot G r :=
      - scrollL (upswell (veiled A) E p 1 e r) (scan Q)
lemma Mending.negate {α : Type} {U : ℕ→Shale α r} {F : Shale α r} (h : Mending U F) : Mending (-U) (-F) := by simpa using h.scale (-1)
lemma WarmExhale {L : Side} {A : Row (Fink G L) (Fink G L)} {Q : Row (Fink G L) (Loc G 1)} (h : Whole A) (hh : Whole Q)
    {E : Canticle (Park G L)} (hv : Gets E) :
    Gets (exhale A Q E none) ∧ ∀ m : ℕ→Side, Tendsto (fun i=>(m i).val) atTop atTop → ∀ e r,Mending (fun i=>exhale A Q E (some (m i)) e r) (exhale A Q E none e r) := by
  have hr:= veiled_whole h; have ht:= scan_whole hh
  have he p t := upswell_deck _ hr _ (fun e r=> (hv.2 e r).1) hv.1 p t
  have hp (m : ℕ→Side) (e : Tendsto (fun i=>(m i).val) atTop atTop) (i j) : Mending (fun k=>exhale A Q E (some (m k)) i j) (exhale A Q E none i j) :=
    (scroll_thread (peals_late (fun i j => Mending.one (E i j) (hv.2 i j).2) hr e 1 i j) ht).negate
  refine ⟨⟨?_,fun i j=>⟨(scroll_tune ((he none 1).2 i j).1 ht).neg,(hp (fun n=> (⟨n+1,Nat.succ_pos _⟩:Side)) (tendsto_add_atTop_nat _) i j).1⟩⟩,hp⟩
  intro i j hj; contrapose! hj; unfold exhale; rw [not_ne_iff.mp (mt ((he none 1).1 i j) hj),nobody _ ht,neg_zero]
lemma exhale_deck {L : Side} {A : Row (Fink G L) (Fink G L)} {Q : Row (Fink G L) (Loc G 1)} (h : Whole A) (hh : Whole Q)
    {E : Canticle (Park G L)} (hv : Gets E) (p : Option Side) : Decked (exhale A Q E p) ∧ ∀ e r,Tunable (exhale A Q E p e r) := by
  have he:= upswell_deck _ (veiled_whole h) E (fun i j=> (hv.2 i j).1) hv.1 p 1
  refine ⟨?_,fun i j => (scroll_tune (he.2 i j).1 (scan_whole hh)).neg⟩
  intro i j hj; contrapose! hj; unfold exhale; rw [not_ne_iff.mp (mt (he.1 i j) hj),nobody _ (scan_whole hh),neg_zero]

def strike (i : G.ColorIndex) (P : Patch) (D : ChartRatio G) (k : KernelChoices) (X : Repeated P.L)
    (t : Train P.J) (F : Air G) (e r) := exhale (conditionalCov G X k t) (coarseMean G X k t) (awakening i P D k.penalty F) none e r

lemma strike_known (i : G.ColorIndex) (t : Train P.J) {F : Air G} (h : Gets F) (he : P.Branches k G) : Gets (strike i P D k X t F) := by
  have ht := (conditional_truth G X k t he).1
  have hm : Whole (coarseMean G X k t) := (ht.prod (probe_recites G P k|>.1.flipped)).weight k.penalty
  exact (WarmExhale ht hm (Gets_awake P D k i h)).1
end YM.RG08
