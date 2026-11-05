import YM.Next.WARD_BIN.Printing
import YM.Next.WARD_BIN.Wake
import YM.Work.G09


/-!
# Coherent discrepancy pages

Read on ONE family's step budgets.

Export a
true PULSE used later with Lane skills; preserves subtraction provenance and
full masks at top.

Physical statement at origin first; use-only covariance
(not retuning singleton) later.

No separated witnesses supplied as inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin
open Function Filter Set MeasureTheory Wilson Lattice RG Source Labels Bid Work.G07 Work.G08 Gas
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {d l m N p : ℕ} {W : Worth} {F : Labels.Frame G d}
    {C : Family G} {S : Finset Cover}

abbrev rentAt (C : Family G) (N : ℕ) := (C.path.levels.params N).columns
abbrev roof (C : Family G) (N p : ℕ) := C.path.rep N p N
abbrev face (C : Family G) (N p : ℕ) := (roof C N p).p
abbrev brim (C : Family G) (d : ℕ) := C.labels.level d
abbrev cash (C : Family G) (N : ℕ) := C.path.levels.clock.forcedAllowance N
abbrev spot (C : Family G) (N p : ℕ) : Site (C.S.side N p) := 0
abbrev native (C : Family G) (N p) (S : Finset Cover) := footprint S (spot C N p)

/-- Literal placed physical function from cutoff test. -/
def cell (C : Family G) (d N p : ℕ) (u : Form G) (o : Site (C.side N p)) :=
  ((C.S.a N:ℂ)^d)⁻¹ • places o u

def Ov (C : Family G) (d N p : ℕ) (x : C.label d) := canonical (C.localSection d) (face C N p).threshold x





/-- A book leaf where the origin test is admissible. Kept alongside `Family`,
whose coefficients read out at refs. Include Pad *before* selection. -/
structure Page (C : Family G) (d N p : ℕ) where
  staple : Pad (roof C N p).activities (face C N p)
  line : Console C.path p (brim C d)
  ink : ℕ
namespace Page
variable (D : Page C d N p)

structure Works (S : Finset Cover) (W : Worth) : Prop where
  realizes : C.ref d ≤ N
  roster : (C.localSection d).stencil⊆S
  traffic : D.line.Purchases (C.ref d) N N W (C.localSection d) C.params
  form : D.line.Prints (C.factory d N p) (C.ref d)
  pressed x : Pressed (C.localSection d) ((C.factory d N p).entries N x) (native C N p S) D.ink (spot C N p)
              (roof C N p) (Ov C d N p x)

def stamp (S : Finset Cover) (u : Form G) (x : Label G d) := kit (C.localSection d) S D.ink (spot C N p) D.staple u x

def refLabel (S : Finset Cover) (u : Form G) (x : Label G d) := D.line.echo N (C.ref d) (D.stamp S u x)
def retLabel (S : Finset Cover) (u : Form G) (x : Label G d) := (C.factory d N p).terminal.symm (D.refLabel S u x)

def tip (c m : ℝ) (C : Family G) (S : Finset Cover) (N p : ℕ) := sif (face C N p) (native C N p S) m*c

lemma stamp_eq (h : Works D S W) : D.line.rods N D.ink=native C N p S :=
  (congr_fun (h.form.uses N h.realizes le_rfl 0) D.ink).symm.trans (h.pressed 0).ink

lemma reference_linear {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V →ₗ[ℂ] Label G d) (f : V →ₗ[ℂ] Form G) :
    IsLinearMap ℂ (fun x => D.refLabel S (f x) (v x)) :=
  ⟨fun x y => by unfold refLabel stamp; rw [(kit_linear v f (C.localSection d) S D.ink (spot C N p) D.staple).map_add,map_add],
    fun a b => by unfold refLabel stamp; rw [(kit_linear v f (C.localSection d) S D.ink (spot C N p) D.staple).map_smul,map_smul]⟩

-- Carries actual discrepancy with same Console, from Pressed cutoff to ref.
structure Pulse (S : Finset Cover) (W : Worth) (R : Duet C.path (brim C d) N p (C.ref d) N) (w c : ℝ)
    (u : Form G) : Prop where
  active : R.Woke C.params W (C.localSection d) w
  sticks : R.atPoint=D.line.centers
  struck : R.voice=D.line.signal N (raw (R.voice N))
  full : Pressed (C.localSection d) (R.voice N) (native C N p S) D.ink (spot C N p) (roof C N p) u
  bought : let q:=primary (brim C d) (face C N p).threshold (R.voice N).x
           let b:=face C N p
           Coin C.params (brim C d) S b.order b (spot C N p) u q c

lemma Pulse.locus {D : Page C d N p} (h : D.Works S W) {R w c u} (hp : Pulse D S W R w c u)
    (i) (hi : C.ref d ≤ i) (hh : i≤N) : R.atPoint i=0 := by rw [hp.sticks,h.form.bases _ hi hh]



lemma Pulse.wind {D : Page C d N p} {R : Duet C.path (brim C d) N p (C.ref d) N} {w c u} (hx : Pulse D S W R w c u)
    (hc : roomCost C.path.levels W) (hb : Bank W C.path.levels) :
    16*(1+rentAt C N)*(brim C d).coeffSize (R.voice N).x ≤ w := by
  have hr := (Work.G09.cone_cost hc hb hx.active N hx.active.basic.1 le_rfl).1.trans
    (Work.G09.cost_finest hc hb hx.active)
  have hh : 0 < (2:ℝ)*(1+rentAt C N) := by have := (C.path.levels.params N).columns_ge; unfold rentAt; linarith
  apply le_of_mul_le_mul_left _ hh
  apply le_trans (le_of_eq _) hr; unfold rentAt; ring

/-- Comparison at the top cutoff call only. w dominates the *combined*
single-source budget BEFORE creating a corresponding primary. -/
theorem flush {m c w : ℝ} (ha : C.Makes) (hf : roomCost C.path.levels W) (hb : Bank W C.path.levels)
    (h : Works D S W) (hn : FitsIn S (C.side N p)) {u x}
    (he : Coin C.params (brim C d) S (face C N p).order (face C N p) (spot C N p) u x c)
    (hw : inkage (face C N p) (native C N p S) d (cash C N) (κ C.path N))
    (hm : 1≤m) (hp : stipend C.params (C.localSection d) (face C N p) S (spot C N p) m) (hW : tip c m C S N p ≤ w) :
    let v := retLabel D S u x
    ∃ R : Duet C.path (brim C d) N p (C.ref d) N,
      Pulse D S W R w (m*‖v‖+c) (Ov C d N p v-u) ∧
        (∀ i,C.ref d ≤ i → i≤N → R.voice i=stepLess ((C.factory d N p).entries i v) (D.line.signal N (D.stamp S u x) i)) ∧
        (R.voice N).x=v-coat (brim C d) (face C N p).threshold x ∧
        ‖v‖ ≤ c+w / (16*(1+rentAt C N)) := by
  intro v
  have hh := h.realizes
  have H := ha.calibrated d N p hh
  have ht : ∀ i,(spot C N p)∈ D.line.rods N i := by
    rw [← h.form.uses N hh le_rfl 0]; exact (H.format _ hh le_rfl _).origin
  have hv := stamp_eq D h
  let V := D.stamp S u x
  let B := D.line.stage N V
  obtain ⟨(hB : B.Format _ _ _),hy,Hz⟩ := kit_pays (ha.sections _) h.roster ht hv D.staple (ha.wilson.represents N p N le_rfl).good hw
    (Real.sqrt_pos.mpr (Real.exp_pos _)) he hm hp hn
  have hj := D.line.first N V
  obtain ⟨R,hr,hg,H0,H1⟩ := D.line.discrepancy (m:=N) h.traffic hh h.form H V w _
    (by unfold Console.ticket; rw [h.form.bases N hh le_rfl]; exact ⟨hB,hy⟩) (Hz.trans hW)
  have heq : D.line.matched N (C.ref d) (C.factory d N p) V = v := rfl
  rw [heq] at H0 H1
  let A := (C.factory d N p).entries N v
  have hq := H1 N hh le_rfl; rw [hj] at hq
  have hQ : (R.voice N).x=v-coat (brim C d) (face C N p).threshold x := by
    rw [hq]; exact congr_arg (· - B.x) (H.bare_coord v)
  have hS : B.support=A.support := (h.form.uses N hh le_rfl v).symm
  have hx : Pulse D S W R w (m*‖v‖+c) (Ov C d N p v-u) := by
    refine ⟨hr,hg,?_,?_,?_⟩
    · rw [hq]; exact H0
    · rw [hq]; exact (h.pressed v).sub (kit_starts _ _ _ _ _ _ _ hv) (H.cap _ hh le_rfl v) hy
    have hz : primary (brim C d) (face C N p).threshold (R.voice N).x=primary (brim C d) (face C N p).threshold v-x := by
      rw [hQ]; let t := (face C N p).threshold
      rw [show primary (brim C d) t (v-coat _ t x) = primary (brim C d) t v-primary (brim C d) t (coat _ t x) by simp only [primary,map_sub], coat_flip x (face C N p).threshold_pos.ne']
    dsimp only; rw [hz]; exact (hp v).sub he
  have hwind := hx.wind hf hb
  refine ⟨R,hx,H1,hQ,?_⟩
  let z := 16*(1+rentAt C N)
  have ho : 0 < z := by unfold z rentAt; have := (C.path.levels.params N).columns_ge; linarith
  apply (coeff_le (F:=brim C d) v).trans <| (size_triangle _ v B.x).trans (add_le_add he.weights ?_)
  apply (le_div_iff₀ ho).2
  rw [mul_comm]; rw [hQ] at hwind; exact hwind


end Page
end YM.WardBin
