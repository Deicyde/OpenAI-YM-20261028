import YM.Extra.MULTISOURCE_BOUNDS.Trajectory
import YM.Work.I02
import YM.Work.I03
import YM.Work.I04

/-!
# Commissioning RMixed / RMetered / RCenter on one Wilson family

Terms used on reflected copies have the literal rotations and conjugations of
the input coefficients in this normalization. Require trajectories on the
copies from cutoff to EACH queried opening (can instead strengthen to a more
general multi-source construction). `Offer` is prior to mixed bounds and
specifies what physical trajectories and one-step estimates are needed. Also
need `Makes`, pricing and the strengthened cutoff-vacuum cost; e.g. pricing
provides the pure numerical part subject to its stated ex ante conditions.
Neither history construction nor any continuum existence conclusion is implied
without further inputs. Wcmain is all p, all sufficiently fine N at each fixed
side; CellHyp is not by definition a bound for every coarse cutoff at every
small side! The further ordered-limit and phase nodes in B use this same family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Multi
open Function Filter Lattice RG Source Wilson Overlay Marker Labels Cells MeasureTheory Extraction Stock Finset
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {G : Gauge} {C : Family G} {d i N m p : ℕ} {t : Tariff} {s : Scope}

def twist (C : Family G) (v : C.label d) (s : Signed × Bool) :=
    if s.2 then star ((C.labels.level d).act s.1.ortho v) else (C.labels.level d).act s.1.ortho v

theorem twist_copy (T : Tiling (C.side N p)) (H : C.Makes) (v : C.label d) (o : Site (C.side N p)) (hv : C.ref d ≤ N)
    (q : T.Cell) : T.copy q (C.O N p v o) = C.O N p (twist C v (Extraction.Spin.way T q)) (T.copyMap q o) := by
  funext U
  have he := C.rotated H hv v (T.omega q) o (T.translateBy q) U
  unfold Tiling.copy twist Extraction.Spin.way; dsimp only
  by_cases h : T.hand q <;> simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  · rw [← he]; exact (C.reality H hv ..).symm
  exact he.symm

theorem twist_price (C : Family G) (d : ℕ) (R : ℝ) : ∃ b : ℝ, 0 < b ∧ ∀ (v : C.label d) s, ‖v‖ ≤ R →
    (C.labels.level d).coeffSize (twist C v s) ≤ b := by
  let f (s : Signed × Bool) (v : C.label d) := (C.labels.level d).coeffSize (twist C v s)
  have hf (s : Signed × Bool) : Continuous (f s) := by
    have ht : Continuous ((C.labels.level d).act s.1.ortho) := LinearMap.continuous_of_finiteDimensional _
    have he : Continuous fun v : C.label d => twist C v s := by unfold twist; split <;> fun_prop
    unfold f Labels.Frame.coeffSize; fun_prop
  choose b hb using fun s => (isCompact_closedBall (0:C.label d) R).bddAbove_image (hf s).continuousOn
  obtain ⟨r,hr⟩ := Finite.bddAbove_range b
  exact ⟨max 1 r,zero_lt_one.trans_le (le_max_left ..),fun v s h =>
    ((hb s) ⟨v,Metric.mem_closedBall.mpr (by rwa [dist_zero_right]),rfl⟩).trans ((hr ⟨s,rfl⟩).trans (le_max_right ..))⟩

abbrev tiling (C : Family G) (p : ℕ) (h : m ≤ N) := Cells.center C.S p h 0
abbrev allCopies (C : Family G) (p : ℕ) (h : m ≤ N) (v : C.label d) (i : Site (C.side m p)) := twist C v
    (Extraction.Spin.way (tiling C p h) i)

/-- Needed from the trajectory builder (in addition to pricing and `Thick`
at the chosen vacuum startup, and actual one-source `C.Makes`). We ask only
for meshes/periods/tickets at the indicated center queries (legs to i,
N-tail MAY depend on that leg). For the incidence estimate the trajectories
must already be in extracted singleton format, on the real common vacuum
including dormant gas addresses. There is no extraction of a subsequence of
volumes/cutoffs in this port. The same exact arrays must work for every
one-step read and pricing operation on their path (`Unbilled.raw` included).
-/
def Offer (C : Family G) (t : Tariff) := ∀ d (r : ℝ),0<r → ∃ b : ℝ,1≤b ∧ ∀ m i,
    C.ref d ≤ m → Tabs.opens C.path.levels b m i →
    ∀ᶠ N in atTop, ∃ h : m ≤ N, ∀ p, Mix.ticket C b N p m i h → ∀ v : C.label d, ‖v‖ ≤ r →
      ∃ L : Lane C.path (census (Site (C.side m p))) N p,
        Unbilled C L (fun _ => d) (allCopies C p h v) i t ∧
        ∀ j, i ≤ j → j ≤ N → ∀ k,(L.sites j).origins k=Mix.camp C p m j k

lemma ticket_far {b : ℝ} (hb : 1≤b) {j : ℕ} {L : Lane C.path (census (Site (C.side m p))) N p}
    {hm : m≤N} (ht : Mix.ticket C b N p m i hm) (hi : i ≤ j) (hj : j≤N)
    (hp : ∀ k, (L.sites j).origins k=Mix.camp C p m j k) : ∀ x y, x≠y →
    (point C j).B^2 ≤ separation ((L.sites j).origins x) ((L.sites j).origins y) := by
  intro x y hxy; rw [hp,hp]
  have hh := (le_mul_of_one_le_right (sq_nonneg _) hb).trans (ht.2.2 j hi hj x y hxy)
  exact_mod_cast hh

theorem circle_of_offer (hG : G.Simple) (H : C.Makes) (hq : Prepared s t C.localSection C.path.levels)
    (hK : ∀ᶠ N in atTop,∀ p, Thick C N p) (h : Offer C t) (d : ℕ) (r : ℝ) (hr : 0<r) : Mix.Circle C d r := by
  obtain ⟨a,ha,hA⟩ := twist_price C d r
  obtain ⟨b,hb,h⟩ := h d r hr
  refine ⟨a,b,strength C.labels d,ha,hb,fun m i hm hi => ?_⟩
  filter_upwards [eventually_ge_atTop i,hK,h m i hm hi] with N hN hK h
  obtain ⟨hw,h⟩ := h
  refine ⟨hw,fun p ht v hv => ?_⟩
  obtain ⟨L,hL,camps⟩ := h p ht v hv
  let V := Site (C.side m p)
  let u := allCopies C p hw v
  have hs j (he : i≤j) (hh : j≤N) := ticket_far hb ht he hh (camps j he hh)
  have ht' j (he : i≤j) (hh : j≤N) : Occupancy (L.sites j).origins (s.markers (year C j)) := by
    apply fun x => le_trans (b:=1) (Occupancy.of_injective ?_ x) (s.markers_pos _)
    intro x y hx; by_contra! hne; have he := hs j he hh x y hne
    rw [hx] at he; have := (point C j).B_pos; simp at he; omega
  have hg j (he : i≤j) (hh : j≤N) : Fresh univ (census V) (L.sites j).origins (point C j).B :=
    fun _ _ _ _ _ hxy => hs j he hh _ _ hxy
  have hz j := hL.realizes (m:=j) H hq univ (fun _ => ha) (fun s => hA v _ hv) hG ht' hg (hK p) (fun _ => hm.trans hi.1)
  have hu k : L.uses k = (tiling C p hw).copy k (C.O N p v 0) := by
    rw [hL.fields,camps N hN le_rfl,← ht.1,twist_copy _ H _ _ (hm.trans hw)]
  refine ⟨L,hi.1,hN,fun k => ⟨congr_fun hL.load k,hu k⟩,camps,fun j he hh => ?_,hL.reads,hL.first,hL.transforms⟩
  simp only [rate, mem_univ, ↓reduceIte] at hz
  obtain ⟨hu,hS⟩ := hz _ he hh
  have hw : rate C j t (univ : Finset V) (fun _ => d) (fun _ => a) N = fun _ => radius C d a j := by
    funext i; simp [rate]
  rw [hw] at hS
  apply hS.stubs (width_pos _ _ ha _).le ?_ ?_ (hL.active _ he hh) (fun x y hxy => ?_) hu
  · have he := Real.abs_exp_sub_one_le (x:=1) (by rw [abs_one])
    rw [abs_one] at he
    have he := (le_abs_self _).trans he
    have hj : gHat C j ≤ 1/4 := (hq.here j).perturb
    have ht := gHat_pos C j
    nlinarith [mul_le_mul_of_nonneg_right (show Real.exp 1 ≤ 3 by linarith) (sq_nonneg (gHat C j))]
  · have hb := div_le_one_of_le₀ ((pow_le_one₀ (n:=2) (gHat_pos C j).le (gHat_le_one C j)).trans (one_le_two)) zero_le_two
    exact mul_le_one₀ (divisor_le C j) (by positivity) hb
  rw [(H.wilson.represents N p j hh).vac]
  exact ⟨(hq.here j).large, by simpa only [sq] using hs j he hh x y hxy⟩

theorem metered (hG : G.Simple) (H : C.Makes) (hq : Prepared s t C.localSection C.path.levels)
    (hK : ∀ᶠ N in atTop,∀ p,Thick C N p) (h : Offer C t) : Input.Metered C :=
  Bid.installs hG Work.I01.answer Work.I02.answer Work.I03.answer Work.I04.answer H hq.factorial hq.tabs
    (circle_of_offer hG H hq hK h)

theorem centered (hG : G.Simple) (H : C.Makes) (hq : Prepared s t C.localSection C.path.levels)
    (hK : ∀ᶠ N in atTop,∀ p,Thick C N p) (h : Offer C t) : Wcmain C ∧ ∀ f : Extraction.Order,CenterPort C f ∧ CellHyp C f := by
  have ht := (metered hG H hq hK h).rootwise hG hq.tabs
  exact ⟨ht, fun f => ⟨ht.projects C f H, (ht.projects C f H).cells⟩⟩

end YM.Extra.Multi
